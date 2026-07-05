//! Mutual, non-nested inductive admission with recursor generation.
//!
//! Function-for-function port of the oracle's `add_inductive_fn`
//! (src/kernel/inductive.cpp:120-790, pinned githash
//! b4812ae53eea93439ad5dce5a5c26591c31cb697, toolchain
//! leanprover/lean4:v4.32.0-rc1). Each method cites its oracle line
//! range; the `operator()` pipeline order (inductive.cpp:778-789) is
//! preserved exactly:
//!   check_inductive_types → declare_inductive_types → check_constructors
//!   → declare_constructors → init_elim_level → init_k_target
//!   → mk_rec_infos → declare_recursors
//!
//! On success the environment gains an `InductiveVal` per type, a
//! `ConstructorVal` per constructor, and a `RecursorVal` per type, with
//! every metadata field computed exactly as the oracle computes it (the
//! ultimate arbiter is Task 12's structural comparison against decoded
//! oleans).
//!
//! ## Deviations forced by Rust (documented per Task 3/6 precedent)
//!
//! - **Environment ownership.** The oracle's `add_inductive_fn` holds
//!   `m_env` by value (a persistent copy-on-write map) and constructs a
//!   fresh `type_checker(m_env, m_lctx, ...)` whenever it needs to check
//!   (inductive.cpp:171), discarding the whole copy on any error. Rust
//!   cannot let one struct hold both `&mut Environment` and a
//!   `TypeChecker` borrowing it. So `AddInductiveFn` mutates the *real*
//!   environment in place (adding each declaration as the oracle does,
//!   for visibility to later phases' checkers) and, on any failure,
//!   removes every constant it added this call (`Environment::remove_core`
//!   rollback) — restoring the exact pre-admission state (every added
//!   name was fresh, guaranteed by the `check_name` preceding each add).
//!   This avoids a full-map clone per inductive during whole-stdlib
//!   replay.
//! - **Shared local context.** The persistent `m_lctx`/`m_ngen` the
//!   oracle shares with each fresh `type_checker` are held here as owned
//!   `lctx`/`fvar_gen` fields, *moved* into a freshly constructed
//!   `TypeChecker` per checker op (via `TypeChecker::new_with`) and moved
//!   back out (`into_parts`). The `FVarIdGen` counter therefore advances
//!   monotonically across both producers (this struct and the checker's
//!   internal binder fvars), so ids never collide even though both mint
//!   the same `_kernel_fresh.<n>` prefix — the oracle instead uses a
//!   distinct `_ind_fresh` prefix, an equivalent uniqueness guarantee.
//! - **Recursion discipline.** Every genuinely recursive expr/level walk
//!   here (`expr_has_ind_occ`, `is_geq`/`is_geq_core`, `has_loose_bvar`,
//!   `has_loose_bvars_in_domain`, `infer_implicit`) is guarded by a
//!   `RecGuard` (error at the cap, never a stack overflow), because the
//!   inductive's declared types/ctors are decoded from untrusted oleans.
//!   Telescope walks are iterative loops over `LocalContext` fvars.

use std::collections::HashSet;
use std::sync::Arc;

use crate::env::{check_duplicated_univ_params, check_name, check_no_metavar_no_fvar};
use crate::{
    instantiate, BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, Environment, Expr,
    ExprNode, FVarIdGen, InductiveType, InductiveVal, KernelError, Level, LocalContext, Name, Nat,
    RecGuard, RecursorRule, RecursorVal, TypeChecker,
};

// ---------------------------------------------------------------------
// Small name/level/expr helpers (free functions).
// ---------------------------------------------------------------------

/// A single-component `Name` with an `Anonymous` parent.
fn mk_simple_name(s: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: s.to_string(),
    })
}

/// oracle: inductive.cpp:22-24 (`mk_rec_name`) — `I ++ `rec``.
fn mk_rec_name(i: &Arc<Name>) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::clone(i),
        part: "rec".to_string(),
    })
}

/// oracle: level.cpp:530-535 (`lparams_to_levels`).
fn lparams_to_levels(ps: &[Arc<Name>]) -> Vec<Arc<Level>> {
    ps.iter()
        .map(|p| Arc::new(Level::Param(Arc::clone(p))))
        .collect()
}

/// oracle: Init/Meta/Defs.lean:317-320 (`Name.appendAfter`), macro-scope
/// case omitted (kernel-generated names carry no macro scopes):
/// `str p s => mkStr p (s ++ suffix)`, else `mkStr n suffix`.
fn append_after_str(n: &Arc<Name>, suffix: &str) -> Arc<Name> {
    match n.as_ref() {
        Name::Str { parent, part } => Arc::new(Name::Str {
            parent: Arc::clone(parent),
            part: format!("{part}{suffix}"),
        }),
        _ => Arc::new(Name::Str {
            parent: Arc::clone(n),
            part: suffix.to_string(),
        }),
    }
}

/// oracle: Init/Meta/Defs.lean:322-326 (`Name.appendIndexAfter`):
/// `str p s => mkStr p (s ++ "_" ++ toString idx)`, else `mkStr n
/// ("_" ++ toString idx)`.
fn append_index_after(n: &Arc<Name>, idx: usize) -> Arc<Name> {
    match n.as_ref() {
        Name::Str { parent, part } => Arc::new(Name::Str {
            parent: Arc::clone(parent),
            part: format!("{part}_{idx}"),
        }),
        _ => Arc::new(Name::Str {
            parent: Arc::clone(n),
            part: format!("_{idx}"),
        }),
    }
}

/// Suffix component captured while walking a name toward its root.
enum NameComp {
    Str(String),
    Num(Nat),
}

/// oracle: `name::replace_prefix` (util/name.cpp) — replace the `pre`
/// prefix of `n` with `new_pre`, leaving `n` unchanged if `pre` is not a
/// prefix. Iterative (walks the parent chain leaf→root) so it is safe on
/// adversarially deep names.
fn replace_prefix(n: &Arc<Name>, pre: &Arc<Name>, new_pre: &Arc<Name>) -> Arc<Name> {
    let mut comps: Vec<NameComp> = Vec::new();
    let mut cur = Arc::clone(n);
    loop {
        if cur.as_ref() == pre.as_ref() {
            let mut result = Arc::clone(new_pre);
            for c in comps.into_iter().rev() {
                result = match c {
                    NameComp::Str(s) => Arc::new(Name::Str {
                        parent: result,
                        part: s,
                    }),
                    NameComp::Num(v) => Arc::new(Name::Num {
                        parent: result,
                        part: v,
                    }),
                };
            }
            return result;
        }
        match cur.as_ref() {
            Name::Anonymous => return Arc::clone(n),
            Name::Str { parent, part } => {
                comps.push(NameComp::Str(part.clone()));
                let p = Arc::clone(parent);
                cur = p;
            }
            Name::Num { parent, part } => {
                comps.push(NameComp::Num(part.clone()));
                let p = Arc::clone(parent);
                cur = p;
            }
        }
    }
}

/// oracle: Lean/Expr.lean:1740-1747 (`consumeTypeAnnotations`) — strip
/// `optParam`/`autoParam`/`outParam`/`semiOutParam` wrappers. Both the
/// arity-2 (`optParam`/`autoParam`: the annotated type is the FIRST arg)
/// and arity-1 (`outParam`/`semiOutParam`: the sole arg) forms leave
/// `args[0]` as the underlying type, so a single `get_app_args()[0]`
/// serves both. Iterative and structurally decreasing (each step moves
/// to a strict subterm), so it terminates without a guard.
fn consume_type_annotations(e: &Arc<Expr>) -> Arc<Expr> {
    let mut cur = Arc::clone(e);
    loop {
        let fn0 = Expr::get_app_fn(&cur);
        let name = match fn0.const_name() {
            Some(n) => n,
            None => return cur,
        };
        let part = match name.as_ref() {
            Name::Str { parent, part } if matches!(parent.as_ref(), Name::Anonymous) => {
                part.as_str()
            }
            _ => return cur,
        };
        let nargs = Expr::get_app_num_args(&cur);
        let strip = matches!(
            (part, nargs),
            ("optParam", 2) | ("autoParam", 2) | ("outParam", 1) | ("semiOutParam", 1)
        );
        if !strip {
            return cur;
        }
        let args = Expr::get_app_args(&cur);
        cur = Arc::clone(&args[0]);
    }
}

/// oracle: expr.h:39 (`is_explicit(binder_info)`) — only `Default` is
/// explicit.
fn is_explicit_bi(bi: BinderInfo) -> bool {
    matches!(bi, BinderInfo::Default)
}

/// If `e` is a `Π`, return an owned copy of its binder pieces
/// `(name, domain, body, info)`, else `None`. Returning owned `Arc`s
/// (rather than borrowing `e`) lets the telescope-walk loops below use
/// `while let Some(..) = peel_forall(&t)` while still reassigning `t`
/// inside the loop body (the oracle's `while (is_pi(t)) { ...; t = ...; }`
/// idiom).
type ForallParts = (Arc<Name>, Arc<Expr>, Arc<Expr>, BinderInfo);
fn peel_forall(e: &Arc<Expr>) -> Option<ForallParts> {
    match e.node() {
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Some((
            Arc::clone(binder_name),
            Arc::clone(binder_type),
            Arc::clone(body),
            *binder_info,
        )),
        _ => None,
    }
}

/// oracle: expr.cpp:389-409 (`has_loose_bvar`) — does bvar index `i`
/// (adjusted by binder depth) occur loose in `e`? Guarded; short-circuits
/// via the cached exact loose-bvar range.
fn has_loose_bvar(e: &Arc<Expr>, i: u64, g: &mut RecGuard) -> Result<bool, KernelError> {
    if let Some(r) = e.data().loose_bvar_range_exact() {
        if i >= r as u64 {
            return Ok(false);
        }
    }
    match e.node() {
        ExprNode::BVar { idx } => Ok(idx == &Nat::from(i)),
        ExprNode::App { f, arg } => {
            let (f, arg) = (Arc::clone(f), Arc::clone(arg));
            g.enter(|g| Ok(has_loose_bvar(&f, i, g)? || has_loose_bvar(&arg, i, g)?))
        }
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => {
            let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
            g.enter(|g| Ok(has_loose_bvar(&bt, i, g)? || has_loose_bvar(&bd, i + 1, g)?))
        }
        ExprNode::LetE {
            ty, value, body, ..
        } => {
            let (t, v, b) = (Arc::clone(ty), Arc::clone(value), Arc::clone(body));
            g.enter(|g| {
                Ok(has_loose_bvar(&t, i, g)?
                    || has_loose_bvar(&v, i, g)?
                    || has_loose_bvar(&b, i + 1, g)?)
            })
        }
        ExprNode::MData { expr, .. }
        | ExprNode::Proj {
            structure: expr, ..
        } => {
            let inner = Arc::clone(expr);
            g.enter(|g| has_loose_bvar(&inner, i, g))
        }
        _ => Ok(false),
    }
}

/// oracle: expr.cpp:370-387 (`has_loose_bvars_in_domain`). The outer
/// Pi-chain walk is a loop (`vidx+1` per binder); the inner
/// "transitivity" search is a guarded recursion.
fn has_loose_bvars_in_domain(
    b: &Arc<Expr>,
    vidx: u64,
    strict: bool,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    let mut b = Arc::clone(b);
    let mut vidx = vidx;
    loop {
        match b.node() {
            ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } => {
                let bt = Arc::clone(binder_type);
                let body = Arc::clone(body);
                let bi = *binder_info;
                if has_loose_bvar(&bt, vidx, g)? {
                    // oracle:373-378 — the binder's var occurs in this
                    // domain; it forces implicit if the binder is explicit
                    // OR (transitivity) the var recurs in an inner domain.
                    if is_explicit_bi(bi)
                        || g.enter(|g| has_loose_bvars_in_domain(&body, 0, strict, g))?
                    {
                        return Ok(true);
                    }
                }
                b = body;
                vidx += 1;
            }
            _ => {
                if strict {
                    return Ok(false);
                } else {
                    return has_loose_bvar(&b, vidx, g);
                }
            }
        }
    }
}

/// oracle: expr.cpp:480-500 (`infer_implicit`, called with
/// `num_params = unsigned::max`, `strict = true`). Marks each top-level
/// Pi binder implicit iff its variable occurs in a later binder's domain
/// (`has_loose_bvars_in_domain`). Iterative (collects the Pi spine, then
/// rebuilds inside-out) so a long recursor telescope cannot overflow.
fn infer_implicit(t: &Arc<Expr>, g: &mut RecGuard) -> Result<Arc<Expr>, KernelError> {
    let mut binders: Vec<(Arc<Name>, Arc<Expr>, BinderInfo)> = Vec::new();
    let mut cur = Arc::clone(t);
    while let Some((bn, bt, body, bi)) = peel_forall(&cur) {
        binders.push((bn, bt, bi));
        cur = body;
    }
    let mut result = cur;
    for (bn, bt, bi) in binders.into_iter().rev() {
        let new_bi = if !is_explicit_bi(bi) {
            bi
        } else if has_loose_bvars_in_domain(&result, 0, true, g)? {
            BinderInfo::Implicit
        } else {
            bi
        };
        result = Expr::forall_e(bn, bt, result, new_bi);
    }
    Ok(result)
}

/// oracle: inductive.cpp:369-379 (`is_ind_occ`/`has_ind_occ`) — does `e`
/// contain a `Const` whose name is one of the datatypes being declared?
/// (`is_ind_occ` compares names only, ignoring levels.) Guarded walk.
fn expr_has_ind_occ(
    e: &Arc<Expr>,
    names: &HashSet<Arc<Name>>,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    match e.node() {
        ExprNode::Const { name, .. } => Ok(names.contains(name)),
        ExprNode::App { f, arg } => {
            let (f, arg) = (Arc::clone(f), Arc::clone(arg));
            g.enter(|g| Ok(expr_has_ind_occ(&f, names, g)? || expr_has_ind_occ(&arg, names, g)?))
        }
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => {
            let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
            g.enter(|g| Ok(expr_has_ind_occ(&bt, names, g)? || expr_has_ind_occ(&bd, names, g)?))
        }
        ExprNode::LetE {
            ty, value, body, ..
        } => {
            let (t, v, b) = (Arc::clone(ty), Arc::clone(value), Arc::clone(body));
            g.enter(|g| {
                Ok(expr_has_ind_occ(&t, names, g)?
                    || expr_has_ind_occ(&v, names, g)?
                    || expr_has_ind_occ(&b, names, g)?)
            })
        }
        ExprNode::MData { expr, .. }
        | ExprNode::Proj {
            structure: expr, ..
        } => {
            let inner = Arc::clone(expr);
            g.enter(|g| expr_has_ind_occ(&inner, names, g))
        }
        _ => Ok(false),
    }
}

/// oracle: level.cpp:527-528 (`is_geq`) — `is_geq_core(normalize l1,
/// normalize l2)`. Guarded (the whole thing recurses through
/// `is_geq_core`).
fn is_geq(a: &Arc<Level>, b: &Arc<Level>, g: &mut RecGuard) -> Result<bool, KernelError> {
    g.enter(|g| {
        let na = Level::normalize(a, g)?;
        let nb = Level::normalize(b, g)?;
        is_geq_core(&na, &nb, g)
    })
}

/// oracle: level.cpp:508-526 (`is_geq_core`). The `Max(l2)` and
/// `IMax(l2)` arms have identical bodies but the oracle checks them in a
/// specific interleaved order (max(l2), max(l1), imax(l2), imax(l1)) —
/// the `is_max(l1)` check sits *between* them and can short-circuit, so
/// the two arms must NOT be merged.
fn is_geq_core(l1: &Arc<Level>, l2: &Arc<Level>, g: &mut RecGuard) -> Result<bool, KernelError> {
    if Level::structural_eq(l1, l2, g)? || l2.is_zero() {
        return Ok(true);
    }
    if let Level::Max(a, b) = l2.as_ref() {
        return Ok(is_geq(l1, a, g)? && is_geq(l1, b, g)?);
    }
    if let Level::Max(a, b) = l1.as_ref() {
        if is_geq(a, l2, g)? || is_geq(b, l2, g)? {
            return Ok(true);
        }
    }
    if let Level::IMax(a, b) = l2.as_ref() {
        return Ok(is_geq(l1, a, g)? && is_geq(l1, b, g)?);
    }
    if let Level::IMax(_, b) = l1.as_ref() {
        return is_geq(b, l2, g);
    }
    let (b1, k1) = Level::to_offset(l1);
    let (b2, k2) = Level::to_offset(l2);
    if Level::structural_eq(b1, b2, g)? || b2.is_zero() {
        return Ok(k1 >= k2);
    }
    if k1 == k2 && k1 > 0 {
        return is_geq(b1, b2, g);
    }
    Ok(false)
}

// ---------------------------------------------------------------------
// AddInductiveFn state (oracle: inductive.cpp:124-160).
// ---------------------------------------------------------------------

/// oracle: inductive.cpp:150-155 (`struct rec_info`).
struct RecInfo {
    c: Arc<Expr>,
    minors: Vec<Arc<Expr>>,
    indices: Vec<Arc<Expr>>,
    major: Arc<Expr>,
}

struct AddInductiveFn {
    lparams: Vec<Arc<Name>>,
    is_unsafe: bool,
    nnested: Nat,
    nparams: usize,
    ind_types: Vec<InductiveType>,
    guard: RecGuard,
    /// Shared with each freshly-built `TypeChecker` (see module docs).
    lctx: LocalContext,
    fvar_gen: FVarIdGen,
    // Computed by check_inductive_types.
    levels: Vec<Arc<Level>>,
    result_level: Arc<Level>,
    is_not_zero: bool,
    nindices: Vec<usize>,
    params: Vec<Arc<Expr>>,
    ind_cnsts: Vec<Arc<Expr>>,
    ind_names: HashSet<Arc<Name>>,
    // Computed by init_elim_level / init_k_target / mk_rec_infos.
    elim_level: Arc<Level>,
    k_target: bool,
    rec_infos: Vec<RecInfo>,
    /// Names add_core'd this call, for failure rollback (see module docs).
    added: Vec<Arc<Name>>,
}

/// The pipeline entry (oracle: `environment::add_inductive`,
/// inductive.cpp:1116-1123, minus nested-inductive elimination — Task
/// 10). `nnested` is threaded from the caller (0 for the non-nested
/// admissions Task 9 handles).
pub(crate) fn add_inductive(
    env: &mut Environment,
    lparams: Vec<Arc<Name>>,
    nparams: Nat,
    types: Vec<InductiveType>,
    is_unsafe: bool,
    nnested: Nat,
) -> Result<(), KernelError> {
    let name0 = types
        .first()
        .map(|t| Arc::clone(&t.name))
        .unwrap_or_else(|| Arc::new(Name::Anonymous));
    // oracle: inductive.cpp:165-167 — the number of parameters must fit
    // a machine word.
    let nparams_small = match nparams.to_usize() {
        Some(v) => v,
        None => {
            return Err(KernelError::InvalidInductive {
                name: name0,
                what: "too many parameters",
            })
        }
    };
    let mut f = AddInductiveFn::new(lparams, nparams_small, types, is_unsafe, nnested);
    match f.run(env) {
        Ok(()) => Ok(()),
        Err(e) => {
            for n in f.added.iter().rev() {
                env.remove_core(n);
            }
            Err(e)
        }
    }
}

impl AddInductiveFn {
    fn new(
        lparams: Vec<Arc<Name>>,
        nparams: usize,
        ind_types: Vec<InductiveType>,
        is_unsafe: bool,
        nnested: Nat,
    ) -> AddInductiveFn {
        AddInductiveFn {
            lparams,
            is_unsafe,
            nnested,
            nparams,
            ind_types,
            guard: RecGuard::new(),
            lctx: LocalContext::default(),
            fvar_gen: FVarIdGen::default(),
            levels: Vec::new(),
            result_level: Arc::new(Level::Zero),
            is_not_zero: false,
            nindices: Vec::new(),
            params: Vec::new(),
            ind_cnsts: Vec::new(),
            ind_names: HashSet::new(),
            elim_level: Arc::new(Level::Zero),
            k_target: false,
            rec_infos: Vec::new(),
            added: Vec::new(),
        }
    }

    fn name0(&self) -> Arc<Name> {
        self.ind_types
            .first()
            .map(|t| Arc::clone(&t.name))
            .unwrap_or_else(|| Arc::new(Name::Anonymous))
    }

    /// oracle: inductive.cpp:778-789 (`operator()`).
    fn run(&mut self, env: &mut Environment) -> Result<(), KernelError> {
        // Nested inductives (num_nested > 0) are handled by Task 10; until
        // then reject rather than mis-process (the caller passes 0, so this
        // is defensive — no Task 9 corpus exercises it).
        if !self.nnested.is_zero() {
            return Err(KernelError::InvalidInductive {
                name: self.name0(),
                what: "nested inductive",
            });
        }
        check_duplicated_univ_params(&self.lparams)?;
        self.check_inductive_types(env)?;
        self.declare_inductive_types(env)?;
        self.check_constructors(env)?;
        self.declare_constructors(env)?;
        self.init_elim_level(env)?;
        self.init_k_target();
        self.mk_rec_infos(env)?;
        self.declare_recursors(env)?;
        Ok(())
    }

    /// Run a checker op against `env`, sharing this struct's persistent
    /// local context / fvar generator (see module docs).
    fn run_tc<R>(
        &mut self,
        env: &Environment,
        f: impl FnOnce(&mut TypeChecker<'_>) -> Result<R, KernelError>,
    ) -> Result<R, KernelError> {
        let lctx = std::mem::take(&mut self.lctx);
        let fvar_gen = std::mem::take(&mut self.fvar_gen);
        let mut tc = TypeChecker::new_with(env, lctx, fvar_gen);
        let r = f(&mut tc);
        let (lctx, fvar_gen) = tc.into_parts();
        self.lctx = lctx;
        self.fvar_gen = fvar_gen;
        r
    }

    /// oracle: inductive.cpp:178-180 (`mk_local_decl`) — the `cdecl`
    /// overload, consuming leading type annotations on the domain.
    fn mk_local(&mut self, name: &Arc<Name>, ty: &Arc<Expr>, bi: BinderInfo) -> Arc<Expr> {
        let t = consume_type_annotations(ty);
        self.lctx.mk_local_decl(&mut self.fvar_gen, name, t, bi)
    }

    /// oracle: inductive.cpp:174-176 (`get_param_type`).
    fn get_param_type(&self, i: usize) -> Arc<Expr> {
        match self.params[i].node() {
            // `params` holds only fvars produced by `mk_local`, always
            // declared in `lctx`: an internal-contract invariant (same
            // precedent as local_ctx.rs's documented panics), not
            // untrusted input.
            ExprNode::FVar { id } => Arc::clone(
                &self
                    .lctx
                    .get(id)
                    .expect("param fvar declared in local context")
                    .ty,
            ),
            _ => unreachable!("params contains only fvars"),
        }
    }

    fn has_ind_occ(&mut self, e: &Arc<Expr>) -> Result<bool, KernelError> {
        expr_has_ind_occ(e, &self.ind_names, &mut self.guard)
    }

    fn add(&mut self, env: &mut Environment, info: ConstantInfo) {
        self.added.push(Arc::clone(info.name()));
        env.add_core(info);
    }

    /// oracle: inductive.cpp:211-262 (`check_inductive_types`).
    fn check_inductive_types(&mut self, env: &Environment) -> Result<(), KernelError> {
        self.levels = lparams_to_levels(&self.lparams);
        let lparams = self.lparams.clone();
        let ntypes = self.ind_types.len();
        let mut first = true;
        for idx in 0..ntypes {
            let ind_name = Arc::clone(&self.ind_types[idx].name);
            let type0 = Arc::clone(&self.ind_types[idx].ty);
            check_name(env, &ind_name)?;
            check_name(env, &mk_rec_name(&ind_name))?;
            check_no_metavar_no_fvar(&ind_name, &type0)?;
            {
                let type_c = Arc::clone(&type0);
                let lp = lparams.clone();
                self.run_tc(env, move |tc| {
                    tc.check(&type_c, &lp)?;
                    Ok(())
                })?;
            }
            self.nindices.push(0);
            let mut i = 0usize;
            let type_c = Arc::clone(&type0);
            let mut ty = self.run_tc(env, move |tc| tc.whnf(&type_c))?;
            while let Some((bn, bt, body, bi)) = peel_forall(&ty) {
                if i < self.nparams {
                    if first {
                        let param = self.mk_local(&bn, &bt, bi);
                        self.params.push(Arc::clone(&param));
                        ty = instantiate(&body, &param, &mut self.guard)?;
                    } else {
                        let pt = self.get_param_type(i);
                        let bt_c = Arc::clone(&bt);
                        let eq = self.run_tc(env, move |tc| tc.is_def_eq(&bt_c, &pt))?;
                        if !eq {
                            return Err(KernelError::InvalidInductive {
                                name: ind_name,
                                what: "parameters must match",
                            });
                        }
                        let p_i = Arc::clone(&self.params[i]);
                        ty = instantiate(&body, &p_i, &mut self.guard)?;
                    }
                    i += 1;
                } else {
                    let local = self.mk_local(&bn, &bt, bi);
                    ty = instantiate(&body, &local, &mut self.guard)?;
                    *self.nindices.last_mut().unwrap() += 1;
                }
                let ty_c = Arc::clone(&ty);
                ty = self.run_tc(env, move |tc| tc.whnf(&ty_c))?;
            }
            if i != self.nparams {
                return Err(KernelError::InvalidInductive {
                    name: ind_name,
                    what: "number of parameters mismatch",
                });
            }
            let ty_c = Arc::clone(&ty);
            let sort_expr = self.run_tc(env, move |tc| tc.ensure_sort(&ty_c))?;
            let lvl = match sort_expr.node() {
                ExprNode::Sort { level } => Arc::clone(level),
                _ => return Err(KernelError::TypeExpected),
            };
            if first {
                self.result_level = Arc::clone(&lvl);
                self.is_not_zero = Level::is_never_zero(&lvl, &mut self.guard)?;
            } else {
                let eq = Level::is_equivalent(&lvl, &self.result_level, &mut self.guard)?;
                if !eq {
                    return Err(KernelError::InvalidInductive {
                        name: ind_name,
                        what: "mutually inductive types must live in the same universe",
                    });
                }
            }
            let cnst = Expr::const_(Arc::clone(&ind_name), self.levels.clone(), &mut self.guard)?;
            self.ind_cnsts.push(cnst);
            self.ind_names.insert(Arc::clone(&ind_name));
            first = false;
        }
        Ok(())
    }

    /// oracle: inductive.cpp:264-286 (`is_rec`).
    fn is_rec(&mut self) -> Result<bool, KernelError> {
        for idx in 0..self.ind_types.len() {
            for c in 0..self.ind_types[idx].ctors.len() {
                let mut t = Arc::clone(&self.ind_types[idx].ctors[c].1);
                while let Some((_, dom, body, _)) = peel_forall(&t) {
                    if self.has_ind_occ(&dom)? {
                        return Ok(true);
                    }
                    t = body;
                }
            }
        }
        Ok(false)
    }

    /// oracle: inductive.cpp:294-309 (`is_reflexive`).
    fn is_reflexive(&mut self) -> Result<bool, KernelError> {
        for idx in 0..self.ind_types.len() {
            for c in 0..self.ind_types[idx].ctors.len() {
                let mut t = Arc::clone(&self.ind_types[idx].ctors[c].1);
                while let Some((bn, bt, body, bi)) = peel_forall(&t) {
                    if matches!(bt.node(), ExprNode::ForallE { .. }) && self.has_ind_occ(&bt)? {
                        return Ok(true);
                    }
                    let local = self.mk_local(&bn, &bt, bi);
                    t = instantiate(&body, &local, &mut self.guard)?;
                }
            }
        }
        Ok(false)
    }

    /// oracle: inductive.cpp:317-332 (`declare_inductive_types`). `is_rec`
    /// and `is_reflexive` are computed here (as the oracle does, right
    /// before declaring), then stored on every `inductive_val`.
    fn declare_inductive_types(&mut self, env: &mut Environment) -> Result<(), KernelError> {
        let rec = self.is_rec()?;
        let reflexive = self.is_reflexive()?;
        let all: Vec<Arc<Name>> = self.ind_types.iter().map(|t| Arc::clone(&t.name)).collect();
        for idx in 0..self.ind_types.len() {
            let n = Arc::clone(&self.ind_types[idx].name);
            let ty = Arc::clone(&self.ind_types[idx].ty);
            let ctors: Vec<Arc<Name>> = self.ind_types[idx]
                .ctors
                .iter()
                .map(|(cn, _)| Arc::clone(cn))
                .collect();
            check_name(env, &n)?;
            let val = InductiveVal {
                val: ConstantVal {
                    name: Arc::clone(&n),
                    level_params: self.lparams.clone(),
                    ty,
                },
                num_params: Nat::from(self.nparams as u64),
                num_indices: Nat::from(self.nindices[idx] as u64),
                all: all.clone(),
                ctors,
                num_nested: self.nnested.clone(),
                is_rec: rec,
                is_unsafe: self.is_unsafe,
                is_reflexive: reflexive,
            };
            self.add(env, ConstantInfo::Induct(val));
        }
        Ok(())
    }

    /// oracle: inductive.cpp:338-357 (`is_valid_ind_app(t, i)`).
    fn is_valid_ind_app_i(&mut self, t: &Arc<Expr>, i: usize) -> Result<bool, KernelError> {
        let head = Arc::clone(Expr::get_app_fn(t));
        let args = Expr::get_app_args(t);
        if !Expr::structural_eq(&head, &self.ind_cnsts[i], &mut self.guard)? {
            return Ok(false);
        }
        if args.len() != self.nparams + self.nindices[i] {
            return Ok(false);
        }
        for (p, a) in self.params.iter().zip(args.iter()).take(self.nparams) {
            if !Expr::structural_eq(p, a, &mut self.guard)? {
                return Ok(false);
            }
        }
        for arg in args.iter().skip(self.nparams) {
            if self.has_ind_occ(arg)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// oracle: inductive.cpp:359-366 (`is_valid_ind_app(t)`).
    fn is_valid_ind_app(&mut self, t: &Arc<Expr>) -> Result<Option<usize>, KernelError> {
        for i in 0..self.ind_types.len() {
            if self.is_valid_ind_app_i(t, i)? {
                return Ok(Some(i));
            }
        }
        Ok(None)
    }

    /// oracle: inductive.cpp:383-390 (`is_rec_argument`) — whnf, peel the
    /// Pi telescope (whnf-ing each codomain), then `is_valid_ind_app`.
    fn is_rec_argument(
        &mut self,
        env: &Environment,
        t: &Arc<Expr>,
    ) -> Result<Option<usize>, KernelError> {
        let t_c = Arc::clone(t);
        let mut t = self.run_tc(env, move |tc| tc.whnf(&t_c))?;
        while let Some((bn, bt, body, bi)) = peel_forall(&t) {
            let local = self.mk_local(&bn, &bt, bi);
            let inst = instantiate(&body, &local, &mut self.guard)?;
            t = self.run_tc(env, move |tc| tc.whnf(&inst))?;
        }
        self.is_valid_ind_app(&t)
    }

    /// oracle: inductive.cpp:393-409 (`check_positivity`). The oracle's
    /// tail recursion on the Pi codomain is flattened into a loop; the
    /// two error cases map to `InvalidInductive` (`positivity` for a
    /// non-positive domain occurrence, `invalid occurrence` otherwise).
    fn check_positivity(
        &mut self,
        env: &Environment,
        t: &Arc<Expr>,
        cnstr_name: &Arc<Name>,
    ) -> Result<(), KernelError> {
        let t_c = Arc::clone(t);
        let mut t = self.run_tc(env, move |tc| tc.whnf(&t_c))?;
        loop {
            if !self.has_ind_occ(&t)? {
                return Ok(()); // nonrecursive argument
            }
            match t.node() {
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    let (bn, bt, body, bi) = (
                        Arc::clone(binder_name),
                        Arc::clone(binder_type),
                        Arc::clone(body),
                        *binder_info,
                    );
                    if self.has_ind_occ(&bt)? {
                        return Err(KernelError::InvalidInductive {
                            name: Arc::clone(cnstr_name),
                            what: "positivity",
                        });
                    }
                    let local = self.mk_local(&bn, &bt, bi);
                    let inst = instantiate(&body, &local, &mut self.guard)?;
                    t = self.run_tc(env, move |tc| tc.whnf(&inst))?;
                }
                _ => {
                    if self.is_valid_ind_app(&t)?.is_some() {
                        return Ok(()); // recursive argument
                    } else {
                        return Err(KernelError::InvalidInductive {
                            name: Arc::clone(cnstr_name),
                            what: "invalid occurrence",
                        });
                    }
                }
            }
        }
    }

    /// oracle: inductive.cpp:413-453 (`check_constructors`).
    fn check_constructors(&mut self, env: &Environment) -> Result<(), KernelError> {
        let lparams = self.lparams.clone();
        for idx in 0..self.ind_types.len() {
            let mut found: HashSet<Arc<Name>> = HashSet::new();
            for c in 0..self.ind_types[idx].ctors.len() {
                let n = Arc::clone(&self.ind_types[idx].ctors[c].0);
                let t0 = Arc::clone(&self.ind_types[idx].ctors[c].1);
                if found.contains(&n) {
                    return Err(KernelError::InvalidInductive {
                        name: n,
                        what: "duplicate constructor",
                    });
                }
                found.insert(Arc::clone(&n));
                check_name(env, &n)?;
                check_no_metavar_no_fvar(&n, &t0)?;
                {
                    let t_c = Arc::clone(&t0);
                    let lp = lparams.clone();
                    self.run_tc(env, move |tc| {
                        tc.check(&t_c, &lp)?;
                        Ok(())
                    })?;
                }
                let mut t = t0;
                let mut i = 0usize;
                while let Some((bn, bt, body, bi)) = peel_forall(&t) {
                    if i < self.nparams {
                        let pt = self.get_param_type(i);
                        let bt_c = Arc::clone(&bt);
                        let eq = self.run_tc(env, move |tc| tc.is_def_eq(&bt_c, &pt))?;
                        if !eq {
                            return Err(KernelError::InvalidInductive {
                                name: n,
                                what: "constructor parameter mismatch",
                            });
                        }
                        let p_i = Arc::clone(&self.params[i]);
                        t = instantiate(&body, &p_i, &mut self.guard)?;
                    } else {
                        // ensure_type(binding_domain(t)) = ensure_sort(infer(dom)).
                        let bt_c = Arc::clone(&bt);
                        let s = self.run_tc(env, move |tc| {
                            let ty = tc.infer_type(&bt_c)?;
                            tc.ensure_sort(&ty)
                        })?;
                        let s_level = match s.node() {
                            ExprNode::Sort { level } => Arc::clone(level),
                            _ => return Err(KernelError::TypeExpected),
                        };
                        // oracle:439 — level <= inductive level OR the
                        // inductive is a Prop (result level zero).
                        let ok = is_geq(&self.result_level, &s_level, &mut self.guard)?
                            || self.result_level.is_zero();
                        if !ok {
                            return Err(KernelError::InvalidInductive {
                                name: n,
                                what: "universe too small",
                            });
                        }
                        if !self.is_unsafe {
                            self.check_positivity(env, &bt, &n)?;
                        }
                        let local = self.mk_local(&bn, &bt, bi);
                        t = instantiate(&body, &local, &mut self.guard)?;
                    }
                    i += 1;
                }
                if !self.is_valid_ind_app_i(&t, idx)? {
                    return Err(KernelError::InvalidInductive {
                        name: n,
                        what: "invalid return type",
                    });
                }
            }
        }
        Ok(())
    }

    /// oracle: inductive.cpp:456-476 (`declare_constructors`).
    fn declare_constructors(&mut self, env: &mut Environment) -> Result<(), KernelError> {
        for idx in 0..self.ind_types.len() {
            let ind_name = Arc::clone(&self.ind_types[idx].name);
            // `cidx` is the constructor index within this type — exactly
            // the loop counter `c` (oracle's `cidx++`, inductive.cpp:473).
            for c in 0..self.ind_types[idx].ctors.len() {
                let n = Arc::clone(&self.ind_types[idx].ctors[c].0);
                let t = Arc::clone(&self.ind_types[idx].ctors[c].1);
                let mut arity = 0usize;
                let mut it = Arc::clone(&t);
                while let Some((_, _, body, _)) = peel_forall(&it) {
                    it = body;
                    arity += 1;
                }
                // arity >= nparams is guaranteed by check_constructors.
                let nfields = arity.saturating_sub(self.nparams);
                check_name(env, &n)?;
                let val = ConstructorVal {
                    val: ConstantVal {
                        name: Arc::clone(&n),
                        level_params: self.lparams.clone(),
                        ty: t,
                    },
                    induct: Arc::clone(&ind_name),
                    cidx: Nat::from(c as u64),
                    num_params: Nat::from(self.nparams as u64),
                    num_fields: Nat::from(nfields as u64),
                    is_unsafe: self.is_unsafe,
                };
                self.add(env, ConstantInfo::Ctor(val));
            }
        }
        Ok(())
    }

    /// oracle: inductive.cpp:479-534 (`elim_only_at_universe_zero`).
    fn elim_only_at_universe_zero(&mut self, env: &Environment) -> Result<bool, KernelError> {
        if self.is_not_zero {
            return Ok(false);
        }
        if self.ind_types.len() > 1 {
            return Ok(true);
        }
        let num_intros = self.ind_types[0].ctors.len();
        if num_intros > 1 {
            return Ok(true);
        }
        if num_intros == 0 {
            return Ok(false);
        }
        // Exactly one constructor.
        let mut ty = Arc::clone(&self.ind_types[0].ctors[0].1);
        let mut i = 0usize;
        let mut to_check: Vec<Arc<Expr>> = Vec::new();
        while let Some((bn, bt, body, bi)) = peel_forall(&ty) {
            let fvar = self.mk_local(&bn, &bt, bi);
            if i >= self.nparams {
                let bt_c = Arc::clone(&bt);
                let s = self.run_tc(env, move |tc| {
                    let ty = tc.infer_type(&bt_c)?;
                    tc.ensure_sort(&ty)
                })?;
                let is_zero = match s.node() {
                    ExprNode::Sort { level } => level.is_zero(),
                    _ => false,
                };
                if !is_zero {
                    to_check.push(Arc::clone(&fvar));
                }
            }
            ty = instantiate(&body, &fvar, &mut self.guard)?;
            i += 1;
        }
        let result_args = Expr::get_app_args(&ty);
        for arg in &to_check {
            let mut found = false;
            for ra in &result_args {
                if Expr::structural_eq(arg, ra, &mut self.guard)? {
                    found = true;
                    break;
                }
            }
            if !found {
                return Ok(true); // condition 2 failed
            }
        }
        Ok(false)
    }

    /// oracle: inductive.cpp:536-549 (`init_elim_level`).
    fn init_elim_level(&mut self, env: &Environment) -> Result<(), KernelError> {
        if self.elim_only_at_universe_zero(env)? {
            self.elim_level = Arc::new(Level::Zero);
        } else {
            let mut u = mk_simple_name("u");
            let mut i = 1usize;
            while self.lparams.iter().any(|p| p.as_ref() == u.as_ref()) {
                u = append_index_after(&mk_simple_name("u"), i);
                i += 1;
            }
            self.elim_level = Arc::new(Level::Param(u));
        }
        Ok(())
    }

    /// oracle: inductive.cpp:551-573 (`init_K_target`).
    fn init_k_target(&mut self) {
        self.k_target = self.ind_types.len() == 1
            && self.result_level.is_zero()
            && self.ind_types[0].ctors.len() == 1;
        if !self.k_target {
            return;
        }
        let mut it = Arc::clone(&self.ind_types[0].ctors[0].1);
        let mut i = 0usize;
        while let Some((_, _, body, _)) = peel_forall(&it) {
            if i < self.nparams {
                it = body;
            } else {
                self.k_target = false;
                break;
            }
            i += 1;
        }
    }

    /// oracle: inductive.cpp:578-586 (`get_I_indices`).
    fn get_i_indices(
        &mut self,
        t: &Arc<Expr>,
        indices: &mut Vec<Arc<Expr>>,
    ) -> Result<usize, KernelError> {
        let r = match self.is_valid_ind_app(t)? {
            Some(r) => r,
            None => {
                return Err(KernelError::InvalidInductive {
                    name: self.name0(),
                    what: "invalid recursor argument",
                })
            }
        };
        let all_args = Expr::get_app_args(t);
        for arg in all_args.iter().skip(self.nparams) {
            indices.push(Arc::clone(arg));
        }
        Ok(r)
    }

    /// oracle: inductive.cpp:588-674 (`mk_rec_infos`).
    fn mk_rec_infos(&mut self, env: &Environment) -> Result<(), KernelError> {
        let ntypes = self.ind_types.len();
        // Phase 1: motive `C`, indices, and major premise per type.
        for d_idx in 0..ntypes {
            let type0 = Arc::clone(&self.ind_types[d_idx].ty);
            let mut indices: Vec<Arc<Expr>> = Vec::new();
            let mut i = 0usize;
            let t_c = Arc::clone(&type0);
            let mut t = self.run_tc(env, move |tc| tc.whnf(&t_c))?;
            while let Some((bn, bt, body, bi)) = peel_forall(&t) {
                if i < self.nparams {
                    let p_i = Arc::clone(&self.params[i]);
                    t = instantiate(&body, &p_i, &mut self.guard)?;
                } else {
                    let idxv = self.mk_local(&bn, &bt, bi);
                    indices.push(Arc::clone(&idxv));
                    t = instantiate(&body, &idxv, &mut self.guard)?;
                }
                i += 1;
                let t_c = Arc::clone(&t);
                t = self.run_tc(env, move |tc| tc.whnf(&t_c))?;
            }
            // major : `I params indices`.
            let mut major_ty = Arc::clone(&self.ind_cnsts[d_idx]);
            for p in &self.params {
                major_ty = Expr::app(major_ty, Arc::clone(p));
            }
            for ix in &indices {
                major_ty = Expr::app(major_ty, Arc::clone(ix));
            }
            let major = self.mk_local(&mk_simple_name("t"), &major_ty, BinderInfo::Default);
            // C_ty = Π indices, Π major, Sort elim_level.
            let sort = Expr::sort(Arc::clone(&self.elim_level), &mut self.guard)?;
            let c_ty = {
                let mut fvars = indices.clone();
                fvars.push(Arc::clone(&major));
                self.lctx.mk_pi(&fvars, &sort, &mut self.guard)?
            };
            let c_name = if ntypes > 1 {
                append_index_after(&mk_simple_name("motive"), d_idx + 1)
            } else {
                mk_simple_name("motive")
            };
            let c = self.mk_local(&c_name, &c_ty, BinderInfo::Default);
            self.rec_infos.push(RecInfo {
                c,
                minors: Vec::new(),
                indices,
                major,
            });
        }
        // Phase 2: minor premises.
        for d_idx in 0..ntypes {
            let ind_type_name = Arc::clone(&self.ind_types[d_idx].name);
            for c in 0..self.ind_types[d_idx].ctors.len() {
                let cnstr_name = Arc::clone(&self.ind_types[d_idx].ctors[c].0);
                let cnstr_ty = Arc::clone(&self.ind_types[d_idx].ctors[c].1);
                let mut b_u: Vec<Arc<Expr>> = Vec::new();
                let mut u: Vec<Arc<Expr>> = Vec::new();
                let mut t = cnstr_ty;
                let mut i = 0usize;
                while let Some((bn, bt, body, bi)) = peel_forall(&t) {
                    if i < self.nparams {
                        let p_i = Arc::clone(&self.params[i]);
                        t = instantiate(&body, &p_i, &mut self.guard)?;
                    } else {
                        let l = self.mk_local(&bn, &bt, bi);
                        b_u.push(Arc::clone(&l));
                        if self.is_rec_argument(env, &bt)?.is_some() {
                            u.push(Arc::clone(&l));
                        }
                        t = instantiate(&body, &l, &mut self.guard)?;
                    }
                    i += 1;
                }
                let mut it_indices: Vec<Arc<Expr>> = Vec::new();
                let it_idx = self.get_i_indices(&t, &mut it_indices)?;
                let mut c_app = Arc::clone(&self.rec_infos[it_idx].c);
                for ix in &it_indices {
                    c_app = Expr::app(c_app, Arc::clone(ix));
                }
                let cnstr_const = Expr::const_(
                    Arc::clone(&cnstr_name),
                    self.levels.clone(),
                    &mut self.guard,
                )?;
                let mut intro_app = cnstr_const;
                for p in &self.params {
                    intro_app = Expr::app(intro_app, Arc::clone(p));
                }
                for x in &b_u {
                    intro_app = Expr::app(intro_app, Arc::clone(x));
                }
                c_app = Expr::app(c_app, intro_app);
                // Induction hypotheses `v`, one per recursive argument `u_i`.
                let mut v: Vec<Arc<Expr>> = Vec::new();
                for u_i in u.clone() {
                    let u_i_c = Arc::clone(&u_i);
                    let mut u_i_ty = self.run_tc(env, move |tc| {
                        let ty = tc.infer_type(&u_i_c)?;
                        tc.whnf(&ty)
                    })?;
                    let mut xs: Vec<Arc<Expr>> = Vec::new();
                    while let Some((bn, bt, body, bi)) = peel_forall(&u_i_ty) {
                        let x = self.mk_local(&bn, &bt, bi);
                        xs.push(Arc::clone(&x));
                        let inst = instantiate(&body, &x, &mut self.guard)?;
                        u_i_ty = self.run_tc(env, move |tc| tc.whnf(&inst))?;
                    }
                    let mut it_indices2: Vec<Arc<Expr>> = Vec::new();
                    let it_idx2 = self.get_i_indices(&u_i_ty, &mut it_indices2)?;
                    let mut c_app2 = Arc::clone(&self.rec_infos[it_idx2].c);
                    for ix in &it_indices2 {
                        c_app2 = Expr::app(c_app2, Arc::clone(ix));
                    }
                    let mut u_app = Arc::clone(&u_i);
                    for x in &xs {
                        u_app = Expr::app(u_app, Arc::clone(x));
                    }
                    c_app2 = Expr::app(c_app2, u_app);
                    let v_i_ty = self.lctx.mk_pi(&xs, &c_app2, &mut self.guard)?;
                    let user_name = match u_i.node() {
                        ExprNode::FVar { id } => Arc::clone(
                            &self
                                .lctx
                                .get(id)
                                .expect("recursive-arg fvar declared")
                                .binder_name,
                        ),
                        _ => unreachable!("u holds only fvars"),
                    };
                    let v_i_name = append_after_str(&user_name, "_ih");
                    let v_i = self.mk_local(&v_i_name, &v_i_ty, BinderInfo::Default);
                    v.push(v_i);
                }
                let minor_ty = {
                    let inner = self.lctx.mk_pi(&v, &c_app, &mut self.guard)?;
                    self.lctx.mk_pi(&b_u, &inner, &mut self.guard)?
                };
                let minor_name =
                    replace_prefix(&cnstr_name, &ind_type_name, &Arc::new(Name::Anonymous));
                let minor = self.mk_local(&minor_name, &minor_ty, BinderInfo::Default);
                self.rec_infos[d_idx].minors.push(minor);
            }
        }
        Ok(())
    }

    /// oracle: inductive.cpp:677-682 (`get_rec_levels`).
    fn get_rec_levels(&self) -> Vec<Arc<Level>> {
        if matches!(self.elim_level.as_ref(), Level::Param(_)) {
            let mut ls = vec![Arc::clone(&self.elim_level)];
            ls.extend(self.levels.iter().cloned());
            ls
        } else {
            self.levels.clone()
        }
    }

    /// oracle: inductive.cpp:685-690 (`get_rec_lparams`).
    fn get_rec_lparams(&self) -> Vec<Arc<Name>> {
        if let Level::Param(u) = self.elim_level.as_ref() {
            let mut ps = vec![Arc::clone(u)];
            ps.extend(self.lparams.iter().cloned());
            ps
        } else {
            self.lparams.clone()
        }
    }

    /// oracle: inductive.cpp:693-697 (`collect_Cs`).
    fn collect_cs(&self) -> Vec<Arc<Expr>> {
        (0..self.ind_types.len())
            .map(|i| Arc::clone(&self.rec_infos[i].c))
            .collect()
    }

    /// oracle: inductive.cpp:699-703 (`collect_minor_premises`).
    fn collect_minors(&self) -> Vec<Arc<Expr>> {
        let mut ms = Vec::new();
        for i in 0..self.ind_types.len() {
            ms.extend(self.rec_infos[i].minors.iter().cloned());
        }
        ms
    }

    /// oracle: inductive.cpp:705-749 (`mk_rec_rules`).
    fn mk_rec_rules(
        &mut self,
        env: &Environment,
        d_idx: usize,
        cs: &[Arc<Expr>],
        minors: &[Arc<Expr>],
        minor_idx: &mut usize,
    ) -> Result<Vec<RecursorRule>, KernelError> {
        let lvls = self.get_rec_levels();
        let params = self.params.clone();
        let mut rules = Vec::new();
        for c in 0..self.ind_types[d_idx].ctors.len() {
            let cnstr_name = Arc::clone(&self.ind_types[d_idx].ctors[c].0);
            let cnstr_ty = Arc::clone(&self.ind_types[d_idx].ctors[c].1);
            let mut b_u: Vec<Arc<Expr>> = Vec::new();
            let mut u: Vec<Arc<Expr>> = Vec::new();
            let mut t = cnstr_ty;
            let mut i = 0usize;
            while let Some((bn, bt, body, bi)) = peel_forall(&t) {
                if i < self.nparams {
                    let p_i = Arc::clone(&self.params[i]);
                    t = instantiate(&body, &p_i, &mut self.guard)?;
                } else {
                    let l = self.mk_local(&bn, &bt, bi);
                    b_u.push(Arc::clone(&l));
                    if self.is_rec_argument(env, &bt)?.is_some() {
                        u.push(Arc::clone(&l));
                    }
                    t = instantiate(&body, &l, &mut self.guard)?;
                }
                i += 1;
            }
            // Recursive calls `v`, one per recursive argument `u_i`.
            let mut v: Vec<Arc<Expr>> = Vec::new();
            for u_i in u.clone() {
                let u_i_c = Arc::clone(&u_i);
                let mut u_i_ty = self.run_tc(env, move |tc| {
                    let ty = tc.infer_type(&u_i_c)?;
                    tc.whnf(&ty)
                })?;
                let mut xs: Vec<Arc<Expr>> = Vec::new();
                while let Some((bn, bt, body, bi)) = peel_forall(&u_i_ty) {
                    let x = self.mk_local(&bn, &bt, bi);
                    xs.push(Arc::clone(&x));
                    let inst = instantiate(&body, &x, &mut self.guard)?;
                    u_i_ty = self.run_tc(env, move |tc| tc.whnf(&inst))?;
                }
                let mut it_indices: Vec<Arc<Expr>> = Vec::new();
                let it_idx = self.get_i_indices(&u_i_ty, &mut it_indices)?;
                let rec_name = mk_rec_name(&self.ind_types[it_idx].name);
                let rec_const = Expr::const_(rec_name, lvls.clone(), &mut self.guard)?;
                let mut rec_app = rec_const;
                for p in &params {
                    rec_app = Expr::app(rec_app, Arc::clone(p));
                }
                for cc in cs {
                    rec_app = Expr::app(rec_app, Arc::clone(cc));
                }
                for mm in minors {
                    rec_app = Expr::app(rec_app, Arc::clone(mm));
                }
                for ix in &it_indices {
                    rec_app = Expr::app(rec_app, Arc::clone(ix));
                }
                let mut u_app = Arc::clone(&u_i);
                for x in &xs {
                    u_app = Expr::app(u_app, Arc::clone(x));
                }
                rec_app = Expr::app(rec_app, u_app);
                let lam = self.lctx.mk_lambda(&xs, &rec_app, &mut self.guard)?;
                v.push(lam);
            }
            // e_app = (minor b_u) v.
            let mut e_app = Arc::clone(&minors[*minor_idx]);
            for x in &b_u {
                e_app = Expr::app(e_app, Arc::clone(x));
            }
            for vi in &v {
                e_app = Expr::app(e_app, Arc::clone(vi));
            }
            // comp_rhs = λ params, λ Cs, λ minors, λ b_u, e_app.
            let comp_rhs = {
                let l1 = self.lctx.mk_lambda(&b_u, &e_app, &mut self.guard)?;
                let l2 = self.lctx.mk_lambda(minors, &l1, &mut self.guard)?;
                let l3 = self.lctx.mk_lambda(cs, &l2, &mut self.guard)?;
                self.lctx.mk_lambda(&params, &l3, &mut self.guard)?
            };
            rules.push(RecursorRule {
                ctor: cnstr_name,
                nfields: Nat::from(b_u.len() as u64),
                rhs: comp_rhs,
            });
            *minor_idx += 1;
        }
        Ok(rules)
    }

    /// oracle: inductive.cpp:752-776 (`declare_recursors`).
    fn declare_recursors(&mut self, env: &mut Environment) -> Result<(), KernelError> {
        let cs = self.collect_cs();
        let minors = self.collect_minors();
        let nminors = minors.len();
        let nmotives = cs.len();
        let all: Vec<Arc<Name>> = self.ind_types.iter().map(|t| Arc::clone(&t.name)).collect();
        let params = self.params.clone();
        let mut minor_idx = 0usize;
        for d_idx in 0..self.ind_types.len() {
            let (c, indices, major) = {
                let info = &self.rec_infos[d_idx];
                (
                    Arc::clone(&info.c),
                    info.indices.clone(),
                    Arc::clone(&info.major),
                )
            };
            // C_app = C indices major.
            let mut c_app = c;
            for ix in &indices {
                c_app = Expr::app(c_app, Arc::clone(ix));
            }
            c_app = Expr::app(c_app, Arc::clone(&major));
            // rec_ty = Π params, Π Cs, Π minors, Π indices, Π major, C_app.
            let mut rec_ty =
                self.lctx
                    .mk_pi(std::slice::from_ref(&major), &c_app, &mut self.guard)?;
            rec_ty = self.lctx.mk_pi(&indices, &rec_ty, &mut self.guard)?;
            rec_ty = self.lctx.mk_pi(&minors, &rec_ty, &mut self.guard)?;
            rec_ty = self.lctx.mk_pi(&cs, &rec_ty, &mut self.guard)?;
            rec_ty = self.lctx.mk_pi(&params, &rec_ty, &mut self.guard)?;
            let rec_ty = infer_implicit(&rec_ty, &mut self.guard)?;
            let rules = self.mk_rec_rules(env, d_idx, &cs, &minors, &mut minor_idx)?;
            let rec_name = mk_rec_name(&self.ind_types[d_idx].name);
            let rec_lparams = self.get_rec_lparams();
            check_name(env, &rec_name)?;
            let val = RecursorVal {
                val: ConstantVal {
                    name: Arc::clone(&rec_name),
                    level_params: rec_lparams,
                    ty: rec_ty,
                },
                all: all.clone(),
                num_params: Nat::from(self.nparams as u64),
                num_indices: Nat::from(self.nindices[d_idx] as u64),
                num_motives: Nat::from(nmotives as u64),
                num_minors: Nat::from(nminors as u64),
                rules,
                k: self.k_target,
                is_unsafe: self.is_unsafe,
            };
            self.add(env, ConstantInfo::Rec(val));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
