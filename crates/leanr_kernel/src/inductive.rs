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

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::env::{check_duplicated_univ_params, check_name, check_no_metavar_no_fvar};
use crate::{
    abstract_fvars, instantiate, instantiate_level_params, instantiate_rev, BinderInfo,
    ConstantInfo, ConstantVal, ConstructorVal, Environment, Expr, ExprNode, FVarIdGen,
    InductiveType, InductiveVal, KernelError, Level, LocalContext, Name, Nat, RecGuard,
    RecursorRule, RecursorVal, TypeChecker,
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

/// oracle: Init/Prelude.lean:5599-5602 (`Name.hasMacroScopes`) — a name
/// carries hygienic macro scopes iff, skipping trailing numeric scope
/// components, its first string component is exactly `_hyg`. Iterative
/// (leaf→root) so it is safe on adversarially deep names.
fn has_macro_scopes(n: &Arc<Name>) -> bool {
    let mut cur = n;
    loop {
        match cur.as_ref() {
            Name::Str { part, .. } => return part == "_hyg",
            Name::Num { parent, .. } => cur = parent,
            Name::Anonymous => return false,
        }
    }
}

/// oracle: Init/Prelude.lean:5604-5609 (`eraseMacroScopesAux`) — the base
/// name obtained by dropping the whole `._@.<…>._hyg.<scopes>` suffix, i.e.
/// everything from the `_@` delimiter onward. Only meaningful when
/// `has_macro_scopes` holds. Iterative for adversarial-depth safety.
fn erase_macro_scopes_aux(n: &Arc<Name>) -> Arc<Name> {
    let mut cur = Arc::clone(n);
    loop {
        match cur.as_ref() {
            Name::Str { parent, part } => {
                if part == "_@" {
                    return Arc::clone(parent);
                }
                let p = Arc::clone(parent);
                cur = p;
            }
            Name::Num { parent, .. } => {
                let p = Arc::clone(parent);
                cur = p;
            }
            Name::Anonymous => return Arc::new(Name::Anonymous),
        }
    }
}

/// oracle: Init/Meta/Defs.lean:309-314 (`Name.modifyBase`) — when `n`
/// carries macro scopes, strip them, apply `f` to the base name, and
/// re-attach the scopes; otherwise apply `f` directly. The oracle does
/// this via `extractMacroScopes`/`.review`; since `.review` re-encodes
/// the untouched `imported`/`ctx`/`scopes` verbatim onto the (modified)
/// base, the round-trip is exactly "replace the base prefix of `n` with
/// `f base`", which `replace_prefix` performs.
///
/// This is the piece the original Task-9 port of `appendAfter`/
/// `appendIndexAfter` was missing: constructor *field* binders in real
/// modules are hygienic (`a._@.<ctx>._hyg.0`), and the recursor's
/// induction-hypothesis binder must be `a_ih._@.<ctx>._hyg.0` (base
/// `a`→`a_ih`, scopes preserved), NOT `a._@.<ctx>._hyg.0._ih` (which a
/// plain suffix-append produces). The old code matched the oracle only
/// for scope-free names, so the inductive unit tests (which used simple
/// field names like `n`) passed while real oleans mismatched on replay.
fn modify_base(n: &Arc<Name>, f: impl FnOnce(&Arc<Name>) -> Arc<Name>) -> Arc<Name> {
    if has_macro_scopes(n) {
        let base = erase_macro_scopes_aux(n);
        let new_base = f(&base);
        replace_prefix(n, &base, &new_base)
    } else {
        f(n)
    }
}

/// oracle: Init/Meta/Defs.lean:315-318 (`Name.appendAfter`) via
/// `modifyBase`: on the base name, `str p s => mkStr p (s ++ suffix)`,
/// else `mkStr base suffix`.
fn append_after_str(n: &Arc<Name>, suffix: &str) -> Arc<Name> {
    modify_base(n, |base| match base.as_ref() {
        Name::Str { parent, part } => Arc::new(Name::Str {
            parent: Arc::clone(parent),
            part: format!("{part}{suffix}"),
        }),
        _ => Arc::new(Name::Str {
            parent: Arc::clone(base),
            part: suffix.to_string(),
        }),
    })
}

/// oracle: Init/Meta/Defs.lean:320-323 (`Name.appendIndexAfter`) via
/// `modifyBase`: on the base name, `str p s => mkStr p (s ++ "_" ++
/// toString idx)`, else `mkStr base ("_" ++ toString idx)`.
fn append_index_after(n: &Arc<Name>, idx: usize) -> Arc<Name> {
    modify_base(n, |base| match base.as_ref() {
        Name::Str { parent, part } => Arc::new(Name::Str {
            parent: Arc::clone(parent),
            part: format!("{part}_{idx}"),
        }),
        _ => Arc::new(Name::Str {
            parent: Arc::clone(base),
            part: format!("_{idx}"),
        }),
    })
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

/// Runs the ordinary (Task-9) `add_inductive_fn` machinery on an already
/// nesting-eliminated block (oracle: `add_inductive_fn(env, diag, decl,
/// nnested)`, inductive.cpp:1120). `nnested` is the count of auxiliary
/// nested types the caller lifted into the block (0 for a genuinely
/// non-nested declaration). Rolls back every added constant on failure.
fn run_add_inductive_fn(
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

// =====================================================================
// Nested-inductive elimination (oracle: inductive.cpp:792-1181).
//
// A constructor field mentioning some OTHER (already-declared) inductive
// `I` applied to a parameter that contains one of the block's own types
// (e.g. `List Tree` inside `Tree`, or `Array Syntax` inside `Syntax`) is
// not directly admissible: `I Ds` is not a valid recursive occurrence.
// The oracle lifts each such `I Ds` to a fresh auxiliary inductive type
// (name under the reserved `_nested` prefix) in the mutual block,
// rewriting occurrences, runs the ordinary machinery on the enlarged
// block in a scratch environment, and then `restore_nested` maps the aux
// constants back to the real nested applications, copying the resulting
// decls into the real env under their real names.
//
// Deviations forced by Rust, same spirit as `AddInductiveFn`'s module
// docs:
//   - The oracle threads its own `name_generator(*g_nested_fresh)` (a
//     `_nested_fresh` prefix distinct from the checker's `_kernel_fresh`).
//     We reuse `FVarIdGen` (`_kernel_fresh.<n>`): every fvar minted here
//     is abstracted away (into bvars) before any term leaves elimination
//     — the aux block's declared types are closed, and `restore_nested`
//     re-abstracts its peeled binders — so elimination fvars never
//     coexist with the scratch `add_inductive_fn`'s own fvars. No
//     collision is possible.
//   - `RecGuard` is threaded as an explicit `&mut` parameter (not a
//     struct field) so the value-depth `replace`/`find` walks below can
//     recurse via `g.enter(|g| self.method(g, ..))` while still mutating
//     `self` (the guard being a separate binding, not a field of `self`).
// =====================================================================

/// oracle: `name("_nested")` (inductive.cpp:1216 `g_nested`).
fn nested_prefix() -> Arc<Name> {
    mk_simple_name("_nested")
}

/// oracle: util/name.cpp:302-318 (`operator+`) — append every component
/// of `n2` (root→leaf) onto `n1`. Iterative (walks `n2`'s parent chain),
/// safe on adversarially deep names.
fn name_append(n1: &Arc<Name>, n2: &Arc<Name>) -> Arc<Name> {
    let mut comps: Vec<NameComp> = Vec::new();
    let mut cur = Arc::clone(n2);
    loop {
        match cur.as_ref() {
            Name::Anonymous => break,
            Name::Str { parent, part } => {
                comps.push(NameComp::Str(part.clone()));
                cur = Arc::clone(parent);
            }
            Name::Num { parent, part } => {
                comps.push(NameComp::Num(part.clone()));
                cur = Arc::clone(parent);
            }
        }
    }
    let mut result = Arc::clone(n1);
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
    result
}

/// oracle: inductive.cpp:936-944 — does `e` contain a `Const` whose name
/// is one of the block's (current) type names? (The oracle's `find`
/// predicate, checking every subterm.) Guarded walk.
fn expr_contains_new_type(
    e: &Arc<Expr>,
    names: &HashSet<Arc<Name>>,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    match e.node() {
        ExprNode::Const { name, .. } => Ok(names.contains(name)),
        ExprNode::App { f, arg } => {
            let (f, arg) = (Arc::clone(f), Arc::clone(arg));
            g.enter(|g| {
                Ok(
                    expr_contains_new_type(&f, names, g)?
                        || expr_contains_new_type(&arg, names, g)?,
                )
            })
        }
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => {
            let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
            g.enter(|g| {
                Ok(
                    expr_contains_new_type(&bt, names, g)?
                        || expr_contains_new_type(&bd, names, g)?,
                )
            })
        }
        ExprNode::LetE {
            ty, value, body, ..
        } => {
            let (t, v, b) = (Arc::clone(ty), Arc::clone(value), Arc::clone(body));
            g.enter(|g| {
                Ok(expr_contains_new_type(&t, names, g)?
                    || expr_contains_new_type(&v, names, g)?
                    || expr_contains_new_type(&b, names, g)?)
            })
        }
        ExprNode::MData { expr, .. }
        | ExprNode::Proj {
            structure: expr, ..
        } => {
            let inner = Arc::clone(expr);
            g.enter(|g| expr_contains_new_type(&inner, names, g))
        }
        _ => Ok(false),
    }
}

/// The head const's `(name, levels)`, or `None` if the head is not a
/// `Const`.
fn head_const(e: &Arc<Expr>) -> Option<(Arc<Name>, Vec<Arc<Level>>)> {
    match Expr::get_app_fn(e).node() {
        ExprNode::Const { name, levels } => Some((Arc::clone(name), levels.clone())),
        _ => None,
    }
}

/// The elimination pass (oracle: `elim_nested_inductive_fn`,
/// inductive.cpp:882-1077).
struct ElimNestedInductiveFn<'e> {
    env: &'e Environment,
    ngen: FVarIdGen,
    /// oracle `m_params_lctx`: holds the block params' fvar decls.
    params_lctx: LocalContext,
    /// oracle `m_params`: the block parameters (fvars), re-used as the
    /// canonical form when comparing/canonicalizing nested occurrences.
    params: Vec<Arc<Expr>>,
    /// oracle `m_nested_aux`: `(I Ds canonicalized over m_params, auxName)`.
    nested_aux: Vec<(Arc<Expr>, Arc<Name>)>,
    /// oracle `m_lvls`: `lparams_to_levels` of the block's level params.
    lvls: Vec<Arc<Level>>,
    /// oracle `m_new_types`: the (growing) enlarged block.
    new_types: Vec<InductiveType>,
    /// Names in `new_types`, for the `is_nested_inductive_app` membership
    /// test (kept in sync as aux types are pushed).
    new_type_names: HashSet<Arc<Name>>,
    /// oracle `m_next_idx`: counter for `mk_unique_name`.
    next_idx: u64,
    nparams: usize,
    name0: Arc<Name>,
}

/// oracle: `elim_nested_inductive_result` (inductive.cpp:796-873) — the
/// value elimination hands back, plus the `restore_*` methods.
struct ElimResult {
    /// oracle `m_params`.
    params: Vec<Arc<Expr>>,
    /// oracle `m_aux2nested`: auxName → `I Ds` (canonical over m_params).
    aux2nested: HashMap<Arc<Name>, Arc<Expr>>,
    /// The enlarged (aux) block's types.
    aux_types: Vec<InductiveType>,
    /// oracle `m_ngen`, advanced as `restore_nested` mints peel fvars.
    ngen: FVarIdGen,
}

impl<'e> ElimNestedInductiveFn<'e> {
    fn new(
        env: &'e Environment,
        lparams: &[Arc<Name>],
        nparams: usize,
        types: &[InductiveType],
        _is_unsafe: bool,
    ) -> ElimNestedInductiveFn<'e> {
        let name0 = types
            .first()
            .map(|t| Arc::clone(&t.name))
            .unwrap_or_else(|| Arc::new(Name::Anonymous));
        let new_types = types.to_vec();
        let new_type_names = new_types.iter().map(|t| Arc::clone(&t.name)).collect();
        ElimNestedInductiveFn {
            env,
            ngen: FVarIdGen::default(),
            params_lctx: LocalContext::default(),
            params: Vec::new(),
            nested_aux: Vec::new(),
            lvls: lparams_to_levels(lparams),
            new_types,
            new_type_names,
            next_idx: 1,
            nparams,
            name0,
        }
    }

    fn ill_formed(&self) -> KernelError {
        // oracle: inductive.cpp:906-908 (`throw_ill_formed`).
        KernelError::InvalidInductive {
            name: Arc::clone(&self.name0),
            what: "invalid nested inductive datatype, ill-formed declaration",
        }
    }

    /// oracle: inductive.cpp:898-904 (`mk_unique_name`) — append indices
    /// to `base` until the name is free in the (original) environment.
    fn mk_unique_name(&mut self, base: &Arc<Name>) -> Arc<Name> {
        loop {
            let r = append_index_after(base, self.next_idx as usize);
            self.next_idx += 1;
            if self.env.get(&r).is_none() {
                return r;
            }
        }
    }

    /// oracle: inductive.cpp:1035-1043 (`get_params`) — peel `nparams`
    /// Π-binders into fresh fvars recorded in `lctx`. Returns the peeled
    /// body and the fvars. Explicit field-refs (not `&mut self`) so a
    /// caller may point `lctx` at `self.params_lctx`.
    fn get_params(
        ngen: &mut FVarIdGen,
        nparams: usize,
        name0: &Arc<Name>,
        lctx: &mut LocalContext,
        mut ty: Arc<Expr>,
        g: &mut RecGuard,
    ) -> Result<(Arc<Expr>, Vec<Arc<Expr>>), KernelError> {
        let mut params = Vec::with_capacity(nparams);
        for _ in 0..nparams {
            let (bn, bt, body, bi) = match ty.node() {
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => (
                    Arc::clone(binder_name),
                    Arc::clone(binder_type),
                    Arc::clone(body),
                    *binder_info,
                ),
                _ => {
                    return Err(KernelError::InvalidInductive {
                        name: Arc::clone(name0),
                        what: "incorrect number of parameters",
                    })
                }
            };
            let fv = lctx.mk_local_decl(ngen, &bn, bt, bi);
            params.push(Arc::clone(&fv));
            ty = instantiate(&body, &fv, g)?;
        }
        Ok((ty, params))
    }

    /// oracle: inductive.cpp:910-913 (`replace_params`) — rewrite the
    /// per-constructor params `as_` back to the canonical `m_params`.
    fn replace_params(
        &self,
        e: &Arc<Expr>,
        as_: &[Arc<Expr>],
        g: &mut RecGuard,
    ) -> Result<Arc<Expr>, KernelError> {
        let t = abstract_fvars(e, as_, g)?;
        instantiate_rev(&t, &self.params, g)
    }

    /// oracle: inductive.cpp:954-960 (`instantiate_pi_params`) — drop
    /// `params.len()` Π-domains then instantiate the body with `params`.
    fn instantiate_pi_params(
        &self,
        mut e: Arc<Expr>,
        params: &[Arc<Expr>],
        g: &mut RecGuard,
    ) -> Result<Arc<Expr>, KernelError> {
        for _ in 0..params.len() {
            match e.node() {
                ExprNode::ForallE { body, .. } => e = Arc::clone(body),
                _ => return Err(self.ill_formed()),
            }
        }
        instantiate_rev(&e, params, g)
    }

    /// oracle: inductive.cpp:920-952 (`is_nested_inductive_app`).
    fn is_nested_inductive_app(
        &mut self,
        e: &Arc<Expr>,
        g: &mut RecGuard,
    ) -> Result<Option<InductiveVal>, KernelError> {
        let env = self.env;
        if !e.is_app() {
            return Ok(None);
        }
        let fn_name = match head_const(e) {
            Some((n, _)) => n,
            None => return Ok(None),
        };
        let info = match env.get(&fn_name) {
            Some(ConstantInfo::Induct(v)) => v.clone(),
            _ => return Ok(None),
        };
        let args = Expr::get_app_args(e);
        let nparams = info
            .num_params
            .to_usize()
            .ok_or_else(|| self.ill_formed())?;
        if nparams > args.len() {
            return Ok(None);
        }
        let mut is_nested = false;
        let mut loose = false;
        for a in &args[0..nparams] {
            // `has_loose_bvars(a)`: exact iff the packed range is 0 (a
            // saturated range is still nonzero — reported as loose).
            if a.data().loose_bvar_range() != 0 {
                loose = true;
            }
            if expr_contains_new_type(a, &self.new_type_names, g)? {
                is_nested = true;
            }
        }
        if !is_nested {
            return Ok(None);
        }
        if loose {
            // oracle: inductive.cpp:949-950.
            return Err(KernelError::InvalidInductive {
                name: fn_name,
                what: "nested inductive parameters cannot contain local variables",
            });
        }
        Ok(Some(info))
    }

    /// oracle: inductive.cpp:963-1028 (`replace_if_nested`). If `e` is a
    /// nested occurrence `I Ds is`, return `Iaux As is` (creating aux
    /// types on first encounter), else `None`.
    fn replace_if_nested(
        &mut self,
        lctx: &LocalContext,
        as_: &[Arc<Expr>],
        e: &Arc<Expr>,
        g: &mut RecGuard,
    ) -> Result<Option<Arc<Expr>>, KernelError> {
        let env = self.env;
        let i_val = match self.is_nested_inductive_app(e, g)? {
            Some(v) => v,
            None => return Ok(None),
        };
        let args = Expr::get_app_args(e);
        let fn0 = Arc::clone(Expr::get_app_fn(e));
        let (i_name, i_lvls) = match head_const(e) {
            Some(p) => p,
            None => return Ok(None),
        };
        let i_nparams = i_val
            .num_params
            .to_usize()
            .ok_or_else(|| self.ill_formed())?;
        // IAs = I Ds (the parametric prefix).
        let i_as = Expr::mk_app_spine(fn0, &args[0..i_nparams]);
        let i_params = self.replace_params(&i_as, as_, g)?;
        // Already lifted?
        let mut found: Option<Arc<Name>> = None;
        for (p_expr, p_name) in &self.nested_aux {
            if Expr::structural_eq(p_expr, &i_params, g)? {
                found = Some(Arc::clone(p_name));
                break;
            }
        }
        if let Some(aux_name) = found {
            let aux_i = Expr::const_(aux_name, self.lvls.clone(), g)?;
            let aux_i = Expr::mk_app_spine(aux_i, as_);
            return Ok(Some(Expr::mk_app_spine(aux_i, &args[i_nparams..])));
        }
        // Copy every inductive `J` mutual with `I` into the block.
        let mut result: Option<Arc<Expr>> = None;
        let all = i_val.all.clone();
        for j_name in &all {
            let j_ind = match env.get(j_name) {
                Some(ConstantInfo::Induct(v)) => v.clone(),
                _ => return Err(self.ill_formed()),
            };
            let j_const = Expr::const_(Arc::clone(j_name), i_lvls.clone(), g)?;
            let j_as = Expr::mk_app_spine(j_const, &args[0..i_nparams]);
            let aux_j_name = self.mk_unique_name(&name_append(&nested_prefix(), j_name));
            // auxJ_type = (Π As, J's index telescope with Ds substituted).
            let mut aux_j_type =
                instantiate_level_params(&j_ind.val.ty, &j_ind.val.level_params, &i_lvls, g)?;
            aux_j_type = self.instantiate_pi_params(aux_j_type, &args[0..i_nparams], g)?;
            aux_j_type = lctx.mk_pi(as_, &aux_j_type, g)?;
            let j_as_canon = self.replace_params(&j_as, as_, g)?;
            self.nested_aux.push((j_as_canon, Arc::clone(&aux_j_name)));
            if j_name.as_ref() == i_name.as_ref() {
                let aux_i = Expr::const_(Arc::clone(&aux_j_name), self.lvls.clone(), g)?;
                let aux_i = Expr::mk_app_spine(aux_i, as_);
                result = Some(Expr::mk_app_spine(aux_i, &args[i_nparams..]));
            }
            // Copy J's constructors (still referencing J; fixed when the
            // aux type is itself dequeued in the main loop).
            let mut aux_ctors: Vec<(Arc<Name>, Arc<Expr>)> = Vec::with_capacity(j_ind.ctors.len());
            for j_cnstr_name in &j_ind.ctors {
                let c_val = match env.get(j_cnstr_name) {
                    Some(ConstantInfo::Ctor(v)) => v.clone(),
                    _ => return Err(self.ill_formed()),
                };
                let aux_c_name = replace_prefix(j_cnstr_name, j_name, &aux_j_name);
                let mut aux_c_type =
                    instantiate_level_params(&c_val.val.ty, &c_val.val.level_params, &i_lvls, g)?;
                aux_c_type = self.instantiate_pi_params(aux_c_type, &args[0..i_nparams], g)?;
                aux_c_type = lctx.mk_pi(as_, &aux_c_type, g)?;
                aux_ctors.push((aux_c_name, aux_c_type));
            }
            self.new_type_names.insert(Arc::clone(&aux_j_name));
            self.new_types.push(InductiveType {
                name: aux_j_name,
                ty: aux_j_type,
                ctors: aux_ctors,
            });
        }
        match result {
            Some(r) => Ok(Some(r)),
            // `I` is always in `I_val.all`, so `result` is set — but never
            // panic on decoded input if some malformed `all` omits it.
            None => Err(self.ill_formed()),
        }
    }

    /// oracle: inductive.cpp:1030-1033 (`replace_all_nested`) — the
    /// top-down `replace` walk. Value-depth ⇒ guarded.
    fn replace_all_nested(
        &mut self,
        lctx: &LocalContext,
        as_: &[Arc<Expr>],
        e: &Arc<Expr>,
        g: &mut RecGuard,
    ) -> Result<Arc<Expr>, KernelError> {
        if let Some(r) = self.replace_if_nested(lctx, as_, e, g)? {
            return Ok(r);
        }
        match e.node() {
            ExprNode::App { f, arg } => {
                let (f, arg) = (Arc::clone(f), Arc::clone(arg));
                let (f2, a2) = g.enter(|g| {
                    Ok((
                        self.replace_all_nested(lctx, as_, &f, g)?,
                        self.replace_all_nested(lctx, as_, &arg, g)?,
                    ))
                })?;
                Ok(Expr::app(f2, a2))
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let (bn, bi) = (Arc::clone(binder_name), *binder_info);
                let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
                let (bt2, bd2) = g.enter(|g| {
                    Ok((
                        self.replace_all_nested(lctx, as_, &bt, g)?,
                        self.replace_all_nested(lctx, as_, &bd, g)?,
                    ))
                })?;
                Ok(Expr::lam(bn, bt2, bd2, bi))
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let (bn, bi) = (Arc::clone(binder_name), *binder_info);
                let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
                let (bt2, bd2) = g.enter(|g| {
                    Ok((
                        self.replace_all_nested(lctx, as_, &bt, g)?,
                        self.replace_all_nested(lctx, as_, &bd, g)?,
                    ))
                })?;
                Ok(Expr::forall_e(bn, bt2, bd2, bi))
            }
            ExprNode::LetE {
                decl_name,
                ty,
                value,
                body,
                non_dep,
            } => {
                let (dn, nd) = (Arc::clone(decl_name), *non_dep);
                let (t, v, b) = (Arc::clone(ty), Arc::clone(value), Arc::clone(body));
                let (t2, v2, b2) = g.enter(|g| {
                    Ok((
                        self.replace_all_nested(lctx, as_, &t, g)?,
                        self.replace_all_nested(lctx, as_, &v, g)?,
                        self.replace_all_nested(lctx, as_, &b, g)?,
                    ))
                })?;
                Ok(Expr::let_e(dn, t2, v2, b2, nd))
            }
            ExprNode::MData { data, expr } => {
                let (data, inner) = (data.clone(), Arc::clone(expr));
                let inner2 = g.enter(|g| self.replace_all_nested(lctx, as_, &inner, g))?;
                Ok(Expr::mdata(data, inner2))
            }
            ExprNode::Proj {
                type_name,
                idx,
                structure,
            } => {
                let (tn, ix, st) = (Arc::clone(type_name), idx.clone(), Arc::clone(structure));
                let st2 = g.enter(|g| self.replace_all_nested(lctx, as_, &st, g))?;
                Ok(Expr::proj(tn, ix, st2))
            }
            _ => Ok(Arc::clone(e)),
        }
    }

    /// oracle: inductive.cpp:1045-1076 (`operator()`).
    fn run(&mut self, g: &mut RecGuard) -> Result<ElimResult, KernelError> {
        if self.new_types.is_empty() {
            // oracle: inductive.cpp:1050. Same error the Task-9 guard in
            // `AddInductiveFn::run` reports, so `rejects_empty_inductive_
            // block` still fires here (this pass now runs first).
            return Err(KernelError::InvalidInductive {
                name: Arc::new(Name::Anonymous),
                what: "empty inductive block",
            });
        }
        // Initialize m_params / m_params_lctx from the first type.
        let type0 = Arc::clone(&self.new_types[0].ty);
        let (_, params) = Self::get_params(
            &mut self.ngen,
            self.nparams,
            &self.name0,
            &mut self.params_lctx,
            type0,
            g,
        )?;
        self.params = params;
        // Main elimination loop — `new_types` grows as aux types are
        // pushed, so re-read `.len()` each iteration.
        let mut qhead = 0;
        while qhead < self.new_types.len() {
            let ind_type = self.new_types[qhead].clone();
            let mut new_cnstrs: Vec<(Arc<Name>, Arc<Expr>)> =
                Vec::with_capacity(ind_type.ctors.len());
            for (cn, ct) in &ind_type.ctors {
                let mut lctx = LocalContext::default();
                // Re-create the params per constructor to preserve
                // binding_info (oracle comment inductive.cpp:1062-1064).
                let (cnstr_type, as_) = Self::get_params(
                    &mut self.ngen,
                    self.nparams,
                    &self.name0,
                    &mut lctx,
                    Arc::clone(ct),
                    g,
                )?;
                let new_ct = self.replace_all_nested(&lctx, &as_, &cnstr_type, g)?;
                let new_ct = lctx.mk_pi(&as_, &new_ct, g)?;
                new_cnstrs.push((Arc::clone(cn), new_ct));
            }
            self.new_types[qhead] = InductiveType {
                name: Arc::clone(&ind_type.name),
                ty: Arc::clone(&ind_type.ty),
                ctors: new_cnstrs,
            };
            qhead += 1;
        }
        let aux2nested = self
            .nested_aux
            .iter()
            .map(|(e, n)| (Arc::clone(n), Arc::clone(e)))
            .collect();
        Ok(ElimResult {
            params: self.params.clone(),
            aux2nested,
            aux_types: self.new_types.clone(),
            ngen: std::mem::take(&mut self.ngen),
        })
    }
}

/// oracle: inductive.cpp:811-818 (`get_nested_if_aux_constructor`) — if
/// `c` is a constructor of an aux inductive type, return its real nested
/// application and the aux type name.
fn get_nested_if_aux_constructor(
    aux_env: &Environment,
    c: &Arc<Name>,
    aux2nested: &HashMap<Arc<Name>, Arc<Expr>>,
) -> Option<(Arc<Expr>, Arc<Name>)> {
    let cv = match aux_env.get(c) {
        Some(ConstantInfo::Ctor(v)) => v,
        _ => return None,
    };
    let aux_i_name = &cv.induct;
    let nested = aux2nested.get(aux_i_name)?;
    Some((Arc::clone(nested), Arc::clone(aux_i_name)))
}

impl ElimResult {
    /// oracle: inductive.cpp:820-826 (`restore_constructor_name`).
    fn restore_constructor_name(
        &self,
        aux_env: &Environment,
        cnstr_name: &Arc<Name>,
    ) -> Result<Arc<Name>, KernelError> {
        let (nested, aux_i_name) =
            get_nested_if_aux_constructor(aux_env, cnstr_name, &self.aux2nested).ok_or(
                KernelError::InvalidInductive {
                    name: Arc::clone(cnstr_name),
                    what: "invalid nested constructor",
                },
            )?;
        let i_name = match head_const(&nested) {
            Some((n, _)) => n,
            None => {
                return Err(KernelError::InvalidInductive {
                    name: Arc::clone(cnstr_name),
                    what: "invalid nested constructor",
                })
            }
        };
        Ok(replace_prefix(cnstr_name, &aux_i_name, &i_name))
    }

    /// oracle: inductive.cpp:837-870 (the `restore_nested` `replace`
    /// callback). Returns the rewritten node or `None` to keep descending.
    fn restore_node(
        &self,
        t: &Arc<Expr>,
        as_: &[Arc<Expr>],
        aux_env: &Environment,
        rec_map: &HashMap<Arc<Name>, Arc<Name>>,
        g: &mut RecGuard,
    ) -> Result<Option<Arc<Expr>>, KernelError> {
        // Aux recursor constant → renamed real recursor.
        if let ExprNode::Const { name, levels } = t.node() {
            if let Some(rec_name) = rec_map.get(name) {
                return Ok(Some(Expr::const_(Arc::clone(rec_name), levels.clone(), g)?));
            }
        }
        let fn_name = match head_const(t) {
            Some((n, _)) => n,
            None => return Ok(None),
        };
        // Aux type application `Iaux As is` → `I Ds is`.
        if let Some(nested) = self.aux2nested.get(&fn_name) {
            let args = Expr::get_app_args(t);
            if args.len() < self.params.len() {
                return Err(KernelError::InvalidInductive {
                    name: Arc::clone(&fn_name),
                    what: "ill-formed nested application",
                });
            }
            let tmp = abstract_fvars(nested, &self.params, g)?;
            let new_head = instantiate_rev(&tmp, as_, g)?;
            return Ok(Some(Expr::mk_app_spine(
                new_head,
                &args[self.params.len()..],
            )));
        }
        // Aux constructor application `Iaux.c As is` → `I.c Ds is`.
        if let Some((nested, aux_i_name)) =
            get_nested_if_aux_constructor(aux_env, &fn_name, &self.aux2nested)
        {
            let args = Expr::get_app_args(t);
            if args.len() < self.params.len() {
                return Err(KernelError::InvalidInductive {
                    name: Arc::clone(&fn_name),
                    what: "ill-formed nested application",
                });
            }
            let tmp = abstract_fvars(&nested, &self.params, g)?;
            let new_nested = instantiate_rev(&tmp, as_, g)?;
            let (i_name, i_lvls) = match head_const(&new_nested) {
                Some(p) => p,
                None => {
                    return Err(KernelError::InvalidInductive {
                        name: Arc::clone(&fn_name),
                        what: "ill-formed nested application",
                    })
                }
            };
            let i_args = Expr::get_app_args(&new_nested);
            let new_fn_name = replace_prefix(&fn_name, &aux_i_name, &i_name);
            let new_fn = Expr::const_(new_fn_name, i_lvls, g)?;
            let head = Expr::mk_app_spine(new_fn, &i_args);
            return Ok(Some(Expr::mk_app_spine(head, &args[self.params.len()..])));
        }
        Ok(None)
    }

    /// The `replace` walk of `restore_nested` (top-down, value-depth ⇒
    /// guarded); `&self` throughout (no mutation), so the recursion needs
    /// no borrow gymnastics.
    fn restore_replace(
        &self,
        e: &Arc<Expr>,
        as_: &[Arc<Expr>],
        aux_env: &Environment,
        rec_map: &HashMap<Arc<Name>, Arc<Name>>,
        g: &mut RecGuard,
    ) -> Result<Arc<Expr>, KernelError> {
        if let Some(r) = self.restore_node(e, as_, aux_env, rec_map, g)? {
            return Ok(r);
        }
        match e.node() {
            ExprNode::App { f, arg } => {
                let (f, arg) = (Arc::clone(f), Arc::clone(arg));
                let (f2, a2) = g.enter(|g| {
                    Ok((
                        self.restore_replace(&f, as_, aux_env, rec_map, g)?,
                        self.restore_replace(&arg, as_, aux_env, rec_map, g)?,
                    ))
                })?;
                Ok(Expr::app(f2, a2))
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let (bn, bi) = (Arc::clone(binder_name), *binder_info);
                let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
                let (bt2, bd2) = g.enter(|g| {
                    Ok((
                        self.restore_replace(&bt, as_, aux_env, rec_map, g)?,
                        self.restore_replace(&bd, as_, aux_env, rec_map, g)?,
                    ))
                })?;
                Ok(Expr::lam(bn, bt2, bd2, bi))
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let (bn, bi) = (Arc::clone(binder_name), *binder_info);
                let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
                let (bt2, bd2) = g.enter(|g| {
                    Ok((
                        self.restore_replace(&bt, as_, aux_env, rec_map, g)?,
                        self.restore_replace(&bd, as_, aux_env, rec_map, g)?,
                    ))
                })?;
                Ok(Expr::forall_e(bn, bt2, bd2, bi))
            }
            ExprNode::LetE {
                decl_name,
                ty,
                value,
                body,
                non_dep,
            } => {
                let (dn, nd) = (Arc::clone(decl_name), *non_dep);
                let (t, v, b) = (Arc::clone(ty), Arc::clone(value), Arc::clone(body));
                let (t2, v2, b2) = g.enter(|g| {
                    Ok((
                        self.restore_replace(&t, as_, aux_env, rec_map, g)?,
                        self.restore_replace(&v, as_, aux_env, rec_map, g)?,
                        self.restore_replace(&b, as_, aux_env, rec_map, g)?,
                    ))
                })?;
                Ok(Expr::let_e(dn, t2, v2, b2, nd))
            }
            ExprNode::MData { data, expr } => {
                let (data, inner) = (data.clone(), Arc::clone(expr));
                let inner2 = g.enter(|g| self.restore_replace(&inner, as_, aux_env, rec_map, g))?;
                Ok(Expr::mdata(data, inner2))
            }
            ExprNode::Proj {
                type_name,
                idx,
                structure,
            } => {
                let (tn, ix, st) = (Arc::clone(type_name), idx.clone(), Arc::clone(structure));
                let st2 = g.enter(|g| self.restore_replace(&st, as_, aux_env, rec_map, g))?;
                Ok(Expr::proj(tn, ix, st2))
            }
            _ => Ok(Arc::clone(e)),
        }
    }

    /// oracle: inductive.cpp:828-872 (`restore_nested`) — peel the block
    /// params, rewrite aux occurrences, re-wrap the telescope.
    fn restore_nested(
        &mut self,
        e: &Arc<Expr>,
        aux_env: &Environment,
        rec_map: &HashMap<Arc<Name>, Arc<Name>>,
        g: &mut RecGuard,
    ) -> Result<Arc<Expr>, KernelError> {
        let mut lctx = LocalContext::default();
        let mut as_: Vec<Arc<Expr>> = Vec::with_capacity(self.params.len());
        let pi = e.is_forall();
        let mut cur = Arc::clone(e);
        for _ in 0..self.params.len() {
            let (bn, bt, body, bi) = match cur.node() {
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                }
                | ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => (
                    Arc::clone(binder_name),
                    Arc::clone(binder_type),
                    Arc::clone(body),
                    *binder_info,
                ),
                _ => {
                    return Err(KernelError::InvalidInductive {
                        name: Arc::new(Name::Anonymous),
                        what: "ill-formed nested declaration",
                    })
                }
            };
            let fv = lctx.mk_local_decl(&mut self.ngen, &bn, bt, bi);
            as_.push(Arc::clone(&fv));
            cur = instantiate(&body, &fv, g)?;
        }
        let body2 = self.restore_replace(&cur, &as_, aux_env, rec_map, g)?;
        if pi {
            lctx.mk_pi(&as_, &body2, g)
        } else {
            lctx.mk_lambda(&as_, &body2, g)
        }
    }
}

/// `(aux recursor names, aux_rec_name → new_rec_name map)`.
type AuxRecNames = (Vec<Arc<Name>>, HashMap<Arc<Name>, Arc<Name>>);

/// oracle: inductive.cpp:1088-1114 (`mk_aux_rec_name_map`). Only called
/// when aux types were created (`all_names.len() > ntypes`), so the
/// recursors for indices `>= ntypes` are the aux ones to rename.
fn mk_aux_rec_name_map(
    aux_env: &Environment,
    orig_types: &[InductiveType],
) -> Result<AuxRecNames, KernelError> {
    let ntypes = orig_types.len();
    let main_name = &orig_types[0].name;
    let main_iv = match aux_env.get(main_name) {
        Some(ConstantInfo::Induct(v)) => v,
        _ => {
            return Err(KernelError::InvalidInductive {
                name: Arc::clone(main_name),
                what: "missing aux inductive",
            })
        }
    };
    let mut old_rec_names = Vec::new();
    let mut rec_map = HashMap::new();
    let mut next_idx = 1usize;
    for (i, ind_name) in main_iv.all.iter().enumerate() {
        if i >= ntypes {
            let old = mk_rec_name(ind_name);
            let new = append_index_after(&mk_rec_name(main_name), next_idx);
            next_idx += 1;
            old_rec_names.push(Arc::clone(&old));
            rec_map.insert(old, new);
        }
    }
    Ok((old_rec_names, rec_map))
}

/// oracle: inductive.cpp:1131-1153 (`process_rec`) — restore one
/// recursor (main or aux) into the real env.
#[allow(clippy::too_many_arguments)]
fn process_rec(
    env: &mut Environment,
    aux_env: &Environment,
    res: &mut ElimResult,
    rec_name: &Arc<Name>,
    rec_map: &HashMap<Arc<Name>, Arc<Name>>,
    all_ind_names: &[Arc<Name>],
    added: &mut Vec<Arc<Name>>,
    g: &mut RecGuard,
) -> Result<(), KernelError> {
    let new_rec_name = rec_map
        .get(rec_name)
        .cloned()
        .unwrap_or_else(|| Arc::clone(rec_name));
    let rv = match aux_env.get(rec_name) {
        Some(ConstantInfo::Rec(v)) => v.clone(),
        _ => {
            return Err(KernelError::InvalidInductive {
                name: Arc::clone(rec_name),
                what: "missing aux recursor",
            })
        }
    };
    let new_rec_type = res.restore_nested(&rv.val.ty, aux_env, rec_map, g)?;
    let renamed = new_rec_name.as_ref() != rec_name.as_ref();
    let mut new_rules = Vec::with_capacity(rv.rules.len());
    for rule in &rv.rules {
        let new_rhs = res.restore_nested(&rule.rhs, aux_env, rec_map, g)?;
        let new_cnstr = if renamed {
            res.restore_constructor_name(aux_env, &rule.ctor)?
        } else {
            Arc::clone(&rule.ctor)
        };
        new_rules.push(RecursorRule {
            ctor: new_cnstr,
            nfields: rule.nfields.clone(),
            rhs: new_rhs,
        });
    }
    check_name(env, &new_rec_name)?;
    let new_rv = RecursorVal {
        val: ConstantVal {
            name: Arc::clone(&new_rec_name),
            level_params: rv.val.level_params.clone(),
            ty: new_rec_type,
        },
        all: all_ind_names.to_vec(),
        num_params: rv.num_params.clone(),
        num_indices: rv.num_indices.clone(),
        num_motives: rv.num_motives.clone(),
        num_minors: rv.num_minors.clone(),
        rules: new_rules,
        k: rv.k,
        is_unsafe: rv.is_unsafe,
    };
    added.push(Arc::clone(&new_rec_name));
    env.add_core(ConstantInfo::Rec(new_rv));
    Ok(())
}

/// oracle: inductive.cpp:1124-1180 (the nested branch of
/// `environment::add_inductive`). Copies the restored inductives, their
/// constructors, and their recursors (main + renamed aux) into the real
/// env. `added` tracks names for the caller's rollback.
fn restore_nested_inductives(
    env: &mut Environment,
    aux_env: &Environment,
    res: &mut ElimResult,
    orig_types: &[InductiveType],
    added: &mut Vec<Arc<Name>>,
    g: &mut RecGuard,
) -> Result<(), KernelError> {
    let all_ind_names: Vec<Arc<Name>> = orig_types.iter().map(|t| Arc::clone(&t.name)).collect();
    let (aux_rec_names, rec_map) = mk_aux_rec_name_map(aux_env, orig_types)?;
    let empty_map: HashMap<Arc<Name>, Arc<Name>> = HashMap::new();
    for ind_type in orig_types {
        let iv = match aux_env.get(&ind_type.name) {
            Some(ConstantInfo::Induct(v)) => v.clone(),
            _ => {
                return Err(KernelError::InvalidInductive {
                    name: Arc::clone(&ind_type.name),
                    what: "missing aux inductive",
                })
            }
        };
        // oracle: only the `all` field needs fixing on the inductive_val.
        check_name(env, &ind_type.name)?;
        let new_iv = InductiveVal {
            val: ConstantVal {
                name: Arc::clone(&iv.val.name),
                level_params: iv.val.level_params.clone(),
                ty: Arc::clone(&iv.val.ty),
            },
            num_params: iv.num_params.clone(),
            num_indices: iv.num_indices.clone(),
            all: all_ind_names.clone(),
            ctors: iv.ctors.clone(),
            num_nested: iv.num_nested.clone(),
            is_rec: iv.is_rec,
            is_unsafe: iv.is_unsafe,
            is_reflexive: iv.is_reflexive,
        };
        added.push(Arc::clone(&ind_type.name));
        env.add_core(ConstantInfo::Induct(new_iv));
        for cnstr_name in &iv.ctors {
            let cv = match aux_env.get(cnstr_name) {
                Some(ConstantInfo::Ctor(v)) => v.clone(),
                _ => {
                    return Err(KernelError::InvalidInductive {
                        name: Arc::clone(cnstr_name),
                        what: "missing aux constructor",
                    })
                }
            };
            let new_type = res.restore_nested(&cv.val.ty, aux_env, &empty_map, g)?;
            check_name(env, cnstr_name)?;
            let new_cv = ConstructorVal {
                val: ConstantVal {
                    name: Arc::clone(&cv.val.name),
                    level_params: cv.val.level_params.clone(),
                    ty: new_type,
                },
                induct: Arc::clone(&cv.induct),
                cidx: cv.cidx.clone(),
                num_params: cv.num_params.clone(),
                num_fields: cv.num_fields.clone(),
                is_unsafe: cv.is_unsafe,
            };
            added.push(Arc::clone(cnstr_name));
            env.add_core(ConstantInfo::Ctor(new_cv));
        }
        process_rec(
            env,
            aux_env,
            res,
            &mk_rec_name(&ind_type.name),
            &rec_map,
            &all_ind_names,
            added,
            g,
        )?;
    }
    for aux_rec in &aux_rec_names {
        process_rec(
            env,
            aux_env,
            res,
            aux_rec,
            &rec_map,
            &all_ind_names,
            added,
            g,
        )?;
    }
    Ok(())
}

/// The pipeline entry (oracle: `environment::add_inductive`,
/// inductive.cpp:1116-1181). Eliminates nested occurrences, runs the
/// ordinary machinery on the enlarged block, and (when nesting occurred)
/// restores the real nested inductives.
pub(crate) fn add_inductive(
    env: &mut Environment,
    lparams: Vec<Arc<Name>>,
    nparams: Nat,
    types: Vec<InductiveType>,
    is_unsafe: bool,
) -> Result<(), KernelError> {
    let name0 = types
        .first()
        .map(|t| Arc::clone(&t.name))
        .unwrap_or_else(|| Arc::new(Name::Anonymous));
    let nparams_usize = match nparams.to_usize() {
        Some(v) => v,
        None => {
            return Err(KernelError::InvalidInductive {
                name: name0,
                what: "too many parameters",
            })
        }
    };
    let mut g = RecGuard::new();
    // Eliminate nested occurrences (borrow of `env` released with `elim`).
    let mut res = {
        let mut elim = ElimNestedInductiveFn::new(env, &lparams, nparams_usize, &types, is_unsafe);
        elim.run(&mut g)?
    };
    let nnested = res.aux2nested.len();
    if nnested == 0 {
        // No nesting: the aux block is the (rebuilt, structurally
        // identical) original. Admit it in place, as Task 9 did.
        run_add_inductive_fn(
            env,
            lparams,
            nparams,
            res.aux_types.clone(),
            is_unsafe,
            Nat::from(0),
        )
    } else {
        // Nesting: run the machinery on the enlarged block in a scratch
        // env, then restore the real nested inductives into `env`.
        let mut scratch = env.clone();
        run_add_inductive_fn(
            &mut scratch,
            lparams,
            nparams,
            res.aux_types.clone(),
            is_unsafe,
            Nat::from(nnested as u64),
        )?;
        let mut added: Vec<Arc<Name>> = Vec::new();
        match restore_nested_inductives(env, &scratch, &mut res, &types, &mut added, &mut g) {
            Ok(()) => Ok(()),
            Err(e) => {
                for n in added.iter().rev() {
                    env.remove_core(n);
                }
                Err(e)
            }
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
        // oracle: inductive.cpp:1050 — the oracle rejects an empty types
        // list in `elim_nested_inductive_fn::operator()`, which runs
        // BEFORE `add_inductive_fn` ("invalid empty (mutual) inductive
        // datatype declaration"); `add_inductive_fn` itself then assumes
        // non-emptiness (e.g. `m_ind_types[0]` in
        // elim_only_at_universe_zero:491/509 and init_K_target:558).
        // Task 9 has no nested-elimination pass, so the guard lives here
        // instead: `run` is the sole entry to the pipeline, so this
        // check dominates every `ind_types[0]` index below (no-panic
        // mandate — `types` comes from decoded olean content via replay).
        if self.ind_types.is_empty() {
            return Err(KernelError::InvalidInductive {
                name: Arc::new(Name::Anonymous),
                what: "empty inductive block",
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
