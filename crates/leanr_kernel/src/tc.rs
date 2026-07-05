//! The kernel type checker: `infer_type`, `whnf` (beta/zeta/delta/proj),
//! and the definitional-equality core. This is a function-for-function
//! port of the oracle's `src/kernel/type_checker.cpp` (pinned githash
//! b4812ae53eea93439ad5dce5a5c26591c31cb697, toolchain
//! leanprover/lean4:v4.32.0-rc1). Every method cites its oracle line
//! range; port order and branch order follow the oracle literally.
//!
//! Task 7 fills the special-reduction branches (iota/quot recursor
//! reduction, nat/native literal reduction, offset defeq, eta / struct
//! eta / unit-like / string-lit expansion). Those branches are present
//! here with their FINAL signatures at the exact oracle sequence
//! positions, returning the neutral stub value (`Ok(None)` /
//! `Lbool::Undef` / `Ok(false)`) and marked `// M1b Task 7:`.
//!
//! Recursion discipline (crate-wide invariant, see lib.rs/guard.rs):
//! every mutually-recursive checker entry (`infer_type_core`,
//! `whnf_core`, `whnf`, `is_def_eq_core`, `lazy_delta_reduction`) enters
//! its frame through `self.guarded(...)`, which counts depth against
//! `MAX_REC_DEPTH` (rejecting past the cap — incompleteness, never a
//! stack overflow) and grows the stack via `stacker::maybe_grow`. This
//! mirrors the oracle's `check_system` interrupt/stack checks at the same
//! sites. Free functions from Tasks 2-5 (instantiate, abstract_fvars,
//! Level ops, structural_eq) keep taking `&mut self.guard` (a `RecGuard`)
//! as before; `guard_depth` is a separate counter for the checker's own
//! frames because the guard-on-`self` cannot be borrowed while `self` is
//! also passed to the recursive call (the brief's structural rule 1).

use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::{
    instantiate, instantiate_level_params, instantiate_rev, BinderInfo, ConstantInfo,
    DefinitionSafety, Environment, Expr, ExprNode, FVarIdGen, KernelError, Level, Literal,
    LocalContext, Name, Nat, RecGuard, ReducibilityHints, MAX_REC_DEPTH,
};

/// Stack-growth constants: identical to `RecGuard`'s (guard.rs), which
/// are private there. The `guarded` self-method below grows the stack
/// with the same red-zone/chunk sizes rustc's own `stacker` use employs.
const RED_ZONE: usize = 128 * 1024;
const STACK_CHUNK: usize = 4 * 1024 * 1024;

/// Three-valued result, oracle `lbool` (type_checker.cpp passim,
/// util/lbool.h). `Undef` = "this method could not decide".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lbool {
    False,
    True,
    Undef,
}

fn to_lbool(b: bool) -> Lbool {
    if b {
        Lbool::True
    } else {
        Lbool::False
    }
}

/// One `lazy_delta_reduction_step` outcome (oracle: `reduction_status`,
/// type_checker.h).
enum ReductionStatus {
    Continue,
    DefUnknown,
    DefEqual,
    DefDiff,
}

/// Pointer-identity cache key holding its `Arc` alive. Sound as a memo
/// key: two structurally-equal expressions with distinct allocations
/// simply miss (a lost cache hit, never a wrong one); the olean decoder's
/// sub-DAG sharing makes real hits common (brief's sharing discipline).
pub(crate) struct ExprPtr(pub Arc<Expr>);

impl PartialEq for ExprPtr {
    fn eq(&self, other: &ExprPtr) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for ExprPtr {}
impl Hash for ExprPtr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (Arc::as_ptr(&self.0) as usize).hash(state);
    }
}

/// Path-compressing union-find over expressions by pointer identity.
/// Port of the role `equiv_manager` plays in `quick_is_def_eq`
/// (type_checker.cpp:741) and `is_def_eq` (1136): `is_equiv` hit ⇒ known
/// equal; a successful `is_def_eq` merges the two classes. Keyed by `Arc`
/// pointer identity (see `ExprPtr`), so it only ever *under*-reports
/// equivalence — never over-reports (soundness).
#[derive(Default)]
struct UnionFind {
    index: HashMap<ExprPtr, usize>,
    parent: Vec<usize>,
}

impl UnionFind {
    fn node_of(&self, e: &Arc<Expr>) -> Option<usize> {
        self.index.get(&ExprPtr(Arc::clone(e))).copied()
    }

    fn add_node(&mut self, e: &Arc<Expr>) -> usize {
        if let Some(i) = self.node_of(e) {
            return i;
        }
        let i = self.parent.len();
        self.parent.push(i);
        self.index.insert(ExprPtr(Arc::clone(e)), i);
        i
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            let g = self.parent[self.parent[x]];
            self.parent[x] = g; // path halving
            x = g;
        }
        x
    }

    /// oracle: `equiv_manager::is_equiv`. Cheap pointer-eq fast path, then
    /// same-class lookup (absent nodes ⇒ not known equal).
    fn is_equiv(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) -> bool {
        if Arc::ptr_eq(t, s) {
            return true;
        }
        let a = match self.node_of(t) {
            Some(a) => a,
            None => return false,
        };
        let b = match self.node_of(s) {
            Some(b) => b,
            None => return false,
        };
        self.find(a) == self.find(b)
    }

    /// oracle: `equiv_manager::add_equiv`.
    fn merge(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) {
        let a = self.add_node(t);
        let b = self.add_node(s);
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.parent[ra] = rb;
        }
    }
}

/// The kernel type checker (oracle: `class type_checker`,
/// type_checker.h). Holds the environment it checks against, the current
/// local context / fresh-fvar generator, the recursion guard, and the
/// memo caches the oracle keeps in its shared `state`.
pub struct TypeChecker<'e> {
    env: &'e Environment,
    /// oracle: `m_definition_safety`. `Safe` unless admitting an unsafe
    /// decl (never, for our Replay-based admission); kept for parity so
    /// `infer_constant`'s unsafe/partial gates read like the oracle.
    safety: DefinitionSafety,
    /// oracle: `m_lparams` — the level params `check` was invoked with;
    /// `check_level` validates every referenced `Param` against it.
    lparams: Vec<Arc<Name>>,
    lctx: LocalContext,
    fvar_gen: FVarIdGen,
    /// `RecGuard` for the free functions of Tasks 2-5 (they still take a
    /// `&mut RecGuard`); the checker's own frames use `guard_depth`.
    guard: RecGuard,
    guard_depth: u32,
    /// oracle: `m_infer_type[2]` — one cache per `infer_only` flag
    /// (type_checker.cpp:276-301), keyed by pointer identity.
    infer_cache: [HashMap<ExprPtr, Arc<Expr>>; 2],
    /// oracle: `m_whnf` (type_checker.cpp:660-677).
    whnf_cache: HashMap<ExprPtr, Arc<Expr>>,
    /// oracle: `m_whnf_core` (type_checker.cpp:423-480; only the
    /// `!cheap_rec && !cheap_proj` results are cached).
    whnf_core_cache: HashMap<ExprPtr, Arc<Expr>>,
    /// oracle: `m_eqv_manager` (type_checker.cpp:741/1136).
    eqv_cache: UnionFind,
    /// oracle: `m_failure` (type_checker.cpp:845-861).
    failure_cache: HashSet<(ExprPtr, ExprPtr)>,
    /// `mk_const("dontcare")` placeholder for unused `is_def_eq_binding`
    /// telescope slots (oracle: `g_dont_care`, type_checker.cpp:1196).
    dont_care: Arc<Expr>,
    /// `Bool.true` (oracle: `g_bool_true`, type_checker.cpp:1193) — used
    /// by the reflection fast path in `is_def_eq_core`.
    bool_true: Arc<Name>,
    /// `Nat` / `String`, the literal types (oracle: `lit_type`,
    /// expr.cpp — `Nat`/`String` constants).
    nat_name: Arc<Name>,
    string_name: Arc<Name>,
}

fn mk_name1(part: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: part.to_string(),
    })
}

fn mk_name2(a: &str, b: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: mk_name1(a),
        part: b.to_string(),
    })
}

/// `has_loose_bvars(e)` (oracle: expr.h) — the cached range is nonzero.
fn has_loose_bvars(e: &Arc<Expr>) -> bool {
    e.data().loose_bvar_range() != 0
}

/// A `Nat` small enough to index a slice, or `None` (oracle: `is_small` /
/// `get_small_value`, util/nat.h). Never truncates.
fn nat_to_usize(n: &Nat) -> Option<usize> {
    let digits = n.0.to_u64_digits();
    if digits.len() > 1 {
        return None;
    }
    let v = digits.first().copied().unwrap_or(0);
    usize::try_from(v).ok()
}

/// `is_constant(e, name)` (oracle: expr.h) — a `Const` node whose name is
/// exactly `name` (levels ignored).
fn is_const_named(e: &Arc<Expr>, name: &Arc<Name>) -> bool {
    matches!(e.node(), ExprNode::Const { name: n, .. } if n == name)
}

/// `info.has_value()` (oracle: declaration.h:466) — `Defn`/`Thm` carry a
/// value the kernel may delta-unfold (opaque needs `allow_opaque`, which
/// the checker never passes).
fn info_has_value(info: &ConstantInfo) -> bool {
    matches!(info, ConstantInfo::Defn(_) | ConstantInfo::Thm(_))
}

/// The value of a `has_value` constant.
fn info_value(info: &ConstantInfo) -> Option<&Arc<Expr>> {
    match info {
        ConstantInfo::Defn(v) => Some(&v.value),
        ConstantInfo::Thm(v) => Some(&v.value),
        _ => None,
    }
}

/// oracle: `constant_info::get_hints` (declaration.cpp:294) — a
/// definition's own hints; everything else is `Opaque`.
fn info_hints(info: &ConstantInfo) -> ReducibilityHints {
    match info {
        ConstantInfo::Defn(v) => v.hints,
        _ => ReducibilityHints::Opaque,
    }
}

/// oracle: `constant_info::is_unsafe` — the per-kind unsafe bit.
fn info_is_unsafe(info: &ConstantInfo) -> bool {
    match info {
        ConstantInfo::Axiom(v) => v.is_unsafe,
        ConstantInfo::Defn(v) => v.safety == DefinitionSafety::Unsafe,
        ConstantInfo::Opaque(v) => v.is_unsafe,
        ConstantInfo::Induct(v) => v.is_unsafe,
        ConstantInfo::Ctor(v) => v.is_unsafe,
        ConstantInfo::Rec(v) => v.is_unsafe,
        ConstantInfo::Thm(_) | ConstantInfo::Quot(_) => false,
    }
}

/// oracle: declaration.cpp:24 (`compare(reducibility_hints)`): `< 0`
/// unfold the first, `> 0` unfold the second, `== 0` unfold both.
fn compare_hints(h1: ReducibilityHints, h2: ReducibilityHints) -> i32 {
    use ReducibilityHints::{Abbrev, Opaque, Regular};
    match (h1, h2) {
        (Regular(a), Regular(b)) => {
            if a == b {
                0
            } else if a > b {
                -1
            } else {
                1
            }
        }
        _ if h1 == h2 => 0, // Opaque/Opaque or Abbrev/Abbrev
        (Opaque, _) => 1,
        (_, Opaque) => -1,
        (Abbrev, _) => -1,
        (_, Abbrev) => 1,
    }
}

/// oracle: `string_lit_to_constructor` (inductive.cpp:1200) — expand a
/// string literal to `String.ofList (List.cons.{0} Char (Char.ofNat c₀)
/// (… (List.nil.{0} Char)))`. Shared with Task 7's string-lit expansion;
/// landed here for `reduce_proj_core`'s string case (brief step 3).
fn string_lit_to_constructor(s: &str, g: &mut RecGuard) -> Result<Arc<Expr>, KernelError> {
    let zero = Arc::new(Level::Zero);
    let char_ty = Expr::const_(mk_name1("Char"), vec![], g)?;
    let list_nil = Expr::const_(mk_name2("List", "nil"), vec![Arc::clone(&zero)], g)?;
    let list_cons = Expr::const_(mk_name2("List", "cons"), vec![zero], g)?;
    let char_of_nat = Expr::const_(mk_name2("Char", "ofNat"), vec![], g)?;
    let string_mk = Expr::const_(mk_name2("String", "ofList"), vec![], g)?;
    // g_list_nil_char / g_list_cons_char are `List.nil/cons.{0}` applied
    // to `Char` (inductive.cpp:1228-1231).
    let nil = Expr::app(list_nil, Arc::clone(&char_ty));
    let cons_char = Expr::app(list_cons, char_ty);
    let mut r = nil;
    for cp in s.chars().rev() {
        let lit = Expr::lit(Literal::NatVal(Nat::from(cp as u64)));
        let c = Expr::app(Arc::clone(&char_of_nat), lit);
        r = Expr::app(Expr::app(Arc::clone(&cons_char), c), r);
    }
    Ok(Expr::app(string_mk, r))
}

/// oracle: level.cpp:274 (`get_undef_param`) — first `Param` in `l` not
/// present in `ps`, else `None`. Guarded structural walk (the oracle's
/// `for_each` with a `has_param` short-circuit; we visit all, same
/// result).
fn get_undef_param(
    l: &Arc<Level>,
    ps: &[Arc<Name>],
    g: &mut RecGuard,
) -> Result<Option<Arc<Name>>, KernelError> {
    match l.as_ref() {
        Level::Zero | Level::MVar(_) => Ok(None),
        Level::Param(n) => {
            if ps.iter().any(|p| p.as_ref() == n.as_ref()) {
                Ok(None)
            } else {
                Ok(Some(Arc::clone(n)))
            }
        }
        Level::Succ(a) => {
            let a = Arc::clone(a);
            g.enter(|g| get_undef_param(&a, ps, g))
        }
        Level::Max(a, b) | Level::IMax(a, b) => {
            let (a, b) = (Arc::clone(a), Arc::clone(b));
            g.enter(|g| {
                if let Some(n) = get_undef_param(&a, ps, g)? {
                    return Ok(Some(n));
                }
                get_undef_param(&b, ps, g)
            })
        }
    }
}

/// oracle: instantiate.cpp:211 (`cheap_beta_reduce`). A cheap partial
/// beta step used to shrink inferred types (type_checker.cpp:130/217):
/// peel `min(#lambdas, #args)` binders; if the resulting head is closed,
/// apply the leftover args; if it is a bound var of a peeled binder,
/// select that arg; otherwise give up and return `e`. Iterative; no
/// substitution, so infallible and guard-free.
fn cheap_beta_reduce(e: &Arc<Expr>) -> Arc<Expr> {
    if !e.is_app() {
        return Arc::clone(e);
    }
    let fn0 = Expr::get_app_fn(e);
    if !fn0.is_lambda() {
        return Arc::clone(e);
    }
    let args = Expr::get_app_args(e);
    let mut cur = Arc::clone(fn0);
    let mut i = 0usize;
    while i < args.len() {
        if let ExprNode::Lam { body, .. } = cur.node() {
            let b = Arc::clone(body);
            i += 1;
            cur = b;
        } else {
            break;
        }
    }
    if cur.data().loose_bvar_range() == 0 {
        Expr::mk_app_spine(cur, &args[i..])
    } else if let ExprNode::BVar { idx } = cur.node() {
        match nat_to_usize(idx) {
            // `bvar_idx < i` for well-formed input (oracle asserts it);
            // if not, fall back to the untouched `e` rather than panic.
            Some(k) if k < i => Expr::mk_app_spine(Arc::clone(&args[i - k - 1]), &args[i..]),
            _ => Arc::clone(e),
        }
    } else {
        Arc::clone(e)
    }
}

impl<'e> TypeChecker<'e> {
    pub fn new(env: &'e Environment) -> TypeChecker<'e> {
        // `mk_const("dontcare")` cannot fail (empty level list ⇒ no
        // guarded level walk); a throwaway guard suffices.
        let dont_care = Expr::const_(mk_name1("dontcare"), vec![], &mut RecGuard::new())
            .expect("mk_const with no levels is infallible");
        TypeChecker {
            env,
            safety: DefinitionSafety::Safe,
            lparams: Vec::new(),
            lctx: LocalContext::default(),
            fvar_gen: FVarIdGen::default(),
            guard: RecGuard::new(),
            guard_depth: 0,
            infer_cache: [HashMap::new(), HashMap::new()],
            whnf_cache: HashMap::new(),
            whnf_core_cache: HashMap::new(),
            eqv_cache: UnionFind::default(),
            failure_cache: HashSet::new(),
            dont_care,
            bool_true: mk_name2("Bool", "true"),
            nat_name: mk_name1("Nat"),
            string_name: mk_name1("String"),
        }
    }

    /// The checker's own guarded frame (see the module doc comment for
    /// why this cannot reuse `self.guard`). Same constants as `RecGuard`.
    fn guarded<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<R, KernelError>,
    ) -> Result<R, KernelError> {
        if self.guard_depth >= MAX_REC_DEPTH {
            return Err(KernelError::DeepRecursion);
        }
        self.guard_depth += 1;
        let r = stacker::maybe_grow(RED_ZONE, STACK_CHUNK, || f(self));
        self.guard_depth -= 1;
        r
    }

    // -- Public entry points ------------------------------------------

    /// oracle: type_checker.cpp:308-312 — THE public checking entry.
    pub fn check(
        &mut self,
        e: &Arc<Expr>,
        lparams: &[Arc<Name>],
    ) -> Result<Arc<Expr>, KernelError> {
        self.lparams = lparams.to_vec();
        self.infer_type_core(e, false)
    }

    /// oracle: type_checker.cpp:304.
    pub fn infer_type(&mut self, e: &Arc<Expr>) -> Result<Arc<Expr>, KernelError> {
        self.infer_type_core(e, true)
    }

    /// oracle: type_checker.cpp:53 (`ensure_sort_core`): the whnf of `e`
    /// is a `Sort`, else `type expected`.
    pub fn ensure_sort(&mut self, e: &Arc<Expr>) -> Result<Arc<Expr>, KernelError> {
        if e.is_sort() {
            return Ok(Arc::clone(e));
        }
        let new_e = self.whnf(e)?;
        if new_e.is_sort() {
            Ok(new_e)
        } else {
            Err(KernelError::TypeExpected)
        }
    }

    /// oracle: type_checker.cpp:65 (`ensure_pi_core`).
    pub fn ensure_pi(&mut self, e: &Arc<Expr>) -> Result<Arc<Expr>, KernelError> {
        if e.is_forall() {
            return Ok(Arc::clone(e));
        }
        let new_e = self.whnf(e)?;
        if new_e.is_forall() {
            Ok(new_e)
        } else {
            Err(KernelError::FunctionExpected)
        }
    }

    /// oracle: type_checker.cpp:327 — `whnf(infer_type(e)) == Prop`.
    pub fn is_prop(&mut self, e: &Arc<Expr>) -> Result<bool, KernelError> {
        let ty = self.infer_type(e)?;
        let w = self.whnf(&ty)?;
        Ok(matches!(w.node(), ExprNode::Sort { level } if level.is_zero()))
    }

    // -- infer --------------------------------------------------------

    /// oracle: type_checker.cpp:270-302. Rejects loose bvars / mvars;
    /// caches per `infer_only`; strips `mdata` transparently.
    fn infer_type_core(
        &mut self,
        e: &Arc<Expr>,
        infer_only: bool,
    ) -> Result<Arc<Expr>, KernelError> {
        self.guarded(|slf| {
            // type_checker.cpp:271-272.
            if has_loose_bvars(e) {
                return Err(KernelError::LooseBVar);
            }
            let idx = infer_only as usize;
            if let Some(r) = slf.infer_cache[idx].get(&ExprPtr(Arc::clone(e))) {
                return Ok(Arc::clone(r));
            }
            let r = match e.node() {
                ExprNode::Lit(l) => slf.infer_lit(l)?,
                // type_checker.cpp:283 — mdata transparent.
                ExprNode::MData { expr, .. } => {
                    let inner = Arc::clone(expr);
                    slf.infer_type_core(&inner, infer_only)?
                }
                ExprNode::Proj { .. } => slf.infer_proj(e, infer_only)?,
                ExprNode::FVar { .. } => slf.infer_fvar(e)?,
                ExprNode::MVar { .. } => return Err(KernelError::MetavarEncountered),
                // type_checker.cpp:287-288 (`lean_unreachable`): a closed
                // input has no loose BVar; the guard above already caught
                // one, but keep an explicit error rather than panic.
                ExprNode::BVar { .. } => return Err(KernelError::LooseBVar),
                ExprNode::Sort { level } => {
                    if !infer_only {
                        let l = Arc::clone(level);
                        slf.check_level(&l)?;
                    }
                    let l = Arc::clone(level);
                    Expr::sort(Level::mk_succ(l), &mut slf.guard)?
                }
                ExprNode::Const { .. } => slf.infer_constant(e, infer_only)?,
                ExprNode::Lam { .. } => slf.infer_lambda(e, infer_only)?,
                ExprNode::ForallE { .. } => slf.infer_pi(e, infer_only)?,
                ExprNode::App { .. } => slf.infer_app(e, infer_only)?,
                ExprNode::LetE { .. } => slf.infer_let(e, infer_only)?,
            };
            slf.infer_cache[idx].insert(ExprPtr(Arc::clone(e)), Arc::clone(&r));
            Ok(r)
        })
    }

    /// oracle: `lit_type` — a literal's type is the `Nat`/`String` const.
    fn infer_lit(&mut self, l: &Literal) -> Result<Arc<Expr>, KernelError> {
        let name = match l {
            Literal::NatVal(_) => Arc::clone(&self.nat_name),
            Literal::StrVal(_) => Arc::clone(&self.string_name),
        };
        Expr::const_(name, vec![], &mut self.guard)
    }

    /// oracle: type_checker.cpp:76-82 (`check_level`). An undefined
    /// universe param maps to the nearest existing `KernelError`,
    /// `UnivParamArityMismatch` (the frozen error list has no dedicated
    /// undefined-universe-param variant; the controller sanctioned this
    /// stretch — a level-scope error at a named constant/sort).
    fn check_level(&mut self, l: &Arc<Level>) -> Result<(), KernelError> {
        if let Some(n) = get_undef_param(l, &self.lparams, &mut self.guard)? {
            return Err(KernelError::UnivParamArityMismatch { name: n });
        }
        Ok(())
    }

    /// oracle: type_checker.cpp:84-90 (`infer_fvar`). An fvar not in the
    /// local context is a kernel-invariant violation; the oracle throws
    /// "unknown free variable" (no dedicated variant here — admission
    /// rejects stray fvars via `HasFVars`, so this is unreachable for
    /// admitted decls). Nearest existing variant: `LooseBVar` (an
    /// unresolvable variable reference).
    fn infer_fvar(&self, e: &Arc<Expr>) -> Result<Arc<Expr>, KernelError> {
        if let ExprNode::FVar { id } = e.node() {
            if let Some(decl) = self.lctx.get(id) {
                return Ok(Arc::clone(&decl.ty));
            }
        }
        Err(KernelError::LooseBVar)
    }

    /// oracle: type_checker.cpp:92-114 (`infer_constant`).
    fn infer_constant(
        &mut self,
        e: &Arc<Expr>,
        infer_only: bool,
    ) -> Result<Arc<Expr>, KernelError> {
        // Copy the env reference out of `self` so the returned
        // `&ConstantInfo` borrows the environment (lifetime 'e), not
        // `self` — freeing `&mut self` for `check_level`/instantiate.
        let env = self.env;
        let (name, levels) = match e.node() {
            ExprNode::Const { name, levels } => (name, levels),
            _ => return Err(KernelError::LooseBVar), // unreachable
        };
        let info = env.get_with(name)?;
        let cv = info.constant_val();
        if cv.level_params.len() != levels.len() {
            return Err(KernelError::UnivParamArityMismatch {
                name: Arc::clone(name),
            });
        }
        if !infer_only {
            // type_checker.cpp:101-103.
            if info_is_unsafe(info) && self.safety != DefinitionSafety::Unsafe {
                return Err(KernelError::UnsafeConstInSafeDecl(Arc::clone(name)));
            }
            // type_checker.cpp:105-107: a safe decl must not use a partial
            // one. No dedicated variant; reuse `UnsafeConstInSafeDecl`
            // (partial ≈ unsafe-in-a-safe-context), documented.
            if let ConstantInfo::Defn(d) = info {
                if d.safety == DefinitionSafety::Partial && self.safety == DefinitionSafety::Safe {
                    return Err(KernelError::UnsafeConstInSafeDecl(Arc::clone(name)));
                }
            }
            // type_checker.cpp:109-111.
            for l in levels {
                self.check_level(l)?;
            }
        }
        // type_checker.cpp:113 (`instantiate_type_lparams`).
        instantiate_level_params(&cv.ty, &cv.level_params, levels, &mut self.guard)
    }

    /// oracle: type_checker.cpp:116-132 (`infer_lambda`).
    fn infer_lambda(&mut self, e: &Arc<Expr>, infer_only: bool) -> Result<Arc<Expr>, KernelError> {
        let saved = self.lctx.save(); // flet<local_ctx>
        let r = self.infer_lambda_body(e, infer_only);
        self.lctx.restore(saved);
        r
    }

    fn infer_lambda_body(
        &mut self,
        e0: &Arc<Expr>,
        infer_only: bool,
    ) -> Result<Arc<Expr>, KernelError> {
        let mut fvars: Vec<Arc<Expr>> = Vec::new();
        let mut e = Arc::clone(e0);
        while let ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = e.node()
        {
            let bn = Arc::clone(binder_name);
            let bt = Arc::clone(binder_type);
            let bi = *binder_info;
            let next = Arc::clone(body);
            let d = instantiate_rev(&bt, &fvars, &mut self.guard)?;
            let fvar = self
                .lctx
                .mk_local_decl(&mut self.fvar_gen, &bn, Arc::clone(&d), bi);
            fvars.push(fvar);
            if !infer_only {
                let dty = self.infer_type_core(&d, infer_only)?;
                self.ensure_sort(&dty)?;
            }
            e = next;
        }
        let inst = instantiate_rev(&e, &fvars, &mut self.guard)?;
        let r = self.infer_type_core(&inst, infer_only)?;
        let r = cheap_beta_reduce(&r);
        self.lctx.mk_pi(&fvars, &r, &mut self.guard)
    }

    /// oracle: type_checker.cpp:134-156 (`infer_pi`).
    fn infer_pi(&mut self, e: &Arc<Expr>, infer_only: bool) -> Result<Arc<Expr>, KernelError> {
        let saved = self.lctx.save();
        let r = self.infer_pi_body(e, infer_only);
        self.lctx.restore(saved);
        r
    }

    fn infer_pi_body(
        &mut self,
        e0: &Arc<Expr>,
        infer_only: bool,
    ) -> Result<Arc<Expr>, KernelError> {
        let mut fvars: Vec<Arc<Expr>> = Vec::new();
        let mut us: Vec<Arc<Level>> = Vec::new();
        let mut e = Arc::clone(e0);
        while let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = e.node()
        {
            let bn = Arc::clone(binder_name);
            let bt = Arc::clone(binder_type);
            let bi = *binder_info;
            let next = Arc::clone(body);
            let d = instantiate_rev(&bt, &fvars, &mut self.guard)?;
            let dty = self.infer_type_core(&d, infer_only)?;
            let t1 = self.ensure_sort(&dty)?;
            let lvl = match t1.node() {
                ExprNode::Sort { level } => Arc::clone(level),
                _ => return Err(KernelError::TypeExpected), // ensure_sort guarantees Sort
            };
            us.push(lvl);
            let fvar = self.lctx.mk_local_decl(&mut self.fvar_gen, &bn, d, bi);
            fvars.push(fvar);
            e = next;
        }
        let inst = instantiate_rev(&e, &fvars, &mut self.guard)?;
        let sty = self.infer_type_core(&inst, infer_only)?;
        let s = self.ensure_sort(&sty)?;
        let mut r = match s.node() {
            ExprNode::Sort { level } => Arc::clone(level),
            _ => return Err(KernelError::TypeExpected),
        };
        let mut i = fvars.len();
        while i > 0 {
            i -= 1;
            r = Level::mk_imax_pair(Arc::clone(&us[i]), r, &mut self.guard)?;
        }
        Expr::sort(r, &mut self.guard)
    }

    /// oracle: type_checker.cpp:163-196 (`infer_app`). The `!infer_only`
    /// branch checks each argument; the `infer_only` branch walks the Pi
    /// spine without checking. (The oracle's `eagerReduce` special-case
    /// at 168-173 is a reduction-mode flag with no bearing on the result;
    /// omitted — it collapses to the plain `is_def_eq` path.)
    fn infer_app(&mut self, e: &Arc<Expr>, infer_only: bool) -> Result<Arc<Expr>, KernelError> {
        if !infer_only {
            let (f, arg) = match e.node() {
                ExprNode::App { f, arg } => (Arc::clone(f), Arc::clone(arg)),
                _ => return Err(KernelError::LooseBVar), // unreachable
            };
            let ft = self.infer_type_core(&f, infer_only)?;
            let f_type = self.ensure_pi(&ft)?;
            let a_type = self.infer_type_core(&arg, infer_only)?;
            let (d_type, body) = match f_type.node() {
                ExprNode::ForallE {
                    binder_type, body, ..
                } => (Arc::clone(binder_type), Arc::clone(body)),
                _ => return Err(KernelError::FunctionExpected),
            };
            if !self.is_def_eq(&a_type, &d_type)? {
                return Err(KernelError::AppTypeMismatch);
            }
            instantiate(&body, &arg, &mut self.guard)
        } else {
            let args = Expr::get_app_args(e);
            let f = Arc::clone(Expr::get_app_fn(e));
            let mut f_type = self.infer_type_core(&f, true)?;
            let mut j = 0usize;
            let nargs = args.len();
            for i in 0..nargs {
                if f_type.is_forall() {
                    f_type = match f_type.node() {
                        ExprNode::ForallE { body, .. } => Arc::clone(body),
                        _ => unreachable!(),
                    };
                } else {
                    f_type = instantiate_rev(&f_type, &args[j..i], &mut self.guard)?;
                    f_type = self.ensure_pi(&f_type)?;
                    f_type = match f_type.node() {
                        ExprNode::ForallE { body, .. } => Arc::clone(body),
                        _ => return Err(KernelError::FunctionExpected),
                    };
                    j = i;
                }
            }
            instantiate_rev(&f_type, &args[j..nargs], &mut self.guard)
        }
    }

    /// oracle: type_checker.cpp:198-219 (`infer_let`). Walks nested lets,
    /// accumulating value-carrying fvars (`mk_let_decl`), infers the body
    /// in that context, and re-wraps via `mk_pi` (whose let-decls rebuild
    /// `let` bindings).
    fn infer_let(&mut self, e: &Arc<Expr>, infer_only: bool) -> Result<Arc<Expr>, KernelError> {
        let saved = self.lctx.save();
        let r = self.infer_let_body(e, infer_only);
        self.lctx.restore(saved);
        r
    }

    fn infer_let_body(
        &mut self,
        e0: &Arc<Expr>,
        infer_only: bool,
    ) -> Result<Arc<Expr>, KernelError> {
        let mut fvars: Vec<Arc<Expr>> = Vec::new();
        let mut e = Arc::clone(e0);
        while let ExprNode::LetE {
            decl_name,
            ty,
            value,
            body,
            ..
        } = e.node()
        {
            let dn = Arc::clone(decl_name);
            let t = Arc::clone(ty);
            let v = Arc::clone(value);
            let next = Arc::clone(body);
            let type_ = instantiate_rev(&t, &fvars, &mut self.guard)?;
            let val = instantiate_rev(&v, &fvars, &mut self.guard)?;
            let fvar = self.lctx.mk_let_decl(
                &mut self.fvar_gen,
                &dn,
                Arc::clone(&type_),
                Arc::clone(&val),
            );
            fvars.push(fvar);
            if !infer_only {
                let tty = self.infer_type_core(&type_, infer_only)?;
                self.ensure_sort(&tty)?;
                let val_type = self.infer_type_core(&val, infer_only)?;
                if !self.is_def_eq(&val_type, &type_)? {
                    return Err(KernelError::LetTypeMismatch);
                }
            }
            e = next;
        }
        let inst = instantiate_rev(&e, &fvars, &mut self.guard)?;
        let r = self.infer_type_core(&inst, infer_only)?;
        let r = cheap_beta_reduce(&r);
        self.lctx.mk_pi(&fvars, &r, &mut self.guard)
    }

    /// oracle: type_checker.cpp:221-266 (`infer_proj`). Every malformed
    /// shape ⇒ `InvalidProj` (never a panic).
    fn infer_proj(&mut self, e: &Arc<Expr>, infer_only: bool) -> Result<Arc<Expr>, KernelError> {
        let (proj_name, idx, structure) = match e.node() {
            ExprNode::Proj {
                type_name,
                idx,
                structure,
            } => (Arc::clone(type_name), idx.clone(), Arc::clone(structure)),
            _ => return Err(KernelError::InvalidProj),
        };
        let sty = self.infer_type_core(&structure, infer_only)?;
        let type_ = self.whnf(&sty)?;
        let idxv = match nat_to_usize(&idx) {
            Some(v) => v,
            None => return Err(KernelError::InvalidProj),
        };
        let args = Expr::get_app_args(&type_);
        let head = Expr::get_app_fn(&type_);
        let (i_name, i_levels) = match head.node() {
            ExprNode::Const { name, levels } => (Arc::clone(name), levels.clone()),
            _ => return Err(KernelError::InvalidProj),
        };
        if i_name != proj_name {
            return Err(KernelError::InvalidProj);
        }
        let env = self.env;
        let i_info = env.get_with(&i_name)?;
        let i_val = match i_info {
            ConstantInfo::Induct(v) => v,
            _ => return Err(KernelError::InvalidProj),
        };
        let nparams = match nat_to_usize(&i_val.num_params) {
            Some(v) => v,
            None => return Err(KernelError::InvalidProj),
        };
        let nindices = match nat_to_usize(&i_val.num_indices) {
            Some(v) => v,
            None => return Err(KernelError::InvalidProj),
        };
        if i_val.ctors.len() != 1 || args.len() != nparams + nindices {
            return Err(KernelError::InvalidProj);
        }
        let ctor_name = Arc::clone(&i_val.ctors[0]);
        let c_info = env.get_with(&ctor_name)?;
        let c_cv = c_info.constant_val();
        // type_checker.cpp:241 (`instantiate_type_lparams(c_info, const_levels(I))`).
        let mut r =
            instantiate_level_params(&c_cv.ty, &c_cv.level_params, &i_levels, &mut self.guard)?;
        // type_checker.cpp:242-247: strip the parameters.
        for arg in args.iter().take(nparams) {
            r = self.whnf(&r)?;
            let body = match r.node() {
                ExprNode::ForallE { body, .. } => Arc::clone(body),
                _ => return Err(KernelError::InvalidProj),
            };
            r = instantiate(&body, arg, &mut self.guard)?;
        }
        // type_checker.cpp:248-259: walk to the idx-th field.
        let is_prop_type = self.is_prop(&type_)?;
        for i in 0..idxv {
            r = self.whnf(&r)?;
            let (dom, body) = match r.node() {
                ExprNode::ForallE {
                    binder_type, body, ..
                } => (Arc::clone(binder_type), Arc::clone(body)),
                _ => return Err(KernelError::InvalidProj),
            };
            if has_loose_bvars(&body) {
                if is_prop_type && !self.is_prop(&dom)? {
                    return Err(KernelError::InvalidProj);
                }
                let proj = Expr::proj(
                    Arc::clone(&i_name),
                    Nat::from(i as u64),
                    Arc::clone(&structure),
                );
                r = instantiate(&body, &proj, &mut self.guard)?;
            } else {
                r = body;
            }
        }
        // type_checker.cpp:260-265.
        r = self.whnf(&r)?;
        let dom = match r.node() {
            ExprNode::ForallE { binder_type, .. } => Arc::clone(binder_type),
            _ => return Err(KernelError::InvalidProj),
        };
        if is_prop_type && !self.is_prop(&dom)? {
            return Err(KernelError::InvalidProj);
        }
        Ok(dom)
    }

    // -- whnf ---------------------------------------------------------

    /// oracle: type_checker.cpp:389-396 (`is_let_fvar`).
    fn is_let_fvar(&self, e: &Arc<Expr>) -> bool {
        matches!(e.node(), ExprNode::FVar { id }
            if self.lctx.get(id).is_some_and(|d| d.value.is_some()))
    }

    /// oracle: type_checker.cpp:641-681 (`whnf`).
    pub fn whnf(&mut self, e: &Arc<Expr>) -> Result<Arc<Expr>, KernelError> {
        self.guarded(|slf| {
            // Easy cases: not cached (type_checker.cpp:643-657).
            match e.node() {
                ExprNode::BVar { .. }
                | ExprNode::Sort { .. }
                | ExprNode::MVar { .. }
                | ExprNode::ForallE { .. }
                | ExprNode::Lit(_) => return Ok(Arc::clone(e)),
                ExprNode::MData { expr, .. } => {
                    let inner = Arc::clone(expr);
                    return slf.whnf(&inner);
                }
                ExprNode::FVar { .. } => {
                    if !slf.is_let_fvar(e) {
                        return Ok(Arc::clone(e));
                    }
                }
                ExprNode::Lam { .. }
                | ExprNode::App { .. }
                | ExprNode::Const { .. }
                | ExprNode::LetE { .. }
                | ExprNode::Proj { .. } => {}
            }
            if let Some(r) = slf.whnf_cache.get(&ExprPtr(Arc::clone(e))) {
                return Ok(Arc::clone(r));
            }
            let mut t = Arc::clone(e);
            loop {
                let t1 = slf.whnf_core(&t, false, false)?;
                if let Some(v) = slf.reduce_native(&t1)? {
                    slf.whnf_cache
                        .insert(ExprPtr(Arc::clone(e)), Arc::clone(&v));
                    return Ok(v);
                } else if let Some(v) = slf.reduce_nat(&t1)? {
                    slf.whnf_cache
                        .insert(ExprPtr(Arc::clone(e)), Arc::clone(&v));
                    return Ok(v);
                } else if let Some(next) = slf.unfold_definition(&t1)? {
                    t = next;
                } else {
                    slf.whnf_cache
                        .insert(ExprPtr(Arc::clone(e)), Arc::clone(&t1));
                    return Ok(t1);
                }
            }
        })
    }

    /// oracle: type_checker.cpp:401-483 (`whnf_core`). Beta / zeta /
    /// projection reduction plus normalizer-extension dispatch; does not
    /// delta-reduce. `cheap_rec`/`cheap_proj` plumb straight through.
    fn whnf_core(
        &mut self,
        e: &Arc<Expr>,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<Arc<Expr>, KernelError> {
        self.guarded(|slf| {
            // Easy cases (type_checker.cpp:405-420).
            match e.node() {
                ExprNode::BVar { .. }
                | ExprNode::Sort { .. }
                | ExprNode::MVar { .. }
                | ExprNode::ForallE { .. }
                | ExprNode::Const { .. }
                | ExprNode::Lam { .. }
                | ExprNode::Lit(_) => return Ok(Arc::clone(e)),
                ExprNode::MData { expr, .. } => {
                    let inner = Arc::clone(expr);
                    return slf.whnf_core(&inner, cheap_rec, cheap_proj);
                }
                ExprNode::FVar { .. } => {
                    if !slf.is_let_fvar(e) {
                        return Ok(Arc::clone(e));
                    }
                }
                ExprNode::App { .. } | ExprNode::LetE { .. } | ExprNode::Proj { .. } => {}
            }
            if let Some(r) = slf.whnf_core_cache.get(&ExprPtr(Arc::clone(e))) {
                return Ok(Arc::clone(r));
            }
            let r = match e.node() {
                // type_checker.cpp:434-435 — early return, not cached.
                ExprNode::FVar { .. } => return slf.whnf_fvar(e, cheap_rec, cheap_proj),
                ExprNode::Proj { .. } => {
                    if let Some(m) = slf.reduce_proj(e, cheap_rec, cheap_proj)? {
                        slf.whnf_core(&m, cheap_rec, cheap_proj)?
                    } else {
                        Arc::clone(e)
                    }
                }
                ExprNode::App { .. } => {
                    let args = Expr::get_app_args(e);
                    let f0 = Arc::clone(Expr::get_app_fn(e));
                    let f = slf.whnf_core(&f0, cheap_rec, cheap_proj)?;
                    if f.is_lambda() {
                        // Beta: peel min(#lambdas, #args) binders, then
                        // instantiate the consumed prefix and re-apply the
                        // rest (type_checker.cpp:447-456).
                        let num_args = args.len();
                        let mut m = 1usize;
                        let mut cur = Arc::clone(&f);
                        loop {
                            let deeper = match cur.node() {
                                ExprNode::Lam { body, .. } if body.is_lambda() && m < num_args => {
                                    Arc::clone(body)
                                }
                                _ => break,
                            };
                            cur = deeper;
                            m += 1;
                        }
                        let body = match cur.node() {
                            ExprNode::Lam { body, .. } => Arc::clone(body),
                            _ => unreachable!(),
                        };
                        let inst = instantiate_rev(&body, &args[0..m], &mut slf.guard)?;
                        let applied = Expr::mk_app_spine(inst, &args[m..num_args]);
                        slf.whnf_core(&applied, cheap_rec, cheap_proj)?
                    } else if Arc::ptr_eq(&f, &f0) {
                        // Head did not reduce: try normalizer extensions
                        // (iota/quot) — Task 7 stub returns None.
                        match slf.reduce_recursor(e, cheap_rec, cheap_proj)? {
                            Some(r) => return slf.whnf_core(&r, cheap_rec, cheap_proj),
                            None => return Ok(Arc::clone(e)),
                        }
                    } else {
                        let applied = Expr::mk_app_spine(f, &args);
                        slf.whnf_core(&applied, cheap_rec, cheap_proj)?
                    }
                }
                // type_checker.cpp:474-476 — zeta.
                ExprNode::LetE { value, body, .. } => {
                    let inst = instantiate(&Arc::clone(body), &Arc::clone(value), &mut slf.guard)?;
                    slf.whnf_core(&inst, cheap_rec, cheap_proj)?
                }
                _ => unreachable!(),
            };
            if !cheap_rec && !cheap_proj {
                slf.whnf_core_cache
                    .insert(ExprPtr(Arc::clone(e)), Arc::clone(&r));
            }
            Ok(r)
        })
    }

    /// oracle: type_checker.cpp:348-356 (`whnf_fvar`) — zeta for a
    /// let-bound fvar.
    fn whnf_fvar(
        &mut self,
        e: &Arc<Expr>,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<Arc<Expr>, KernelError> {
        let val = match e.node() {
            ExprNode::FVar { id } => self.lctx.get(id).and_then(|d| d.value.clone()),
            _ => None,
        };
        match val {
            Some(v) => self.whnf_core(&v, cheap_rec, cheap_proj),
            None => Ok(Arc::clone(e)),
        }
    }

    /// oracle: type_checker.cpp:377-387 (`reduce_proj`).
    fn reduce_proj(
        &mut self,
        e: &Arc<Expr>,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<Option<Arc<Expr>>, KernelError> {
        let (idx, structure) = match e.node() {
            ExprNode::Proj { idx, structure, .. } => (idx.clone(), Arc::clone(structure)),
            _ => return Ok(None),
        };
        let idxv = match nat_to_usize(&idx) {
            Some(v) => v,
            None => return Ok(None),
        };
        let c = if cheap_proj {
            self.whnf_core(&structure, cheap_rec, cheap_proj)?
        } else {
            self.whnf(&structure)?
        };
        self.reduce_proj_core(&c, idxv)
    }

    /// oracle: type_checker.cpp:359-374 (`reduce_proj_core`). Includes the
    /// string-literal case (359-365).
    fn reduce_proj_core(
        &mut self,
        c: &Arc<Expr>,
        idx: usize,
    ) -> Result<Option<Arc<Expr>>, KernelError> {
        let c = if let ExprNode::Lit(Literal::StrVal(s)) = c.node() {
            let ctor = string_lit_to_constructor(s, &mut self.guard)?;
            self.whnf(&ctor)?
        } else {
            Arc::clone(c)
        };
        let args = Expr::get_app_args(&c);
        let mk = Expr::get_app_fn(&c);
        let name = match mk.node() {
            ExprNode::Const { name, .. } => name,
            _ => return Ok(None),
        };
        let env = self.env;
        let mk_info = env.get_with(name)?;
        let nparams = match mk_info {
            ConstantInfo::Ctor(v) => match nat_to_usize(&v.num_params) {
                Some(n) => n,
                None => return Ok(None),
            },
            _ => return Ok(None),
        };
        if nparams + idx < args.len() {
            Ok(Some(Arc::clone(&args[nparams + idx])))
        } else {
            Ok(None)
        }
    }

    /// oracle: type_checker.cpp:487-494 (`is_delta`) — the constant_info
    /// to unfold when `e`'s head is a value-carrying constant applied to
    /// the right number of universe levels, else `None`. The returned
    /// reference borrows the environment (lifetime 'e), independent of
    /// `&self`, so callers may hold it across `&mut self` calls.
    fn is_delta(&self, e: &Arc<Expr>) -> Option<&'e ConstantInfo> {
        let f = Expr::get_app_fn(e);
        if let ExprNode::Const { name, levels } = f.node() {
            let env = self.env;
            if let Some(info) = env.get(name) {
                if info_has_value(info) && info.constant_val().level_params.len() == levels.len() {
                    return Some(info);
                }
            }
        }
        None
    }

    /// oracle: type_checker.cpp:497-518 (`unfold_definition_core`). (The
    /// oracle's `m_unfold` memo is a pure-perf cache; instantiate is
    /// deterministic, so omitting it changes performance, not results —
    /// the brief's cache list does not include it.)
    fn unfold_definition_core(&mut self, e: &Arc<Expr>) -> Result<Option<Arc<Expr>>, KernelError> {
        if let ExprNode::Const { name, levels } = e.node() {
            let env = self.env;
            if let Some(info) = env.get(name) {
                if info_has_value(info) && info.constant_val().level_params.len() == levels.len() {
                    let value = info_value(info).expect("has_value ⇒ Some value");
                    let params = info.constant_val().level_params.clone();
                    let levels = levels.clone();
                    let result =
                        instantiate_level_params(value, &params, &levels, &mut self.guard)?;
                    return Ok(Some(result));
                }
            }
        }
        Ok(None)
    }

    /// oracle: type_checker.cpp:521-534 (`unfold_definition`).
    fn unfold_definition(&mut self, e: &Arc<Expr>) -> Result<Option<Arc<Expr>>, KernelError> {
        if e.is_app() {
            let f0 = Arc::clone(Expr::get_app_fn(e));
            match self.unfold_definition_core(&f0)? {
                Some(f) => {
                    let args = Expr::get_app_args(e);
                    Ok(Some(Expr::mk_app_spine(f, &args)))
                }
                None => Ok(None),
            }
        } else {
            self.unfold_definition_core(e)
        }
    }

    // -- Task 7 stubs (final signatures, exact oracle positions) ------

    /// oracle: type_checker.cpp:333-346 (`reduce_recursor`) — iota + quot.
    fn reduce_recursor(
        &mut self,
        _e: &Arc<Expr>,
        _cheap_rec: bool,
        _cheap_proj: bool,
    ) -> Result<Option<Arc<Expr>>, KernelError> {
        // M1b Task 7: iota-reduction (inductive recursors) and quotient
        // reduction.
        Ok(None)
    }

    /// oracle: type_checker.cpp:609-638 (`reduce_nat`).
    fn reduce_nat(&mut self, _e: &Arc<Expr>) -> Result<Option<Arc<Expr>>, KernelError> {
        // M1b Task 7: Nat literal built-in reductions.
        Ok(None)
    }

    /// oracle: type_checker.cpp:546-567 (`reduce_native`).
    fn reduce_native(&mut self, _e: &Arc<Expr>) -> Result<Option<Arc<Expr>>, KernelError> {
        // M1b Task 7: Lean.reduceBool / Lean.reduceNat native reduction.
        Ok(None)
    }

    /// oracle: type_checker.cpp:961-970 (`is_def_eq_offset`).
    fn is_def_eq_offset(&mut self, _t: &Arc<Expr>, _s: &Arc<Expr>) -> Result<Lbool, KernelError> {
        // M1b Task 7: Nat succ/zero offset defeq.
        Ok(Lbool::Undef)
    }

    /// oracle: type_checker.cpp:778-790 (`try_eta_expansion`).
    fn try_eta_expansion(&mut self, _t: &Arc<Expr>, _s: &Arc<Expr>) -> Result<bool, KernelError> {
        // M1b Task 7: eta-expansion for functions.
        Ok(false)
    }

    /// oracle: type_checker.cpp:793-809 (`try_eta_struct`).
    fn try_eta_struct(&mut self, _t: &Arc<Expr>, _s: &Arc<Expr>) -> Result<bool, KernelError> {
        // M1b Task 7: structure eta.
        Ok(false)
    }

    /// oracle: type_checker.cpp:1030-1041 (`try_string_lit_expansion`).
    fn try_string_lit_expansion(
        &mut self,
        _t: &Arc<Expr>,
        _s: &Arc<Expr>,
    ) -> Result<Lbool, KernelError> {
        // M1b Task 7: string literal vs String.ofList constructor.
        Ok(Lbool::Undef)
    }

    /// oracle: type_checker.cpp:1044-1054 (`is_def_eq_unit_like`).
    fn is_def_eq_unit_like(&mut self, _t: &Arc<Expr>, _s: &Arc<Expr>) -> Result<bool, KernelError> {
        // M1b Task 7: unit-like (single fieldless constructor) defeq.
        Ok(false)
    }

    // -- is_def_eq ----------------------------------------------------

    /// oracle: type_checker.cpp:1133-1138 (`is_def_eq`). On success,
    /// records the equivalence in the union-find.
    pub fn is_def_eq(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) -> Result<bool, KernelError> {
        let r = self.is_def_eq_core(t, s)?;
        if r {
            self.eqv_cache.merge(t, s);
        }
        Ok(r)
    }

    /// oracle: type_checker.cpp:740-763 (`quick_is_def_eq`) — the "easy
    /// cases". No hash fast-reject here (the oracle has none at this
    /// point, and defeq-unequal hashes prove nothing — defeq ≠
    /// structural).
    fn quick_is_def_eq(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) -> Result<Lbool, KernelError> {
        if self.eqv_cache.is_equiv(t, s) {
            return Ok(Lbool::True);
        }
        match (t.node(), s.node()) {
            (ExprNode::Lam { .. }, ExprNode::Lam { .. })
            | (ExprNode::ForallE { .. }, ExprNode::ForallE { .. }) => {
                Ok(to_lbool(self.is_def_eq_binding(t, s)?))
            }
            (ExprNode::Sort { level: lt }, ExprNode::Sort { level: ls }) => {
                let (a, b) = (Arc::clone(lt), Arc::clone(ls));
                Ok(to_lbool(Level::is_equivalent(&a, &b, &mut self.guard)?))
            }
            (ExprNode::MData { expr: et, .. }, ExprNode::MData { expr: es, .. }) => {
                let (a, b) = (Arc::clone(et), Arc::clone(es));
                Ok(to_lbool(self.is_def_eq(&a, &b)?))
            }
            (ExprNode::Lit(la), ExprNode::Lit(lb)) => Ok(to_lbool(la == lb)),
            // BVar/FVar/App/Const/Let/Proj (and mixed kinds): not an easy
            // case (type_checker.cpp:753-757).
            _ => Ok(Lbool::Undef),
        }
    }

    /// oracle: type_checker.cpp:690-717 (`is_def_eq_binding`).
    fn is_def_eq_binding(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) -> Result<bool, KernelError> {
        let saved = self.lctx.save();
        let r = self.is_def_eq_binding_body(t, s);
        self.lctx.restore(saved);
        r
    }

    fn is_def_eq_binding_body(
        &mut self,
        t0: &Arc<Expr>,
        s0: &Arc<Expr>,
    ) -> Result<bool, KernelError> {
        let mut subst: Vec<Arc<Expr>> = Vec::new();
        let mut t = Arc::clone(t0);
        let mut s = Arc::clone(s0);
        // The two nodes share their kind (invariant from quick_is_def_eq).
        let is_lam = t.is_lambda();
        loop {
            let (t_dom, t_body) = binder_dom_body(&t);
            let (s_dom, s_body, s_name, s_info) = binder_full(&s);
            let mut var_s_type: Option<Arc<Expr>> = None;
            if !Expr::structural_eq(&t_dom, &s_dom, &mut self.guard)? {
                let vst = instantiate_rev(&s_dom, &subst, &mut self.guard)?;
                let vtt = instantiate_rev(&t_dom, &subst, &mut self.guard)?;
                if !self.is_def_eq(&vtt, &vst)? {
                    return Ok(false);
                }
                var_s_type = Some(vst);
            }
            if has_loose_bvars(&t_body) || has_loose_bvars(&s_body) {
                let vst = match var_s_type {
                    Some(v) => v,
                    None => instantiate_rev(&s_dom, &subst, &mut self.guard)?,
                };
                let fvar = self
                    .lctx
                    .mk_local_decl(&mut self.fvar_gen, &s_name, vst, s_info);
                subst.push(fvar);
            } else {
                subst.push(Arc::clone(&self.dont_care));
            }
            t = t_body;
            s = s_body;
            let same = if is_lam {
                t.is_lambda() && s.is_lambda()
            } else {
                t.is_forall() && s.is_forall()
            };
            if !same {
                break;
            }
        }
        let ti = instantiate_rev(&t, &subst, &mut self.guard)?;
        let si = instantiate_rev(&s, &subst, &mut self.guard)?;
        self.is_def_eq(&ti, &si)
    }

    /// oracle: type_checker.cpp:767-775 (`is_def_eq_args`).
    fn is_def_eq_args(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) -> Result<bool, KernelError> {
        let mut t = Arc::clone(t);
        let mut s = Arc::clone(s);
        while t.is_app() && s.is_app() {
            let (tf, ta) = match t.node() {
                ExprNode::App { f, arg } => (Arc::clone(f), Arc::clone(arg)),
                _ => unreachable!(),
            };
            let (sf, sa) = match s.node() {
                ExprNode::App { f, arg } => (Arc::clone(f), Arc::clone(arg)),
                _ => unreachable!(),
            };
            if !self.is_def_eq(&ta, &sa)? {
                return Ok(false);
            }
            t = tf;
            s = sf;
        }
        Ok(!t.is_app() && !s.is_app())
    }

    /// oracle: type_checker.cpp:815-832 (`is_def_eq_app`).
    fn is_def_eq_app(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) -> Result<bool, KernelError> {
        if t.is_app() && s.is_app() {
            let t_args = Expr::get_app_args(t);
            let t_fn = Arc::clone(Expr::get_app_fn(t));
            let s_args = Expr::get_app_args(s);
            let s_fn = Arc::clone(Expr::get_app_fn(s));
            if self.is_def_eq(&t_fn, &s_fn)? && t_args.len() == s_args.len() {
                for (ta, sa) in t_args.iter().zip(s_args.iter()) {
                    if !self.is_def_eq(ta, sa)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// oracle: type_checker.cpp:836-843 (`is_def_eq_proof_irrel`). NOT a
    /// stub — proofs are pervasive.
    fn is_def_eq_proof_irrel(
        &mut self,
        t: &Arc<Expr>,
        s: &Arc<Expr>,
    ) -> Result<Lbool, KernelError> {
        let t_type = self.infer_type(t)?;
        if !self.is_prop(&t_type)? {
            return Ok(Lbool::Undef);
        }
        let s_type = self.infer_type(s)?;
        Ok(to_lbool(self.is_def_eq(&t_type, &s_type)?))
    }

    /// oracle: type_checker.cpp:727-737 (`is_def_eq(levels, levels)`).
    fn is_def_eq_levels(
        &mut self,
        ls1: &[Arc<Level>],
        ls2: &[Arc<Level>],
    ) -> Result<bool, KernelError> {
        if ls1.len() != ls2.len() {
            return Ok(false);
        }
        for (a, b) in ls1.iter().zip(ls2.iter()) {
            if !Level::is_equivalent(a, b, &mut self.guard)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// oracle: type_checker.cpp:845-855 (`failed_before`).
    fn failed_before(&self, t: &Arc<Expr>, s: &Arc<Expr>) -> bool {
        let (ht, hs) = (t.data().hash(), s.data().hash());
        if ht < hs {
            self.failure_cache
                .contains(&(ExprPtr(Arc::clone(t)), ExprPtr(Arc::clone(s))))
        } else if ht > hs {
            self.failure_cache
                .contains(&(ExprPtr(Arc::clone(s)), ExprPtr(Arc::clone(t))))
        } else {
            self.failure_cache
                .contains(&(ExprPtr(Arc::clone(t)), ExprPtr(Arc::clone(s))))
                || self
                    .failure_cache
                    .contains(&(ExprPtr(Arc::clone(s)), ExprPtr(Arc::clone(t))))
        }
    }

    /// oracle: type_checker.cpp:857-862 (`cache_failure`).
    fn cache_failure(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) {
        if t.data().hash() <= s.data().hash() {
            self.failure_cache
                .insert((ExprPtr(Arc::clone(t)), ExprPtr(Arc::clone(s))));
        } else {
            self.failure_cache
                .insert((ExprPtr(Arc::clone(s)), ExprPtr(Arc::clone(t))));
        }
    }

    /// oracle: type_checker.cpp:868-875 (`try_unfold_proj_app`).
    fn try_unfold_proj_app(&mut self, e: &Arc<Expr>) -> Result<Option<Arc<Expr>>, KernelError> {
        let f = Expr::get_app_fn(e);
        if f.is_proj() {
            let e_new = self.whnf_core(e, false, false)?;
            if !Arc::ptr_eq(&e_new, e) {
                return Ok(Some(e_new));
            }
        }
        Ok(None)
    }

    /// oracle: type_checker.cpp:884-941 (`lazy_delta_reduction_step`).
    /// Updates `t_n` / `s_n`.
    fn lazy_delta_reduction_step(
        &mut self,
        t_n: &mut Arc<Expr>,
        s_n: &mut Arc<Expr>,
    ) -> Result<ReductionStatus, KernelError> {
        let d_t = self.is_delta(t_n);
        let d_s = self.is_delta(s_n);
        match (d_t, d_s) {
            (None, None) => return Ok(ReductionStatus::DefUnknown),
            (Some(_), None) => {
                // type_checker.cpp:889-902.
                if let Some(s_new) = self.try_unfold_proj_app(s_n)? {
                    *s_n = s_new;
                } else {
                    *t_n = self.unfold_and_whnf(t_n)?;
                }
            }
            (None, Some(_)) => {
                // type_checker.cpp:903-909.
                if let Some(t_new) = self.try_unfold_proj_app(t_n)? {
                    *t_n = t_new;
                } else {
                    *s_n = self.unfold_and_whnf(s_n)?;
                }
            }
            (Some(dt), Some(ds)) => {
                // type_checker.cpp:910-933.
                let c = compare_hints(info_hints(dt), info_hints(ds));
                if c < 0 {
                    *t_n = self.unfold_and_whnf(t_n)?;
                } else if c > 0 {
                    *s_n = self.unfold_and_whnf(s_n)?;
                } else {
                    if t_n.is_app()
                        && s_n.is_app()
                        && std::ptr::eq(dt, ds)
                        && info_hints(dt).is_regular_hint()
                        && !self.failed_before(t_n, s_n)
                    {
                        let lt = const_levels_of_head(t_n);
                        let ls = const_levels_of_head(s_n);
                        if self.is_def_eq_levels(&lt, &ls)? && self.is_def_eq_args(t_n, s_n)? {
                            return Ok(ReductionStatus::DefEqual);
                        }
                        self.cache_failure(t_n, s_n);
                    }
                    *t_n = self.unfold_and_whnf(t_n)?;
                    *s_n = self.unfold_and_whnf(s_n)?;
                }
            }
        }
        match self.quick_is_def_eq(t_n, s_n)? {
            Lbool::True => Ok(ReductionStatus::DefEqual),
            Lbool::False => Ok(ReductionStatus::DefDiff),
            Lbool::Undef => Ok(ReductionStatus::Continue),
        }
    }

    /// `whnf_core(unfold_definition(e), false, true)` — the delta-unfold
    /// step (type_checker.cpp:901/908/913/915/931/932). `is_delta`
    /// guaranteed the unfold succeeds; a `None` (should be impossible) is
    /// treated as no progress by leaving `e` unchanged via the caller's
    /// `DefUnknown` handling — here we return `e` itself so the round's
    /// `quick_is_def_eq` re-probe drives termination.
    fn unfold_and_whnf(&mut self, e: &Arc<Expr>) -> Result<Arc<Expr>, KernelError> {
        match self.unfold_definition(e)? {
            Some(u) => self.whnf_core(&u, false, true),
            None => Ok(Arc::clone(e)),
        }
    }

    /// oracle: type_checker.cpp:973-999 (`lazy_delta_reduction`). Updates
    /// `t_n` / `s_n` even when returning `Undef`.
    fn lazy_delta_reduction(
        &mut self,
        t_n: &mut Arc<Expr>,
        s_n: &mut Arc<Expr>,
    ) -> Result<Lbool, KernelError> {
        self.guarded(|slf| {
            loop {
                let r = slf.is_def_eq_offset(t_n, s_n)?;
                if r != Lbool::Undef {
                    return Ok(r);
                }
                // type_checker.cpp:978-984 (reduce_nat is gated on no
                // fvars); reduce_nat/reduce_native are Task 7 stubs.
                if !t_n.data().has_fvar() && !s_n.data().has_fvar() {
                    if let Some(tv) = slf.reduce_nat(t_n)? {
                        return Ok(to_lbool(slf.is_def_eq_core(&tv, s_n)?));
                    }
                    if let Some(sv) = slf.reduce_nat(s_n)? {
                        return Ok(to_lbool(slf.is_def_eq_core(t_n, &sv)?));
                    }
                }
                if let Some(tv) = slf.reduce_native(t_n)? {
                    return Ok(to_lbool(slf.is_def_eq_core(&tv, s_n)?));
                }
                if let Some(sv) = slf.reduce_native(s_n)? {
                    return Ok(to_lbool(slf.is_def_eq_core(t_n, &sv)?));
                }
                match slf.lazy_delta_reduction_step(t_n, s_n)? {
                    ReductionStatus::Continue => {}
                    ReductionStatus::DefUnknown => return Ok(Lbool::Undef),
                    ReductionStatus::DefEqual => return Ok(Lbool::True),
                    ReductionStatus::DefDiff => return Ok(Lbool::False),
                }
            }
        })
    }

    /// oracle: type_checker.cpp:1008-1025 (`lazy_delta_proj_reduction`).
    fn lazy_delta_proj_reduction(
        &mut self,
        t_n: &mut Arc<Expr>,
        s_n: &mut Arc<Expr>,
        idx: &Nat,
    ) -> Result<bool, KernelError> {
        loop {
            match self.lazy_delta_reduction_step(t_n, s_n)? {
                ReductionStatus::Continue => {}
                ReductionStatus::DefEqual => return Ok(true),
                ReductionStatus::DefUnknown | ReductionStatus::DefDiff => {
                    if let Some(i) = nat_to_usize(idx) {
                        if let Some(t) = self.reduce_proj_core(t_n, i)? {
                            if let Some(s) = self.reduce_proj_core(s_n, i)? {
                                return self.is_def_eq_core(&t, &s);
                            }
                        }
                    }
                    return self.is_def_eq_core(t_n, s_n);
                }
            }
        }
    }

    /// oracle: type_checker.cpp:1056-1131 (`is_def_eq_core`). Branch order
    /// follows the oracle literally.
    fn is_def_eq_core(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) -> Result<bool, KernelError> {
        self.guarded(|slf| {
            // type_checker.cpp:1058-1060.
            let r = slf.quick_is_def_eq(t, s)?;
            if r != Lbool::Undef {
                return Ok(r == Lbool::True);
            }

            // type_checker.cpp:1066-1070: reflection fast path for
            // `decide`-style `_ =?= Bool.true`.
            if !t.data().has_fvar() && is_const_named(s, &slf.bool_true) {
                let wt = slf.whnf(t)?;
                if is_const_named(&wt, &slf.bool_true) {
                    return Ok(true);
                }
            }

            // type_checker.cpp:1079-1085: whnf both with cheap_proj.
            let mut t_n = slf.whnf_core(t, false, true)?;
            let mut s_n = slf.whnf_core(s, false, true)?;
            if !Arc::ptr_eq(&t_n, t) || !Arc::ptr_eq(&s_n, s) {
                let r = slf.quick_is_def_eq(&t_n, &s_n)?;
                if r != Lbool::Undef {
                    return Ok(r == Lbool::True);
                }
            }

            // type_checker.cpp:1087-1088.
            let r = slf.is_def_eq_proof_irrel(&t_n, &s_n)?;
            if r != Lbool::Undef {
                return Ok(r == Lbool::True);
            }

            // type_checker.cpp:1091-1092 (mutates t_n / s_n).
            let r = slf.lazy_delta_reduction(&mut t_n, &mut s_n)?;
            if r != Lbool::Undef {
                return Ok(r == Lbool::True);
            }

            // type_checker.cpp:1094-1096: const/const heads.
            if let (
                ExprNode::Const {
                    name: nt,
                    levels: lt,
                },
                ExprNode::Const {
                    name: ns,
                    levels: ls,
                },
            ) = (t_n.node(), s_n.node())
            {
                if nt == ns {
                    let (lt, ls) = (lt.clone(), ls.clone());
                    if slf.is_def_eq_levels(&lt, &ls)? {
                        return Ok(true);
                    }
                }
            }

            // type_checker.cpp:1098-1099: fvar/fvar.
            if let (ExprNode::FVar { id: it }, ExprNode::FVar { id: is }) = (t_n.node(), s_n.node())
            {
                if it == is {
                    return Ok(true);
                }
            }

            // type_checker.cpp:1101-1106: proj/proj.
            if let (
                ExprNode::Proj {
                    idx: ix_t,
                    structure: ct,
                    ..
                },
                ExprNode::Proj {
                    idx: ix_s,
                    structure: cs,
                    ..
                },
            ) = (t_n.node(), s_n.node())
            {
                if ix_t == ix_s {
                    let idx = ix_t.clone();
                    let mut tc = Arc::clone(ct);
                    let mut sc = Arc::clone(cs);
                    if slf.lazy_delta_proj_reduction(&mut tc, &mut sc, &idx)? {
                        return Ok(true);
                    }
                }
            }

            // type_checker.cpp:1108-1112: whnf again, reducing projections
            // via full whnf this time.
            let t_n_n = slf.whnf_core(&t_n, false, false)?;
            let s_n_n = slf.whnf_core(&s_n, false, false)?;
            if !Arc::ptr_eq(&t_n_n, &t_n) || !Arc::ptr_eq(&s_n_n, &s_n) {
                return slf.is_def_eq_core(&t_n_n, &s_n_n);
            }

            // type_checker.cpp:1115-1116.
            if slf.is_def_eq_app(&t_n, &s_n)? {
                return Ok(true);
            }
            // type_checker.cpp:1118-1119 — Task 7 stub.
            if slf.try_eta_expansion(&t_n, &s_n)? {
                return Ok(true);
            }
            // type_checker.cpp:1121-1122 — Task 7 stub.
            if slf.try_eta_struct(&t_n, &s_n)? {
                return Ok(true);
            }
            // type_checker.cpp:1124-1125 — Task 7 stub.
            let r = slf.try_string_lit_expansion(&t_n, &s_n)?;
            if r != Lbool::Undef {
                return Ok(r == Lbool::True);
            }
            // type_checker.cpp:1127-1128 — Task 7 stub.
            if slf.is_def_eq_unit_like(&t_n, &s_n)? {
                return Ok(true);
            }

            // type_checker.cpp:1130 — the oracle does NOT cache_failure
            // here (cache_failure fires only inside
            // lazy_delta_reduction_step, 927); the brief's "on false:
            // cache_failure" paraphrase is imprecise. Follow the oracle.
            Ok(false)
        })
    }
}

/// The domain/body of a binder node (Lam or ForallE).
fn binder_dom_body(e: &Arc<Expr>) -> (Arc<Expr>, Arc<Expr>) {
    match e.node() {
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => (Arc::clone(binder_type), Arc::clone(body)),
        _ => unreachable!("binder_dom_body on non-binder"),
    }
}

/// Domain/body plus binder name and info of a binder node.
fn binder_full(e: &Arc<Expr>) -> (Arc<Expr>, Arc<Expr>, Arc<Name>, BinderInfo) {
    match e.node() {
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        }
        | ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => (
            Arc::clone(binder_type),
            Arc::clone(body),
            Arc::clone(binder_name),
            *binder_info,
        ),
        _ => unreachable!("binder_full on non-binder"),
    }
}

/// Universe levels of an application's head constant (empty if the head
/// is not a `Const` — the callers only reach here with a const head).
fn const_levels_of_head(e: &Arc<Expr>) -> Vec<Arc<Level>> {
    match Expr::get_app_fn(e).node() {
        ExprNode::Const { levels, .. } => levels.clone(),
        _ => Vec::new(),
    }
}

impl ReducibilityHints {
    fn is_regular_hint(self) -> bool {
        matches!(self, ReducibilityHints::Regular(_))
    }
}

#[cfg(test)]
mod tests;
