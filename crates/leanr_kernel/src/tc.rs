//! The kernel type checker: `infer_type`, `whnf` (beta/zeta/delta/proj),
//! and the definitional-equality core. This is a function-for-function
//! port of the oracle's `src/kernel/type_checker.cpp` (pinned githash
//! b4812ae53eea93439ad5dce5a5c26591c31cb697, toolchain
//! leanprover/lean4:v4.32.0-rc1). Every method cites its oracle line
//! range; port order and branch order follow the oracle literally.
//!
//! Task 7 filled the special-reduction branches (iota / quot recursor
//! reduction, Nat literal folding, offset defeq, eta / struct eta /
//! unit-like / string-lit expansion). `reduce_native` (Lean's
//! `reduceBool`/`reduceNat`) remains a permanent skip-stub: it needs the
//! Lean compiler/runtime, out of scope for the pure-Rust kernel — terms
//! using it fail to reduce (incompleteness, never unsoundness).
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

use crate::quot_red::quot_reduce_rec;
use crate::{
    instantiate, instantiate_level_params, instantiate_rev, BinderInfo, ConstantInfo,
    DefinitionSafety, Environment, Expr, ExprNode, FVarIdGen, KernelError, Level, Literal,
    LocalContext, Name, Nat, RecGuard, RecursorRule, ReducibilityHints, MAX_REC_DEPTH,
};

/// Stack-growth constants: identical to `RecGuard`'s (guard.rs), which
/// are private there. The `guarded` self-method below grows the stack
/// with the same red-zone/chunk sizes rustc's own `stacker` use employs.
const RED_ZONE: usize = 128 * 1024;
const STACK_CHUNK: usize = 4 * 1024 * 1024;

/// oracle: type_checker.cpp:586 (`#define ReducePowMaxExp 1<<24`) — the
/// exact exponent above which `reduce_pow` refuses to fold, so untrusted
/// literals cannot force an unbounded `Nat.pow` computation.
const REDUCE_POW_MAX_EXP: usize = 1 << 24;

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
/// Port of `equiv_manager` (kernel/equiv_manager.{h,cpp}), the structure
/// backing `quick_is_def_eq` (type_checker.cpp:741) and `is_def_eq`'s
/// success merge (1136). `is_equiv` is a *structural* (alpha-,
/// binder-name-/info-insensitive) equality test memoised in a union-find:
/// once two subterms are proven equal their nodes are merged, so a later
/// pointer-distinct-but-structurally-equal comparison short-circuits at
/// the class lookup. This memoisation — absent from a pointer-only cache —
/// is what makes defeq of terms that reduce through the same stuck
/// sub-expression (e.g. `List.reverse`/`Poly.norm` on a symbolic list)
/// terminate instead of re-descending indefinitely.
///
/// Soundness: the structural comparison is exact (it never reports two
/// unequal terms as equal); `merge` only records pairs it just proved
/// equal. The `use_hash` fast-reject is sound because structurally equal
/// terms share a hash — a hash mismatch proves inequality.
#[derive(Default)]
struct UnionFind {
    /// `equiv_manager::m_nodes` — parent + rank, indexed by `node_ref`.
    parent: Vec<usize>,
    rank: Vec<u32>,
    /// `equiv_manager::m_to_node` — `Arc`-pointer-keyed node handles.
    index: HashMap<ExprPtr, usize>,
}

impl UnionFind {
    /// oracle: `equiv_manager::mk_node` + `to_node`. Named for the oracle;
    /// it interns (mutates), so `&mut self` is required despite the `to_`
    /// prefix clippy associates with by-value conversions.
    #[allow(clippy::wrong_self_convention)]
    fn to_node(&mut self, e: &Arc<Expr>) -> usize {
        if let Some(i) = self.index.get(&ExprPtr(Arc::clone(e))) {
            return *i;
        }
        let i = self.parent.len();
        self.parent.push(i);
        self.rank.push(0);
        self.index.insert(ExprPtr(Arc::clone(e)), i);
        i
    }

    /// oracle: `equiv_manager::find` (no path compression, matching the
    /// oracle's plain parent walk).
    fn find(&self, mut n: usize) -> usize {
        while self.parent[n] != n {
            n = self.parent[n];
        }
        n
    }

    /// oracle: `equiv_manager::merge` — union by rank.
    fn merge_refs(&mut self, n1: usize, n2: usize) {
        let r1 = self.find(n1);
        let r2 = self.find(n2);
        if r1 == r2 {
            return;
        }
        match self.rank[r1].cmp(&self.rank[r2]) {
            std::cmp::Ordering::Less => self.parent[r1] = r2,
            std::cmp::Ordering::Greater => self.parent[r2] = r1,
            std::cmp::Ordering::Equal => {
                self.parent[r2] = r1;
                self.rank[r1] += 1;
            }
        }
    }

    /// oracle: `equiv_manager::is_equiv` — sets the hash flag and delegates.
    fn is_equiv(
        &mut self,
        a: &Arc<Expr>,
        b: &Arc<Expr>,
        use_hash: bool,
        g: &mut RecGuard,
    ) -> Result<bool, KernelError> {
        self.is_equiv_core(a, b, use_hash, g)
    }

    /// oracle: `equiv_manager::is_equiv_core`. Structural equality up to
    /// alpha (binder names/infos ignored) and level `==`, short-circuited
    /// by pointer identity, the optional hash fast-reject, and the
    /// union-find class. Recursion threads `RecGuard` (the one sanctioned
    /// pattern): depth-capped and OS-stack-safe via `stacker`.
    fn is_equiv_core(
        &mut self,
        a: &Arc<Expr>,
        b: &Arc<Expr>,
        use_hash: bool,
        g: &mut RecGuard,
    ) -> Result<bool, KernelError> {
        if Arc::ptr_eq(a, b) {
            return Ok(true);
        }
        if use_hash && a.data().hash() != b.data().hash() {
            return Ok(false);
        }
        if let (ExprNode::BVar { idx: ia }, ExprNode::BVar { idx: ib }) = (a.node(), b.node()) {
            return Ok(ia == ib);
        }
        let na = self.to_node(a);
        let nb = self.to_node(b);
        let r1 = self.find(na);
        let r2 = self.find(nb);
        if r1 == r2 {
            return Ok(true);
        }
        // Fall back to structural equality (kind mismatch ⇒ not equal).
        let result = g.enter(|g| match (a.node(), b.node()) {
            (ExprNode::BVar { .. }, ExprNode::BVar { .. }) => unreachable!(),
            (
                ExprNode::Const {
                    name: n1,
                    levels: l1,
                },
                ExprNode::Const {
                    name: n2,
                    levels: l2,
                },
            ) => {
                if n1 != n2 || l1.len() != l2.len() {
                    return Ok(false);
                }
                for (x, y) in l1.iter().zip(l2.iter()) {
                    if !Level::structural_eq(x, y, g)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (ExprNode::MVar { id: i1 }, ExprNode::MVar { id: i2 }) => Ok(i1 == i2),
            (ExprNode::FVar { id: i1 }, ExprNode::FVar { id: i2 }) => Ok(i1 == i2),
            (ExprNode::App { f: f1, arg: a1 }, ExprNode::App { f: f2, arg: a2 }) => Ok(self
                .is_equiv_core(f1, f2, use_hash, g)?
                && self.is_equiv_core(a1, a2, use_hash, g)?),
            (
                ExprNode::Lam {
                    binder_type: d1,
                    body: b1,
                    ..
                },
                ExprNode::Lam {
                    binder_type: d2,
                    body: b2,
                    ..
                },
            )
            | (
                ExprNode::ForallE {
                    binder_type: d1,
                    body: b1,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: d2,
                    body: b2,
                    ..
                },
            ) => Ok(self.is_equiv_core(d1, d2, use_hash, g)?
                && self.is_equiv_core(b1, b2, use_hash, g)?),
            (ExprNode::Sort { level: l1 }, ExprNode::Sort { level: l2 }) => {
                Level::structural_eq(l1, l2, g)
            }
            (ExprNode::Lit(v1), ExprNode::Lit(v2)) => Ok(v1 == v2),
            (ExprNode::MData { expr: e1, .. }, ExprNode::MData { expr: e2, .. }) => {
                self.is_equiv_core(e1, e2, use_hash, g)
            }
            (
                ExprNode::Proj {
                    idx: ix1,
                    structure: s1,
                    ..
                },
                ExprNode::Proj {
                    idx: ix2,
                    structure: s2,
                    ..
                },
                // `type_name` (`..`) is deliberately ignored here, per the
                // oracle's `equiv_manager`; `ExprData::hash` DOES fold it
                // in, so `use_hash = true` can only false-*reject* on this
                // arm (incompleteness, never unsoundness) — don't "fix" it.
            ) => Ok(self.is_equiv_core(s1, s2, use_hash, g)? && ix1 == ix2),
            (
                ExprNode::LetE {
                    ty: t1,
                    value: v1,
                    body: b1,
                    ..
                },
                ExprNode::LetE {
                    ty: t2,
                    value: v2,
                    body: b2,
                    ..
                },
            ) => Ok(self.is_equiv_core(t1, t2, use_hash, g)?
                && self.is_equiv_core(v1, v2, use_hash, g)?
                && self.is_equiv_core(b1, b2, use_hash, g)?),
            _ => Ok(false),
        })?;
        if result {
            self.merge_refs(r1, r2);
        }
        Ok(result)
    }

    /// oracle: `equiv_manager::add_equiv`.
    fn merge(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) {
        let a = self.to_node(t);
        let b = self.to_node(s);
        self.merge_refs(a, b);
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
    /// oracle: `m_unfold` (type_checker.cpp:505-511) — memoizes
    /// `unfold_definition_core` for universe-polymorphic constants so a
    /// repeated unfold of one `Const` returns the SAME expr. Not just a
    /// speed cache: pointer-stable unfolds are what let the other
    /// pointer-keyed caches above hit on re-reduced terms; without it a
    /// reduction-heavy proof re-instantiates the same definition values
    /// millions of times (fresh pointers → every downstream cache
    /// misses → unbounded allocation churn).
    unfold_memo: HashMap<ExprPtr, Arc<Expr>>,
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
    /// `Bool.false` (oracle: `g_bool_false`) — `Nat.beq`/`Nat.ble`
    /// falsehood result in `reduce_nat`.
    bool_false: Arc<Name>,
    /// `Nat.zero` / `Nat.succ` (oracle: `g_nat_zero` / `g_nat_succ`) —
    /// consulted by `is_nat_lit_ext`, `reduce_nat` and offset defeq.
    nat_zero: Arc<Name>,
    nat_succ: Arc<Name>,
    /// `String.ofList` (oracle: `g_string_mk`, type_checker.cpp:1028) —
    /// the head `try_string_lit_expansion` matches against.
    string_mk: Arc<Name>,
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

/// oracle: inductive.cpp:1191-1198 (`nat_lit_to_constructor`) — a nat
/// literal in constructor form: `0 ↦ Nat.zero`, `n+1 ↦ Nat.succ n`.
fn nat_lit_to_constructor(
    e: &Arc<Expr>,
    nat_zero: &Arc<Name>,
    nat_succ: &Arc<Name>,
    g: &mut RecGuard,
) -> Result<Arc<Expr>, KernelError> {
    let v = match e.node() {
        ExprNode::Lit(Literal::NatVal(v)) => v,
        _ => return Ok(Arc::clone(e)),
    };
    if v.is_zero() {
        Expr::const_(Arc::clone(nat_zero), vec![], g)
    } else {
        let pred = Expr::lit(Literal::NatVal(v.sub(&Nat::from(1))));
        let succ = Expr::const_(Arc::clone(nat_succ), vec![], g)?;
        Ok(Expr::app(succ, pred))
    }
}

/// oracle: inductive.cpp:113-121 (`get_rec_rule_for`) — the recursor rule
/// whose constructor matches `major`'s head constant.
fn get_rec_rule_for<'a>(rules: &'a [RecursorRule], major: &Arc<Expr>) -> Option<&'a RecursorRule> {
    let fn0 = Expr::get_app_fn(major);
    let name = fn0.const_name()?;
    rules.iter().find(|r| &r.ctor == name)
}

/// oracle: declaration.cpp:145-154 (`recursor_val::get_major_induct`) —
/// the inductive being recursed on: skip `major_idx` binders of the
/// recursor's type, then read the head constant of the next binder's
/// domain (the major premise's type).
fn get_major_induct(ty: &Arc<Expr>, major_idx: usize) -> Option<Arc<Name>> {
    let mut t = Arc::clone(ty);
    for _ in 0..major_idx {
        t = match t.node() {
            ExprNode::ForallE { body, .. } => Arc::clone(body),
            _ => return None,
        };
    }
    let dom = match t.node() {
        ExprNode::ForallE { binder_type, .. } => Arc::clone(binder_type),
        _ => return None,
    };
    match Expr::get_app_fn(&dom).node() {
        ExprNode::Const { name, .. } => Some(Arc::clone(name)),
        _ => None,
    }
}

/// oracle: inductive.cpp:52-59 (`is_constructor_app`) — `e`'s head is a
/// `Const` naming a constructor of `env`.
fn is_constructor_app(env: &Environment, e: &Arc<Expr>) -> bool {
    if let ExprNode::Const { name, .. } = Expr::get_app_fn(e).node() {
        matches!(env.get(name), Some(ConstantInfo::Ctor(_)))
    } else {
        false
    }
}

/// The `Nat.<op>` builtin named by `name`, if any (oracle: `g_nat_*`
/// constants, type_checker.cpp:28-43). Recognizes a two-component name
/// `Nat.op` and returns `op`.
fn nat_binop(name: &Name) -> Option<&str> {
    if let Name::Str { parent, part } = name {
        if let Name::Str {
            parent: grand,
            part: ns,
        } = parent.as_ref()
        {
            if matches!(grand.as_ref(), Name::Anonymous) && ns == "Nat" {
                return Some(part.as_str());
            }
        }
    }
    None
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
            unfold_memo: HashMap::new(),
            dont_care,
            bool_true: mk_name2("Bool", "true"),
            nat_name: mk_name1("Nat"),
            string_name: mk_name1("String"),
            bool_false: mk_name2("Bool", "false"),
            nat_zero: mk_name2("Nat", "zero"),
            nat_succ: mk_name2("Nat", "succ"),
            string_mk: mk_name2("String", "ofList"),
        }
    }

    /// Build a checker seeded with a pre-populated local context and
    /// fvar generator. The inductive-admission pipeline (inductive.rs,
    /// Task 9) owns the persistent `local_ctx`/`name_generator` that the
    /// oracle's `add_inductive_fn` keeps in `m_lctx`/`m_ngen` and shares
    /// with each freshly-constructed `type_checker(m_env, m_lctx, ...)`
    /// (inductive.cpp:171). Rust cannot let `add_inductive_fn` hold both
    /// `&mut Environment` and a borrowing `TypeChecker` at once, so it
    /// instead *moves* its context in here per checker op and moves it
    /// back out via `into_parts`, keeping the `FVarIdGen` counter
    /// monotonic across both producers (so ids never collide even though
    /// both mint the same `_kernel_fresh.<n>` prefix — the oracle uses a
    /// distinct `_ind_fresh` prefix instead; a monotonic shared counter
    /// is an equivalent uniqueness guarantee, documented in inductive.rs).
    pub(crate) fn new_with(
        env: &'e Environment,
        lctx: LocalContext,
        fvar_gen: FVarIdGen,
    ) -> TypeChecker<'e> {
        let mut tc = TypeChecker::new(env);
        tc.lctx = lctx;
        tc.fvar_gen = fvar_gen;
        tc
    }

    /// Reclaim the (possibly-extended, then save/restore-trimmed) local
    /// context and the advanced fvar generator after a checker op. See
    /// `new_with`.
    pub(crate) fn into_parts(self) -> (LocalContext, FVarIdGen) {
        (self.lctx, self.fvar_gen)
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
                    // type_checker.cpp:505-511 — memoize the polymorphic
                    // (`len > 0`) case so a repeated unfold returns the
                    // SAME expr (see `unfold_memo`). The monomorphic case
                    // is already pointer-stable: `instantiate_level_params`
                    // returns `value` itself when nothing substitutes.
                    if !levels.is_empty() {
                        if let Some(r) = self.unfold_memo.get(&ExprPtr(Arc::clone(e))) {
                            return Ok(Some(Arc::clone(r)));
                        }
                    }
                    let value = info_value(info).expect("has_value ⇒ Some value");
                    let params = info.constant_val().level_params.clone();
                    let levels_owned = levels.clone();
                    let result =
                        instantiate_level_params(value, &params, &levels_owned, &mut self.guard)?;
                    if !levels_owned.is_empty() {
                        self.unfold_memo
                            .insert(ExprPtr(Arc::clone(e)), Arc::clone(&result));
                    }
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

    // -- Task 7: special reductions -----------------------------------

    /// `cheap_rec ? whnf_core(e, cheap_rec, cheap_proj) : whnf(e)` — the
    /// whnf callback `reduce_recursor` hands to `inductive_reduce_rec`
    /// (type_checker.cpp:340). `quot_reduce_rec` always gets full `whnf`
    /// (type_checker.cpp:335), never the cheap form.
    fn rec_whnf(
        &mut self,
        e: &Arc<Expr>,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<Arc<Expr>, KernelError> {
        if cheap_rec {
            self.whnf_core(e, cheap_rec, cheap_proj)
        } else {
            self.whnf(e)
        }
    }

    /// oracle: type_checker.cpp:333-346 (`reduce_recursor`) — apply the
    /// quotient and inductive normalizer extensions.
    fn reduce_recursor(
        &mut self,
        e: &Arc<Expr>,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<Option<Arc<Expr>>, KernelError> {
        // type_checker.cpp:334-338: quotient reduction (full whnf).
        if self.env.quot_initialized() {
            // Split the &mut borrow: `quot_reduce_rec` calls back into
            // `self.whnf`, so `self` is captured only by the closure.
            let r = quot_reduce_rec(e, |x| self.whnf(x))?;
            if r.is_some() {
                return Ok(r);
            }
        }
        // type_checker.cpp:339-344: inductive iota reduction.
        self.inductive_reduce_rec(e, cheap_rec, cheap_proj)
    }

    /// oracle: inductive.h:76-119 (`inductive_reduce_rec`). Iota-reduce a
    /// recursor application: whnf (and, for K-recursors / literal majors,
    /// canonicalize) the major premise to a constructor application, pick
    /// the matching rule, and beta-apply its `rhs` to the recursor's
    /// params/motives/minors followed by the constructor's fields.
    fn inductive_reduce_rec(
        &mut self,
        e: &Arc<Expr>,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<Option<Arc<Expr>>, KernelError> {
        // inductive.h:78-84.
        let rec_fn = Arc::clone(Expr::get_app_fn(e));
        let (rec_name, rec_levels) = match rec_fn.node() {
            ExprNode::Const { name, levels } => (Arc::clone(name), levels.clone()),
            _ => return Ok(None),
        };
        let env = self.env;
        let rec_val = match env.get(&rec_name) {
            Some(ConstantInfo::Rec(v)) => v,
            _ => return Ok(None),
        };
        // Extract everything needed before re-borrowing `self` mutably.
        let nparams = match nat_to_usize(&rec_val.num_params) {
            Some(v) => v,
            None => return Ok(None),
        };
        let nmotives = match nat_to_usize(&rec_val.num_motives) {
            Some(v) => v,
            None => return Ok(None),
        };
        let nminors = match nat_to_usize(&rec_val.num_minors) {
            Some(v) => v,
            None => return Ok(None),
        };
        let nindices = match nat_to_usize(&rec_val.num_indices) {
            Some(v) => v,
            None => return Ok(None),
        };
        let major_idx = nparams + nmotives + nminors + nindices;
        let is_k = rec_val.k;
        let lparams = rec_val.val.level_params.clone();
        let rules = rec_val.rules.clone();
        let rec_ty = Arc::clone(&rec_val.val.ty);

        // inductive.h:82-87.
        let rec_args = Expr::get_app_args(e);
        if major_idx >= rec_args.len() {
            return Ok(None); // major premise is missing
        }
        // recursor_val::get_major_induct (declaration.cpp:145-154).
        let major_induct = match get_major_induct(&rec_ty, major_idx) {
            Some(n) => n,
            None => return Ok(None),
        };
        let mut major = Arc::clone(&rec_args[major_idx]);
        // inductive.h:88-90: K-recursor major canonicalization.
        if is_k {
            major = self.to_cnstr_when_K(&major_induct, nparams, &major, cheap_rec, cheap_proj)?;
        }
        // inductive.h:91-97.
        major = self.rec_whnf(&major, cheap_rec, cheap_proj)?;
        major = match major.node() {
            ExprNode::Lit(Literal::NatVal(_)) => {
                nat_lit_to_constructor(&major, &self.nat_zero, &self.nat_succ, &mut self.guard)?
            }
            ExprNode::Lit(Literal::StrVal(s)) => {
                let c = string_lit_to_constructor(s, &mut self.guard)?;
                self.rec_whnf(&c, cheap_rec, cheap_proj)?
            }
            _ => self.to_cnstr_when_structure(&major_induct, &major, cheap_rec, cheap_proj)?,
        };
        // inductive.h:98-103.
        let rule = match get_rec_rule_for(&rules, &major) {
            Some(r) => r.clone(),
            None => return Ok(None),
        };
        let major_args = Expr::get_app_args(&major);
        let nfields = match nat_to_usize(&rule.nfields) {
            Some(v) => v,
            None => return Ok(None),
        };
        if nfields > major_args.len() {
            return Ok(None);
        }
        if rec_levels.len() != lparams.len() {
            return Ok(None);
        }
        // inductive.h:104-117: build the reduced right-hand side.
        let mut rhs = instantiate_level_params(&rule.rhs, &lparams, &rec_levels, &mut self.guard)?;
        // Params, motives and minor premises from the recursor application.
        let pmm = nparams + nmotives + nminors;
        rhs = Expr::mk_app_spine(rhs, &rec_args[..pmm]);
        // Fields from the major premise (the constructor's own params —
        // which for nested inductives may differ from the recursor's — are
        // dropped by taking the LAST `nfields` args).
        let nctor_params = major_args.len() - nfields;
        rhs = Expr::mk_app_spine(rhs, &major_args[nctor_params..]);
        // Reapply any surplus recursor-application args past the major.
        if rec_args.len() > major_idx + 1 {
            rhs = Expr::mk_app_spine(rhs, &rec_args[major_idx + 1..]);
        }
        Ok(Some(rhs))
    }

    /// oracle: inductive.h:31-50 (`to_cnstr_when_K`). For a K-supporting
    /// datatype, replace `e` by the datatype's unique constructor
    /// application when `e`'s type matches (e.g. `e : a = a` ↦ `Eq.refl
    /// a`). `rval.is_k()` is guaranteed by the caller.
    #[allow(non_snake_case)] // mirrors the oracle's `to_cnstr_when_K`
    #[allow(clippy::wrong_self_convention)] // oracle name; reduces `self`
    fn to_cnstr_when_K(
        &mut self,
        major_induct: &Arc<Name>,
        nparams: usize,
        e: &Arc<Expr>,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<Arc<Expr>, KernelError> {
        // inductive.h:34-36.
        let it = self.infer_type(e)?;
        let app_type = self.rec_whnf(&it, cheap_rec, cheap_proj)?;
        let app_type_i = Expr::get_app_fn(&app_type);
        if !is_const_named(app_type_i, major_induct) {
            return Ok(Arc::clone(e)); // type incorrect
        }
        // inductive.h:37-44: bail if an index carries a metavariable. Our
        // admitted terms are mvar-free, but the guard is ported for parity.
        if app_type.data().has_expr_mvar() {
            let app_type_args = Expr::get_app_args(&app_type);
            for arg in app_type_args.iter().skip(nparams) {
                if arg.data().has_expr_mvar() {
                    return Ok(Arc::clone(e));
                }
            }
        }
        // inductive.h:45-49.
        let new_cnstr_app = match self.mk_nullary_cnstr(&app_type, nparams)? {
            Some(c) => c,
            None => return Ok(Arc::clone(e)),
        };
        let new_type = self.infer_type(&new_cnstr_app)?;
        if !self.is_def_eq(&app_type, &new_type)? {
            return Ok(Arc::clone(e));
        }
        Ok(new_cnstr_app)
    }

    /// oracle: inductive.cpp:87-96 (`mk_nullary_cnstr`). Build the head
    /// constructor of `type`'s inductive applied to `type`'s first
    /// `num_params` arguments.
    fn mk_nullary_cnstr(
        &mut self,
        type_: &Arc<Expr>,
        num_params: usize,
    ) -> Result<Option<Arc<Expr>>, KernelError> {
        let args = Expr::get_app_args(type_);
        let d = Expr::get_app_fn(type_);
        let (d_name, d_levels) = match d.node() {
            ExprNode::Const { name, levels } => (Arc::clone(name), levels.clone()),
            _ => return Ok(None),
        };
        let cnstr_name = match self.first_cnstr(&d_name) {
            Some(c) => c,
            None => return Ok(None),
        };
        if args.len() < num_params {
            return Ok(None);
        }
        let cnstr = Expr::const_(cnstr_name, d_levels, &mut self.guard)?;
        Ok(Some(Expr::mk_app_spine(cnstr, &args[..num_params])))
    }

    /// oracle: inductive.h:62-73 (`to_cnstr_when_structure`). If `e` is not
    /// a constructor application and its type is a non-recursive, non-Prop
    /// structure `induct_name ...`, expand it via `expand_eta_struct`.
    #[allow(clippy::wrong_self_convention)] // oracle name; reduces `self`
    fn to_cnstr_when_structure(
        &mut self,
        induct_name: &Arc<Name>,
        e: &Arc<Expr>,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<Arc<Expr>, KernelError> {
        if !self.env.is_structure_like(induct_name) || is_constructor_app(self.env, e) {
            return Ok(Arc::clone(e));
        }
        let it = self.infer_type(e)?;
        let e_type = self.rec_whnf(&it, cheap_rec, cheap_proj)?;
        if !is_const_named(Expr::get_app_fn(&e_type), induct_name) {
            return Ok(Arc::clone(e));
        }
        // inductive.h:70-71: skip Prop-valued structures.
        let et = self.infer_type(&e_type)?;
        let etw = self.rec_whnf(&et, cheap_rec, cheap_proj)?;
        if matches!(etw.node(), ExprNode::Sort { level } if level.is_zero()) {
            return Ok(Arc::clone(e));
        }
        self.expand_eta_struct(&e_type, e)
    }

    /// oracle: inductive.cpp:98-111 (`expand_eta_struct`). Convert `e` into
    /// `mk e.0 … e.(n-1)` where `mk` is `e_type`'s constructor.
    fn expand_eta_struct(
        &mut self,
        e_type: &Arc<Expr>,
        e: &Arc<Expr>,
    ) -> Result<Arc<Expr>, KernelError> {
        let args = Expr::get_app_args(e_type);
        let i = Expr::get_app_fn(e_type);
        let (i_name, i_levels) = match i.node() {
            ExprNode::Const { name, levels } => (Arc::clone(name), levels.clone()),
            _ => return Ok(Arc::clone(e)),
        };
        let ctor_name = match self.first_cnstr(&i_name) {
            Some(c) => c,
            None => return Ok(Arc::clone(e)),
        };
        let (nparams, nfields) = match self.env.get(&ctor_name) {
            Some(ConstantInfo::Ctor(v)) => {
                (nat_to_usize(&v.num_params), nat_to_usize(&v.num_fields))
            }
            _ => return Ok(Arc::clone(e)),
        };
        let (nparams, nfields) = match (nparams, nfields) {
            (Some(p), Some(f)) => (p, f),
            _ => return Ok(Arc::clone(e)),
        };
        if args.len() < nparams {
            return Ok(Arc::clone(e));
        }
        let ctor = Expr::const_(ctor_name, i_levels, &mut self.guard)?;
        let mut result = Expr::mk_app_spine(ctor, &args[..nparams]);
        for f in 0..nfields {
            let proj = Expr::proj(Arc::clone(&i_name), Nat::from(f as u64), Arc::clone(e));
            result = Expr::app(result, proj);
        }
        Ok(result)
    }

    /// oracle: inductive.cpp:79-85 (`get_first_cnstr`) — first constructor
    /// of the (non-empty) inductive `name`.
    fn first_cnstr(&self, name: &Arc<Name>) -> Option<Arc<Name>> {
        match self.env.get(name) {
            Some(ConstantInfo::Induct(v)) => v.ctors.first().map(Arc::clone),
            _ => None,
        }
    }

    /// oracle: type_checker.cpp:609-638 (`reduce_nat`). Fold built-in
    /// `Nat.succ` / binary `Nat.*` operations on whnf-literal arguments.
    fn reduce_nat(&mut self, e: &Arc<Expr>) -> Result<Option<Arc<Expr>>, KernelError> {
        let nargs = Expr::get_app_num_args(e);
        if nargs == 1 {
            // type_checker.cpp:611-618: `Nat.succ lit → lit+1`.
            let (f, arg) = match e.node() {
                ExprNode::App { f, arg } => (f, arg),
                _ => return Ok(None),
            };
            if is_const_named(f, &self.nat_succ) {
                let arg = Arc::clone(arg);
                let v = match self.get_nat_lit_ext(&arg)? {
                    Some(v) => v,
                    None => return Ok(None),
                };
                return Ok(Some(Expr::lit(Literal::NatVal(v.add(&Nat::from(1))))));
            }
            return Ok(None);
        }
        if nargs != 2 {
            return Ok(None);
        }
        // type_checker.cpp:619-635: binary op dispatch on the head const.
        let (ff, a2) = match e.node() {
            ExprNode::App { f, arg } => (f, Arc::clone(arg)),
            _ => return Ok(None),
        };
        let (head, a1) = match ff.node() {
            ExprNode::App { f, arg } => (f, Arc::clone(arg)),
            _ => return Ok(None),
        };
        let op = match head.node() {
            ExprNode::Const { name, .. } => match nat_binop(name) {
                Some(o) => o,
                None => return Ok(None),
            },
            _ => return Ok(None),
        };
        // Both operands must whnf to nat literals (`is_nat_lit_ext`).
        let v1 = match self.get_nat_lit_ext(&a1)? {
            Some(v) => v,
            None => return Ok(None),
        };
        let v2 = match self.get_nat_lit_ext(&a2)? {
            Some(v) => v,
            None => return Ok(None),
        };
        let lit = |n: Nat| Expr::lit(Literal::NatVal(n));
        let r = match op {
            "add" => lit(v1.add(&v2)),
            "sub" => lit(v1.sub(&v2)),
            "mul" => lit(v1.mul(&v2)),
            "gcd" => lit(v1.gcd(&v2)),
            "mod" => lit(v1.modulo(&v2)),
            "div" => lit(v1.div(&v2)),
            "land" => lit(v1.land(&v2)),
            "lor" => lit(v1.lor(&v2)),
            "xor" => lit(v1.lxor(&v2)),
            // type_checker.cpp:586-597: refuse huge exponents.
            "pow" => match v2.to_usize() {
                Some(exp) if exp <= REDUCE_POW_MAX_EXP => lit(v1.pow(exp as u32)),
                _ => return Ok(None),
            },
            // A shift amount that does not fit `usize` cannot be
            // materialized (`Nat.shiftLeft`) — leave the term un-reduced
            // rather than attempt an unbounded allocation.
            "shiftLeft" => match v2.to_usize() {
                Some(k) => lit(v1.shiftl(k)),
                None => return Ok(None),
            },
            // A shift wider than the value's bit length is `0`.
            "shiftRight" => lit(v1.shiftr(v2.to_usize().unwrap_or(usize::MAX))),
            "beq" => self.bool_const(v1.beq(&v2))?,
            "ble" => self.bool_const(v1.ble(&v2))?,
            _ => return Ok(None),
        };
        Ok(Some(r))
    }

    /// `Bool.true` / `Bool.false` const (oracle: `mk_bool_true` /
    /// `mk_bool_false`).
    fn bool_const(&mut self, b: bool) -> Result<Arc<Expr>, KernelError> {
        let name = if b {
            Arc::clone(&self.bool_true)
        } else {
            Arc::clone(&self.bool_false)
        };
        Expr::const_(name, vec![], &mut self.guard)
    }

    /// oracle: type_checker.cpp:569-574 (`is_nat_lit_ext` / `get_nat_val`).
    /// whnf `e`, then read its `Nat` value if it is a nat literal or the
    /// `Nat.zero` constant, else `None`.
    fn get_nat_lit_ext(&mut self, e: &Arc<Expr>) -> Result<Option<Nat>, KernelError> {
        let w = self.whnf(e)?;
        match w.node() {
            ExprNode::Lit(Literal::NatVal(v)) => Ok(Some(v.clone())),
            ExprNode::Const { name, .. } if name == &self.nat_zero => Ok(Some(Nat::from(0))),
            _ => Ok(None),
        }
    }

    /// oracle: type_checker.cpp:546-567 (`reduce_native`). Native
    /// `Lean.reduceBool` / `Lean.reduceNat` compile-and-run reduction. A
    /// permanent skip-stub: it requires the Lean compiler/runtime, which
    /// is out of scope for the pure-Rust kernel. Terms using it fail to
    /// reduce here (incompleteness, never unsoundness); documented in the
    /// codebase map.
    fn reduce_native(&mut self, _e: &Arc<Expr>) -> Result<Option<Arc<Expr>>, KernelError> {
        Ok(None)
    }

    /// oracle: type_checker.cpp:961-969 (`is_def_eq_offset`). Peel
    /// `Nat.succ`/literal towers off both sides and compare the stems.
    fn is_def_eq_offset(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) -> Result<Lbool, KernelError> {
        if self.is_nat_zero(t) && self.is_nat_zero(s) {
            return Ok(Lbool::True);
        }
        let pred_t = self.is_nat_succ(t);
        let pred_s = self.is_nat_succ(s);
        if let (Some(pt), Some(ps)) = (pred_t, pred_s) {
            return Ok(to_lbool(self.is_def_eq_core(&pt, &ps)?));
        }
        Ok(Lbool::Undef)
    }

    /// oracle: type_checker.cpp:943-945 (`is_nat_zero`).
    fn is_nat_zero(&self, t: &Arc<Expr>) -> bool {
        is_const_named(t, &self.nat_zero)
            || matches!(t.node(), ExprNode::Lit(Literal::NatVal(v)) if v.is_zero())
    }

    /// oracle: type_checker.cpp:947-959 (`is_nat_succ`) — the predecessor
    /// of `t`, from either a positive nat literal or a `Nat.succ _` app.
    fn is_nat_succ(&self, t: &Arc<Expr>) -> Option<Arc<Expr>> {
        if let ExprNode::Lit(Literal::NatVal(v)) = t.node() {
            if !v.is_zero() {
                return Some(Expr::lit(Literal::NatVal(v.sub(&Nat::from(1)))));
            }
        }
        if is_const_named(Expr::get_app_fn(t), &self.nat_succ) && Expr::get_app_num_args(t) == 1 {
            if let ExprNode::App { arg, .. } = t.node() {
                return Some(Arc::clone(arg));
            }
        }
        None
    }

    /// oracle: type_checker.h:87-89 / type_checker.cpp:778-790
    /// (`try_eta_expansion` + `_core`). Tries both argument orders.
    fn try_eta_expansion(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) -> Result<bool, KernelError> {
        if self.try_eta_expansion_core(t, s)? {
            return Ok(true);
        }
        self.try_eta_expansion_core(s, t)
    }

    /// oracle: type_checker.cpp:778-790 (`try_eta_expansion_core`). Solve
    /// `(λ x, _) =?= s` by comparing against `λ x, s x`.
    fn try_eta_expansion_core(
        &mut self,
        t: &Arc<Expr>,
        s: &Arc<Expr>,
    ) -> Result<bool, KernelError> {
        if !t.is_lambda() || s.is_lambda() {
            return Ok(false);
        }
        let st = self.infer_type(s)?;
        let s_type = self.whnf(&st)?;
        let (bn, dom, bi) = match s_type.node() {
            ExprNode::ForallE {
                binder_name,
                binder_type,
                binder_info,
                ..
            } => (
                Arc::clone(binder_name),
                Arc::clone(binder_type),
                *binder_info,
            ),
            _ => return Ok(false),
        };
        // `s` is loose-bvar-free here, so placing it under the new binder
        // and applying `bvar 0` needs no lifting (oracle: `mk_app(s,
        // mk_bvar(0))`).
        let body = Expr::app(Arc::clone(s), Expr::bvar(Nat::from(0)));
        let new_s = Expr::lam(bn, dom, body, bi);
        self.is_def_eq(t, &new_s)
    }

    /// oracle: type_checker.h:91-93 / type_checker.cpp:793-809
    /// (`try_eta_struct` + `_core`). Tries both argument orders.
    fn try_eta_struct(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) -> Result<bool, KernelError> {
        if self.try_eta_struct_core(t, s)? {
            return Ok(true);
        }
        self.try_eta_struct_core(s, t)
    }

    /// oracle: type_checker.cpp:793-809 (`try_eta_struct_core`). Check
    /// whether `s` is `mk t.0 … t.n` for a non-recursive structure and, if
    /// so, compare fieldwise via projections on `t`.
    fn try_eta_struct_core(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) -> Result<bool, KernelError> {
        let f = Expr::get_app_fn(s);
        let fname = match f.node() {
            ExprNode::Const { name, .. } => name,
            _ => return Ok(false),
        };
        let env = self.env;
        let (nparams, nfields, induct) = match env.get(fname) {
            Some(ConstantInfo::Ctor(v)) => (
                nat_to_usize(&v.num_params),
                nat_to_usize(&v.num_fields),
                Arc::clone(&v.induct),
            ),
            _ => return Ok(false),
        };
        let (nparams, nfields) = match (nparams, nfields) {
            (Some(p), Some(f)) => (p, f),
            _ => return Ok(false),
        };
        if Expr::get_app_num_args(s) != nparams + nfields {
            return Ok(false);
        }
        if !self.env.is_structure_like(&induct) {
            return Ok(false);
        }
        let tt = self.infer_type(t)?;
        let ss = self.infer_type(s)?;
        if !self.is_def_eq(&tt, &ss)? {
            return Ok(false);
        }
        let s_args = Expr::get_app_args(s);
        for (i, sa) in s_args.iter().enumerate().skip(nparams) {
            let proj = Expr::proj(
                Arc::clone(&induct),
                Nat::from((i - nparams) as u64),
                Arc::clone(t),
            );
            if !self.is_def_eq(&proj, sa)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// oracle: type_checker.cpp:1037-1041 (`try_string_lit_expansion`).
    /// Tries both argument orders.
    fn try_string_lit_expansion(
        &mut self,
        t: &Arc<Expr>,
        s: &Arc<Expr>,
    ) -> Result<Lbool, KernelError> {
        let r = self.try_string_lit_expansion_core(t, s)?;
        if r != Lbool::Undef {
            return Ok(r);
        }
        self.try_string_lit_expansion_core(s, t)
    }

    /// oracle: type_checker.cpp:1030-1035 (`try_string_lit_expansion_core`).
    /// `strLit =?= String.ofList _` reduces the literal to its `String.ofList`
    /// char-list form and compares.
    fn try_string_lit_expansion_core(
        &mut self,
        t: &Arc<Expr>,
        s: &Arc<Expr>,
    ) -> Result<Lbool, KernelError> {
        if let ExprNode::Lit(Literal::StrVal(str_val)) = t.node() {
            if s.is_app() && is_const_named(Expr::get_app_fn(s), &self.string_mk) {
                let ctor = string_lit_to_constructor(str_val, &mut self.guard)?;
                let w = self.whnf(&ctor)?;
                return Ok(to_lbool(self.is_def_eq_core(&w, s)?));
            }
        }
        Ok(Lbool::Undef)
    }

    /// oracle: type_checker.cpp:1044-1054 (`is_def_eq_unit_like`). Two
    /// terms whose types whnf to the same fieldless structure inductive
    /// are equal.
    fn is_def_eq_unit_like(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) -> Result<bool, KernelError> {
        let tt = self.infer_type(t)?;
        let t_type = self.whnf(&tt)?;
        let i = Expr::get_app_fn(&t_type);
        let i_name = match i.node() {
            ExprNode::Const { name, .. } => Arc::clone(name),
            _ => return Ok(false),
        };
        if !self.env.is_structure_like(&i_name) {
            return Ok(false);
        }
        let ctor_name = match self.first_cnstr(&i_name) {
            Some(c) => c,
            None => return Ok(false),
        };
        let nfields = match self.env.get(&ctor_name) {
            Some(ConstantInfo::Ctor(v)) => nat_to_usize(&v.num_fields),
            _ => return Ok(false),
        };
        if nfields != Some(0) {
            return Ok(false);
        }
        let st = self.infer_type(s)?;
        self.is_def_eq_core(&t_type, &st)
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
    fn quick_is_def_eq(
        &mut self,
        t: &Arc<Expr>,
        s: &Arc<Expr>,
        use_hash: bool,
    ) -> Result<Lbool, KernelError> {
        if self.eqv_cache.is_equiv(t, s, use_hash, &mut self.guard)? {
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
        match self.quick_is_def_eq(t_n, s_n, false)? {
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
            // type_checker.cpp:1058-1060 (`use_hash = true`).
            let r = slf.quick_is_def_eq(t, s, true)?;
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
                let r = slf.quick_is_def_eq(&t_n, &s_n, false)?;
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
