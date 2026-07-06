//! The id-based kernel type checker (migration Task 4): a
//! representation-only port of `crate::tc` (`infer_type`, `whnf`,
//! `is_def_eq`) onto the term bank. Every method below cites the same
//! oracle line range its Arc counterpart does; port order and branch
//! order follow the Arc source literally. Porting rules (verbatim from
//! the task brief): `e.node()` -> `self.node(e)`; `Expr::app(f,a)` ->
//! `self.scratch.expr_app(base, f, a)?`; pointer-keyed caches -> plain
//! `ExprId`-keyed caches (the interning invariant makes `==` the exact
//! id-space analog of `Arc::ptr_eq`, with strictly more hits);
//! `Expr::structural_eq(a,b,g)?` -> `a == b` (no guard); env lookups ->
//! `self.env_get_with(name)?` (a thin `Option<NameId>`-aware wrapper
//! around `EnvView::get`/`get_with`, see its own doc comment for why it
//! does not call `EnvView::get_with` directly); `instantiate*` ->
//! `bank::subst::*`.
//!
//! `EnvView` is defined here per the brief (Task 6's `Environment::view()`
//! will produce it).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use super::decl::{ConstantInfo, RecursorRule};
use super::local_ctx::{FVarIdGen, LocalContext};
use super::names::NameRow;
use super::quot_red::{self, QuotCtx};
use super::subst::{instantiate, instantiate_level_params, instantiate_rev};
use super::terms::Node;
use super::{ExprId, LevelId, NameId, Store};
use crate::{
    BinderInfo, DefinitionSafety, KernelError, Level, Name, Nat, RecGuard, ReducibilityHints,
    MAX_REC_DEPTH,
};

/// Stack-growth constants: identical to `RecGuard`'s (guard.rs), which
/// are private there.
const RED_ZONE: usize = 128 * 1024;
const STACK_CHUNK: usize = 4 * 1024 * 1024;

/// oracle: type_checker.cpp:586 (`#define ReducePowMaxExp 1<<24`).
const REDUCE_POW_MAX_EXP: usize = 1 << 24;

/// Three-valued result, oracle `lbool`.
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

/// oracle: `reduction_status` (type_checker.h).
enum ReductionStatus {
    Continue,
    DefUnknown,
    DefEqual,
    DefDiff,
}

/// Path-compressing union-find over expressions by structural identity.
/// Port of `equiv_manager` (kernel/equiv_manager.{h,cpp}). `index` is
/// keyed by raw id bits (`ExprId::bits()`), not a pointer wrapper: the
/// interning invariant (equal ids <=> structurally equal terms) makes
/// this sound, and `to_node`/`find`/`merge_refs`/`merge` need no store
/// access at all — only `is_equiv_core`'s structural fallback does,
/// threaded in as explicit `st`/`base` parameters (an `ExprId` cannot
/// decode itself the way an `Arc<Expr>` can).
#[derive(Default)]
struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<u32>,
    index: HashMap<u32, usize>,
}

impl UnionFind {
    #[allow(clippy::wrong_self_convention)]
    fn to_node(&mut self, e: ExprId) -> usize {
        if let Some(&i) = self.index.get(&e.bits()) {
            return i;
        }
        let i = self.parent.len();
        self.parent.push(i);
        self.rank.push(0);
        self.index.insert(e.bits(), i);
        i
    }

    fn find(&self, mut n: usize) -> usize {
        while self.parent[n] != n {
            n = self.parent[n];
        }
        n
    }

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

    fn is_equiv(
        &mut self,
        st: &Store,
        base: Option<&Store>,
        a: ExprId,
        b: ExprId,
        use_hash: bool,
        g: &mut RecGuard,
    ) -> Result<bool, KernelError> {
        self.is_equiv_core(st, base, a, b, use_hash, g)
    }

    /// oracle: `equiv_manager::is_equiv_core`. Structural equality up to
    /// alpha (binder names/infos ignored) and level structural equality,
    /// short-circuited by id equality (interning invariant — strictly
    /// more hits than the oracle's pointer check), the optional hash
    /// fast-reject, and the union-find class.
    fn is_equiv_core(
        &mut self,
        st: &Store,
        base: Option<&Store>,
        a: ExprId,
        b: ExprId,
        use_hash: bool,
        g: &mut RecGuard,
    ) -> Result<bool, KernelError> {
        if a == b {
            return Ok(true);
        }
        if use_hash && st.expr_data(base, a).hash() != st.expr_data(base, b).hash() {
            return Ok(false);
        }
        let (na, nb) = (st.expr_node(base, a), st.expr_node(base, b));
        let is_bvarish = |n: Node| matches!(n, Node::BVar { .. } | Node::BVarBig { .. });
        if is_bvarish(na) && is_bvarish(nb) {
            return Ok(bvar_index_nat(st, base, na) == bvar_index_nat(st, base, nb));
        }
        let node1 = self.to_node(a);
        let node2 = self.to_node(b);
        let r1 = self.find(node1);
        let r2 = self.find(node2);
        if r1 == r2 {
            return Ok(true);
        }
        let result = g.enter(|g| match (na, nb) {
            (
                Node::BVar { .. } | Node::BVarBig { .. },
                Node::BVar { .. } | Node::BVarBig { .. },
            ) => {
                unreachable!("handled by the bvar/bvar-ish return above")
            }
            (
                Node::Const {
                    name: n1,
                    levels: l1,
                },
                Node::Const {
                    name: n2,
                    levels: l2,
                },
            ) => Ok(n1 == n2 && l1 == l2),
            (Node::MVar { id: i1 }, Node::MVar { id: i2 }) => Ok(i1 == i2),
            (Node::FVar { id: i1 }, Node::FVar { id: i2 }) => Ok(i1 == i2),
            (Node::App { f: f1, arg: a1 }, Node::App { f: f2, arg: a2 }) => Ok(self
                .is_equiv_core(st, base, f1, f2, use_hash, g)?
                && self.is_equiv_core(st, base, a1, a2, use_hash, g)?),
            (
                Node::Lam {
                    binder_type: d1,
                    body: b1,
                    ..
                },
                Node::Lam {
                    binder_type: d2,
                    body: b2,
                    ..
                },
            )
            | (
                Node::Forall {
                    binder_type: d1,
                    body: b1,
                    ..
                },
                Node::Forall {
                    binder_type: d2,
                    body: b2,
                    ..
                },
            ) => Ok(self.is_equiv_core(st, base, d1, d2, use_hash, g)?
                && self.is_equiv_core(st, base, b1, b2, use_hash, g)?),
            (Node::Sort { level: l1 }, Node::Sort { level: l2 }) => Ok(l1 == l2),
            (Node::LitNat { v: v1 }, Node::LitNat { v: v2 }) => Ok(v1 == v2),
            (Node::LitStr { v: v1 }, Node::LitStr { v: v2 }) => Ok(v1 == v2),
            (Node::MData { expr: e1, .. }, Node::MData { expr: e2, .. }) => {
                self.is_equiv_core(st, base, e1, e2, use_hash, g)
            }
            (
                n1 @ (Node::Proj { .. } | Node::ProjBig { .. }),
                n2 @ (Node::Proj { .. } | Node::ProjBig { .. }),
                // `type_name` is deliberately ignored, per the oracle's
                // `equiv_manager` (see the Arc port's own note).
            ) => {
                let (_, ix1, s1) = proj_parts_of(st, base, n1);
                let (_, ix2, s2) = proj_parts_of(st, base, n2);
                Ok(self.is_equiv_core(st, base, s1, s2, use_hash, g)? && ix1 == ix2)
            }
            (
                Node::LetE {
                    ty: t1,
                    value: v1,
                    body: b1,
                    ..
                },
                Node::LetE {
                    ty: t2,
                    value: v2,
                    body: b2,
                    ..
                },
            ) => Ok(self.is_equiv_core(st, base, t1, t2, use_hash, g)?
                && self.is_equiv_core(st, base, v1, v2, use_hash, g)?
                && self.is_equiv_core(st, base, b1, b2, use_hash, g)?),
            _ => Ok(false),
        })?;
        if result {
            self.merge_refs(r1, r2);
        }
        Ok(result)
    }

    fn merge(&mut self, t: ExprId, s: ExprId) {
        let a = self.to_node(t);
        let b = self.to_node(s);
        self.merge_refs(a, b);
    }
}

/// Read a `BVar`/`BVarBig` row's raw index as a `Nat` (mirrors
/// `bank::subst`'s private helper of the same shape).
fn bvar_index_nat(st: &Store, base: Option<&Store>, node: Node) -> Nat {
    match node {
        Node::BVar { idx } => Nat::from(idx as u64),
        Node::BVarBig { idx } => st.nat_at(base, idx).clone(),
        _ => unreachable!("bvar_index_nat: caller already matched on BVar/BVarBig"),
    }
}

/// `(type_name, idx, structure)` of a `Proj`/`ProjBig` row.
fn proj_parts_of(st: &Store, base: Option<&Store>, node: Node) -> (Option<NameId>, Nat, ExprId) {
    match node {
        Node::Proj {
            type_name,
            idx,
            structure,
        } => (type_name, Nat::from(idx as u64), structure),
        Node::ProjBig {
            type_name,
            idx,
            structure,
        } => (type_name, st.nat_at(base, idx).clone(), structure),
        _ => unreachable!("proj_parts_of: caller already matched on Proj/ProjBig"),
    }
}

/// The environment view the checker consults (brief's Task 4 interface;
/// Task 6's `Environment::view()` will produce one of these from the
/// real persistent + scratch banks).
pub struct EnvView<'a> {
    pub consts: &'a std::collections::HashMap<NameId, ConstantInfo>,
    pub extra: Option<&'a std::collections::HashMap<NameId, ConstantInfo>>,
    pub quot_initialized: bool,
    pub store: &'a Store,
}

impl<'a> EnvView<'a> {
    pub fn get(&self, n: NameId) -> Option<&'a ConstantInfo> {
        self.extra
            .and_then(|e| e.get(&n))
            .or_else(|| self.consts.get(&n))
    }

    /// Lookup with error on miss; **callers must pass a PERSISTENT-region `NameId`**.
    ///
    /// This method's error path calls `to_name(None, ...)`, which reads the
    /// persistent `store` only. A scratch-region `NameId` resolved that way
    /// reads the WRONG row out of `store`'s own pools, yielding a wrong name
    /// or out-of-bounds panic. Callers must ensure `n` is from the persistent
    /// region; if the id may come from scratch, use region-correct resolution
    /// instead (see `TypeChecker::env_get_with` for the pattern).
    pub fn get_with(&self, n: NameId) -> Result<&'a ConstantInfo, KernelError> {
        self.get(n)
            .ok_or_else(|| {
                debug_assert!(!n.is_scratch(), "EnvView::get_with: passed scratch-region NameId; see doc comment for region contract");
                KernelError::UnknownConstant(self.store.to_name(None, Some(n)))
            })
    }

    /// oracle: inductive.cpp:27 (`is_non_rec_structure`) — mirrors
    /// `Environment::is_structure_like` exactly; not part of the
    /// brief's literal two-method list, but a pure derived query the
    /// checker needs (structure eta / unit-like / eta-when-structure)
    /// and Task 6 gets for free.
    pub fn is_structure_like(&self, name: NameId) -> bool {
        matches!(self.get(name), Some(ConstantInfo::Induct(v))
            if v.ctors.len() == 1 && v.num_indices == Nat::from(0u64) && !v.is_rec)
    }
}

/// The kernel type checker (oracle: `class type_checker`). Every
/// remaining private field of Arc `tc.rs` carried over with
/// `Arc<Expr>`->`ExprId`, `Arc<Name>`->`NameId`, `Arc<Level>`->`LevelId`.
pub struct TypeChecker<'e> {
    view: EnvView<'e>,
    /// The scratch store is BORROWED, not owned: one scratch per
    /// declaration, several checkers (region discipline, Global
    /// Constraints).
    scratch: &'e mut Store,
    safety: DefinitionSafety,
    lparams: Vec<NameId>,
    lctx: LocalContext,
    fvar_gen: FVarIdGen,
    guard: RecGuard,
    guard_depth: u32,
    infer_cache: [HashMap<ExprId, ExprId>; 2],
    whnf_cache: HashMap<ExprId, ExprId>,
    whnf_core_cache: HashMap<ExprId, ExprId>,
    eqv_cache: UnionFind,
    failure_cache: HashSet<(ExprId, ExprId)>,
    unfold_memo: HashMap<ExprId, ExprId>,
    dont_care: ExprId,
    bool_true: NameId,
    nat_name: NameId,
    string_name: NameId,
    bool_false: NameId,
    nat_zero: NameId,
    nat_succ: NameId,
    string_mk: NameId,
}

fn mk_name1_id(st: &mut Store, base: Option<&Store>, part: &str) -> Result<NameId, KernelError> {
    let s = st.intern_str(base, part)?;
    st.name_str(base, None, s)
}

fn mk_name2_id(
    st: &mut Store,
    base: Option<&Store>,
    a: &str,
    b: &str,
) -> Result<NameId, KernelError> {
    let p = mk_name1_id(st, base, a)?;
    let s = st.intern_str(base, b)?;
    st.name_str(base, Some(p), s)
}

/// A `Nat` small enough to index a slice, or `None`. Never truncates.
/// Verbatim port of `crate::tc`'s own free function (pure `Nat`
/// arithmetic — no representation to change).
fn nat_to_usize(n: &Nat) -> Option<usize> {
    let digits = n.0.to_u64_digits();
    if digits.len() > 1 {
        return None;
    }
    let v = digits.first().copied().unwrap_or(0);
    usize::try_from(v).ok()
}

/// oracle: declaration.h:466 (`info.has_value()`).
fn info_has_value(info: &ConstantInfo) -> bool {
    matches!(info, ConstantInfo::Defn(_) | ConstantInfo::Thm(_))
}

/// The value of a `has_value` constant.
fn info_value(info: &ConstantInfo) -> Option<ExprId> {
    match info {
        ConstantInfo::Defn(v) => Some(v.value),
        ConstantInfo::Thm(v) => Some(v.value),
        _ => None,
    }
}

/// oracle: `constant_info::get_hints` (declaration.cpp:294).
fn info_hints(info: &ConstantInfo) -> ReducibilityHints {
    match info {
        ConstantInfo::Defn(v) => v.hints,
        _ => ReducibilityHints::Opaque,
    }
}

/// oracle: `constant_info::is_unsafe`.
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

/// oracle: declaration.cpp:24 (`compare(reducibility_hints)`).
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
        _ if h1 == h2 => 0,
        (Opaque, _) => 1,
        (_, Opaque) => -1,
        (Abbrev, _) => -1,
        (_, Abbrev) => 1,
    }
}

/// Free function (not an inherent impl): `crate::tc` already defines a
/// private `impl ReducibilityHints { fn is_regular_hint }` in its own
/// module, and Rust's inherent-impl coherence forbids a second
/// same-named method on the same concrete type from a different module
/// in this crate (E0592) — a free function sidesteps that collision.
fn is_regular_hint(h: ReducibilityHints) -> bool {
    matches!(h, ReducibilityHints::Regular(_))
}

/// oracle: level.cpp:274 (`get_undef_param`) — first `Param` in `l` not
/// present in `ps`, else `None`. Id-native (over `LevelId`/`LevelRow`)
/// rather than bridged through `Arc<Level>`: this is a pure structural
/// presence-check with no level-normalization semantics (unlike
/// `mk_max_pair`/`mk_imax_pair`/`is_equivalent`, which stay on the Arc
/// side via `to_level`/`intern_level` bridging because they actually
/// transform/compare levels up to non-structural equivalence), so a
/// direct `NameId` comparison is exact and avoids an `Arc<Name>` bridge
/// per visited node. Returns `Some(Option<NameId>)`: the inner
/// `Option` is `None` exactly when the undefined param is itself
/// anonymous (`Level::Param(Name::Anonymous)`, storable inside an expr
/// tree though never as a real declaration-position name) — a case
/// `to_name` cannot bridge (there is no `NameId` for it), so the error
/// site builds `Arc::new(Name::Anonymous)` directly instead.
fn get_undef_param_id(
    st: &Store,
    base: Option<&Store>,
    l: LevelId,
    ps: &[NameId],
    g: &mut RecGuard,
) -> Result<Option<Option<NameId>>, KernelError> {
    match *st.level_row(base, l) {
        super::levels::LevelRow::Zero | super::levels::LevelRow::MVar(_) => Ok(None),
        super::levels::LevelRow::Param(n) => {
            if let Some(id) = n {
                if ps.contains(&id) {
                    return Ok(None);
                }
            }
            Ok(Some(n))
        }
        super::levels::LevelRow::Succ(a) => g.enter(|g| get_undef_param_id(st, base, a, ps, g)),
        super::levels::LevelRow::Max(a, b) | super::levels::LevelRow::IMax(a, b) => g.enter(|g| {
            if let Some(n) = get_undef_param_id(st, base, a, ps, g)? {
                return Ok(Some(n));
            }
            get_undef_param_id(st, base, b, ps, g)
        }),
    }
}

impl<'e> TypeChecker<'e> {
    /// **the scratch store is borrowed, not owned** (Global Constraints:
    /// one scratch per declaration, several checkers). Building the
    /// handful of tiny fixed-string constants below (`.expect(...)`,
    /// mirroring the Arc port's own `.expect("mk_const with no levels is
    /// infallible")`) can only fail via `BankExhausted`, and only if the
    /// PERSISTENT bank is already exhausted (these calls check `base`
    /// first before touching the freshly-created `scratch`) — at that
    /// point every other kernel operation is already failing too, the
    /// same accepted-degenerate-case posture the brief's mandated
    /// `Result`-free signature implies.
    pub fn new(view: EnvView<'e>, scratch: &'e mut Store) -> TypeChecker<'e> {
        let base = view.store;
        let no_levels = scratch
            .intern_level_list(Some(base), &[])
            .expect("interning the empty level list is infallible");
        let dont_care_name = mk_name1_id(scratch, Some(base), "dontcare")
            .expect("interning a tiny fixed name is infallible");
        let dont_care = scratch
            .expr_const(Some(base), Some(dont_care_name), no_levels)
            .expect("mk_const with no levels is infallible");
        let bool_true = mk_name2_id(scratch, Some(base), "Bool", "true")
            .expect("interning a tiny fixed name is infallible");
        let nat_name = mk_name1_id(scratch, Some(base), "Nat")
            .expect("interning a tiny fixed name is infallible");
        let string_name = mk_name1_id(scratch, Some(base), "String")
            .expect("interning a tiny fixed name is infallible");
        let bool_false = mk_name2_id(scratch, Some(base), "Bool", "false")
            .expect("interning a tiny fixed name is infallible");
        let nat_zero = mk_name2_id(scratch, Some(base), "Nat", "zero")
            .expect("interning a tiny fixed name is infallible");
        let nat_succ = mk_name2_id(scratch, Some(base), "Nat", "succ")
            .expect("interning a tiny fixed name is infallible");
        let string_mk = mk_name2_id(scratch, Some(base), "String", "ofList")
            .expect("interning a tiny fixed name is infallible");
        TypeChecker {
            view,
            scratch,
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
            bool_true,
            nat_name,
            string_name,
            bool_false,
            nat_zero,
            nat_succ,
            string_mk,
        }
    }

    /// Build a checker seeded with a pre-populated local context and
    /// fvar generator. The inductive-admission pipeline (`bank/
    /// inductive.rs`, Task 5) owns the persistent `lctx`/`fvar_gen` that
    /// the oracle's `add_inductive_fn` keeps in `m_lctx`/`m_ngen` and
    /// shares with each freshly-constructed `type_checker(m_env, m_lctx,
    /// ...)` (inductive.cpp:171). Rust cannot let `AddInductiveFn` hold
    /// both a `&mut Store` (for its own term-building) and a
    /// `TypeChecker` borrowing that same store at once, so it instead
    /// *moves* its context in here per checker op and moves it back out
    /// via `into_parts`, keeping the `FVarIdGen` counter monotonic across
    /// both producers (id-twin of the Arc `TypeChecker::new_with`,
    /// `crate::tc.rs:687-696` — same rationale, same doc comment,
    /// `Arc<Expr>`/`Arc<Name>` swapped for `ExprId`/`NameId` throughout).
    pub(crate) fn new_with(
        view: EnvView<'e>,
        scratch: &'e mut Store,
        lctx: LocalContext,
        fvar_gen: FVarIdGen,
    ) -> TypeChecker<'e> {
        let mut tc = TypeChecker::new(view, scratch);
        tc.lctx = lctx;
        tc.fvar_gen = fvar_gen;
        tc
    }

    /// Reclaim the (possibly-extended, then save/restore-trimmed) local
    /// context and the advanced fvar generator after a checker op. See
    /// `new_with`. Id-twin of the Arc `TypeChecker::into_parts`
    /// (`crate::tc.rs:698-703`).
    pub(crate) fn into_parts(self) -> (LocalContext, FVarIdGen) {
        (self.lctx, self.fvar_gen)
    }

    /// The checker's own guarded frame — same constants as `RecGuard`;
    /// cannot reuse `self.guard` (already threaded to Tasks 2-5's free
    /// functions) because it cannot be borrowed while `self` is also
    /// passed to the recursive call.
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

    // -- Small store-facing helpers (porting-rule row 1, generalized) --

    fn node(&self, e: ExprId) -> Node {
        self.scratch.expr_node(Some(self.view.store), e)
    }

    fn data(&self, e: ExprId) -> crate::ExprData {
        self.scratch.expr_data(Some(self.view.store), e)
    }

    fn has_loose_bvars(&self, e: ExprId) -> bool {
        self.data(e).loose_bvar_range() != 0
    }

    fn get_app_fn(&self, e: ExprId) -> ExprId {
        let mut cur = e;
        while let Node::App { f, .. } = self.node(cur) {
            cur = f;
        }
        cur
    }

    fn get_app_args(&self, e: ExprId) -> Vec<ExprId> {
        let mut args = Vec::new();
        let mut cur = e;
        while let Node::App { f, arg } = self.node(cur) {
            args.push(arg);
            cur = f;
        }
        args.reverse();
        args
    }

    fn get_app_num_args(&self, e: ExprId) -> usize {
        let mut n = 0usize;
        let mut cur = e;
        while let Node::App { f, .. } = self.node(cur) {
            n += 1;
            cur = f;
        }
        n
    }

    fn mk_app_spine(&mut self, f: ExprId, args: &[ExprId]) -> Result<ExprId, KernelError> {
        let mut r = f;
        for &a in args {
            r = self.scratch.expr_app(Some(self.view.store), r, a)?;
        }
        Ok(r)
    }

    fn is_app(&self, e: ExprId) -> bool {
        matches!(self.node(e), Node::App { .. })
    }

    fn is_lambda(&self, e: ExprId) -> bool {
        matches!(self.node(e), Node::Lam { .. })
    }

    fn is_forall(&self, e: ExprId) -> bool {
        matches!(self.node(e), Node::Forall { .. })
    }

    fn is_sort(&self, e: ExprId) -> bool {
        matches!(self.node(e), Node::Sort { .. })
    }

    fn is_proj(&self, e: ExprId) -> bool {
        matches!(self.node(e), Node::Proj { .. } | Node::ProjBig { .. })
    }

    /// `(type_name, idx, structure)` of a `Proj`/`ProjBig` node.
    fn proj_parts(&self, node: Node) -> (Option<NameId>, Nat, ExprId) {
        proj_parts_of(self.scratch, Some(self.view.store), node)
    }

    /// The domain/body of a binder node (Lam or ForallE).
    fn binder_dom_body(&self, e: ExprId) -> (ExprId, ExprId) {
        match self.node(e) {
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => (binder_type, body),
            _ => unreachable!("binder_dom_body on non-binder"),
        }
    }

    /// Domain/body plus binder name and info of a binder node.
    fn binder_full(&self, e: ExprId) -> (ExprId, ExprId, Option<NameId>, BinderInfo) {
        match self.node(e) {
            Node::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            }
            | Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => (binder_type, body, binder_name, binder_info),
            _ => unreachable!("binder_full on non-binder"),
        }
    }

    /// Universe levels of an application's head constant (empty if the
    /// head is not a `Const`).
    fn const_levels_of_head(&self, e: ExprId) -> Vec<LevelId> {
        match self.node(self.get_app_fn(e)) {
            Node::Const { levels, .. } => self
                .scratch
                .level_list_at(Some(self.view.store), levels)
                .to_vec(),
            _ => Vec::new(),
        }
    }

    /// The `Const`'s name if `e` is a `Const` node with a non-anonymous
    /// name, else `None` (collapses "not a `Const`" and "`Const` with an
    /// anonymous name" — see `bank::quot_red::QuotCtx::const_name`'s doc
    /// comment for why that collapse is exact for every caller here).
    fn const_name(&self, e: ExprId) -> Option<NameId> {
        match self.node(e) {
            Node::Const { name, .. } => name,
            _ => None,
        }
    }

    /// `is_constant(e, name)` (oracle: expr.h) — a `Const` node whose
    /// name is exactly `name` (levels ignored).
    fn is_const_named(&self, e: ExprId, name: NameId) -> bool {
        self.const_name(e) == Some(name)
    }

    /// `EnvView::get`, but for a possibly-anonymous `Const.name` field.
    /// Bank `Node::Const.name: Option<NameId>` mirrors the expr-row
    /// convention of encoding `Name::Anonymous` as `None`; the oracle's
    /// `Arc<Name>` CAN be `Name::Anonymous` directly, so `env.get(name)`
    /// there is a real (always-missing) hashmap probe there — here that
    /// probe collapses to `None` without touching the environment, since
    /// no declaration is ever named `Name::Anonymous`.
    fn env_get(&self, name: Option<NameId>) -> Option<&'e ConstantInfo> {
        name.and_then(|n| self.view.get(n))
    }

    /// NOT implemented via `self.view.get_with` (whose own `to_name`
    /// call resolves the miss's `NameId` with `base = None`, i.e.
    /// against `store` alone — correct for a persistent-region name,
    /// but a scratch id resolved that way reads the WRONG row out of
    /// `store`'s own pools, since `store_for`'s scratch-bit branch
    /// returns `self` unconditionally regardless of which store
    /// actually owns that id — see `Store::store_for`'s doc comment).
    /// `Const` node names the checker looks up here routinely ARE
    /// scratch ids (an expression tree interned into scratch that
    /// references a name never before seen in the persistent
    /// environment — exactly the "unknown constant" case this method
    /// exists to report — mints a fresh SCRATCH row, not a persistent
    /// one, so this is not a corner case). This checker knows both
    /// `scratch` and `store`, so it builds the error with the correctly
    /// region-routed `self.to_name` bridge instead.
    fn env_get_with(&self, name: Option<NameId>) -> Result<&'e ConstantInfo, KernelError> {
        match name {
            Some(n) => self
                .view
                .get(n)
                .ok_or_else(|| KernelError::UnknownConstant(self.to_name(n))),
            None => Err(KernelError::UnknownConstant(Arc::new(Name::Anonymous))),
        }
    }

    /// The `to_name` bridge — the ONLY Arc construction this checker
    /// performs, and only at error sites (cold path): no scratch id
    /// ever enters a `KernelError`.
    fn to_name(&self, id: NameId) -> Arc<Name> {
        self.scratch.to_name(Some(self.view.store), Some(id))
    }

    /// The `Nat.<op>` builtin named by `name`, if any (oracle: `g_nat_*`
    /// constants). Recognizes a two-component name `Nat.op` and returns
    /// `op`.
    fn nat_binop_id(&self, name: Option<NameId>) -> Option<String> {
        let id = name?;
        let st: &Store = &*self.scratch;
        let base = Some(self.view.store);
        match st.name_row(base, id) {
            NameRow::Str {
                parent: Some(p),
                part,
            } => match st.name_row(base, *p) {
                NameRow::Str {
                    parent: None,
                    part: nat_part,
                } if st.str_at(base, *nat_part) == "Nat" => {
                    Some(st.str_at(base, *part).to_string())
                }
                _ => None,
            },
            _ => None,
        }
    }
}

impl<'e> TypeChecker<'e> {
    // -- Public entry points ------------------------------------------

    /// oracle: type_checker.cpp:308-312 — THE public checking entry.
    pub fn check(&mut self, e: ExprId, lparams: &[NameId]) -> Result<ExprId, KernelError> {
        self.lparams = lparams.to_vec();
        self.infer_type_core(e, false)
    }

    /// oracle: type_checker.cpp:304.
    pub fn infer_type(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        self.infer_type_core(e, true)
    }

    /// oracle: type_checker.cpp:53 (`ensure_sort_core`).
    pub fn ensure_sort(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        if self.is_sort(e) {
            return Ok(e);
        }
        let new_e = self.whnf(e)?;
        if self.is_sort(new_e) {
            Ok(new_e)
        } else {
            Err(KernelError::TypeExpected)
        }
    }

    /// oracle: type_checker.cpp:65 (`ensure_pi_core`).
    pub fn ensure_pi(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        if self.is_forall(e) {
            return Ok(e);
        }
        let new_e = self.whnf(e)?;
        if self.is_forall(new_e) {
            Ok(new_e)
        } else {
            Err(KernelError::FunctionExpected)
        }
    }

    /// oracle: type_checker.cpp:327 — `whnf(infer_type(e)) == Prop`.
    pub fn is_prop(&mut self, e: ExprId) -> Result<bool, KernelError> {
        let ty = self.infer_type(e)?;
        let w = self.whnf(ty)?;
        let zero = self.scratch.level_zero(Some(self.view.store))?;
        Ok(matches!(self.node(w), Node::Sort { level } if level == zero))
    }

    // -- infer ----------------------------------------------------------

    /// oracle: type_checker.cpp:270-302. Rejects loose bvars / mvars;
    /// caches per `infer_only`; strips `mdata` transparently.
    fn infer_type_core(&mut self, e: ExprId, infer_only: bool) -> Result<ExprId, KernelError> {
        self.guarded(|slf| {
            if slf.has_loose_bvars(e) {
                return Err(KernelError::LooseBVar);
            }
            let idx = infer_only as usize;
            if let Some(&r) = slf.infer_cache[idx].get(&e) {
                return Ok(r);
            }
            let node = slf.node(e);
            let r = match node {
                Node::LitNat { .. } | Node::LitStr { .. } => slf.infer_lit(node)?,
                Node::MData { expr, .. } => slf.infer_type_core(expr, infer_only)?,
                Node::Proj { .. } | Node::ProjBig { .. } => slf.infer_proj(e, infer_only)?,
                Node::FVar { .. } => slf.infer_fvar(e)?,
                Node::MVar { .. } => return Err(KernelError::MetavarEncountered),
                Node::BVar { .. } | Node::BVarBig { .. } => return Err(KernelError::LooseBVar),
                Node::Sort { level } => {
                    if !infer_only {
                        slf.check_level(level)?;
                    }
                    let l2 = slf.scratch.level_succ(Some(slf.view.store), level)?;
                    slf.scratch.expr_sort(Some(slf.view.store), l2)?
                }
                Node::Const { .. } => slf.infer_constant(e, infer_only)?,
                Node::Lam { .. } => slf.infer_lambda(e, infer_only)?,
                Node::Forall { .. } => slf.infer_pi(e, infer_only)?,
                Node::App { .. } => slf.infer_app(e, infer_only)?,
                Node::LetE { .. } => slf.infer_let(e, infer_only)?,
            };
            slf.infer_cache[idx].insert(e, r);
            Ok(r)
        })
    }

    /// oracle: `lit_type` — a literal's type is the `Nat`/`String` const.
    fn infer_lit(&mut self, node: Node) -> Result<ExprId, KernelError> {
        let name = match node {
            Node::LitNat { .. } => self.nat_name,
            Node::LitStr { .. } => self.string_name,
            _ => unreachable!("infer_lit: caller already matched on LitNat/LitStr"),
        };
        let no_levels = self.scratch.intern_level_list(Some(self.view.store), &[])?;
        self.scratch
            .expr_const(Some(self.view.store), Some(name), no_levels)
    }

    /// oracle: type_checker.cpp:76-82 (`check_level`).
    fn check_level(&mut self, l: LevelId) -> Result<(), KernelError> {
        if let Some(n) = get_undef_param_id(
            self.scratch,
            Some(self.view.store),
            l,
            &self.lparams,
            &mut self.guard,
        )? {
            let name = match n {
                Some(id) => self.to_name(id),
                None => Arc::new(Name::Anonymous),
            };
            return Err(KernelError::UnivParamArityMismatch { name });
        }
        Ok(())
    }

    /// oracle: type_checker.cpp:84-90 (`infer_fvar`).
    fn infer_fvar(&self, e: ExprId) -> Result<ExprId, KernelError> {
        if let Node::FVar { id: Some(id) } = self.node(e) {
            if let Some(decl) = self.lctx.get(id) {
                return Ok(decl.ty);
            }
        }
        Err(KernelError::LooseBVar)
    }

    /// oracle: type_checker.cpp:92-114 (`infer_constant`).
    fn infer_constant(&mut self, e: ExprId, infer_only: bool) -> Result<ExprId, KernelError> {
        let (name, levels) = match self.node(e) {
            Node::Const { name, levels } => (name, levels),
            _ => return Err(KernelError::LooseBVar), // unreachable
        };
        let info = self.env_get_with(name)?;
        let cv = info.constant_val();
        let level_ids: Vec<LevelId> = self
            .scratch
            .level_list_at(Some(self.view.store), levels)
            .to_vec();
        if cv.level_params.len() != level_ids.len() {
            let name = self.to_name(cv.name);
            return Err(KernelError::UnivParamArityMismatch { name });
        }
        if !infer_only {
            if info_is_unsafe(info) && self.safety != DefinitionSafety::Unsafe {
                let name = self.to_name(cv.name);
                return Err(KernelError::UnsafeConstInSafeDecl(name));
            }
            if let ConstantInfo::Defn(d) = info {
                if d.safety == DefinitionSafety::Partial && self.safety == DefinitionSafety::Safe {
                    let name = self.to_name(cv.name);
                    return Err(KernelError::UnsafeConstInSafeDecl(name));
                }
            }
            for &l in &level_ids {
                self.check_level(l)?;
            }
        }
        let (ty, params) = (cv.ty, cv.level_params.clone());
        instantiate_level_params(
            self.scratch,
            Some(self.view.store),
            ty,
            &params,
            &level_ids,
            &mut self.guard,
        )
    }

    /// oracle: type_checker.cpp:116-132 (`infer_lambda`).
    fn infer_lambda(&mut self, e: ExprId, infer_only: bool) -> Result<ExprId, KernelError> {
        let saved = self.lctx.save();
        let r = self.infer_lambda_body(e, infer_only);
        self.lctx.restore(saved);
        r
    }

    fn infer_lambda_body(&mut self, e0: ExprId, infer_only: bool) -> Result<ExprId, KernelError> {
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut e = e0;
        while let Node::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = self.node(e)
        {
            let d = instantiate_rev(
                self.scratch,
                Some(self.view.store),
                binder_type,
                &fvars,
                &mut self.guard,
            )?;
            let fvar = self.lctx.mk_local_decl(
                self.scratch,
                Some(self.view.store),
                &mut self.fvar_gen,
                binder_name,
                d,
                binder_info,
            )?;
            fvars.push(fvar);
            if !infer_only {
                let dty = self.infer_type_core(d, infer_only)?;
                self.ensure_sort(dty)?;
            }
            e = body;
        }
        let inst = instantiate_rev(
            self.scratch,
            Some(self.view.store),
            e,
            &fvars,
            &mut self.guard,
        )?;
        let r = self.infer_type_core(inst, infer_only)?;
        let r = self.cheap_beta_reduce(r)?;
        super::subst::mk_pi(
            self.scratch,
            Some(self.view.store),
            &self.lctx,
            &fvars,
            r,
            &mut self.guard,
        )
    }

    /// oracle: type_checker.cpp:134-156 (`infer_pi`).
    fn infer_pi(&mut self, e: ExprId, infer_only: bool) -> Result<ExprId, KernelError> {
        let saved = self.lctx.save();
        let r = self.infer_pi_body(e, infer_only);
        self.lctx.restore(saved);
        r
    }

    fn infer_pi_body(&mut self, e0: ExprId, infer_only: bool) -> Result<ExprId, KernelError> {
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut us: Vec<LevelId> = Vec::new();
        let mut e = e0;
        while let Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = self.node(e)
        {
            let d = instantiate_rev(
                self.scratch,
                Some(self.view.store),
                binder_type,
                &fvars,
                &mut self.guard,
            )?;
            let dty = self.infer_type_core(d, infer_only)?;
            let t1 = self.ensure_sort(dty)?;
            let lvl = match self.node(t1) {
                Node::Sort { level } => level,
                _ => return Err(KernelError::TypeExpected),
            };
            us.push(lvl);
            let fvar = self.lctx.mk_local_decl(
                self.scratch,
                Some(self.view.store),
                &mut self.fvar_gen,
                binder_name,
                d,
                binder_info,
            )?;
            fvars.push(fvar);
            e = body;
        }
        let inst = instantiate_rev(
            self.scratch,
            Some(self.view.store),
            e,
            &fvars,
            &mut self.guard,
        )?;
        let sty = self.infer_type_core(inst, infer_only)?;
        let s = self.ensure_sort(sty)?;
        let mut r = match self.node(s) {
            Node::Sort { level } => level,
            _ => return Err(KernelError::TypeExpected),
        };
        let mut i = fvars.len();
        while i > 0 {
            i -= 1;
            let ul = self.scratch.to_level(Some(self.view.store), us[i]);
            let rl = self.scratch.to_level(Some(self.view.store), r);
            let merged = Level::mk_imax_pair(ul, rl, &mut self.guard)?;
            r = self.scratch.intern_level(Some(self.view.store), &merged)?;
        }
        self.scratch.expr_sort(Some(self.view.store), r)
    }

    /// oracle: type_checker.cpp:163-196 (`infer_app`).
    fn infer_app(&mut self, e: ExprId, infer_only: bool) -> Result<ExprId, KernelError> {
        if !infer_only {
            let (f, arg) = match self.node(e) {
                Node::App { f, arg } => (f, arg),
                _ => return Err(KernelError::LooseBVar), // unreachable
            };
            let ft = self.infer_type_core(f, infer_only)?;
            let f_type = self.ensure_pi(ft)?;
            let a_type = self.infer_type_core(arg, infer_only)?;
            let (d_type, body) = match self.node(f_type) {
                Node::Forall {
                    binder_type, body, ..
                } => (binder_type, body),
                _ => return Err(KernelError::FunctionExpected),
            };
            if !self.is_def_eq(a_type, d_type)? {
                return Err(KernelError::AppTypeMismatch);
            }
            instantiate(
                self.scratch,
                Some(self.view.store),
                body,
                arg,
                &mut self.guard,
            )
        } else {
            let args = self.get_app_args(e);
            let f = self.get_app_fn(e);
            let mut f_type = self.infer_type_core(f, true)?;
            let mut j = 0usize;
            let nargs = args.len();
            for i in 0..nargs {
                if self.is_forall(f_type) {
                    f_type = match self.node(f_type) {
                        Node::Forall { body, .. } => body,
                        _ => unreachable!(),
                    };
                } else {
                    f_type = instantiate_rev(
                        self.scratch,
                        Some(self.view.store),
                        f_type,
                        &args[j..i],
                        &mut self.guard,
                    )?;
                    f_type = self.ensure_pi(f_type)?;
                    f_type = match self.node(f_type) {
                        Node::Forall { body, .. } => body,
                        _ => return Err(KernelError::FunctionExpected),
                    };
                    j = i;
                }
            }
            instantiate_rev(
                self.scratch,
                Some(self.view.store),
                f_type,
                &args[j..nargs],
                &mut self.guard,
            )
        }
    }

    /// oracle: type_checker.cpp:198-219 (`infer_let`).
    fn infer_let(&mut self, e: ExprId, infer_only: bool) -> Result<ExprId, KernelError> {
        let saved = self.lctx.save();
        let r = self.infer_let_body(e, infer_only);
        self.lctx.restore(saved);
        r
    }

    fn infer_let_body(&mut self, e0: ExprId, infer_only: bool) -> Result<ExprId, KernelError> {
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut e = e0;
        while let Node::LetE {
            decl_name,
            ty,
            value,
            body,
            ..
        } = self.node(e)
        {
            let type_ = instantiate_rev(
                self.scratch,
                Some(self.view.store),
                ty,
                &fvars,
                &mut self.guard,
            )?;
            let val = instantiate_rev(
                self.scratch,
                Some(self.view.store),
                value,
                &fvars,
                &mut self.guard,
            )?;
            let fvar = self.lctx.mk_let_decl(
                self.scratch,
                Some(self.view.store),
                &mut self.fvar_gen,
                decl_name,
                type_,
                val,
            )?;
            fvars.push(fvar);
            if !infer_only {
                let tty = self.infer_type_core(type_, infer_only)?;
                self.ensure_sort(tty)?;
                let val_type = self.infer_type_core(val, infer_only)?;
                if !self.is_def_eq(val_type, type_)? {
                    return Err(KernelError::LetTypeMismatch);
                }
            }
            e = body;
        }
        let inst = instantiate_rev(
            self.scratch,
            Some(self.view.store),
            e,
            &fvars,
            &mut self.guard,
        )?;
        let r = self.infer_type_core(inst, infer_only)?;
        let r = self.cheap_beta_reduce(r)?;
        super::subst::mk_pi(
            self.scratch,
            Some(self.view.store),
            &self.lctx,
            &fvars,
            r,
            &mut self.guard,
        )
    }

    /// oracle: type_checker.cpp:221-266 (`infer_proj`). Every malformed
    /// shape ⇒ `InvalidProj` (never a panic).
    fn infer_proj(&mut self, e: ExprId, infer_only: bool) -> Result<ExprId, KernelError> {
        let (proj_name, idx, structure) = match self.node(e) {
            n @ (Node::Proj { .. } | Node::ProjBig { .. }) => self.proj_parts(n),
            _ => return Err(KernelError::InvalidProj),
        };
        let sty = self.infer_type_core(structure, infer_only)?;
        let type_ = self.whnf(sty)?;
        let idxv = match nat_to_usize(&idx) {
            Some(v) => v,
            None => return Err(KernelError::InvalidProj),
        };
        let args = self.get_app_args(type_);
        let head = self.get_app_fn(type_);
        let (i_name, i_levels) = match self.node(head) {
            Node::Const { name, levels } => (name, levels),
            _ => return Err(KernelError::InvalidProj),
        };
        if i_name != proj_name {
            return Err(KernelError::InvalidProj);
        }
        let i_info = self.env_get_with(i_name)?;
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
        let ctor_name = i_val.ctors[0];
        let c_info = self.env_get_with(Some(ctor_name))?;
        let c_cv = c_info.constant_val();
        let i_level_ids: Vec<LevelId> = self
            .scratch
            .level_list_at(Some(self.view.store), i_levels)
            .to_vec();
        let (c_ty, c_lparams) = (c_cv.ty, c_cv.level_params.clone());
        let mut r = instantiate_level_params(
            self.scratch,
            Some(self.view.store),
            c_ty,
            &c_lparams,
            &i_level_ids,
            &mut self.guard,
        )?;
        for &arg in args.iter().take(nparams) {
            r = self.whnf(r)?;
            let body = match self.node(r) {
                Node::Forall { body, .. } => body,
                _ => return Err(KernelError::InvalidProj),
            };
            r = instantiate(
                self.scratch,
                Some(self.view.store),
                body,
                arg,
                &mut self.guard,
            )?;
        }
        let is_prop_type = self.is_prop(type_)?;
        for i in 0..idxv {
            r = self.whnf(r)?;
            let (dom, body) = match self.node(r) {
                Node::Forall {
                    binder_type, body, ..
                } => (binder_type, body),
                _ => return Err(KernelError::InvalidProj),
            };
            if self.has_loose_bvars(body) {
                if is_prop_type && !self.is_prop(dom)? {
                    return Err(KernelError::InvalidProj);
                }
                let proj = self.scratch.expr_proj(
                    Some(self.view.store),
                    i_name,
                    &Nat::from(i as u64),
                    structure,
                )?;
                r = instantiate(
                    self.scratch,
                    Some(self.view.store),
                    body,
                    proj,
                    &mut self.guard,
                )?;
            } else {
                r = body;
            }
        }
        r = self.whnf(r)?;
        let dom = match self.node(r) {
            Node::Forall { binder_type, .. } => binder_type,
            _ => return Err(KernelError::InvalidProj),
        };
        if is_prop_type && !self.is_prop(dom)? {
            return Err(KernelError::InvalidProj);
        }
        Ok(dom)
    }
}

impl<'e> TypeChecker<'e> {
    // -- whnf -----------------------------------------------------------

    /// oracle: type_checker.cpp:389-396 (`is_let_fvar`).
    fn is_let_fvar(&self, e: ExprId) -> bool {
        matches!(self.node(e), Node::FVar { id: Some(id) }
            if self.lctx.get(id).is_some_and(|d| d.value.is_some()))
    }

    /// oracle: type_checker.cpp:641-681 (`whnf`).
    pub fn whnf(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        self.guarded(|slf| {
            match slf.node(e) {
                Node::BVar { .. }
                | Node::BVarBig { .. }
                | Node::Sort { .. }
                | Node::MVar { .. }
                | Node::Forall { .. }
                | Node::LitNat { .. }
                | Node::LitStr { .. } => return Ok(e),
                Node::MData { expr, .. } => return slf.whnf(expr),
                Node::FVar { .. } => {
                    if !slf.is_let_fvar(e) {
                        return Ok(e);
                    }
                }
                Node::Lam { .. }
                | Node::App { .. }
                | Node::Const { .. }
                | Node::LetE { .. }
                | Node::Proj { .. }
                | Node::ProjBig { .. } => {}
            }
            if let Some(&r) = slf.whnf_cache.get(&e) {
                return Ok(r);
            }
            let mut t = e;
            loop {
                let t1 = slf.whnf_core(t, false, false)?;
                if let Some(v) = slf.reduce_native(t1)? {
                    slf.whnf_cache.insert(e, v);
                    return Ok(v);
                } else if let Some(v) = slf.reduce_nat(t1)? {
                    slf.whnf_cache.insert(e, v);
                    return Ok(v);
                } else if let Some(next) = slf.unfold_definition(t1)? {
                    t = next;
                } else {
                    slf.whnf_cache.insert(e, t1);
                    return Ok(t1);
                }
            }
        })
    }

    /// oracle: type_checker.cpp:401-483 (`whnf_core`). Beta / zeta /
    /// projection reduction plus normalizer-extension dispatch; does not
    /// delta-reduce.
    fn whnf_core(
        &mut self,
        e: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<ExprId, KernelError> {
        self.guarded(|slf| {
            match slf.node(e) {
                Node::BVar { .. }
                | Node::Sort { .. }
                | Node::MVar { .. }
                | Node::Forall { .. }
                | Node::BVarBig { .. }
                | Node::Const { .. }
                | Node::Lam { .. }
                | Node::LitNat { .. }
                | Node::LitStr { .. } => return Ok(e),
                Node::MData { expr, .. } => return slf.whnf_core(expr, cheap_rec, cheap_proj),
                Node::FVar { .. } => {
                    if !slf.is_let_fvar(e) {
                        return Ok(e);
                    }
                }
                Node::App { .. } | Node::LetE { .. } | Node::Proj { .. } | Node::ProjBig { .. } => {
                }
            }
            if let Some(&r) = slf.whnf_core_cache.get(&e) {
                return Ok(r);
            }
            let r = match slf.node(e) {
                Node::FVar { .. } => return slf.whnf_fvar(e, cheap_rec, cheap_proj),
                Node::Proj { .. } | Node::ProjBig { .. } => {
                    if let Some(m) = slf.reduce_proj(e, cheap_rec, cheap_proj)? {
                        slf.whnf_core(m, cheap_rec, cheap_proj)?
                    } else {
                        e
                    }
                }
                Node::App { .. } => {
                    let args = slf.get_app_args(e);
                    let f0 = slf.get_app_fn(e);
                    let f = slf.whnf_core(f0, cheap_rec, cheap_proj)?;
                    if slf.is_lambda(f) {
                        let num_args = args.len();
                        let mut m = 1usize;
                        let mut cur = f;
                        loop {
                            let deeper = match slf.node(cur) {
                                Node::Lam { body, .. } if slf.is_lambda(body) && m < num_args => {
                                    body
                                }
                                _ => break,
                            };
                            cur = deeper;
                            m += 1;
                        }
                        let body = match slf.node(cur) {
                            Node::Lam { body, .. } => body,
                            _ => unreachable!(),
                        };
                        let inst = instantiate_rev(
                            slf.scratch,
                            Some(slf.view.store),
                            body,
                            &args[0..m],
                            &mut slf.guard,
                        )?;
                        let applied = slf.mk_app_spine(inst, &args[m..num_args])?;
                        slf.whnf_core(applied, cheap_rec, cheap_proj)?
                    } else if f == f0 {
                        match slf.reduce_recursor(e, cheap_rec, cheap_proj)? {
                            Some(r) => return slf.whnf_core(r, cheap_rec, cheap_proj),
                            None => return Ok(e),
                        }
                    } else {
                        let applied = slf.mk_app_spine(f, &args)?;
                        slf.whnf_core(applied, cheap_rec, cheap_proj)?
                    }
                }
                Node::LetE { value, body, .. } => {
                    let inst = instantiate(
                        slf.scratch,
                        Some(slf.view.store),
                        body,
                        value,
                        &mut slf.guard,
                    )?;
                    slf.whnf_core(inst, cheap_rec, cheap_proj)?
                }
                _ => unreachable!(),
            };
            if !cheap_rec && !cheap_proj {
                slf.whnf_core_cache.insert(e, r);
            }
            Ok(r)
        })
    }

    /// oracle: type_checker.cpp:348-356 (`whnf_fvar`) — zeta for a
    /// let-bound fvar.
    fn whnf_fvar(
        &mut self,
        e: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<ExprId, KernelError> {
        let val = match self.node(e) {
            Node::FVar { id: Some(id) } => self.lctx.get(id).and_then(|d| d.value),
            _ => None,
        };
        match val {
            Some(v) => self.whnf_core(v, cheap_rec, cheap_proj),
            None => Ok(e),
        }
    }

    /// oracle: type_checker.cpp:377-387 (`reduce_proj`).
    fn reduce_proj(
        &mut self,
        e: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<Option<ExprId>, KernelError> {
        let (_, idx, structure) = match self.node(e) {
            n @ (Node::Proj { .. } | Node::ProjBig { .. }) => self.proj_parts(n),
            _ => return Ok(None),
        };
        let idxv = match nat_to_usize(&idx) {
            Some(v) => v,
            None => return Ok(None),
        };
        let c = if cheap_proj {
            self.whnf_core(structure, cheap_rec, cheap_proj)?
        } else {
            self.whnf(structure)?
        };
        self.reduce_proj_core(c, idxv)
    }

    /// oracle: type_checker.cpp:359-374 (`reduce_proj_core`). Includes
    /// the string-literal case (359-365).
    fn reduce_proj_core(&mut self, c: ExprId, idx: usize) -> Result<Option<ExprId>, KernelError> {
        let c = if let Node::LitStr { v } = self.node(c) {
            let s = self.scratch.str_at(Some(self.view.store), v).to_string();
            let ctor = self.string_lit_to_constructor(&s)?;
            self.whnf(ctor)?
        } else {
            c
        };
        let args = self.get_app_args(c);
        let mk = self.get_app_fn(c);
        let name = match self.node(mk) {
            Node::Const { name, .. } => name,
            _ => return Ok(None),
        };
        let mk_info = self.env_get_with(name)?;
        let nparams = match mk_info {
            ConstantInfo::Ctor(v) => match nat_to_usize(&v.num_params) {
                Some(n) => n,
                None => return Ok(None),
            },
            _ => return Ok(None),
        };
        if nparams + idx < args.len() {
            Ok(Some(args[nparams + idx]))
        } else {
            Ok(None)
        }
    }

    /// oracle: type_checker.cpp:487-494 (`is_delta`).
    fn is_delta(&self, e: ExprId) -> Option<&'e ConstantInfo> {
        let f = self.get_app_fn(e);
        if let Node::Const { name, levels } = self.node(f) {
            if let Some(info) = self.env_get(name) {
                let nlevels = self
                    .scratch
                    .level_list_at(Some(self.view.store), levels)
                    .len();
                if info_has_value(info) && info.constant_val().level_params.len() == nlevels {
                    return Some(info);
                }
            }
        }
        None
    }

    /// oracle: type_checker.cpp:497-518 (`unfold_definition_core`). (The
    /// oracle's `m_unfold` memo is a pure-perf cache; instantiate is
    /// deterministic, so omitting it changes performance, not results —
    /// the brief's cache list does not include it. `unfold_memo` here IS
    /// on the brief's list and IS ported below.)
    fn unfold_definition_core(&mut self, e: ExprId) -> Result<Option<ExprId>, KernelError> {
        if let Node::Const { name, levels } = self.node(e) {
            if let Some(info) = self.env_get(name) {
                let level_ids: Vec<LevelId> = self
                    .scratch
                    .level_list_at(Some(self.view.store), levels)
                    .to_vec();
                if info_has_value(info) && info.constant_val().level_params.len() == level_ids.len()
                {
                    if !level_ids.is_empty() {
                        if let Some(&r) = self.unfold_memo.get(&e) {
                            return Ok(Some(r));
                        }
                    }
                    let value = info_value(info).expect("has_value ⇒ Some value");
                    let params = info.constant_val().level_params.clone();
                    let result = instantiate_level_params(
                        self.scratch,
                        Some(self.view.store),
                        value,
                        &params,
                        &level_ids,
                        &mut self.guard,
                    )?;
                    if !level_ids.is_empty() {
                        self.unfold_memo.insert(e, result);
                    }
                    return Ok(Some(result));
                }
            }
        }
        Ok(None)
    }

    /// oracle: type_checker.cpp:521-534 (`unfold_definition`).
    fn unfold_definition(&mut self, e: ExprId) -> Result<Option<ExprId>, KernelError> {
        if self.is_app(e) {
            let f0 = self.get_app_fn(e);
            match self.unfold_definition_core(f0)? {
                Some(f) => {
                    let args = self.get_app_args(e);
                    Ok(Some(self.mk_app_spine(f, &args)?))
                }
                None => Ok(None),
            }
        } else {
            self.unfold_definition_core(e)
        }
    }
}

impl<'e> TypeChecker<'e> {
    // -- Task 7: special reductions -----------------------------------

    /// `cheap_beta_reduce(e)` (oracle: instantiate.cpp:211). A cheap
    /// partial beta step used to shrink inferred types: peel
    /// `min(#lambdas, #args)` binders; if the resulting head is closed,
    /// apply the leftover args; if it is a bound var of a peeled binder,
    /// select that arg; otherwise give up and return `e`.
    fn cheap_beta_reduce(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        if !self.is_app(e) {
            return Ok(e);
        }
        let fn0 = self.get_app_fn(e);
        if !self.is_lambda(fn0) {
            return Ok(e);
        }
        let args = self.get_app_args(e);
        let mut cur = fn0;
        let mut i = 0usize;
        while i < args.len() {
            if let Node::Lam { body, .. } = self.node(cur) {
                i += 1;
                cur = body;
            } else {
                break;
            }
        }
        if self.data(cur).loose_bvar_range() == 0 {
            self.mk_app_spine(cur, &args[i..])
        } else if let Node::BVar { idx } = self.node(cur) {
            let k = idx as usize;
            if k < i {
                self.mk_app_spine(args[i - k - 1], &args[i..])
            } else {
                Ok(e)
            }
        } else {
            Ok(e)
        }
    }

    /// `cheap_rec ? whnf_core(e, cheap_rec, cheap_proj) : whnf(e)`.
    fn rec_whnf(
        &mut self,
        e: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<ExprId, KernelError> {
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
        e: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<Option<ExprId>, KernelError> {
        if self.view.quot_initialized {
            let r = quot_red::quot_reduce_rec(self, e)?;
            if r.is_some() {
                return Ok(r);
            }
        }
        self.inductive_reduce_rec(e, cheap_rec, cheap_proj)
    }

    /// oracle: inductive.h:76-119 (`inductive_reduce_rec`).
    fn inductive_reduce_rec(
        &mut self,
        e: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<Option<ExprId>, KernelError> {
        let rec_fn = self.get_app_fn(e);
        let (rec_name, rec_levels) = match self.node(rec_fn) {
            Node::Const { name, levels } => (name, levels),
            _ => return Ok(None),
        };
        let rec_val = match self.env_get(rec_name) {
            Some(ConstantInfo::Rec(v)) => v,
            _ => return Ok(None),
        };
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
        let rec_ty = rec_val.val.ty;

        let rec_args = self.get_app_args(e);
        if major_idx >= rec_args.len() {
            return Ok(None);
        }
        let major_induct = match self.get_major_induct(rec_ty, major_idx) {
            Some(n) => n,
            None => return Ok(None),
        };
        let mut major = rec_args[major_idx];
        if is_k {
            major = self.to_cnstr_when_k(major_induct, nparams, major, cheap_rec, cheap_proj)?;
        }
        major = self.rec_whnf(major, cheap_rec, cheap_proj)?;
        major = match self.node(major) {
            Node::LitNat { .. } => self.nat_lit_to_constructor(major)?,
            Node::LitStr { v } => {
                let s = self.scratch.str_at(Some(self.view.store), v).to_string();
                let c = self.string_lit_to_constructor(&s)?;
                self.rec_whnf(c, cheap_rec, cheap_proj)?
            }
            _ => self.to_cnstr_when_structure(major_induct, major, cheap_rec, cheap_proj)?,
        };
        let rule = match self.get_rec_rule_for(rules.as_slice(), major) {
            Some(r) => r.clone(),
            None => return Ok(None),
        };
        let major_args = self.get_app_args(major);
        let nfields = match nat_to_usize(&rule.nfields) {
            Some(v) => v,
            None => return Ok(None),
        };
        if nfields > major_args.len() {
            return Ok(None);
        }
        let rec_level_ids: Vec<LevelId> = self
            .scratch
            .level_list_at(Some(self.view.store), rec_levels)
            .to_vec();
        if rec_level_ids.len() != lparams.len() {
            return Ok(None);
        }
        let mut rhs = instantiate_level_params(
            self.scratch,
            Some(self.view.store),
            rule.rhs,
            &lparams,
            &rec_level_ids,
            &mut self.guard,
        )?;
        let pmm = nparams + nmotives + nminors;
        rhs = self.mk_app_spine(rhs, &rec_args[..pmm])?;
        let nctor_params = major_args.len() - nfields;
        rhs = self.mk_app_spine(rhs, &major_args[nctor_params..])?;
        if rec_args.len() > major_idx + 1 {
            rhs = self.mk_app_spine(rhs, &rec_args[major_idx + 1..])?;
        }
        Ok(Some(rhs))
    }

    /// oracle: inductive.h:31-50 (`to_cnstr_when_K`).
    #[allow(non_snake_case)] // mirrors the oracle's `to_cnstr_when_K`
    #[allow(clippy::wrong_self_convention)] // oracle name; reduces `self`
    fn to_cnstr_when_k(
        &mut self,
        major_induct: NameId,
        nparams: usize,
        e: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<ExprId, KernelError> {
        let it = self.infer_type(e)?;
        let app_type = self.rec_whnf(it, cheap_rec, cheap_proj)?;
        let app_type_i = self.get_app_fn(app_type);
        if !self.is_const_named(app_type_i, major_induct) {
            return Ok(e);
        }
        if self.data(app_type).has_expr_mvar() {
            let app_type_args = self.get_app_args(app_type);
            for &arg in app_type_args.iter().skip(nparams) {
                if self.data(arg).has_expr_mvar() {
                    return Ok(e);
                }
            }
        }
        let new_cnstr_app = match self.mk_nullary_cnstr(app_type, nparams)? {
            Some(c) => c,
            None => return Ok(e),
        };
        let new_type = self.infer_type(new_cnstr_app)?;
        if !self.is_def_eq(app_type, new_type)? {
            return Ok(e);
        }
        Ok(new_cnstr_app)
    }

    /// oracle: inductive.cpp:87-96 (`mk_nullary_cnstr`).
    fn mk_nullary_cnstr(
        &mut self,
        type_: ExprId,
        num_params: usize,
    ) -> Result<Option<ExprId>, KernelError> {
        let args = self.get_app_args(type_);
        let d = self.get_app_fn(type_);
        let (d_name, d_levels) = match self.node(d) {
            Node::Const { name, levels } => (name, levels),
            _ => return Ok(None),
        };
        let cnstr_name = match self.first_cnstr(d_name) {
            Some(c) => c,
            None => return Ok(None),
        };
        if args.len() < num_params {
            return Ok(None);
        }
        let cnstr = self
            .scratch
            .expr_const(Some(self.view.store), Some(cnstr_name), d_levels)?;
        Ok(Some(self.mk_app_spine(cnstr, &args[..num_params])?))
    }

    /// oracle: inductive.h:62-73 (`to_cnstr_when_structure`).
    #[allow(clippy::wrong_self_convention)] // oracle name; reduces `self`
    fn to_cnstr_when_structure(
        &mut self,
        induct_name: NameId,
        e: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<ExprId, KernelError> {
        if !self.view.is_structure_like(induct_name) || self.is_constructor_app(e) {
            return Ok(e);
        }
        let it = self.infer_type(e)?;
        let e_type = self.rec_whnf(it, cheap_rec, cheap_proj)?;
        if !self.is_const_named(self.get_app_fn(e_type), induct_name) {
            return Ok(e);
        }
        let et = self.infer_type(e_type)?;
        let etw = self.rec_whnf(et, cheap_rec, cheap_proj)?;
        let zero = self.scratch.level_zero(Some(self.view.store))?;
        if matches!(self.node(etw), Node::Sort { level } if level == zero) {
            return Ok(e);
        }
        self.expand_eta_struct(e_type, e)
    }

    /// oracle: inductive.cpp:98-111 (`expand_eta_struct`).
    fn expand_eta_struct(&mut self, e_type: ExprId, e: ExprId) -> Result<ExprId, KernelError> {
        let args = self.get_app_args(e_type);
        let i = self.get_app_fn(e_type);
        let (i_name, i_levels) = match self.node(i) {
            Node::Const { name, levels } => (name, levels),
            _ => return Ok(e),
        };
        let ctor_name = match self.first_cnstr(i_name) {
            Some(c) => c,
            None => return Ok(e),
        };
        let (nparams, nfields) = match self.env_get(Some(ctor_name)) {
            Some(ConstantInfo::Ctor(v)) => {
                (nat_to_usize(&v.num_params), nat_to_usize(&v.num_fields))
            }
            _ => return Ok(e),
        };
        let (nparams, nfields) = match (nparams, nfields) {
            (Some(p), Some(f)) => (p, f),
            _ => return Ok(e),
        };
        if args.len() < nparams {
            return Ok(e);
        }
        let ctor = self
            .scratch
            .expr_const(Some(self.view.store), Some(ctor_name), i_levels)?;
        let mut result = self.mk_app_spine(ctor, &args[..nparams])?;
        for f in 0..nfields {
            let proj =
                self.scratch
                    .expr_proj(Some(self.view.store), i_name, &Nat::from(f as u64), e)?;
            result = self.scratch.expr_app(Some(self.view.store), result, proj)?;
        }
        Ok(result)
    }

    /// oracle: inductive.cpp:79-85 (`get_first_cnstr`).
    fn first_cnstr(&self, name: Option<NameId>) -> Option<NameId> {
        match self.env_get(name) {
            Some(ConstantInfo::Induct(v)) => v.ctors.first().copied(),
            _ => None,
        }
    }

    /// oracle: type_checker.cpp:609-638 (`reduce_nat`).
    fn reduce_nat(&mut self, e: ExprId) -> Result<Option<ExprId>, KernelError> {
        let nargs = self.get_app_num_args(e);
        if nargs == 1 {
            let (f, arg) = match self.node(e) {
                Node::App { f, arg } => (f, arg),
                _ => return Ok(None),
            };
            if self.is_const_named(f, self.nat_succ) {
                let v = match self.get_nat_lit_ext(arg)? {
                    Some(v) => v,
                    None => return Ok(None),
                };
                return Ok(Some(
                    self.scratch
                        .expr_lit_nat(Some(self.view.store), &v.add(&Nat::from(1u64)))?,
                ));
            }
            return Ok(None);
        }
        if nargs != 2 {
            return Ok(None);
        }
        let (ff, a2) = match self.node(e) {
            Node::App { f, arg } => (f, arg),
            _ => return Ok(None),
        };
        let (head, a1) = match self.node(ff) {
            Node::App { f, arg } => (f, arg),
            _ => return Ok(None),
        };
        let op = match self.node(head) {
            Node::Const { name, .. } => match self.nat_binop_id(name) {
                Some(o) => o,
                None => return Ok(None),
            },
            _ => return Ok(None),
        };
        let v1 = match self.get_nat_lit_ext(a1)? {
            Some(v) => v,
            None => return Ok(None),
        };
        let v2 = match self.get_nat_lit_ext(a2)? {
            Some(v) => v,
            None => return Ok(None),
        };
        let r = match op.as_str() {
            "add" => self
                .scratch
                .expr_lit_nat(Some(self.view.store), &v1.add(&v2))?,
            "sub" => self
                .scratch
                .expr_lit_nat(Some(self.view.store), &v1.sub(&v2))?,
            "mul" => self
                .scratch
                .expr_lit_nat(Some(self.view.store), &v1.mul(&v2))?,
            "gcd" => self
                .scratch
                .expr_lit_nat(Some(self.view.store), &v1.gcd(&v2))?,
            "mod" => self
                .scratch
                .expr_lit_nat(Some(self.view.store), &v1.modulo(&v2))?,
            "div" => self
                .scratch
                .expr_lit_nat(Some(self.view.store), &v1.div(&v2))?,
            "land" => self
                .scratch
                .expr_lit_nat(Some(self.view.store), &v1.land(&v2))?,
            "lor" => self
                .scratch
                .expr_lit_nat(Some(self.view.store), &v1.lor(&v2))?,
            "xor" => self
                .scratch
                .expr_lit_nat(Some(self.view.store), &v1.lxor(&v2))?,
            "pow" => match v2.to_usize() {
                Some(exp) if exp <= REDUCE_POW_MAX_EXP => self
                    .scratch
                    .expr_lit_nat(Some(self.view.store), &v1.pow(exp as u32))?,
                _ => return Ok(None),
            },
            "shiftLeft" => match v2.to_usize() {
                Some(k) => self
                    .scratch
                    .expr_lit_nat(Some(self.view.store), &v1.shiftl(k))?,
                None => return Ok(None),
            },
            "shiftRight" => self.scratch.expr_lit_nat(
                Some(self.view.store),
                &v1.shiftr(v2.to_usize().unwrap_or(usize::MAX)),
            )?,
            "beq" => self.bool_const(v1.beq(&v2))?,
            "ble" => self.bool_const(v1.ble(&v2))?,
            _ => return Ok(None),
        };
        Ok(Some(r))
    }

    /// `Bool.true` / `Bool.false` const.
    fn bool_const(&mut self, b: bool) -> Result<ExprId, KernelError> {
        let name = if b { self.bool_true } else { self.bool_false };
        let no_levels = self.scratch.intern_level_list(Some(self.view.store), &[])?;
        self.scratch
            .expr_const(Some(self.view.store), Some(name), no_levels)
    }

    /// oracle: type_checker.cpp:569-574 (`is_nat_lit_ext` / `get_nat_val`).
    fn get_nat_lit_ext(&mut self, e: ExprId) -> Result<Option<Nat>, KernelError> {
        let w = self.whnf(e)?;
        match self.node(w) {
            Node::LitNat { v } => Ok(Some(self.scratch.nat_at(Some(self.view.store), v).clone())),
            Node::Const { name, .. } if name == Some(self.nat_zero) => Ok(Some(Nat::from(0u64))),
            _ => Ok(None),
        }
    }

    /// oracle: type_checker.cpp:546-567 (`reduce_native`). A permanent
    /// skip-stub (out of scope for the pure-Rust kernel).
    fn reduce_native(&mut self, _e: ExprId) -> Result<Option<ExprId>, KernelError> {
        Ok(None)
    }

    /// oracle: type_checker.cpp:961-969 (`is_def_eq_offset`).
    fn is_def_eq_offset(&mut self, t: ExprId, s: ExprId) -> Result<Lbool, KernelError> {
        if self.is_nat_zero(t) && self.is_nat_zero(s) {
            return Ok(Lbool::True);
        }
        let pred_t = self.is_nat_succ(t)?;
        let pred_s = self.is_nat_succ(s)?;
        if let (Some(pt), Some(ps)) = (pred_t, pred_s) {
            return Ok(to_lbool(self.is_def_eq_core(pt, ps)?));
        }
        Ok(Lbool::Undef)
    }

    /// oracle: type_checker.cpp:943-945 (`is_nat_zero`).
    fn is_nat_zero(&self, t: ExprId) -> bool {
        self.is_const_named(t, self.nat_zero)
            || matches!(self.node(t), Node::LitNat { v } if self.scratch.nat_at(Some(self.view.store), v).is_zero())
    }

    /// oracle: type_checker.cpp:947-959 (`is_nat_succ`) — the
    /// predecessor of `t`, from either a positive nat literal or a
    /// `Nat.succ _` app.
    fn is_nat_succ(&mut self, t: ExprId) -> Result<Option<ExprId>, KernelError> {
        if let Node::LitNat { v } = self.node(t) {
            let n = self.scratch.nat_at(Some(self.view.store), v).clone();
            if !n.is_zero() {
                return Ok(Some(
                    self.scratch
                        .expr_lit_nat(Some(self.view.store), &n.sub(&Nat::from(1u64)))?,
                ));
            }
        }
        if self.is_const_named(self.get_app_fn(t), self.nat_succ) && self.get_app_num_args(t) == 1 {
            if let Node::App { arg, .. } = self.node(t) {
                return Ok(Some(arg));
            }
        }
        Ok(None)
    }

    /// oracle: type_checker.h:87-89 / type_checker.cpp:778-790
    /// (`try_eta_expansion` + `_core`). Tries both argument orders.
    fn try_eta_expansion(&mut self, t: ExprId, s: ExprId) -> Result<bool, KernelError> {
        if self.try_eta_expansion_core(t, s)? {
            return Ok(true);
        }
        self.try_eta_expansion_core(s, t)
    }

    /// oracle: type_checker.cpp:778-790 (`try_eta_expansion_core`).
    fn try_eta_expansion_core(&mut self, t: ExprId, s: ExprId) -> Result<bool, KernelError> {
        if !self.is_lambda(t) || self.is_lambda(s) {
            return Ok(false);
        }
        let st = self.infer_type(s)?;
        let s_type = self.whnf(st)?;
        let (bn, dom, bi) = match self.node(s_type) {
            Node::Forall {
                binder_name,
                binder_type,
                binder_info,
                ..
            } => (binder_name, binder_type, binder_info),
            _ => return Ok(false),
        };
        let b0 = self
            .scratch
            .expr_bvar(Some(self.view.store), &Nat::from(0u64))?;
        let body = self.scratch.expr_app(Some(self.view.store), s, b0)?;
        let new_s = self
            .scratch
            .expr_lam(Some(self.view.store), bn, dom, body, bi)?;
        self.is_def_eq(t, new_s)
    }

    /// oracle: type_checker.h:91-93 / type_checker.cpp:793-809
    /// (`try_eta_struct` + `_core`). Tries both argument orders.
    fn try_eta_struct(&mut self, t: ExprId, s: ExprId) -> Result<bool, KernelError> {
        if self.try_eta_struct_core(t, s)? {
            return Ok(true);
        }
        self.try_eta_struct_core(s, t)
    }

    /// oracle: type_checker.cpp:793-809 (`try_eta_struct_core`).
    fn try_eta_struct_core(&mut self, t: ExprId, s: ExprId) -> Result<bool, KernelError> {
        let f = self.get_app_fn(s);
        let fname = match self.node(f) {
            Node::Const { name, .. } => name,
            _ => return Ok(false),
        };
        let (nparams, nfields, induct) = match self.env_get(fname) {
            Some(ConstantInfo::Ctor(v)) => (
                nat_to_usize(&v.num_params),
                nat_to_usize(&v.num_fields),
                v.induct,
            ),
            _ => return Ok(false),
        };
        let (nparams, nfields) = match (nparams, nfields) {
            (Some(p), Some(f)) => (p, f),
            _ => return Ok(false),
        };
        if self.get_app_num_args(s) != nparams + nfields {
            return Ok(false);
        }
        if !self.view.is_structure_like(induct) {
            return Ok(false);
        }
        let tt = self.infer_type(t)?;
        let ss = self.infer_type(s)?;
        if !self.is_def_eq(tt, ss)? {
            return Ok(false);
        }
        let s_args = self.get_app_args(s);
        for (i, &sa) in s_args.iter().enumerate().skip(nparams) {
            let proj = self.scratch.expr_proj(
                Some(self.view.store),
                Some(induct),
                &Nat::from((i - nparams) as u64),
                t,
            )?;
            if !self.is_def_eq(proj, sa)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// oracle: type_checker.cpp:1037-1041 (`try_string_lit_expansion`).
    /// Tries both argument orders.
    fn try_string_lit_expansion(&mut self, t: ExprId, s: ExprId) -> Result<Lbool, KernelError> {
        let r = self.try_string_lit_expansion_core(t, s)?;
        if r != Lbool::Undef {
            return Ok(r);
        }
        self.try_string_lit_expansion_core(s, t)
    }

    /// oracle: type_checker.cpp:1030-1035 (`try_string_lit_expansion_core`).
    fn try_string_lit_expansion_core(
        &mut self,
        t: ExprId,
        s: ExprId,
    ) -> Result<Lbool, KernelError> {
        if let Node::LitStr { v } = self.node(t) {
            if self.is_app(s) && self.is_const_named(self.get_app_fn(s), self.string_mk) {
                let str_val = self.scratch.str_at(Some(self.view.store), v).to_string();
                let ctor = self.string_lit_to_constructor(&str_val)?;
                let w = self.whnf(ctor)?;
                return Ok(to_lbool(self.is_def_eq_core(w, s)?));
            }
        }
        Ok(Lbool::Undef)
    }

    /// oracle: type_checker.cpp:1044-1054 (`is_def_eq_unit_like`).
    fn is_def_eq_unit_like(&mut self, t: ExprId, s: ExprId) -> Result<bool, KernelError> {
        let tt = self.infer_type(t)?;
        let t_type = self.whnf(tt)?;
        let i = self.get_app_fn(t_type);
        let i_name = match self.node(i) {
            Node::Const { name: Some(n), .. } => n,
            _ => return Ok(false),
        };
        if !self.view.is_structure_like(i_name) {
            return Ok(false);
        }
        let ctor_name = match self.first_cnstr(Some(i_name)) {
            Some(c) => c,
            None => return Ok(false),
        };
        let nfields = match self.env_get(Some(ctor_name)) {
            Some(ConstantInfo::Ctor(v)) => nat_to_usize(&v.num_fields),
            _ => return Ok(false),
        };
        if nfields != Some(0) {
            return Ok(false);
        }
        let st = self.infer_type(s)?;
        self.is_def_eq_core(t_type, st)
    }

    /// oracle: inductive.cpp:1200 (`string_lit_to_constructor`) — expand
    /// a string literal to `String.ofList (List.cons.{0} Char
    /// (Char.ofNat c₀) (… (List.nil.{0} Char)))`.
    fn string_lit_to_constructor(&mut self, s: &str) -> Result<ExprId, KernelError> {
        let base = Some(self.view.store);
        let zero = self.scratch.level_zero(base)?;
        let no_levels = self.scratch.intern_level_list(base, &[])?;
        let zero_list = self.scratch.intern_level_list(base, &[zero])?;
        let char_name = mk_name1_id(self.scratch, base, "Char")?;
        let char_ty = self.scratch.expr_const(base, Some(char_name), no_levels)?;
        let list_nil_name = mk_name2_id(self.scratch, base, "List", "nil")?;
        let list_nil = self
            .scratch
            .expr_const(base, Some(list_nil_name), zero_list)?;
        let list_cons_name = mk_name2_id(self.scratch, base, "List", "cons")?;
        let list_cons = self
            .scratch
            .expr_const(base, Some(list_cons_name), zero_list)?;
        let char_of_nat_name = mk_name2_id(self.scratch, base, "Char", "ofNat")?;
        let char_of_nat = self
            .scratch
            .expr_const(base, Some(char_of_nat_name), no_levels)?;
        let string_mk_name = mk_name2_id(self.scratch, base, "String", "ofList")?;
        let string_mk_const = self
            .scratch
            .expr_const(base, Some(string_mk_name), no_levels)?;
        let nil = self.scratch.expr_app(base, list_nil, char_ty)?;
        let cons_char = self.scratch.expr_app(base, list_cons, char_ty)?;
        let mut r = nil;
        for cp in s.chars().rev() {
            let lit = self.scratch.expr_lit_nat(base, &Nat::from(cp as u64))?;
            let c = self.scratch.expr_app(base, char_of_nat, lit)?;
            let step1 = self.scratch.expr_app(base, cons_char, c)?;
            r = self.scratch.expr_app(base, step1, r)?;
        }
        self.scratch.expr_app(base, string_mk_const, r)
    }

    /// oracle: inductive.cpp:1191-1198 (`nat_lit_to_constructor`) — a
    /// nat literal in constructor form.
    fn nat_lit_to_constructor(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        let base = Some(self.view.store);
        let v = match self.node(e) {
            Node::LitNat { v } => self.scratch.nat_at(base, v).clone(),
            _ => return Ok(e),
        };
        if v.is_zero() {
            let no_levels = self.scratch.intern_level_list(base, &[])?;
            self.scratch
                .expr_const(base, Some(self.nat_zero), no_levels)
        } else {
            let pred = self.scratch.expr_lit_nat(base, &v.sub(&Nat::from(1u64)))?;
            let no_levels = self.scratch.intern_level_list(base, &[])?;
            let succ = self
                .scratch
                .expr_const(base, Some(self.nat_succ), no_levels)?;
            self.scratch.expr_app(base, succ, pred)
        }
    }

    /// oracle: inductive.cpp:113-121 (`get_rec_rule_for`).
    fn get_rec_rule_for<'a>(
        &self,
        rules: &'a [RecursorRule],
        major: ExprId,
    ) -> Option<&'a RecursorRule> {
        let fn0 = self.get_app_fn(major);
        let name = self.const_name(fn0)?;
        rules.iter().find(|r| r.ctor == name)
    }

    /// oracle: declaration.cpp:145-154 (`recursor_val::get_major_induct`).
    fn get_major_induct(&self, ty: ExprId, major_idx: usize) -> Option<NameId> {
        let mut t = ty;
        for _ in 0..major_idx {
            t = match self.node(t) {
                Node::Forall { body, .. } => body,
                _ => return None,
            };
        }
        let dom = match self.node(t) {
            Node::Forall { binder_type, .. } => binder_type,
            _ => return None,
        };
        match self.node(self.get_app_fn(dom)) {
            Node::Const { name, .. } => name,
            _ => None,
        }
    }

    /// oracle: inductive.cpp:52-59 (`is_constructor_app`).
    fn is_constructor_app(&self, e: ExprId) -> bool {
        if let Node::Const { name, .. } = self.node(self.get_app_fn(e)) {
            matches!(self.env_get(name), Some(ConstantInfo::Ctor(_)))
        } else {
            false
        }
    }
}

impl<'e> TypeChecker<'e> {
    // -- is_def_eq ------------------------------------------------------

    /// oracle: type_checker.cpp:1133-1138 (`is_def_eq`). On success,
    /// records the equivalence in the union-find.
    pub fn is_def_eq(&mut self, t: ExprId, s: ExprId) -> Result<bool, KernelError> {
        let r = self.is_def_eq_core(t, s)?;
        if r {
            self.eqv_cache.merge(t, s);
        }
        Ok(r)
    }

    /// oracle: type_checker.cpp:740-763 (`quick_is_def_eq`).
    fn quick_is_def_eq(
        &mut self,
        t: ExprId,
        s: ExprId,
        use_hash: bool,
    ) -> Result<Lbool, KernelError> {
        let st: &Store = &*self.scratch;
        let base = Some(self.view.store);
        if self
            .eqv_cache
            .is_equiv(st, base, t, s, use_hash, &mut self.guard)?
        {
            return Ok(Lbool::True);
        }
        match (self.node(t), self.node(s)) {
            (Node::Lam { .. }, Node::Lam { .. }) | (Node::Forall { .. }, Node::Forall { .. }) => {
                Ok(to_lbool(self.is_def_eq_binding(t, s)?))
            }
            (Node::Sort { level: lt }, Node::Sort { level: ls }) => {
                let a = self.scratch.to_level(Some(self.view.store), lt);
                let b = self.scratch.to_level(Some(self.view.store), ls);
                Ok(to_lbool(Level::is_equivalent(&a, &b, &mut self.guard)?))
            }
            (Node::MData { expr: et, .. }, Node::MData { expr: es, .. }) => {
                Ok(to_lbool(self.is_def_eq(et, es)?))
            }
            (Node::LitNat { v: va }, Node::LitNat { v: vb }) => Ok(to_lbool(va == vb)),
            (Node::LitStr { v: va }, Node::LitStr { v: vb }) => Ok(to_lbool(va == vb)),
            _ => Ok(Lbool::Undef),
        }
    }

    /// oracle: type_checker.cpp:690-717 (`is_def_eq_binding`).
    fn is_def_eq_binding(&mut self, t: ExprId, s: ExprId) -> Result<bool, KernelError> {
        let saved = self.lctx.save();
        let r = self.is_def_eq_binding_body(t, s);
        self.lctx.restore(saved);
        r
    }

    fn is_def_eq_binding_body(&mut self, t0: ExprId, s0: ExprId) -> Result<bool, KernelError> {
        let mut subst: Vec<ExprId> = Vec::new();
        let mut t = t0;
        let mut s = s0;
        let is_lam = self.is_lambda(t);
        loop {
            let (t_dom, t_body) = self.binder_dom_body(t);
            let (s_dom, s_body, s_name, s_info) = self.binder_full(s);
            let mut var_s_type: Option<ExprId> = None;
            if t_dom != s_dom {
                let vst = instantiate_rev(
                    self.scratch,
                    Some(self.view.store),
                    s_dom,
                    &subst,
                    &mut self.guard,
                )?;
                let vtt = instantiate_rev(
                    self.scratch,
                    Some(self.view.store),
                    t_dom,
                    &subst,
                    &mut self.guard,
                )?;
                if !self.is_def_eq(vtt, vst)? {
                    return Ok(false);
                }
                var_s_type = Some(vst);
            }
            if self.has_loose_bvars(t_body) || self.has_loose_bvars(s_body) {
                let vst = match var_s_type {
                    Some(v) => v,
                    None => instantiate_rev(
                        self.scratch,
                        Some(self.view.store),
                        s_dom,
                        &subst,
                        &mut self.guard,
                    )?,
                };
                let fvar = self.lctx.mk_local_decl(
                    self.scratch,
                    Some(self.view.store),
                    &mut self.fvar_gen,
                    s_name,
                    vst,
                    s_info,
                )?;
                subst.push(fvar);
            } else {
                subst.push(self.dont_care);
            }
            t = t_body;
            s = s_body;
            let same = if is_lam {
                self.is_lambda(t) && self.is_lambda(s)
            } else {
                self.is_forall(t) && self.is_forall(s)
            };
            if !same {
                break;
            }
        }
        let ti = instantiate_rev(
            self.scratch,
            Some(self.view.store),
            t,
            &subst,
            &mut self.guard,
        )?;
        let si = instantiate_rev(
            self.scratch,
            Some(self.view.store),
            s,
            &subst,
            &mut self.guard,
        )?;
        self.is_def_eq(ti, si)
    }

    /// oracle: type_checker.cpp:767-775 (`is_def_eq_args`).
    fn is_def_eq_args(&mut self, t: ExprId, s: ExprId) -> Result<bool, KernelError> {
        let mut t = t;
        let mut s = s;
        while self.is_app(t) && self.is_app(s) {
            let (tf, ta) = match self.node(t) {
                Node::App { f, arg } => (f, arg),
                _ => unreachable!(),
            };
            let (sf, sa) = match self.node(s) {
                Node::App { f, arg } => (f, arg),
                _ => unreachable!(),
            };
            if !self.is_def_eq(ta, sa)? {
                return Ok(false);
            }
            t = tf;
            s = sf;
        }
        Ok(!self.is_app(t) && !self.is_app(s))
    }

    /// oracle: type_checker.cpp:815-832 (`is_def_eq_app`).
    fn is_def_eq_app(&mut self, t: ExprId, s: ExprId) -> Result<bool, KernelError> {
        if self.is_app(t) && self.is_app(s) {
            let t_args = self.get_app_args(t);
            let t_fn = self.get_app_fn(t);
            let s_args = self.get_app_args(s);
            let s_fn = self.get_app_fn(s);
            if self.is_def_eq(t_fn, s_fn)? && t_args.len() == s_args.len() {
                for (&ta, &sa) in t_args.iter().zip(s_args.iter()) {
                    if !self.is_def_eq(ta, sa)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// oracle: type_checker.cpp:836-843 (`is_def_eq_proof_irrel`).
    fn is_def_eq_proof_irrel(&mut self, t: ExprId, s: ExprId) -> Result<Lbool, KernelError> {
        let t_type = self.infer_type(t)?;
        if !self.is_prop(t_type)? {
            return Ok(Lbool::Undef);
        }
        let s_type = self.infer_type(s)?;
        Ok(to_lbool(self.is_def_eq(t_type, s_type)?))
    }

    /// oracle: type_checker.cpp:727-737 (`is_def_eq(levels, levels)`).
    fn is_def_eq_levels(&mut self, ls1: &[LevelId], ls2: &[LevelId]) -> Result<bool, KernelError> {
        if ls1.len() != ls2.len() {
            return Ok(false);
        }
        for (&a, &b) in ls1.iter().zip(ls2.iter()) {
            let la = self.scratch.to_level(Some(self.view.store), a);
            let lb = self.scratch.to_level(Some(self.view.store), b);
            if !Level::is_equivalent(&la, &lb, &mut self.guard)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// oracle: type_checker.cpp:845-855 (`failed_before`).
    fn failed_before(&self, t: ExprId, s: ExprId) -> bool {
        let (ht, hs) = (self.data(t).hash(), self.data(s).hash());
        if ht < hs {
            self.failure_cache.contains(&(t, s))
        } else if ht > hs {
            self.failure_cache.contains(&(s, t))
        } else {
            self.failure_cache.contains(&(t, s)) || self.failure_cache.contains(&(s, t))
        }
    }

    /// oracle: type_checker.cpp:857-862 (`cache_failure`).
    fn cache_failure(&mut self, t: ExprId, s: ExprId) {
        if self.data(t).hash() <= self.data(s).hash() {
            self.failure_cache.insert((t, s));
        } else {
            self.failure_cache.insert((s, t));
        }
    }

    /// oracle: type_checker.cpp:868-875 (`try_unfold_proj_app`).
    fn try_unfold_proj_app(&mut self, e: ExprId) -> Result<Option<ExprId>, KernelError> {
        let f = self.get_app_fn(e);
        if self.is_proj(f) {
            let e_new = self.whnf_core(e, false, false)?;
            if e_new != e {
                return Ok(Some(e_new));
            }
        }
        Ok(None)
    }

    /// oracle: type_checker.cpp:884-941 (`lazy_delta_reduction_step`).
    fn lazy_delta_reduction_step(
        &mut self,
        t_n: &mut ExprId,
        s_n: &mut ExprId,
    ) -> Result<ReductionStatus, KernelError> {
        let d_t = self.is_delta(*t_n);
        let d_s = self.is_delta(*s_n);
        match (d_t, d_s) {
            (None, None) => return Ok(ReductionStatus::DefUnknown),
            (Some(_), None) => {
                if let Some(s_new) = self.try_unfold_proj_app(*s_n)? {
                    *s_n = s_new;
                } else {
                    *t_n = self.unfold_and_whnf(*t_n)?;
                }
            }
            (None, Some(_)) => {
                if let Some(t_new) = self.try_unfold_proj_app(*t_n)? {
                    *t_n = t_new;
                } else {
                    *s_n = self.unfold_and_whnf(*s_n)?;
                }
            }
            (Some(dt), Some(ds)) => {
                let (dt_hints, ds_hints) = (info_hints(dt), info_hints(ds));
                let c = compare_hints(dt_hints, ds_hints);
                if c < 0 {
                    *t_n = self.unfold_and_whnf(*t_n)?;
                } else if c > 0 {
                    *s_n = self.unfold_and_whnf(*s_n)?;
                } else {
                    if self.is_app(*t_n)
                        && self.is_app(*s_n)
                        && std::ptr::eq(dt, ds)
                        && is_regular_hint(dt_hints)
                        && !self.failed_before(*t_n, *s_n)
                    {
                        let lt = self.const_levels_of_head(*t_n);
                        let ls = self.const_levels_of_head(*s_n);
                        if self.is_def_eq_levels(&lt, &ls)? && self.is_def_eq_args(*t_n, *s_n)? {
                            return Ok(ReductionStatus::DefEqual);
                        }
                        self.cache_failure(*t_n, *s_n);
                    }
                    *t_n = self.unfold_and_whnf(*t_n)?;
                    *s_n = self.unfold_and_whnf(*s_n)?;
                }
            }
        }
        match self.quick_is_def_eq(*t_n, *s_n, false)? {
            Lbool::True => Ok(ReductionStatus::DefEqual),
            Lbool::False => Ok(ReductionStatus::DefDiff),
            Lbool::Undef => Ok(ReductionStatus::Continue),
        }
    }

    /// `whnf_core(unfold_definition(e), false, true)` — the delta-unfold
    /// step.
    fn unfold_and_whnf(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        match self.unfold_definition(e)? {
            Some(u) => self.whnf_core(u, false, true),
            None => Ok(e),
        }
    }

    /// oracle: type_checker.cpp:973-999 (`lazy_delta_reduction`).
    fn lazy_delta_reduction(
        &mut self,
        t_n: &mut ExprId,
        s_n: &mut ExprId,
    ) -> Result<Lbool, KernelError> {
        self.guarded(|slf| loop {
            let r = slf.is_def_eq_offset(*t_n, *s_n)?;
            if r != Lbool::Undef {
                return Ok(r);
            }
            if !slf.data(*t_n).has_fvar() && !slf.data(*s_n).has_fvar() {
                if let Some(tv) = slf.reduce_nat(*t_n)? {
                    return Ok(to_lbool(slf.is_def_eq_core(tv, *s_n)?));
                }
                if let Some(sv) = slf.reduce_nat(*s_n)? {
                    return Ok(to_lbool(slf.is_def_eq_core(*t_n, sv)?));
                }
            }
            if let Some(tv) = slf.reduce_native(*t_n)? {
                return Ok(to_lbool(slf.is_def_eq_core(tv, *s_n)?));
            }
            if let Some(sv) = slf.reduce_native(*s_n)? {
                return Ok(to_lbool(slf.is_def_eq_core(*t_n, sv)?));
            }
            match slf.lazy_delta_reduction_step(t_n, s_n)? {
                ReductionStatus::Continue => {}
                ReductionStatus::DefUnknown => return Ok(Lbool::Undef),
                ReductionStatus::DefEqual => return Ok(Lbool::True),
                ReductionStatus::DefDiff => return Ok(Lbool::False),
            }
        })
    }

    /// oracle: type_checker.cpp:1008-1025 (`lazy_delta_proj_reduction`).
    fn lazy_delta_proj_reduction(
        &mut self,
        t_n: &mut ExprId,
        s_n: &mut ExprId,
        idx: &Nat,
    ) -> Result<bool, KernelError> {
        loop {
            match self.lazy_delta_reduction_step(t_n, s_n)? {
                ReductionStatus::Continue => {}
                ReductionStatus::DefEqual => return Ok(true),
                ReductionStatus::DefUnknown | ReductionStatus::DefDiff => {
                    if let Some(i) = nat_to_usize(idx) {
                        if let Some(t) = self.reduce_proj_core(*t_n, i)? {
                            if let Some(s) = self.reduce_proj_core(*s_n, i)? {
                                return self.is_def_eq_core(t, s);
                            }
                        }
                    }
                    return self.is_def_eq_core(*t_n, *s_n);
                }
            }
        }
    }

    /// oracle: type_checker.cpp:1056-1131 (`is_def_eq_core`). Branch
    /// order follows the oracle literally.
    fn is_def_eq_core(&mut self, t: ExprId, s: ExprId) -> Result<bool, KernelError> {
        self.guarded(|slf| {
            let r = slf.quick_is_def_eq(t, s, true)?;
            if r != Lbool::Undef {
                return Ok(r == Lbool::True);
            }

            if !slf.data(t).has_fvar() && slf.is_const_named(s, slf.bool_true) {
                let wt = slf.whnf(t)?;
                if slf.is_const_named(wt, slf.bool_true) {
                    return Ok(true);
                }
            }

            let mut t_n = slf.whnf_core(t, false, true)?;
            let mut s_n = slf.whnf_core(s, false, true)?;
            if t_n != t || s_n != s {
                let r = slf.quick_is_def_eq(t_n, s_n, false)?;
                if r != Lbool::Undef {
                    return Ok(r == Lbool::True);
                }
            }

            let r = slf.is_def_eq_proof_irrel(t_n, s_n)?;
            if r != Lbool::Undef {
                return Ok(r == Lbool::True);
            }

            let r = slf.lazy_delta_reduction(&mut t_n, &mut s_n)?;
            if r != Lbool::Undef {
                return Ok(r == Lbool::True);
            }

            if let (
                Node::Const {
                    name: nt,
                    levels: lt,
                },
                Node::Const {
                    name: ns,
                    levels: ls,
                },
            ) = (slf.node(t_n), slf.node(s_n))
            {
                if nt == ns {
                    let lt_ids = slf.scratch.level_list_at(Some(slf.view.store), lt).to_vec();
                    let ls_ids = slf.scratch.level_list_at(Some(slf.view.store), ls).to_vec();
                    if slf.is_def_eq_levels(&lt_ids, &ls_ids)? {
                        return Ok(true);
                    }
                }
            }

            if let (Node::FVar { id: it }, Node::FVar { id: is_ }) = (slf.node(t_n), slf.node(s_n))
            {
                if it == is_ {
                    return Ok(true);
                }
            }

            if let (
                n1 @ (Node::Proj { .. } | Node::ProjBig { .. }),
                n2 @ (Node::Proj { .. } | Node::ProjBig { .. }),
            ) = (slf.node(t_n), slf.node(s_n))
            {
                let (_, ix_t, ct) = slf.proj_parts(n1);
                let (_, ix_s, cs) = slf.proj_parts(n2);
                if ix_t == ix_s {
                    let mut tc = ct;
                    let mut sc = cs;
                    if slf.lazy_delta_proj_reduction(&mut tc, &mut sc, &ix_t)? {
                        return Ok(true);
                    }
                }
            }

            let t_n_n = slf.whnf_core(t_n, false, false)?;
            let s_n_n = slf.whnf_core(s_n, false, false)?;
            if t_n_n != t_n || s_n_n != s_n {
                return slf.is_def_eq_core(t_n_n, s_n_n);
            }

            if slf.is_def_eq_app(t_n, s_n)? {
                return Ok(true);
            }
            if slf.try_eta_expansion(t_n, s_n)? {
                return Ok(true);
            }
            if slf.try_eta_struct(t_n, s_n)? {
                return Ok(true);
            }
            let r = slf.try_string_lit_expansion(t_n, s_n)?;
            if r != Lbool::Undef {
                return Ok(r == Lbool::True);
            }
            if slf.is_def_eq_unit_like(t_n, s_n)? {
                return Ok(true);
            }

            Ok(false)
        })
    }
}

impl<'e> QuotCtx for TypeChecker<'e> {
    fn get_app_fn(&self, e: ExprId) -> ExprId {
        TypeChecker::get_app_fn(self, e)
    }
    fn get_app_args(&self, e: ExprId) -> Vec<ExprId> {
        TypeChecker::get_app_args(self, e)
    }
    fn const_name(&self, e: ExprId) -> Option<NameId> {
        TypeChecker::const_name(self, e)
    }
    fn mk_app_spine(&mut self, f: ExprId, args: &[ExprId]) -> Result<ExprId, KernelError> {
        TypeChecker::mk_app_spine(self, f, args)
    }
    fn whnf(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        TypeChecker::whnf(self, e)
    }
    fn quot_names(&mut self) -> Result<(NameId, NameId, NameId), KernelError> {
        let base = Some(self.view.store);
        let lift = mk_name2_id(self.scratch, base, "Quot", "lift")?;
        let ind = mk_name2_id(self.scratch, base, "Quot", "ind")?;
        let mk = mk_name2_id(self.scratch, base, "Quot", "mk")?;
        Ok((lift, ind, mk))
    }
}

#[cfg(test)]
mod tests;
