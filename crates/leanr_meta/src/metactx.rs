//! All shared `MetaM` state. Each concern module (`whnf`, `infer`, ...)
//! contributes an `impl MetaCtx` block — inherent impls split across
//! files, direct calls, no dynamic dispatch (spec § MetaCtx).
//!
//! Traversal is ExprId-native over the bank, the `tc.rs` idiom: nodes
//! decode one level at a time via `Store::expr_node`, caches key on
//! ids, and `Store::to_expr` is never called on a hot path.

use std::collections::HashMap;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId, Store};
use leanr_kernel::{EnvView, ExprData, FVarIdGen, LocalContext, RecGuard, MAX_REC_DEPTH};
use leanr_olean::{EntryScope, MatcherEntry, ReducibilityEntry, ReducibilityStatus};

use crate::{Config, MetaError, MetavarContext, TransparencyMode};

/// Stack-growth constants — the same values `tc.rs` uses (private
/// there, so restated; keep in sync by inspection). Verified against
/// `crates/leanr_kernel/src/tc.rs`'s own `RED_ZONE`/`STACK_CHUNK`
/// constants.
const RED_ZONE: usize = 128 * 1024;
const STACK_CHUNK: usize = 4 * 1024 * 1024;

/// Deterministic step budget (spec § Determinism: a step counter, not
/// maxHeartbeats — machine-independent by construction, a knowing
/// divergence from the oracle). The value is leanr-specific; queries
/// that come near it must be excluded from the differential corpus.
pub const DEFAULT_STEP_BUDGET: u64 = 10_000_000;

pub struct MetaCtx<'e> {
    pub(crate) view: EnvView<'e>,
    pub(crate) scratch: &'e mut Store,
    pub(crate) cfg: Config,
    pub(crate) mctx: MetavarContext,
    pub(crate) lctx: LocalContext,
    pub(crate) fvar_gen: FVarIdGen,
    pub(crate) guard: RecGuard,
    guard_depth: u32,
    steps: u64,
    step_budget: u64,
    /// (config cache key, expr) -> whnf result. Permanent entries only
    /// (mvar- and fvar-free inputs); the transient side arrives with
    /// defeq in plan 3. See `cacheable` below.
    ///
    /// `whnf`/`whnf_core` (task 5, `whnf.rs`) are this field's real
    /// readers/writers.
    pub(crate) whnf_cache: HashMap<(u64, ExprId), ExprId>,
    /// `whnf_core`'s own memo table (task 5) — a leanr-specific
    /// addition (the oracle's `whnfCore` itself carries no cache; only
    /// `whnfImp` does, `whnf_cache` above). Since `whnf_core` recurses
    /// on itself pervasively (beta/zeta/iota/proj chains), memoizing at
    /// this layer too is a pure performance win under the same
    /// `cacheable` predicate — reduction is a deterministic function of
    /// `(Config, ExprId)`, so extra memoization cannot change a result,
    /// only how fast it's produced.
    pub(crate) whnf_core_cache: HashMap<(u64, ExprId), ExprId>,
    pub(crate) infer_cache: HashMap<(u64, ExprId), ExprId>,
    /// ReducibilityStatus per constant; absent => Semireducible.
    reducibility: HashMap<NameId, ReducibilityStatus>,
    matchers: HashMap<NameId, MatcherEntry>,
    /// The `smartUnfolding` option (oracle default: true), consulted by
    /// `unfold_definition`'s app/const arms (task 7).
    pub(crate) smart_unfolding: bool,
    /// Plan-3/4 seam: the `canUnfold?` override predicate channel
    /// (oracle: Meta.Context.canUnfold?). `whnf_matcher` (task 6) is
    /// its only setter this plan. When set, results are not cached
    /// (oracle useWHNFCache, WHNF.lean:1082-1088).
    pub(crate) can_unfold_override: bool,
    /// `Nat.<op>` builtin name -> which op, for `whnf.rs`'s `reduce_nat`
    /// (oracle: `reduceNat?`'s dispatch, WHNF.lean:1054-1078). Interned
    /// once here — the `tc.rs` constructor idiom
    /// (`TypeChecker::new`, tc.rs:508-556): tiny fixed names, `.expect()`
    /// on the (persistent-bank-exhaustion-only) failure case.
    pub(crate) nat_bin_ops: HashMap<NameId, NatOp>,
    pub(crate) nat_succ: NameId,
    pub(crate) nat_zero: NameId,
    pub(crate) bool_true: NameId,
    pub(crate) bool_false: NameId,
    /// `Acc.rec` / `WellFounded.rec` — the `isWFRec` transparency bump
    /// in `reduce_rec` (oracle: WHNF.lean:207-209, :230-237).
    pub(crate) acc_rec: NameId,
    pub(crate) wf_rec: NameId,
    /// `` `sunfoldMatch `` / `` `sunfoldMatchAlt `` — the two smart-
    /// unfolding annotation kinds (oracle: `markSmartUnfoldingMatch`/
    /// `markSmartUnfoldingMatchAlt`, WHNF.lean:64-70), read by
    /// `whnf.rs`'s `annotation` (task 7). Root (single-component, no
    /// parent) names, like Lean's own backtick literals — interned via
    /// `mk_name1`, not `mk_name2` (that helper is for two-part dotted
    /// names like `Nat.add`).
    pub(crate) sunfold_match: NameId,
    pub(crate) sunfold_match_alt: NameId,
}

/// The `Nat.*` builtins `reduce_nat` folds on `LitNat`/`Nat.zero`
/// operands (oracle: `reduceNat?`, WHNF.lean:1054-1078).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NatOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Gcd,
    Beq,
    Ble,
    Land,
    Lor,
    Xor,
    ShiftLeft,
    ShiftRight,
    Pow,
}

/// `mk_name2_id` (tc.rs:365-374), restated: that helper is private to
/// `leanr_kernel`. `.expect(...)` matches tc.rs's own constructor
/// posture — a tiny fixed name can only fail to intern if the
/// PERSISTENT bank is already exhausted, at which point every other
/// kernel operation is already failing too.
/// Single-component ("root") name — a `mk_name2` twin for names with no
/// dotted parent, e.g. `` `sunfoldMatch ``.
fn mk_name1(scratch: &mut Store, base: Option<&Store>, a: &str) -> NameId {
    let a_str = scratch
        .intern_str(base, a)
        .expect("interning a tiny fixed name is infallible");
    scratch
        .name_str(base, None, a_str)
        .expect("interning a tiny fixed name is infallible")
}

fn mk_name2(scratch: &mut Store, base: Option<&Store>, a: &str, b: &str) -> NameId {
    let a_str = scratch
        .intern_str(base, a)
        .expect("interning a tiny fixed name is infallible");
    let parent = scratch
        .name_str(base, None, a_str)
        .expect("interning a tiny fixed name is infallible");
    let b_str = scratch
        .intern_str(base, b)
        .expect("interning a tiny fixed name is infallible");
    scratch
        .name_str(base, Some(parent), b_str)
        .expect("interning a tiny fixed name is infallible")
}

impl<'e> MetaCtx<'e> {
    pub fn new(
        view: EnvView<'e>,
        scratch: &'e mut Store,
        cfg: Config,
        reducibility: &[ReducibilityEntry],
        matchers: &[MatcherEntry],
    ) -> MetaCtx<'e> {
        // Global entries only: scoped reducibility entries require the
        // M3b3-style activation model, out of scope for the meta core
        // (they are rare and Mathlib's are decoded but unconsulted
        // here; revisit when a corpus divergence implicates one).
        let reducibility = reducibility
            .iter()
            .filter(|e| matches!(e.scope, EntryScope::Global))
            .map(|e| (e.name, e.status))
            .collect();
        let matchers = matchers.iter().map(|m| (m.name, m.clone())).collect();

        let base = Some(view.store);
        let nat_add = mk_name2(scratch, base, "Nat", "add");
        let nat_sub = mk_name2(scratch, base, "Nat", "sub");
        let nat_mul = mk_name2(scratch, base, "Nat", "mul");
        let nat_div = mk_name2(scratch, base, "Nat", "div");
        let nat_mod = mk_name2(scratch, base, "Nat", "mod");
        let nat_gcd = mk_name2(scratch, base, "Nat", "gcd");
        let nat_beq = mk_name2(scratch, base, "Nat", "beq");
        let nat_ble = mk_name2(scratch, base, "Nat", "ble");
        let nat_land = mk_name2(scratch, base, "Nat", "land");
        let nat_lor = mk_name2(scratch, base, "Nat", "lor");
        let nat_xor = mk_name2(scratch, base, "Nat", "xor");
        let nat_shift_left = mk_name2(scratch, base, "Nat", "shiftLeft");
        let nat_shift_right = mk_name2(scratch, base, "Nat", "shiftRight");
        let nat_pow = mk_name2(scratch, base, "Nat", "pow");
        let nat_succ = mk_name2(scratch, base, "Nat", "succ");
        let nat_zero = mk_name2(scratch, base, "Nat", "zero");
        let bool_true = mk_name2(scratch, base, "Bool", "true");
        let bool_false = mk_name2(scratch, base, "Bool", "false");
        let acc_rec = mk_name2(scratch, base, "Acc", "rec");
        let wf_rec = mk_name2(scratch, base, "WellFounded", "rec");
        let sunfold_match = mk_name1(scratch, base, "sunfoldMatch");
        let sunfold_match_alt = mk_name1(scratch, base, "sunfoldMatchAlt");

        let mut nat_bin_ops = HashMap::new();
        nat_bin_ops.insert(nat_add, NatOp::Add);
        nat_bin_ops.insert(nat_sub, NatOp::Sub);
        nat_bin_ops.insert(nat_mul, NatOp::Mul);
        nat_bin_ops.insert(nat_div, NatOp::Div);
        nat_bin_ops.insert(nat_mod, NatOp::Mod);
        nat_bin_ops.insert(nat_gcd, NatOp::Gcd);
        nat_bin_ops.insert(nat_beq, NatOp::Beq);
        nat_bin_ops.insert(nat_ble, NatOp::Ble);
        nat_bin_ops.insert(nat_land, NatOp::Land);
        nat_bin_ops.insert(nat_lor, NatOp::Lor);
        nat_bin_ops.insert(nat_xor, NatOp::Xor);
        nat_bin_ops.insert(nat_shift_left, NatOp::ShiftLeft);
        nat_bin_ops.insert(nat_shift_right, NatOp::ShiftRight);
        nat_bin_ops.insert(nat_pow, NatOp::Pow);

        MetaCtx {
            view,
            scratch,
            cfg,
            mctx: MetavarContext::new(),
            lctx: LocalContext::default(),
            fvar_gen: FVarIdGen::default(),
            guard: RecGuard::new(),
            guard_depth: 0,
            steps: 0,
            step_budget: DEFAULT_STEP_BUDGET,
            whnf_cache: HashMap::new(),
            whnf_core_cache: HashMap::new(),
            infer_cache: HashMap::new(),
            reducibility,
            matchers,
            smart_unfolding: true,
            can_unfold_override: false,
            nat_bin_ops,
            nat_succ,
            nat_zero,
            bool_true,
            bool_false,
            acc_rec,
            wf_rec,
            sunfold_match,
            sunfold_match_alt,
        }
    }

    pub fn cfg(&self) -> Config {
        self.cfg
    }

    pub fn set_transparency(&mut self, t: TransparencyMode) {
        self.cfg.transparency = t;
    }

    pub fn mctx(&self) -> &MetavarContext {
        &self.mctx
    }

    pub fn mctx_mut(&mut self) -> &mut MetavarContext {
        &mut self.mctx
    }

    pub fn status_of(&self, n: NameId) -> ReducibilityStatus {
        // Absent => Semireducible (getReducibilityStatusCore's
        // fallback; plan-1 Global Constraint).
        self.reducibility
            .get(&n)
            .copied()
            .unwrap_or(ReducibilityStatus::Semireducible)
    }

    pub fn matcher_of(&self, n: NameId) -> Option<&MatcherEntry> {
        self.matchers.get(&n)
    }

    /// One deterministic step. Every whnf_core / whnf / infer entry
    /// calls this once; exhaustion is a distinct error, never a
    /// verdict (spec § Error handling).
    pub(crate) fn step(&mut self) -> Result<(), MetaError> {
        self.steps += 1;
        if self.steps > self.step_budget {
            return Err(MetaError::StepBudgetExhausted);
        }
        Ok(())
    }

    /// Depth guard + stack growth, the tc.rs `guarded` idiom.
    pub(crate) fn guarded<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<R, MetaError>,
    ) -> Result<R, MetaError> {
        if self.guard_depth >= MAX_REC_DEPTH {
            return Err(MetaError::DepthBudgetExhausted);
        }
        self.guard_depth += 1;
        let r = stacker::maybe_grow(RED_ZONE, STACK_CHUNK, || f(self));
        self.guard_depth -= 1;
        r
    }

    // -- ExprId-native traversal helpers (tc.rs idiom) --

    pub(crate) fn node(&self, e: ExprId) -> Node {
        self.scratch.expr_node(Some(self.view.store), e)
    }

    pub(crate) fn data(&self, e: ExprId) -> ExprData {
        self.scratch.expr_data(Some(self.view.store), e)
    }

    pub(crate) fn get_app_fn(&self, e: ExprId) -> ExprId {
        let mut cur = e;
        while let Node::App { f, .. } = self.node(cur) {
            cur = f;
        }
        cur
    }

    pub(crate) fn get_app_args(&self, e: ExprId) -> Vec<ExprId> {
        let mut args = Vec::new();
        let mut cur = e;
        while let Node::App { f, arg } = self.node(cur) {
            args.push(arg);
            cur = f;
        }
        args.reverse();
        args
    }

    /// `infer.rs` always needs the full argument spine (`get_app_args`),
    /// never just its length; `whnf.rs`'s `reduce_nat` (task 5) is this
    /// helper's real consumer (mirroring
    /// `leanr_kernel::tc::TypeChecker::reduce_nat`'s own use of its
    /// twin, tc.rs:2007).
    pub(crate) fn get_app_num_args(&self, e: ExprId) -> usize {
        let mut n = 0;
        let mut cur = e;
        while let Node::App { f, .. } = self.node(cur) {
            n += 1;
            cur = f;
        }
        n
    }

    pub(crate) fn mk_app_spine(&mut self, f: ExprId, args: &[ExprId]) -> Result<ExprId, MetaError> {
        let mut r = f;
        for &a in args {
            r = self.scratch.expr_app(Some(self.view.store), r, a)?;
        }
        Ok(r)
    }

    /// Permanent-cache predicate: closed, mvar-free, no override
    /// predicate active. oracle: useWHNFCache (WHNF.lean:1082-1088)
    /// — "cache only closed terms without expr metavars", plus the
    /// canUnfold? escape. The transient side of the spec's cache
    /// split arrives with defeq (plan 3); until then non-cacheable
    /// terms are simply recomputed, which is correct and slow, never
    /// wrong.
    pub(crate) fn cacheable(&self, e: ExprId) -> bool {
        let d = self.data(e);
        !d.has_fvar() && !d.has_expr_mvar() && !self.can_unfold_override
    }

    /// Test-only budget override, so budget-exhaustion tests don't need
    /// to run `DEFAULT_STEP_BUDGET` steps.
    #[cfg(test)]
    pub(crate) fn set_step_budget(&mut self, n: u64) {
        self.step_budget = n;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::MetaError;

    // Reconcile against schedule.rs:324 — the shape, not the letter:
    // an EnvView over an empty persistent store and no constants.
    fn with_ctx<R>(f: impl FnOnce(&mut MetaCtx) -> R) -> R {
        let base = Store::persistent();
        let mut scratch = Store::scratch();
        let empty = leanr_kernel::CheckedConstants::new(HashMap::new());
        let view = EnvView {
            consts: leanr_kernel::ConstSource::Gated(&empty),
            extra: None,
            quot_initialized: false,
            store: &base,
        };
        let mut ctx = MetaCtx::new(view, &mut scratch, Config::default(), &[], &[]);
        f(&mut ctx)
    }

    #[test]
    fn step_budget_exhausts_as_its_own_error() {
        with_ctx(|ctx| {
            ctx.set_step_budget(2);
            assert!(ctx.step().is_ok());
            assert!(ctx.step().is_ok());
            assert_eq!(ctx.step(), Err(MetaError::StepBudgetExhausted));
        });
    }

    #[test]
    fn status_defaults_to_semireducible() {
        with_ctx(|ctx| {
            let s = ctx.scratch.intern_str(None, "ghost").expect("intern");
            let n = ctx.scratch.name_str(None, None, s).expect("name");
            assert_eq!(ctx.status_of(n), ReducibilityStatus::Semireducible);
        });
    }

    #[test]
    fn app_helpers_roundtrip() {
        with_ctx(|ctx| {
            let s = ctx.scratch.intern_str(None, "f").expect("intern");
            let n = ctx.scratch.name_str(None, None, s).expect("name");
            let f = ctx.scratch.expr_fvar(None, Some(n)).expect("fvar");
            let z = ctx.scratch.level_zero(None).expect("level");
            let a = ctx.scratch.expr_sort(None, z).expect("sort");
            let app = ctx.mk_app_spine(f, &[a, a]).expect("spine");
            assert_eq!(ctx.get_app_fn(app), f);
            assert_eq!(ctx.get_app_args(app), vec![a, a]);
            assert_eq!(ctx.get_app_num_args(app), 2);
        });
    }
}
