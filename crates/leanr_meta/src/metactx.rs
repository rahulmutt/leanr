//! All shared `MetaM` state. Each concern module (`whnf`, `infer`, ...)
//! contributes an `impl MetaCtx` block — inherent impls split across
//! files, direct calls, no dynamic dispatch (spec § MetaCtx).
//!
//! Traversal is ExprId-native over the bank, the `tc.rs` idiom: nodes
//! decode one level at a time via `Store::expr_node`, caches key on
//! ids, and `Store::to_expr` is never called on a hot path.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use leanr_kernel::abstract_fvars;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId, Store};
use leanr_kernel::{
    BinderInfo, ConstantInfo, EnvView, ExprData, FVarIdGen, LocalContext, RecGuard, MAX_REC_DEPTH,
};
use leanr_olean::{
    ClassEntry, DefaultInstanceEntry, EntryScope, InstanceEntry, MatcherEntry, ProjectionFnInfo,
    ReducibilityEntry, ReducibilityStatus,
};

use crate::instances::{ClassTable, InstanceTable};
use crate::local_instance::LocalInstanceStack;
use crate::local_snapshot::LocalCtxSnapshot;
use crate::{Config, LMVarId, LOption, MVarId, MetaError, MetavarContext, TransparencyMode};

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
    /// Task 3 (M4b-2) addition, additive/TCB-neutral: a by-user-name
    /// index parallel to `lctx`'s own decl list, one entry per
    /// `push_local_decl`/`push_let_decl` call (`None` name for an
    /// anonymous binder, kept so the two stay 1:1 in length). Exists
    /// ONLY because `LocalContext`'s `decls`/`index` fields are private
    /// even within `leanr_kernel` (module-private to `local_ctx.rs`) —
    /// the kernel's own public surface is `get(fvar_id)` (by id) and
    /// `save`/`restore` (by count), no by-name scan, and adding one to
    /// `LocalContext` itself would touch the byte-untouched kernel TCB.
    ///
    /// EVERY internal telescope-opening site in this crate
    /// (`infer.rs`'s `infer_forall_body`/`infer_lambda_body`,
    /// `whnf.rs`'s `reduce_matcher_telescope`/`sunfold_go_let`/
    /// `sunfold_go_lam`, `assign.rs`'s `forall_bounded_telescope`,
    /// `defeq.rs`'s `is_def_eq_binding_shallow_body`) mints its
    /// transient fvars via `push_local_decl`/`push_let_decl` and
    /// brackets its OWN caller's checkpoint with `lctx_checkpoint`/
    /// `lctx_restore` (metavariable-local-contexts slice, fix round 1
    /// — before that, these called `self.lctx.mk_local_decl`/
    /// `mk_let_decl` directly and bracketed with the bare
    /// `self.lctx.save`/`restore`, which kept `lctx` itself
    /// self-consistent but left THIS field, and the `lctx_snapshot`
    /// cache below, silently unaware of every such fvar for as long as
    /// it stayed open — reachable from `current_lctx()`, itself
    /// reachable from arbitrarily deep inside `is_def_eq` via
    /// `mk_aux_mvar`'s `constApprox` fallback). So `lctx.decls.len()`
    /// net-changes, across any span bracketed by `lctx_checkpoint`/
    /// `lctx_restore`, ONLY via `push_local_decl`/`push_let_decl` —
    /// which are this field's sole writers too. The two therefore stay
    /// in lockstep EVERYWHERE, not merely at top-level entry points, and
    /// `lctx_restore`'s existing `checkpoint: usize` (already
    /// `lctx.save()`'s own return value) doubles as this field's
    /// truncation point with no second
    /// checkpoint API. See `lctx_lookup_by_name` (the reader) below.
    pub(crate) local_names: Vec<(Option<NameId>, ExprId)>,
    /// The local instances in scope — oracle: `Meta.Context.localInstances`
    /// (`Basic.lean`), stored per metavariable as
    /// `MetavarDecl.localInstances` (`MetavarContext.lean:320`).
    ///
    /// SPARSE, unlike `local_names` above: only a class-typed
    /// declaration produces an entry, so this length is unrelated to
    /// `lctx.save()` and there is no lockstep invariant to assert. See
    /// `local_instance.rs` for the truncation rule.
    pub(crate) local_instances: LocalInstanceStack,
    /// Memoized `LocalCtxSnapshot` of the CURRENT `lctx`/`local_names`,
    /// dropped by every writer of either. `current_lctx` rebuilds it on
    /// demand, so N metavariables minted at one binder depth share one
    /// copy — the difference between one clone per binder scope and one
    /// per metavariable on instance search's hottest path.
    lctx_snapshot: Option<Arc<LocalCtxSnapshot>>,
    pub(crate) fvar_gen: FVarIdGen,
    pub(crate) guard: RecGuard,
    guard_depth: u32,
    /// oracle: `Context.synthPendingDepth` (`Meta/Basic.lean:502`) — a
    /// counter DISTINCT from `guard_depth` above: the general recursion
    /// guard bounds total `MetaM` call-stack depth (`withIncRecDepth`),
    /// while this one bounds only NESTED `synthPending` invocations
    /// specifically (`withIncSynthPending`, `Meta/Basic.lean:1177`),
    /// against the much tighter `maxSynthPendingDepth` option (default
    /// `1`, `Meta/Basic.lean:458-461` — this crate has no options table,
    /// so the default is restated as `whnf.rs`'s own
    /// `MAX_SYNTH_PENDING_DEPTH` constant). See `whnf.rs::synth_pending`
    /// (task B6) for the increment/check/decrement span.
    pub(crate) synth_pending_depth: u32,
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
    /// Postponed level-equality constraints (`?u`-bearing `max`/`imax`
    /// shapes neither decidable nor refutable yet). oracle: `getPostponed`
    /// / `postponeIsLevelDefEq` (LevelDefEq.lean:87). Drained by
    /// `process_postponed` (task 4) at checkpoint boundaries; part of the
    /// snapshot so a failed trial unification restores it.
    pub(crate) postponed: Vec<(LevelId, LevelId)>,
    /// Permanent defeq cache: mvar-free pairs (`hasExprMVar ||
    /// hasLevelMVar`, oracle's `hasMVar`) under a standard config (no
    /// `canUnfold?` override) — NOT fvar-free; see `cache.rs`'s module
    /// doc for why an fvar-mentioning pair is still safe to cache here
    /// forever. Survives across `is_def_eq` calls. oracle: the
    /// persistent half of the defeq cache (`getDefEqCacheKind`,
    /// ExprDefEq.lean:2238). Wired in by task 8 (`cache.rs`'s
    /// `defeq_cache_kind`/`cache_lookup`/`cache_store`, consulted from
    /// `defeq.rs::is_def_eq_core`'s cache seam).
    pub(crate) defeq_cache_perm: HashMap<(u64, ExprId, ExprId), bool>,
    /// Transient defeq cache: everything else. Cleared at every
    /// `checkpoint` (oracle: `modifyDefEqTransientCache fun _ => {}` in
    /// `checkpointDefEq`, Basic.lean:2446) — unsafe to keep across calls
    /// because the result depends on mctx state and config.
    pub(crate) defeq_cache_transient: HashMap<(u64, ExprId, ExprId), bool>,
    /// ReducibilityStatus per constant; absent => Semireducible.
    reducibility: HashMap<NameId, ReducibilityStatus>,
    matchers: HashMap<NameId, MatcherEntry>,
    /// The instance table (Task B3): a discrimination tree over decoded
    /// `instanceExtension` entries plus the flat `defaultInstanceExtension`
    /// list, built once here and queried per-goal by
    /// `instances.rs::{get_instances,default_instances,instance_named}`.
    /// `pub(crate)` (unlike `reducibility`/`matchers` just above, which
    /// stay module-private behind `status_of`/`matcher_of` accessors)
    /// because its own consumer methods live in a SEPARATE file
    /// (`instances.rs`, the `discr_path.rs`/`whnf.rs` cross-module
    /// `impl MetaCtx` idiom), which needs direct field access the way
    /// `self.cfg`/`self.mctx` already get it.
    pub(crate) instances: InstanceTable,
    /// Decoded `Lean.classExtension` state (M4b-3 P2b-i task 4) — see
    /// [`crate::instances::ClassTable`]'s own doc for the oracle
    /// citation. Read by [`MetaCtx::get_out_param_positions`],
    /// [`MetaCtx::get_out_level_param_positions`] and
    /// [`MetaCtx::has_out_params`]; consulted from `synth.rs`'s
    /// `preprocess` and `preprocess_out_param`, the real consumers
    /// landed by M4b-3 P2b-i tasks 5-7.
    pub(crate) classes: ClassTable,
    /// The `@[coe_decl]` name set (`Meta/Coe.lean:21-29`), built once
    /// from `EnvExtensions::coe_decls`. Read by `coe.rs::expand_coe`.
    pub(crate) coe_decls: HashSet<NameId>,
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
    /// Monotone counter backing `level.rs`'s `fresh_level_mvar` (oracle:
    /// `mkFreshLevelMVar`, Basic.lean:861-863) — this crate's own
    /// name-generator stand-in, mirroring `FVarIdGen`'s "fixed prefix +
    /// counter" idiom (`local_ctx.rs::fresh_fvar_id`) rather than
    /// reusing that type directly (a level mvar name is not an fvar
    /// name, and the two counters must not collide on the same prefix).
    pub(crate) level_mvar_gen: u64,
    /// Monotone counter backing `assign.rs`'s `mk_aux_mvar` (oracle:
    /// `mkAuxMVar`, `ExprDefEq.lean` — `constApprox`'s `isDefEqMVarSelf`
    /// fallback fresh-EXPR-mvar mint, task 7). Mirrors `level_mvar_gen`'s
    /// own "fixed prefix + counter" idiom, distinct from both it and
    /// `FVarIdGen` (an expr-mvar name must not collide with either a
    /// level-mvar or an fvar name).
    pub(crate) expr_mvar_gen: u64,
    /// Decoded `Lean.projectionFnInfoExt` entries (task B6), keyed by
    /// the projection function's own name — oracle `getProjectionFnInfo?`
    /// (`ProjFns.lean:37-59`, a plain `NameMap` point lookup). Consulted
    /// by `whnf.rs`'s `get_stuck_mvar`'s `Const` arm and
    /// `unfold_proj_inst_when_instances`, both task B6's own seams. Point
    /// lookup only (never iterated in an order-significant way — Global
    /// Constraints: no `HashMap` iteration on order-significant paths).
    pub(crate) projection_fns: HashMap<NameId, ProjectionFnInfo>,
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

/// The decoded environment-extension entries `MetaCtx` reads, grouped so
/// adding one is a field rather than a positional parameter across every
/// call site. Introduced by M4b-3 P2b-i, whose `ClassTable` is the sixth
/// such table and whose successor (M4b-3 P4's `coe_decl`) is the
/// seventh; before this the constructor took five bare slices.
///
/// `Default` gives all-empty slices, so a caller that needs only one
/// table writes `EnvExtensions { instances: &insts, ..Default::default() }`.
#[derive(Default, Clone, Copy)]
pub struct EnvExtensions<'a> {
    pub reducibility: &'a [ReducibilityEntry],
    pub matchers: &'a [MatcherEntry],
    pub instances: &'a [InstanceEntry],
    pub default_instances: &'a [DefaultInstanceEntry],
    pub projection_fns: &'a [ProjectionFnInfo],
    /// Decoded `Lean.classExtension` entries (M4b-3 P2b-i task 4) — see
    /// [`crate::instances::ClassTable`] for how `MetaCtx::new` consumes
    /// this slice.
    pub classes: &'a [ClassEntry],
    /// Decoded `Lean.Meta.coeDeclAttr` entries (M4b-3 P4 task 2) — the
    /// `@[coe_decl]` name set `MetaCtx::is_coe_decl` answers from.
    pub coe_decls: &'a [NameId],
}

impl<'e> MetaCtx<'e> {
    /// Task B6 added the 8th (`projection_fn_entries`) decoded-slice
    /// parameter, crossing clippy's default `too_many_arguments`
    /// threshold (7) — same "decoded slices in, private fields out"
    /// constructor shape B3's `instance_entries`/`default_instance_entries`
    /// pair already established (this module's own doc, above).
    ///
    /// M4b-3 P2b-i task 3 fulfilled the follow-up flagged then (opus
    /// review round 1): the decoded slices are grouped into the
    /// `EnvExtensions` struct above (one field per table) instead of
    /// widening this positional list further, so a caller now passes one
    /// `exts: EnvExtensions` argument and a future decoded extension is a
    /// new field there, not a new parameter here. See that struct's own
    /// doc for the rationale.
    pub fn new(
        view: EnvView<'e>,
        scratch: &'e mut Store,
        cfg: Config,
        exts: EnvExtensions<'_>,
    ) -> MetaCtx<'e> {
        // Global entries only: scoped reducibility entries require the
        // M3b3-style activation model, out of scope for the meta core
        // (they are rare and Mathlib's are decoded but unconsulted
        // here; revisit when a corpus divergence implicates one).
        let reducibility = exts
            .reducibility
            .iter()
            .filter(|e| matches!(e.scope, EntryScope::Global))
            .map(|e| (e.name, e.status))
            .collect();
        let matchers = exts.matchers.iter().map(|m| (m.name, m.clone())).collect();
        let instances = InstanceTable::build(view, exts.instances, exts.default_instances);
        let classes = ClassTable::build(exts.classes);
        let coe_decls: HashSet<NameId> = exts.coe_decls.iter().copied().collect();
        // oracle: `projectionFnInfoExt`'s own `NameMap` (`ProjFns.lean:30,
        // 37-59`) — the extension's own key IS `ProjectionFnInfo.projFn`
        // (see that struct's doc, `leanr_olean::ProjectionFnInfo`), so no
        // filtering/dedup decision is needed here beyond keying by it;
        // a real `.olean` never registers the same projection fn name
        // twice (`mkMapDeclarationExtension`'s own map semantics), so a
        // colliding second entry (last-write-wins) is reachable only via
        // adversarial/malformed bytes, same untrusted-input posture as
        // every other decoder in this crate (never panics either way).
        let projection_fns = exts
            .projection_fns
            .iter()
            .map(|p| (p.proj_fn, p.clone()))
            .collect();

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
            local_names: Vec::new(),
            local_instances: LocalInstanceStack::default(),
            lctx_snapshot: None,
            fvar_gen: FVarIdGen::default(),
            guard: RecGuard::new(),
            guard_depth: 0,
            synth_pending_depth: 0,
            steps: 0,
            step_budget: DEFAULT_STEP_BUDGET,
            whnf_cache: HashMap::new(),
            whnf_core_cache: HashMap::new(),
            infer_cache: HashMap::new(),
            postponed: Vec::new(),
            defeq_cache_perm: HashMap::new(),
            defeq_cache_transient: HashMap::new(),
            reducibility,
            matchers,
            instances,
            classes,
            coe_decls,
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
            level_mvar_gen: 0,
            expr_mvar_gen: 0,
            projection_fns,
        }
    }

    pub fn cfg(&self) -> Config {
        self.cfg
    }

    pub fn set_transparency(&mut self, t: TransparencyMode) {
        self.cfg.transparency = t;
    }

    /// oracle: `withTransparency` as `withDefault` / `withReducible` /
    /// `withReducibleAndInstances` use it (`Basic.lean:1278-1292`) —
    /// save, set, run, restore. `pub` so `leanr_elab`'s ladder can run
    /// the `.coe` arm's `withDefault isDefEq` (`SyntheticMVars.lean:546`).
    ///
    /// Plain save/run/restore with no drop guard, the same posture as
    /// `with_assignable_synthetic_opaque` below and for the same reason
    /// (its doc, design spec § Follow-ups item 4): every caller is
    /// `Result`-based and catches nothing, so an unwinding caller cannot
    /// observe the un-restored flag.
    pub fn with_transparency<R>(
        &mut self,
        t: TransparencyMode,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let saved = self.cfg.transparency;
        self.cfg.transparency = t;
        let r = f(self);
        self.cfg.transparency = saved;
        r
    }

    /// oracle: `mkArrow` (`Lean/Meta/Basic.lean`, `mkForall _ .default d b`
    /// with a fresh user name) — a NON-dependent `forallE`. The binder
    /// name is `None`: the only consumer is the TYPE of `coerceToFunction?`'s
    /// `?γ` (`Coe.lean:105`), which is never emitted, and the canonical
    /// encoder erases binder names anyway.
    ///
    pub(crate) fn mk_arrow(&mut self, dom: ExprId, cod: ExprId) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        Ok(self
            .scratch
            .expr_forall(base, None, dom, cod, BinderInfo::Default)?)
    }

    pub fn mctx(&self) -> &MetavarContext {
        &self.mctx
    }

    pub fn mctx_mut(&mut self) -> &mut MetavarContext {
        &mut self.mctx
    }

    /// The `scratch` term/level bank this `MetaCtx` was constructed
    /// with — the same store every internal `whnf`/`infer`/`is_def_eq`
    /// call already interns new nodes into via `self.scratch` directly.
    /// **M4b-1 addition**: a term ELABORATOR (`leanr_elab`, layered on
    /// top of this crate) has to construct brand-new `Expr` nodes
    /// *during* elaboration — e.g. `Store::expr_lit_str` for a string
    /// literal — while it (necessarily) also holds a live `MetaCtx` for
    /// the same query, so it needs the identical capability this
    /// module's own free functions (`mk_name1`/`mk_name2` above) have
    /// always had from *inside* the crate. Before this there was no
    /// external accessor at all — `scratch` is `pub(crate)` — which
    /// made `leanr_elab`'s leaf elaborators (M4b-1 Task 4) literally
    /// unimplementable: there is no id-translation between two
    /// independent `Store`s (`ExprId` is only meaningful relative to
    /// the exact `Store` that produced it), so a caller cannot work
    /// around this with a Store of its own. Read-only/mutable pair
    /// mirrors the existing `mctx()`/`mctx_mut()` precedent immediately
    /// above, and `leanr_kernel::Environment::store()`/`store_mut()`'s
    /// own public-accessor precedent for the persistent side.
    pub fn store(&self) -> &Store {
        self.scratch
    }

    /// See `store`'s doc comment.
    pub fn store_mut(&mut self) -> &mut Store {
        self.scratch
    }

    /// The ambient local context as a shareable value — what a freshly
    /// minted metavariable records (oracle: `mkFreshExprMVarCore`'s
    /// `(← getLCtx)`, `Meta/Basic.lean:866-867`).
    pub fn current_lctx(&mut self) -> Arc<LocalCtxSnapshot> {
        if let Some(snap) = &self.lctx_snapshot {
            return Arc::clone(snap);
        }
        let snap = Arc::new(LocalCtxSnapshot::new(
            self.lctx.clone(),
            self.local_names.clone(),
            self.local_instances.to_vec(),
        ));
        self.lctx_snapshot = Some(Arc::clone(&snap));
        snap
    }

    /// The local context a metavariable was minted in, if it is declared.
    pub fn mvar_lctx(&self, mvar_id: MVarId) -> Option<Arc<LocalCtxSnapshot>> {
        self.mctx.decl(mvar_id).map(|d| Arc::clone(&d.lctx))
    }

    /// Install `snapshot` as the ambient local context, returning the one
    /// it replaced. `lctx` and `local_names` swap together, because they
    /// are asserted to stay in lockstep at every checkpoint, restore and
    /// push — including the ones the caller performs while the snapshot
    /// is installed. `local_instances` swaps along with them (Task 5):
    /// the oracle's `withLocalContextImp` (`Basic.lean:2002-2004`)
    /// installs `lctx` and `localInstances` together in one
    /// `withReader`, and leaving the instance stack behind would let a
    /// metavariable's own context see a different instance set than the
    /// one it was minted under. The cache is set to the installed
    /// snapshot so a metavariable minted while it is in force records the
    /// installed context without a fresh copy.
    ///
    /// Callers must pair the two calls. `with_mvar_context` is the safe
    /// wrapper and is what in-crate code should use; `install_lctx` is
    /// `pub` only because `leanr_elab`'s ladder needs the closure to own
    /// the whole elaborator, not just `MetaCtx`.
    pub fn install_lctx(&mut self, snapshot: Arc<LocalCtxSnapshot>) -> Arc<LocalCtxSnapshot> {
        let previous = self.current_lctx();
        let (lctx, names, instances) = snapshot.parts();
        self.lctx = lctx.clone();
        self.local_names = names.to_vec();
        self.local_instances.replace(instances.to_vec());
        debug_assert_eq!(
            self.local_names.len(),
            self.lctx.save(),
            "local_names/lctx lockstep invariant violated"
        );
        self.lctx_snapshot = Some(snapshot);
        previous
    }

    /// oracle: `MVarId.withContext` / `withMVarContextImp`
    /// (`Meta/Basic.lean:2043-2052`) — `withLocalContextImp mvarDecl.lctx
    /// mvarDecl.localInstances x`. Runs `f` with the metavariable's own
    /// local context installed as the ambient one, and restores the
    /// caller's on the way out.
    ///
    /// `localInstances` travels inside the snapshot (`local_snapshot.rs`),
    /// so this reinstalls the metavariable's instances along with its
    /// declarations — the oracle's `withLocalContextImp` swaps both in
    /// one `withReader` (`Basic.lean:2002-2004`).
    ///
    /// The oracle does NOT flush a synthesis cache here, and neither does
    /// leanr: `withLocalContextImp` is a plain reader swap with no flush
    /// in it, and leanr has no synthesis cache at all yet (the M4b-3 spec
    /// assigns one to "the slice that builds the synthesis cache").
    ///
    /// **Why there is no flush, and what the slice that builds the cache
    /// must do instead.** The oracle needs none because its cache is
    /// KEYED by the local instances: `SynthInstanceCacheKey`
    /// (`Basic.lean:328-336`) is `localInsts : LocalInstances`
    /// (`:329`) + `type` (`:330`) + `synthPendingDepth` (`:335`), so a
    /// lookup under a different `LocalInstances` simply misses. A leanr
    /// synthesis cache must key by the local instances the same way;
    /// caching by goal type alone would return an answer synthesized
    /// under a different instance set, which is wrong under a binder,
    /// and this reader swap is exactly where the two sets differ.
    /// Do not read "no flush to port" as "nothing to do".
    ///
    /// `MVarId.withContext`'s own docstring (`:2047-2050`) appears to
    /// say the opposite — "The type class resolution cache is flushed
    /// when executing `x` if its `LocalInstances` are different from
    /// the current ones". It describes the EFFECT, not the mechanism:
    /// `withMVarContextImp` (`:2043-2045`) is `withLocalContextImp
    /// mvarDecl.lctx mvarDecl.localInstances x`, `withLocalContextImp`
    /// (`:2002-2004`) is a bare `withReader`, and nothing on that path
    /// touches the cache — the "flush" is the key miss described above.
    /// Recorded so a future reader who goes to check that sentence
    /// finds the resolution here rather than an apparent contradiction,
    /// and does not port a flush that does not exist.
    ///
    /// Plain save/run/restore with no drop guard, the same posture (and
    /// the same justification) as `with_transparency` and
    /// `with_assignable_synthetic_opaque`: every caller is `Result`-based
    /// and catches nothing, so an unwinding caller cannot observe the
    /// un-restored context.
    ///
    /// An UNDECLARED metavariable leaves the ambient context alone and
    /// runs `f` as-is: the oracle's `getDecl` would throw, but every
    /// leanr caller reaches this with an id it has just read a
    /// declaration for, and inventing an error variant for an
    /// unreachable case is surface without a producer.
    pub fn with_mvar_context<R>(&mut self, mvar_id: MVarId, f: impl FnOnce(&mut Self) -> R) -> R {
        let Some(snapshot) = self.mvar_lctx(mvar_id) else {
            return f(self);
        };
        let saved = self.install_lctx(snapshot);
        let out = f(self);
        self.install_lctx(saved);
        out
    }

    /// Record the current `lctx` depth. Pair with `lctx_restore` to bracket
    /// a telescope (the `flet<local_ctx> save_lctx` idiom, assign.rs:563).
    /// Additive + behavior-neutral.
    pub fn lctx_checkpoint(&mut self) -> usize {
        debug_assert_eq!(
            self.local_names.len(),
            self.lctx.save(),
            "local_names/lctx lockstep invariant violated"
        );
        self.lctx.save()
    }

    /// Restore `lctx` to a `lctx_checkpoint` depth, dropping every decl
    /// added since (fvar ids are globally unique via `fvar_gen`, so the
    /// truncation is exact). Also truncates `local_names` to the same
    /// point (Task 3 addition — see that field's own doc comment for why
    /// the single `checkpoint` value is valid for both).
    pub fn lctx_restore(&mut self, checkpoint: usize) {
        debug_assert_eq!(
            self.local_names.len(),
            self.lctx.save(),
            "local_names/lctx lockstep invariant violated"
        );
        self.lctx.restore(checkpoint);
        self.local_names.truncate(checkpoint);
        // Sparse, so truncated by RECORDED DEPTH rather than by index —
        // see `local_instance.rs`'s module doc.
        self.local_instances.truncate_to(checkpoint);
        self.lctx_snapshot = None;
    }

    /// The mint-and-push half shared by `push_local_decl` and
    /// `push_local_decl_without_instance` below — everything EXCEPT the
    /// local-instance install, which the two callers do at different
    /// times. Returns `(fvar, depth)`; `depth` is this declaration's own
    /// index in `lctx.decls`, read BEFORE the push (see
    /// `local_instance.rs` for why the stack truncates by depth rather
    /// than by index) — a caller that defers the install needs it too
    /// (`install_local_instance_for_last_pushed` re-derives the same
    /// value from `lctx.save()` afterward, since nothing else may push
    /// in between).
    fn push_local_decl_inner(
        &mut self,
        name: Option<NameId>,
        ty: ExprId,
        bi: BinderInfo,
    ) -> Result<(ExprId, usize), MetaError> {
        debug_assert_eq!(
            self.local_names.len(),
            self.lctx.save(),
            "local_names/lctx lockstep invariant violated"
        );
        let depth = self.lctx.save();
        let fvar = self.lctx.mk_local_decl(
            self.scratch,
            Some(self.view.store),
            &mut self.fvar_gen,
            name,
            ty,
            bi,
        )?;
        // Task 3 addition: record `(name, fvar)` in `local_names` too —
        // see that field's own doc comment. One entry per call, matching
        // `lctx.decls`'s own growth exactly (including `None` names).
        self.local_names.push((name, fvar));
        Ok((fvar, depth))
    }

    /// Mint a cdecl fvar `(name : ty)` with binder-info `bi` into the ambient
    /// `lctx` and return its `Expr::fvar`. The additive elab-layer seam for
    /// `mk_local_decl`, already used internally at assign.rs:633. The caller
    /// brackets with `lctx_checkpoint`/`lctx_restore`. The invariant (checked
    /// via debug_assert) is safe because `leanr_meta` internal code never
    /// re-enters the elab layer, so no internal `mk_local_decl` decl is ever
    /// transiently present in `lctx` at a `checkpoint`/`restore` boundary.
    pub fn push_local_decl(
        &mut self,
        name: Option<NameId>,
        ty: ExprId,
        bi: BinderInfo,
    ) -> Result<ExprId, MetaError> {
        let (fvar, depth) = self.push_local_decl_inner(name, ty, bi)?;
        // oracle: `withLocalDeclImp` → `withNewFVar`
        // (`Basic.lean:1791`, `:1785-1789`) — a class-typed declaration
        // becomes a local instance. Keyed on the TYPE only; binder info
        // plays no part, so `fun (inst : Add N) => …` counts exactly as
        // `[inst : Add N]` does.
        self.install_local_instance_for(fvar, ty, depth)?;
        self.lctx_snapshot = None;
        Ok(fvar)
    }

    /// The mint-and-push half of `push_local_decl`, WITHOUT the
    /// automatic local-instance install that normally follows
    /// immediately — paired with `install_local_instance_for_last_pushed`
    /// below. Exists for a caller that must refine `ty` (e.g. an
    /// `isDefEq` mvar assignment) AFTER the fvar already exists but
    /// BEFORE the class check runs, matching the oracle's own ordering
    /// in `elabFunBinderViews`: mint the fvar, run
    /// `propagateExpectedType`, THEN test `isClass? type`
    /// (`Lean/Elab/Binders.lean:429-444`) — `push_local_decl`'s own
    /// ordering (class-check immediately, before any later refinement)
    /// only diverges from that for a `fun` binder whose domain is an
    /// ELIDED (fresh-mvar) type that `propagateExpectedType` then
    /// assigns to a class (M4b-3 P5 task 4's own finding).
    ///
    /// Every OTHER `push_local_decl` caller (`forall`/`depArrow`/
    /// `let`/`have`) has its domain fully elaborated BEFORE the push —
    /// nothing refines it afterward — so this split changes nothing for
    /// them and they keep calling `push_local_decl` unchanged.
    /// Additive + behavior-neutral: `push_local_decl` itself still does
    /// mint-and-install in one call via the same shared
    /// `push_local_decl_inner`, byte-for-byte the same sequence of
    /// operations as before this split.
    pub fn push_local_decl_without_instance(
        &mut self,
        name: Option<NameId>,
        ty: ExprId,
        bi: BinderInfo,
    ) -> Result<ExprId, MetaError> {
        let (fvar, _depth) = self.push_local_decl_inner(name, ty, bi)?;
        self.lctx_snapshot = None;
        Ok(fvar)
    }

    /// The install half `push_local_decl_without_instance` defers — see
    /// that method's own doc. `fvar` must be the MOST RECENTLY pushed
    /// local decl (no intervening `push_local_decl`/`push_let_decl`/
    /// `push_local_decl_without_instance` call), checked via
    /// `debug_assert` against `local_names`' own tail — the same
    /// lockstep invariant `push_local_decl_inner` itself asserts on
    /// entry. `ty` is read fresh from the caller rather than
    /// re-derived from `lctx`, so a caller that assigned an mvar via
    /// `is_def_eq` in between (M4b-3 P5 task 4's own use) sees that
    /// assignment: `is_class` (`Basic.lean:1358-1381` port) reduces
    /// through it via `is_class_expensive`'s whnf fallback.
    ///
    /// **Fix round 2**: this used to return without dropping
    /// `lctx_snapshot`, leaving the memo stale across the very window
    /// this method exists to close — anything between the push and this
    /// call that repopulates the cache (`with_mvar_context`'s own
    /// `install_lctx`, reachable from `propagate_expected_type` through
    /// `whnf.rs`'s pending-instance-mvar path or `assign.rs`'s
    /// `mk_aux_mvar_for` rescue) left a snapshot missing the
    /// just-installed instance in force for every mvar minted
    /// afterward, silently. The drop now lives inside
    /// `install_local_instance_for` itself (this method's own callee),
    /// so it is no longer this method's job to remember — see that
    /// method's doc for why the fix sits there instead of here.
    pub fn install_local_instance_for_last_pushed(
        &mut self,
        fvar: ExprId,
        ty: ExprId,
    ) -> Result<(), MetaError> {
        debug_assert_eq!(
            self.local_names.last().map(|(_, f)| *f),
            Some(fvar),
            "fvar must be the most recently pushed local decl"
        );
        let depth = self.lctx.save().saturating_sub(1);
        self.install_local_instance_for(fvar, ty, depth)
    }

    /// Mint an ldecl fvar `(name : ty := value)` into the ambient `lctx`
    /// and return its `Expr::fvar` — the let twin of `push_local_decl`,
    /// wrapping the kernel's existing `LocalContext::mk_let_decl` (the
    /// ldecl overload, local_ctx.rs:128). Oracle: `withLetDecl`'s
    /// declaration half. The caller brackets with `lctx_checkpoint`/
    /// `lctx_restore`. Additive + behavior-neutral: no new state, no
    /// existing path changed.
    pub fn push_let_decl(
        &mut self,
        name: Option<NameId>,
        ty: ExprId,
        value: ExprId,
    ) -> Result<ExprId, MetaError> {
        debug_assert_eq!(
            self.local_names.len(),
            self.lctx.save(),
            "local_names/lctx lockstep invariant violated"
        );
        // Read BEFORE the push below — see `push_local_decl`'s own
        // `depth` comment.
        let depth = self.lctx.save();
        let fvar = self.lctx.mk_let_decl(
            self.scratch,
            Some(self.view.store),
            &mut self.fvar_gen,
            name,
            ty,
            value,
        )?;
        // Same `local_names` bookkeeping as `push_local_decl`: one entry
        // per call, matching `lctx.decls`'s own growth exactly, so a body
        // occurrence of the binder name resolves via
        // `lctx_lookup_by_name`.
        self.local_names.push((name, fvar));
        // oracle: `withLetDeclImp` (`Basic.lean:1905-1911`) routes
        // through the same `withNewFVar` as `push_local_decl` — a
        // let-bound instance counts too.
        self.install_local_instance_for(fvar, ty, depth)?;
        self.lctx_snapshot = None;
        Ok(fvar)
    }

    /// Install `fvar` as a local instance if its type is a class.
    ///
    /// oracle: `withNewFVar` (`Basic.lean:1785-1789`). The oracle's
    /// implementation-detail filter (`withNewLocalInstanceImp`,
    /// `:1383-1388`) is **vacuously satisfied** here: leanr's
    /// `LocalDecl` (`leanr_kernel/src/local_ctx.rs:37-43`) carries no
    /// kind field, and nothing in leanr mints an implementation-detail
    /// declaration, so there is nothing to filter. Adding a field to a
    /// kernel struct for a producer that does not exist would widen the
    /// TCB for nothing. SEAM — trigger for revisiting: the slice that
    /// builds the tactic framework or the match compiler is the first to
    /// mint one, and it must add the filter in the same change.
    ///
    /// **`lctx_snapshot` correctness (fix round 2)**: this is the ONE
    /// place that ever writes `local_instances`, so the memo-drop that
    /// invariant needs (`lctx_snapshot`'s own doc: "dropped by every
    /// writer of either [`lctx` or `local_instances`]") lives HERE,
    /// unconditionally, rather than at each of this method's callers.
    /// Round 1 put it at two of the three call sites
    /// (`push_local_decl`, `push_let_decl`) and missed the third
    /// (`install_local_instance_for_last_pushed`) — a caller-side
    /// convention that is easy to forget exactly because nothing
    /// enforces it. Folding the drop in here makes it structural: ANY
    /// future caller of this method gets it for free, and it fires even
    /// on the `is_class? = none` branch (a no-op clear is always safe;
    /// a missed one on the ELSE branch — reachable whenever `is_class`
    /// itself repopulates the cache internally via its own reduction —
    /// would reopen the same hole for a class-typed `ty` that answers
    /// `none`). The two callers below keep their own EXPLICIT clears
    /// too, since `push_local_decl_inner`'s mint-and-push half is
    /// ALSO independently a writer of `lctx`/`local_names` and would
    /// need one regardless of this method ever running — harmless
    /// double-clearing, not load-bearing duplication.
    fn install_local_instance_for(
        &mut self,
        fvar: ExprId,
        ty: ExprId,
        depth: usize,
    ) -> Result<(), MetaError> {
        if let Some(class_name) = self.is_class(ty)? {
            self.local_instances.push(class_name, fvar, depth);
        }
        self.lctx_snapshot = None;
        Ok(())
    }

    /// Look up `name` in the ambient local context, most-recently-pushed
    /// first (a later same-named binder shadows an earlier one — ordinary
    /// lexical shadowing; oracle: `LocalContext.findFromUserName?` scans
    /// from the innermost decl outward). Returns the SAME `ExprId`
    /// `push_local_decl` returned for that binder (an `Expr::fvar`
    /// referencing `lctx`'s own decl — `mk_forall`/`abstract_fvars`
    /// recognize it identically, since `local_names` never stores
    /// anything but a verbatim copy of a `push_local_decl` return value).
    /// `None` on a miss (including an empty `lctx`) — the caller falls
    /// back to global-constant resolution exactly as before this field
    /// existed, so this is a pure no-op for any query that never enters a
    /// binder (`local_names` stays empty, `None` unconditionally).
    pub fn lctx_lookup_by_name(&self, name: NameId) -> Option<ExprId> {
        self.local_names
            .iter()
            .rev()
            .find(|(n, _)| *n == Some(name))
            .map(|(_, fvar)| *fvar)
    }

    /// Shared telescope-abstraction loop backing `mk_forall`/`mk_lambda`
    /// (oracles `mkForallFVars`/`mkLambdaFVars`, the cdecl case). Abstracts
    /// `body` over the telescope `fvars` (each an fvar declared in
    /// `self.lctx`, no let value in this plan) and wraps in nested
    /// `forallE`/`lam` (per `is_lambda`), innermost fvar last. Transcribed
    /// from `infer.rs::rebuild_forall`'s `None`-value branch (infer.rs:802),
    /// the crate's own oracle-verified abstraction loop, since the kernel's
    /// `mk_pi`/`mk_lambda` are not re-exported from `leanr_kernel`.
    ///
    /// # `MkBinding.elimMVarDeps`
    ///
    /// The oracle's `mkBinding` is not a bare abstraction. Before it
    /// abstracts, it runs `elimMVarDeps` (`MetavarContext.lean`) over
    /// `body`: an unassigned metavariable whose own local context
    /// contains the fvars being abstracted is replaced by a fresh
    /// metavariable APPLIED to them — delayed-assigned when the original
    /// is `syntheticOpaque`, plainly assigned otherwise — so the
    /// occurrence abstracts like any other argument and the original
    /// metavariable stays assignable in its own context.
    ///
    /// This is now modelled: `mk_binding.rs`'s `elim_mvar_deps`, called
    /// twice below at the oracle's own two insertion points. Without it,
    /// a metavariable assigned LATER (the elaborator's synthetic-mvar
    /// fixpoint resuming a postponed goal after the binder has closed)
    /// had its value spliced in with the free variables never
    /// abstracted, so leanr emitted an unabstracted `fvar` where the
    /// oracle emits a `bvar`. That divergence is pinned executably one
    /// crate up by `leanr_elab`'s
    /// `postponed_coe_under_a_binder_abstracts_via_elim_mvar_deps`
    /// (`tests/seam_audit.rs`), which asserted the WRONG answer until
    /// the elimMVarDeps slice landed and asserts the oracle's now.
    fn mk_binding(
        &mut self,
        is_lambda: bool,
        fvars: &[ExprId],
        body: ExprId,
    ) -> Result<ExprId, MetaError> {
        // oracle: `mkBinding` abstracts through `abstractRange`
        // (`MetavarContext.lean:1313`), which runs `elimMVarDeps` over
        // the FULL telescope before abstracting. The peel-one-fvar-at-
        // a-time loop below is leanr's own oracle-verified abstraction
        // (transcribed from `infer.rs::rebuild_forall`), so the
        // insertion points are what change, not the loop.
        let body = self.elim_mvar_deps(fvars, body)?;
        let mut r = body;
        let mut i = fvars.len();
        while i > 0 {
            i -= 1;
            r = abstract_fvars(
                self.scratch,
                Some(self.view.store),
                r,
                std::slice::from_ref(&fvars[i]),
                &mut self.guard,
            )?;
            let (binder_name, ty, binder_info) = match self.node(fvars[i]) {
                Node::FVar { id: Some(id) } => {
                    let decl = self.lctx.get(id).ok_or_else(|| {
                        MetaError::Infer("mk_binding: telescope fvar not declared".into())
                    })?;
                    // The kernel's own rebuild twin (`subst.rs::mk_binding`,
                    // fn at :1020) has a `Some(value)` branch that emits
                    // `expr_let` for an ldecl entry (subst.rs:1038-1040).
                    // This accessor has no such branch — deliberately: it
                    // is `mkForallFVars`/`mkLambdaFVars`'s cdecl-only case
                    // (see this fn's own doc), and a `letI`/`letrec`/mixed
                    // telescope is a later slice's problem, not this one's.
                    // Refuse rather than silently building a `lam`/`forallE`
                    // that drops the ldecl's value on the floor — a wrong
                    // `ExprId`, not a named seam.
                    if decl.value.is_some() {
                        return Err(MetaError::Infer(
                            "mk_binding: let-decl fvar in a cdecl telescope".into(),
                        ));
                    }
                    (decl.binder_name, decl.ty, decl.binder_info)
                }
                _ => {
                    return Err(MetaError::Infer(
                        "mk_binding: telescope entry is not an fvar".into(),
                    ))
                }
            };
            // oracle: `abstractRange xs i type` (`:1320`) — note the
            // FULL `fvars`, not `&fvars[..i]`: a binder type has its
            // metavariable dependencies eliminated with respect to
            // every telescope variable, including ones declared after
            // it. That asymmetry is exactly what `abstract_range`
            // (task 9's port of `abstractRange`) encapsulates, so this
            // calls it rather than inlining its two halves.
            let ty2 = self.abstract_range(fvars, i, ty)?;
            r = if is_lambda {
                self.scratch
                    .expr_lam(Some(self.view.store), binder_name, ty2, r, binder_info)?
            } else {
                self.scratch
                    .expr_forall(Some(self.view.store), binder_name, ty2, r, binder_info)?
            };
        }
        Ok(r)
    }

    /// oracle: `mkForallFVars` (the cdecl case). Abstract `body` over the
    /// telescope `fvars` (each an fvar declared in `self.lctx`, no let
    /// value in this plan) and wrap in nested `forallE`, innermost fvar
    /// last. See `mk_binding` for the shared implementation.
    pub fn mk_forall(&mut self, fvars: &[ExprId], body: ExprId) -> Result<ExprId, MetaError> {
        self.mk_binding(false, fvars, body)
    }

    /// oracle: `mkLambdaFVars` (the cdecl case). Abstract `body` over the
    /// telescope `fvars` (each an fvar declared in `self.lctx`, no let
    /// value in this plan) and wrap in nested `lam`, innermost fvar last.
    /// The `mk_forall` twin — see `mk_binding` for the shared
    /// implementation. Additive + behavior-neutral: exposes capability the
    /// crate already exercises (`expr_lam` + `abstract_fvars`), adds no
    /// state, changes no existing path.
    pub fn mk_lambda(&mut self, fvars: &[ExprId], body: ExprId) -> Result<ExprId, MetaError> {
        self.mk_binding(true, fvars, body)
    }

    /// oracle: `mkLetFVars #[fvar] body (usedLetOnly := false)
    /// (generalizeNondepLet := false)` — abstract `body` over the single
    /// let-bound `fvar` and wrap in `Expr.letE`, carrying `non_dep`
    /// (`false` for `let`, `true` for `have`; design spec § Amendment 2).
    ///
    /// Deliberately NOT a `mk_binding` case: the kernel's own rebuild
    /// path (`subst.rs`'s `mk_binding`, :1020) hardcodes `non_dep =
    /// false` for a rebuilt `LetE`, so it cannot express `have`. Reads
    /// `ty`/`value` off the lctx decl exactly as `mk_binding` reads
    /// `ty`/`binder_info`. Additive + behavior-neutral: exposes
    /// capability the crate already exercises (`expr_let` +
    /// `abstract_fvars`), adds no state, changes no existing path.
    pub fn mk_let_expr(
        &mut self,
        fvar: ExprId,
        body: ExprId,
        non_dep: bool,
    ) -> Result<ExprId, MetaError> {
        let (binder_name, ty, value) = match self.node(fvar) {
            Node::FVar { id: Some(id) } => {
                let decl = self
                    .lctx
                    .get(id)
                    .ok_or_else(|| MetaError::Infer("mk_let_expr: fvar not declared".into()))?;
                let value = decl.value.ok_or_else(|| {
                    MetaError::Infer("mk_let_expr: fvar is not a let-bound decl".into())
                })?;
                (decl.binder_name, decl.ty, value)
            }
            _ => {
                return Err(MetaError::Infer(
                    "mk_let_expr: telescope entry is not an fvar".into(),
                ))
            }
        };
        let body = abstract_fvars(
            self.scratch,
            Some(self.view.store),
            body,
            std::slice::from_ref(&fvar),
            &mut self.guard,
        )?;
        let e =
            self.scratch
                .expr_let(Some(self.view.store), binder_name, ty, value, body, non_dep)?;
        Ok(e)
    }

    /// oracle: `Expr.instantiateBetaRevRange 0 args.size args`
    /// (`Lean/Meta/InferType.lean:37-45`), as used by
    /// `ElabAppArgs.State.getFType` (`Lean/Elab/App.lean:232-237`) to
    /// instantiate a partially-applied function type's loose bvars with the
    /// arguments consumed so far. `args` is OUTERMOST-first, i.e. binder
    /// order — the same convention `leanr_kernel::instantiate_rev`
    /// documents (`subst[len-1]` replaces `#0`, so the LAST element is the
    /// innermost binder's argument).
    ///
    /// The oracle's shape, which this mirrors arm for arm:
    /// ```lean
    /// if e.hasLooseBVars && stop > start then
    ///   if args.any (·.consumeMData.isLambda) start stop then visit e 0 |>.run
    ///   else instantiateRevRange e start stop args
    /// else e
    /// ```
    /// Both short-circuits matter and both are implemented below: a term
    /// with NO loose bvars is returned untouched (no substitution, and in
    /// particular no beta), and when none of `args` is a lambda the
    /// substitution alone is the whole answer — there is no redex a beta
    /// step could fire on. This is not a cost optimization: this function
    /// computes the expected type an argument is elaborated against
    /// (`getParamType` / `getArgExpectedType`), and beta-reducing a term
    /// the oracle leaves alone hands the argument elaborator a DIFFERENT
    /// term.
    ///
    /// **Named limitation — nested redexes are not reduced.** The oracle's
    /// `visit` walks the whole tree and betas any bvar-headed application
    /// it finds; this uses `head_beta`, which fires only at the term's own
    /// head. So for a lambda-carrying `args`, leanr reduces the head redex
    /// the oracle's docstring names (`motive n` with
    /// `motive := fun x => f m = f x` becomes `f m = f n`) but leaves a
    /// redex sitting under a constructor — e.g. `Foo (motive n)` — as
    /// `Foo ((fun x => ..) n)` where the oracle would produce
    /// `Foo (f m = f n)`. The two terms are defeq, so no unification
    /// verdict changes; what can differ is the SHAPE of a type reported in
    /// a message, and any future syntactic test run on the result. This is
    /// the only remaining divergence from the oracle here, it can only ever
    /// UNDER-reduce (never emit a term the oracle would not), and closing
    /// it means porting `visit`'s traversal — which needs a bvar-offset
    /// walk this crate has no other caller for.
    ///
    /// Additive + behavior-neutral, and the reason it lives HERE rather than
    /// in `leanr_elab`: the substitution half (`instantiate_rev`) is public
    /// kernel API the elaborator could call itself, but the beta half
    /// (`head_beta`, `whnf.rs:1767`) is `pub(crate)` to this crate. Exposes
    /// no new capability, adds no state, changes no existing path.
    pub fn instantiate_beta_rev_range(
        &mut self,
        e: ExprId,
        args: &[ExprId],
    ) -> Result<ExprId, MetaError> {
        // oracle: `stop > start` — with `start = 0, stop = args.size`,
        // exactly "`args` is non-empty".
        if args.is_empty() {
            return Ok(e);
        }
        // oracle: `e.hasLooseBVars`. Nothing to substitute AND nothing to
        // beta — the oracle returns `e` itself from the `else` arm.
        if self.data(e).loose_bvar_range() == 0 {
            return Ok(e);
        }
        // oracle: `args.any (·.consumeMData.isLambda) start stop`.
        let any_lambda = args.iter().any(|&a| self.consume_mdata_is_lambda(a));
        let inst = leanr_kernel::instantiate_rev(
            self.scratch,
            Some(self.view.store),
            e,
            args,
            &mut self.guard,
        )?;
        if any_lambda {
            self.head_beta(inst)
        } else {
            // oracle's own comment: "If there are no lambdas, then
            // `instantiateRevRange` suffices."
            Ok(inst)
        }
    }

    /// oracle: `Expr.consumeMData` followed by `Expr.isLambda` — the test
    /// `instantiateBetaRevRange` runs on each substituted argument.
    fn consume_mdata_is_lambda(&self, e: ExprId) -> bool {
        let mut cur = e;
        loop {
            match self.node(cur) {
                Node::MData { expr, .. } => cur = expr,
                Node::Lam { .. } => return true,
                _ => return false,
            }
        }
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

    /// oracle: `processPostponed (mayPostpone := false)`
    /// (`Lean/Meta/LevelDefEq.lean`), reached from
    /// `Lean.Elab.Term.processPostponedUniverseConstraints`
    /// (`SyntheticMVars.lean:409-411`) — the ladder's final step when
    /// `postpone == .no`.
    ///
    /// Additive and behavior-neutral: a thin `pub` forwarder to the
    /// existing `pub(crate)` `level::process_postponed`
    /// (`level.rs:741`), which `defeq.rs:102` already calls on the same
    /// queue. No new logic, no TCB surface — `leanr_elab` simply cannot
    /// reach a `pub(crate)` item from another crate.
    ///
    /// Returns `true` when every postponed constraint was solved.
    /// leanr does NOT model the oracle's `exceptionOnFailure` parameter:
    /// that flag exists to guarantee `throwStuckAtUniverseCnstr`'s
    /// "entries is not empty" precondition, and leanr's caller reports
    /// stuck constraints from the `false` verdict instead of from a
    /// thrown exception (`leanr_elab`'s `synthetic/ladder.rs`,
    /// `process_postponed_universe_constraints`).
    pub fn process_postponed_levels(&mut self) -> Result<bool, MetaError> {
        self.process_postponed()
    }

    /// The number of postponed level constraints. The oracle's
    /// `getNumPostponed` (`Lean/Meta/Basic.lean`), used by
    /// `defeq.rs:173`'s own postponed-count guard and, from P2a on, by
    /// the ladder's checkpoint bookkeeping.
    pub fn postponed_len(&self) -> usize {
        self.postponed.len()
    }

    /// oracle: `getDefaultInstances` (`Lean/Meta/Instances.lean`),
    /// consumed by `synthesizeSomeUsingDefaultPrio`
    /// (`SyntheticMVars.lean:213-221`).
    ///
    /// Additive: a `pub` forwarder to the existing `pub(crate)`
    /// `MetaCtx::default_instances` (`instances.rs:520`). P2a uses it
    /// only to shape-guard the `synthesize_using_default` seam — "are
    /// there default instances that WOULD apply here?" — so that P3 can
    /// replace the seam body without the guard having lied in the
    /// meantime. Each entry is `(instance name, priority)`.
    pub fn default_instances_of(&self, class: NameId) -> Vec<(NameId, usize)> {
        self.default_instances(class)
    }

    /// oracle: `getOutParamPositions?` (`Class.lean:81-82`). `Some(&[])`
    /// means "is a class, with no output parameters"; `None` means "not
    /// a class" — the oracle's `isClass` is precisely the `Some`/`None`
    /// distinction (`Class.lean:77-78`), so they must not be collapsed.
    pub fn get_out_param_positions(&self, class_name: NameId) -> Option<&[usize]> {
        self.classes.out_params(class_name)
    }

    /// oracle: `getOutLevelParamPositions?` (`Class.lean:91-92`).
    pub fn get_out_level_param_positions(&self, class_name: NameId) -> Option<&[usize]> {
        self.classes.out_level_params(class_name)
    }

    /// oracle: `hasOutParams` (`Class.lean:85-88`) — a class with a
    /// NON-EMPTY output-parameter array.
    ///
    /// No production consumer yet (test-only today) — a planned M4b-3
    /// P2b-ii accessor for the elaborator-side `resultTypeOutParam?`
    /// producer, not dead API.
    pub fn has_out_params(&self, class_name: NameId) -> bool {
        matches!(self.get_out_param_positions(class_name), Some(p) if !p.is_empty())
    }

    /// oracle: `isCoeDecl` (`Meta/Coe.lean:28-29`) — `coeDeclAttr.hasTag
    /// env declName`. `pub` because `leanr_elab`'s tests assert the gate
    /// directly; the production reader is `coe.rs::expand_coe`.
    pub fn is_coe_decl(&self, name: NameId) -> bool {
        self.coe_decls.contains(&name)
    }

    /// oracle: `Lean.occursCheck` (`Lean/Util/OccursCheck.lean:18-53`),
    /// consumed by `resumePostponed`'s assignment guard
    /// (`SyntheticMVars.lean:56-58`): `if (← occursCheck mvarId result)
    /// then mvarId.assign result; return true else return false`. `true`
    /// means `mvar_id` is safe to assign `e` to — it does NOT occur in
    /// `e` (following assigned mvars, same as the oracle).
    ///
    /// Additive: a `pub` forwarder to the existing `pub(crate)`
    /// `MetaCtx::occurs_check` (`assign.rs:1117`), which `assign.rs`'s
    /// own assignment path already calls on the same traversal. Named
    /// `check_occurs` rather than reusing `occurs_check` verbatim: Rust
    /// merges inherent `impl` blocks for one type across files, so a
    /// second same-named method on `MetaCtx` would not compile. No new
    /// logic, no new fields, no TCB surface — `leanr_elab` simply
    /// cannot reach a `pub(crate)` item from another crate.
    pub fn check_occurs(&mut self, mvar_id: MVarId, e: ExprId) -> Result<bool, MetaError> {
        self.occurs_check(mvar_id, e)
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

    /// Test-only step-count observer. `is_class`'s quick path (below)
    /// must never call `whnf` — every `whnf` entry calls `step()`
    /// (`whnf.rs:194`) — so a test that wants to tell "answered `None`
    /// without reducing" apart from "reduced its way to the same
    /// `None`" needs to see this counter move, not just the `Option`
    /// result (`is_class_rejects_a_sort_without_reducing`'s own
    /// mutation-table entry: both readings answer `None`).
    #[cfg(test)]
    pub(crate) fn steps(&self) -> u64 {
        self.steps
    }

    /// oracle: `isClass?` (`Basic.lean:1542-1543`) — `isClassImp?`
    /// (`:1524-1528`) with every exception swallowed (`try … catch _ =>
    /// return none`). The swallow is modelled as error -> `None` rather
    /// than propagated: a failure to decide makes something not-a-class,
    /// never a hard error, and diverging here would turn an ordinary
    /// binder into an elaboration failure.
    ///
    /// Called from `push_local_decl`/`push_let_decl` (Task 4) and from
    /// `get_instances` (Task 6), which resolves its goal's class name
    /// through this.
    ///
    /// **The swallow covers the two budget errors too, and they are not
    /// alike.** `StepBudgetExhausted` is SELF-LIMITING: `self.steps`
    /// only ever increases (`step`, `:1164-1170`), so the very next
    /// `step()` anywhere re-raises it and the swallowed answer cannot
    /// travel far. `DepthBudgetExhausted` is NOT sticky: `guarded`
    /// (`:1173-1184`) decrements `guard_depth` on the way out, so an
    /// `is_class` called near `MAX_REC_DEPTH` can answer "not a class"
    /// while a shallower caller goes on to succeed. The consequence is
    /// that a class-typed binder can fail to install its local instance,
    /// which is INCOMPLETENESS (a synthesis that finds fewer candidates
    /// than the oracle), never unsoundness — no wrong term is built.
    /// Left as-is deliberately: propagating would turn an ordinary
    /// binder into an elaboration failure, which is the very thing the
    /// oracle's own `catch _ => return none` avoids.
    pub(crate) fn is_class(&mut self, ty: ExprId) -> Result<Option<NameId>, MetaError> {
        match self.is_class_quick(ty) {
            LOption::Some(c) => Ok(Some(c)),
            LOption::None => Ok(None),
            LOption::Undef => Ok(self.is_class_expensive(ty).unwrap_or(None)),
        }
    }

    /// oracle: `isClassQuick?` (`Basic.lean:1358-1381`) — a purely
    /// structural walk that NEVER reduces; deciding needs `.undef` to
    /// hand off to `is_class_expensive`, which does.
    ///
    /// **Correction (task 6)**: an earlier version of this comment
    /// claimed the whnf-free quick path was load-bearing for
    /// `get_instances`' `mem::take` window. It is not, and the premise
    /// was wrong anyway — `is_class_quick_const` reads the AMBIENT
    /// transparency, so at `TransparencyMode::Default` every
    /// definition-headed type answers `.undef` and reaches whnf after
    /// all. What actually protects that window is placement:
    /// `get_instances` calls `is_class` BEFORE it takes its table (see
    /// that function's own invariant note), so whatever this reduces
    /// cannot re-enter an emptied table.
    ///
    /// Called from [`MetaCtx::is_class`] — see that method's own doc.
    ///
    /// **Review round 1, I3**: opened as a `loop` rather than the
    /// straight-line recursion every other arm of the oracle port
    /// (`self.is_class_quick(body)`) reads more naturally as. All three
    /// of the oracle's recursive arms (`.forallE`, `.mdata`, the
    /// assigned-`.mvar` case) are TAIL calls with nothing left to do
    /// after the recursive result comes back, so a `loop` reproduces
    /// them exactly with zero Rust call-stack growth — unlike every
    /// other recursive `ExprId` traversal in this crate (35 call sites,
    /// `occurs_check` at `assign.rs:1153-1157` the direct structural
    /// analogue), this one is not routed through `MetaCtx::guarded`
    /// (`:1173-1184`, `MAX_REC_DEPTH` + `stacker::maybe_grow`) because a
    /// tail loop has no frames to grow a guard against. The `.mvar` arm
    /// still needs an explicit bound distinct from stack depth: it
    /// follows `MetavarContext::assignment` chains, and — same posture
    /// `whnf_easy_cases` documents for its own `MVar`/`FVar` dereference
    /// loop (`whnf.rs:227-234`) — `MetavarContext::assign` has no cycle
    /// detection, so an unbounded chain here is a hang, not merely deep
    /// recursion. Bounded with a local counter (`MAX_REC_DEPTH`, the
    /// same budget `guarded` uses), never `self.step()`: `step()` would
    /// move `steps()` on the ordinary (non-cyclic, non-pathological)
    /// path too, which would falsify `is_class_rejects_a_sort_without_reducing`
    /// and `is_class_rejects_a_real_inductive_without_reducing`'s own
    /// "never reaches whnf" step-delta assertions — this function must
    /// stay invisible to that counter, not merely bounded.
    fn is_class_quick(&mut self, mut ty: ExprId) -> LOption<NameId> {
        let mut mvar_chain_budget = MAX_REC_DEPTH;
        loop {
            match self.node(ty) {
                // `:1359-1363` — outright `.none`, never the expensive path.
                Node::BVar { .. }
                | Node::BVarBig { .. }
                | Node::LitNat { .. }
                | Node::LitStr { .. }
                | Node::FVar { .. }
                | Node::Sort { .. }
                | Node::Lam { .. } => return LOption::None,
                // `:1364-1365` — `.undef`: deciding needs reduction.
                Node::LetE { .. } | Node::Proj { .. } | Node::ProjBig { .. } => {
                    return LOption::Undef
                }
                // `:1366` — look THROUGH the binder at the conclusion.
                Node::Forall { body, .. } => ty = body,
                Node::MData { expr, .. } => ty = expr,
                Node::Const { name, .. } => return self.is_class_quick_const(name),
                // `:1369-1372` — an assigned mvar is its value; unassigned
                // is `.none`. A chain that outruns `mvar_chain_budget`
                // (only reachable via a hypothetical assignment cycle,
                // never real elaborator output — see the doc comment
                // above) answers `.none`: a failure to decide is
                // not-a-class, never a hang, same posture as
                // `is_class`'s own exception-swallow.
                Node::MVar { id } => match id.and_then(|n| self.mctx.assignment(MVarId(n))) {
                    Some(v) if mvar_chain_budget > 0 => {
                        mvar_chain_budget -= 1;
                        ty = v;
                    }
                    _ => return LOption::None,
                },
                // `:1374-1381` — the head of the application decides.
                // Not a further `is_class_quick` recursion (the oracle's
                // own `.app` arm never calls `isClassQuick?` again
                // either — it inspects `f.getAppFn` directly), so this
                // arm needs neither the loop nor the budget above.
                Node::App { .. } => {
                    return match self.node(self.get_app_fn(ty)) {
                        Node::Const { name, .. } => self.is_class_quick_const(name),
                        Node::Lam { .. } => LOption::Undef,
                        Node::MVar { id } => {
                            match id.and_then(|n| self.mctx.assignment(MVarId(n))) {
                                Some(v) => match self.node(self.get_app_fn(v)) {
                                    Node::Const { name, .. } => self.is_class_quick_const(name),
                                    _ => LOption::Undef,
                                },
                                None => LOption::None,
                            }
                        }
                        _ => LOption::None,
                    }
                }
            }
        }
    }

    /// oracle: `isClassQuickConst?` composed with `getConstTemp?` /
    /// `getDefInfoTemp` (`Basic.lean:1329-1356`, transcribed verbatim —
    /// **not** the task brief's own sketch, which collapsed every
    /// non-class constant to `.undef`; Ruling R5 corrects that). `.some
    /// c` when `c` is a registered class. Otherwise `.undef` **iff** `c`
    /// is a `Defn` that is currently unfoldable (transparency `.all` /
    /// `.default`, or else `status_of(c) == Reducible`); `.none` for a
    /// theorem, an inductive/constructor/recursor/axiom/quotient/
    /// opaque, a transparency-gated definition, an empty `Node::Const`
    /// name, or an unknown constant. The oracle's unknown-constant arm
    /// THROWS (`getConstTemp?`'s `none => throwUnknownConstantAt ..`);
    /// `isClass?`'s top-level `try .. catch _ => return none` swallows
    /// it, so the observable behavior is `.none` — modelled directly as
    /// `.none` here rather than as a propagated error, same posture as
    /// `is_class`'s own doc comment above.
    ///
    /// Called from [`MetaCtx::is_class_quick`] — see [`MetaCtx::is_class`]'s
    /// own doc.
    fn is_class_quick_const(&self, name: Option<NameId>) -> LOption<NameId> {
        let Some(n) = name else {
            return LOption::None;
        };
        if self.classes.is_class_name(n) {
            return LOption::Some(n);
        }
        match self.view.get(n) {
            // `getConstTemp?`'s `thmInfo => none` arm.
            Some(ConstantInfo::Thm(_)) => LOption::None,
            // `getConstTemp?`'s `defnInfo => getDefInfoTemp info` arm.
            Some(ConstantInfo::Defn(_)) => match self.cfg.transparency {
                TransparencyMode::All | TransparencyMode::Default => LOption::Undef,
                _ if self.status_of(n) == ReducibilityStatus::Reducible => LOption::Undef,
                _ => LOption::None,
            },
            // Every other known `ConstantInfo` (inductive, constructor,
            // recursor, axiom, quotient, opaque) passes through
            // `getConstTemp?` as `some info`, but is not a `.defnInfo`,
            // so `isClassQuickConst?`'s own match falls to its `_ =>
            // .none` arm.
            Some(_) => LOption::None,
            // Unknown constant: see the doc comment above.
            None => LOption::None,
        }
    }

    /// oracle: `isClassExpensive?` (`Basic.lean:1520-1522`) —
    /// `withReducible`, telescope the foralls down to the conclusion
    /// (`forallTelescopeReducingAux .. (whnfType := true)`), then
    /// `isClassApp?` (`:1510-1518`): the head constant, if the
    /// environment says it is a class.
    ///
    /// **Plan-mandated deviation (Controller Ruling R6), not a bug**:
    /// the oracle's telescope (`forallTelescopeReducingAuxAux.process`,
    /// `Basic.lean:1458-1487`, inside `forallTelescopeReducingAuxAux`
    /// itself at `:1453-1488`) peels each `Forall` by substituting a
    /// FRESH FVAR for the bound variable (`instantiateRevRange`,
    /// `:1462`, backed by `mkFreshFVarId`/`lctx.mkLocalDecl`) before
    /// whnf-ing the next binder's body. This loop does not: it whnfs
    /// `body` directly, still carrying a loose bvar for the binder just
    /// stripped. Porting the real telescope would mean opening each
    /// binder with `push_local_decl`, which is exactly the fvar-pushing
    /// chokepoint Task 4 owns — R6 keeps that producer out of this task
    /// rather than widening it past its brief.
    ///
    /// This is sound, not merely harmless, and the reason is a real
    /// (verified, not assumed) fact about THIS crate's `whnf`, not a
    /// claim about where a bare bvar can appear: `whnf_easy_cases`
    /// (`whnf.rs:232-246`) calls `self.step()` and then, on a
    /// `Node::BVar`/`Node::BVarBig` HEAD, returns
    /// `Err(MetaError::Infer("loose bvar in whnf"))` — this crate's
    /// substitute for the oracle's own `panic! "loose bvar in
    /// expression"` at the same site (`WHNF.lean:391`; Global
    /// Constraints forbid the panic). `whnf` is not a leaf function: the
    /// nat/recursor/proj/smart-unfolding arms it dispatches to each
    /// recursively `whnf` a subterm (an argument, a major premise, a
    /// projected structure, a match discriminant), so a dangling bvar
    /// left under a stripped binder can surface this `Err` from
    /// anywhere inside the call, not only at the very top. That `Err`
    /// propagates out of THIS function via `?` and is swallowed by
    /// `is_class`'s `unwrap_or(None)` (this file, `MetaCtx::is_class`)
    /// — exactly the oracle's own `isClass?`'s `try .. catch _ => none`
    /// swallow, just reached via a different failure than the oracle's
    /// (whose telescope never produces a loose bvar in the first place,
    /// since it substitutes one before whnf ever sees it). And a
    /// genuinely stuck-on-a-variable reduction — bvar, fvar, an
    /// unresolved recursor/matcher, or an un-unfolded `Defn` under
    /// `Reducible` transparency — is never itself a registered class
    /// (`is_class_name` only ever matches an inductive/structure head),
    /// so on every path that does NOT error, this loop's answer agrees
    /// with the oracle's real telescope too: `isClassApp?` only ever
    /// inspects the FINAL non-forall type's spine HEAD, never an
    /// argument value, and a dangling bvar can only ever occupy that
    /// head position itself (not a `Const` either way) or sit buried in
    /// an argument `isClassApp?` never looks at. **This soundness
    /// depends on `whnf.rs:241-246` staying an `Err` rather than
    /// becoming a `panic!` or a silent no-op** — if a future change
    /// makes whnf tolerate a loose bvar (e.g. by treating it as stuck
    /// and returning it unchanged instead of erroring), this reasoning
    /// would need re-checking, since the "errors instead of misanswering"
    /// half of the argument is what closes the gap, not the "always
    /// agrees" half alone.
    ///
    /// Called from [`MetaCtx::is_class`] — see that method's own doc.
    fn is_class_expensive(&mut self, ty: ExprId) -> Result<Option<NameId>, MetaError> {
        self.with_transparency(TransparencyMode::Reducible, |ctx| {
            let mut cur = ctx.whnf(ty)?;
            while let Node::Forall { body, .. } = ctx.node(cur) {
                cur = ctx.whnf(body)?;
            }
            Ok(match ctx.node(ctx.get_app_fn(cur)) {
                Node::Const { name: Some(n), .. } if ctx.classes.is_class_name(n) => Some(n),
                _ => None,
            })
        })
    }

    /// `pub` since M4b-3 P3 task 4 (design spec § Accessor ledger, P3's
    /// row): the elaborator's `commitWhen`
    /// (`Lean/Util/MonadBacktrack.lean:50-60`) is a
    /// save / run / restore-unless-it-returned-true bracket over exactly
    /// this state, and `synthesizeUsingDefaultInstance`
    /// (`SyntheticMVars.lean:155-156`) runs inside one. Additive and
    /// behavior-neutral — a visibility widening only.
    pub fn checkpoint(&self) -> MetaSnapshot {
        let (expr_assignments, level_assignments, delayed_assignments) =
            self.mctx.snapshot_assignments();
        MetaSnapshot {
            expr_assignments,
            level_assignments,
            delayed_assignments,
            postponed: self.postponed.clone(),
        }
    }

    /// `pub` since M4b-3 P3 task 4 — see [`MetaCtx::checkpoint`].
    pub fn rollback(&mut self, snap: MetaSnapshot) {
        self.mctx.restore_assignments(
            snap.expr_assignments,
            snap.level_assignments,
            snap.delayed_assignments,
        );
        self.postponed = snap.postponed;
    }

    /// oracle: `withAssignableSyntheticOpaque` (`Lean/Meta/Basic.lean:1312-1313`)
    /// — run `f` with `Config.assignSyntheticOpaque := true`, restoring
    /// the previous value on the normal and on the `Err` path alike
    /// (`f` RETURNS a `Result` rather than unwinding, so a plain
    /// save/run/restore covers both).
    ///
    /// **Not panic-safe, and this is now `pub`.** There is no drop
    /// guard: if `f` unwinds, the flag stays `true` in `self.cfg`. That
    /// was defensible while the function was `pub(crate)` — every
    /// in-crate caller is `Result`-based and a panic there is already a
    /// bug that aborts the run — but M4b-3 P3 task 4 widened it to
    /// `pub` (design spec § Accessor ledger, P3's row), so an external
    /// caller can now pass an `f` that panics, catch the unwind with
    /// `catch_unwind`, and keep using the same `MetaCtx`. The residual
    /// risk is therefore real but narrow: it needs a caller that both
    /// panics inside the scope AND continues on the same context. The
    /// only production caller in-tree is `leanr_elab`'s
    /// `synthesize_using_default_instance`, which is `Result`-based and
    /// catches no unwind (the other two are this crate's own unit tests,
    /// where a panicking `expect` fails the test rather than resuming),
    /// so no path in-tree reaches it today. Fixing it
    /// properly means a drop guard, which is a behaviour change to
    /// `leanr_meta` and so is recorded as a follow-up in the design
    /// spec's deferred-work section rather than made here.
    ///
    /// The config is part of the defeq CACHE KEY (`config.rs`'s own
    /// doc), so entries cached inside the scope cannot leak out to
    /// queries asked with the flag off. That is why this is a config
    /// field rather than an ambient toggle. Note the leak above is a
    /// leak of the FLAG, not of cache entries: a stuck-`true` flag makes
    /// later queries ask a different question, it does not let an
    /// inside-the-scope answer be served outside it.
    pub fn with_assignable_synthetic_opaque<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = self.cfg.assign_synthetic_opaque;
        self.cfg.assign_synthetic_opaque = true;
        let r = f(self);
        self.cfg.assign_synthetic_opaque = saved;
        r
    }
}

/// A save point for `checkpointDefEq` (oracle Basic.lean:2438). Holds
/// exactly what a failed trial unification must restore: the expr,
/// level, and delayed assignment maps and the postponed queue. NOT the
/// permanent cache (it is monotone and shared) and NOT declarations (an
/// mvar stays declared, but a delayed assignment made inside a trial is
/// undone by rollback).
///
/// `Clone` (task B5): the tabled-synthesis driver stores one snapshot
/// PER NODE (the oracle's own `GeneratorNode.mctx`/`ConsumerNode.mctx`
/// fields, `SynthInstance.lean:49`/`:57`) and re-enters it repeatedly
/// via a `withMCtx`-equivalent, so it must be able to restore the same
/// snapshot more than once — `rollback` consumes its argument.
///
/// `pub` since M4b-3 P3 task 4: [`MetaCtx::checkpoint`]/
/// [`MetaCtx::rollback`] are now public, so their currency has to be
/// nameable outside the crate. The fields stay private — a snapshot is
/// an opaque token, only ever produced by `checkpoint` and consumed by
/// `rollback`.
#[derive(Clone)]
pub struct MetaSnapshot {
    expr_assignments: HashMap<MVarId, ExprId>,
    level_assignments: HashMap<LMVarId, LevelId>,
    delayed_assignments: HashMap<MVarId, crate::DelayedMVarAssignment>,
    postponed: Vec<(LevelId, LevelId)>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{
        class_app, const_named, fresh_mvar, render_name, with_class_ctx, with_ctx,
        with_instances_ctx, with_prelude0_ctx,
    };
    use crate::MetaError;

    /// TDD RED for the checkpoint/push/restore + `mk_forall` accessors
    /// (M4b-2 plan1 task 1): declares a local `(x : Nat)`, checks the
    /// fvar is visible while the checkpoint is open, abstracts it back
    /// into `∀ (x : Nat), x`, then restores and checks `lctx` is back to
    /// the checkpoint depth. Uses `with_prelude0_ctx`/`const_named` (this
    /// crate's real test-context/constant-lookup helpers, `test_support.rs`)
    /// rather than the task brief's sketched `with_test_ctx`/`const_nat` —
    /// `with_ctx`'s empty environment has no `Nat` constant to look up.
    #[test]
    fn push_local_decl_scopes_and_mk_forall_abstracts() {
        with_prelude0_ctx(|ctx| {
            let nat = const_named(ctx, "Nat");
            let checkpoint = ctx.lctx_checkpoint();
            let fvar = ctx
                .push_local_decl(None, nat, BinderInfo::Default)
                .expect("push_local_decl");
            // fvar is a declared local while the checkpoint is open
            assert!(matches!(ctx.node(fvar), Node::FVar { .. }));
            // body = the fvar itself → ∀ (x : Nat), x  (a `pi` whose body is `bvar 0`)
            let built = ctx
                .mk_forall(std::slice::from_ref(&fvar), fvar)
                .expect("mk_forall");
            ctx.lctx_restore(checkpoint);
            // lctx restored: the decl count is back to the checkpoint
            assert_eq!(ctx.lctx.save(), checkpoint);
            // built is a Forall node whose body is bvar 0
            match ctx.node(built) {
                Node::Forall { body, .. } => {
                    assert!(matches!(ctx.node(body), Node::BVar { idx: 0 }));
                }
                other => panic!("expected Forall, got {other:?}"),
            }
        });
    }

    /// TDD RED/GREEN for M4b-2 plan2 task 1: `mk_lambda`, the
    /// `mkLambdaFVars` twin of `mk_forall`. Mirrors
    /// `push_local_decl_scopes_and_mk_forall_abstracts` above, using the
    /// same real test helpers (`with_prelude0_ctx`/`const_named`) rather
    /// than the task brief's sketched `with_test_ctx`/`const_nat`.
    #[test]
    fn mk_lambda_abstracts_body_over_fvar() {
        with_prelude0_ctx(|ctx| {
            let nat = const_named(ctx, "Nat");
            let checkpoint = ctx.lctx_checkpoint();
            let fvar = ctx
                .push_local_decl(None, nat, BinderInfo::Default)
                .expect("push_local_decl");
            // body = the fvar itself → fun (x : Nat) => x  (a `lam` whose body is `bvar 0`)
            let built = ctx
                .mk_lambda(std::slice::from_ref(&fvar), fvar)
                .expect("mk_lambda");
            ctx.lctx_restore(checkpoint);
            match ctx.node(built) {
                Node::Lam { body, .. } => {
                    assert!(matches!(ctx.node(body), Node::BVar { idx: 0 }));
                }
                other => panic!("expected Lam, got {other:?}"),
            }
        });
    }

    /// TDD RED/GREEN for M4b-2 plan3 task 1: the let-decl pair
    /// (`push_let_decl` + `mk_let_expr`). Structure only — the value
    /// here is `Nat` rather than a `Nat`-typed term, since abstraction
    /// and the `non_dep` bit are what is under test, not type checking.
    /// Both `non_dep` values are exercised: `false` is `let`, `true` is
    /// `have` (the ONLY difference between the two forms, design spec
    /// § Amendment 2).
    #[test]
    fn push_let_decl_and_mk_let_expr_carry_non_dep() {
        with_prelude0_ctx(|ctx| {
            let nat = const_named(ctx, "Nat");
            for want_non_dep in [false, true] {
                let checkpoint = ctx.lctx_checkpoint();
                let fvar = ctx.push_let_decl(None, nat, nat).expect("push_let_decl");
                assert!(matches!(ctx.node(fvar), Node::FVar { .. }));
                // body = the fvar itself → `let x : Nat := Nat; x`
                // (a `LetE` whose body is `bvar 0`).
                let built = ctx
                    .mk_let_expr(fvar, fvar, want_non_dep)
                    .expect("mk_let_expr");
                ctx.lctx_restore(checkpoint);
                assert_eq!(ctx.lctx.save(), checkpoint);
                match ctx.node(built) {
                    Node::LetE {
                        ty,
                        value,
                        body,
                        non_dep,
                        ..
                    } => {
                        assert_eq!(ty, nat);
                        assert_eq!(value, nat);
                        assert!(matches!(ctx.node(body), Node::BVar { idx: 0 }));
                        assert_eq!(non_dep, want_non_dep);
                    }
                    other => panic!("expected LetE, got {other:?}"),
                }
            }
        });
    }

    /// `mk_let_expr` on a cdecl (non-let) fvar is an error, never a
    /// silently wrong node: a `LetE` needs a value and a cdecl has none.
    #[test]
    fn mk_let_expr_rejects_a_cdecl_fvar() {
        with_prelude0_ctx(|ctx| {
            let nat = const_named(ctx, "Nat");
            let checkpoint = ctx.lctx_checkpoint();
            let fvar = ctx
                .push_local_decl(None, nat, BinderInfo::Default)
                .expect("push_local_decl");
            let err = ctx.mk_let_expr(fvar, fvar, false);
            ctx.lctx_restore(checkpoint);
            assert!(err.is_err(), "expected Err for a cdecl fvar, got {err:?}");
        });
    }

    /// A class-typed binder becomes a local instance; a non-class binder
    /// does not. oracle: `withNewFVar` (`Basic.lean:1785-1789`).
    #[test]
    fn pushing_a_class_typed_decl_installs_a_local_instance() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let n = const_named(ctx, "N");

            let cp = ctx.lctx_checkpoint();
            let _plain = ctx
                .push_local_decl(None, n, BinderInfo::Default)
                .expect("push");
            assert!(
                ctx.local_instances.entries().is_empty(),
                "`(x : N)` is not a class-typed binder"
            );

            let inst = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push");
            assert_eq!(ctx.local_instances.entries().len(), 1);
            assert_eq!(ctx.local_instances.entries()[0].class_name, add);
            assert_eq!(ctx.local_instances.entries()[0].fvar, inst);

            // A checkpoint taken immediately AFTER the class-typed push,
            // and a restore to it after pushing something else on top:
            // the instance was installed BEFORE this checkpoint, so it
            // must survive. This is the discriminator the brief's fourth
            // mutation (capture `depth` after the push instead of
            // before) needs and the original brief's sole restore
            // assertion below does NOT provide — that one restores all
            // the way to `cp` (depth 0), and `truncate_to` pops any
            // recorded depth `>= 0` regardless of whether it is off by
            // one, so the bug is invisible there. Here the recorded
            // depth, if captured post-push, EQUALS this checkpoint, and
            // `truncate_to`'s `>=` pops entries at exactly the
            // checkpoint depth too — so the off-by-one bug pops an
            // instance that a correct depth (this decl's own pre-push
            // index) would have kept.
            let cp_after_inst = ctx.lctx_checkpoint();
            let _another_plain = ctx
                .push_local_decl(None, n, BinderInfo::Default)
                .expect("push");
            ctx.lctx_restore(cp_after_inst);
            assert_eq!(
                ctx.local_instances.entries().len(),
                1,
                "the instance was pushed before this checkpoint, so restoring to it \
                 must leave it in scope"
            );

            ctx.lctx_restore(cp);
            assert!(
                ctx.local_instances.entries().is_empty(),
                "restoring the local context takes the instance out of scope"
            );
        });
    }

    /// Fix round 2: `install_local_instance_for_last_pushed`
    /// (`push_local_decl_without_instance`'s deferred install half,
    /// added round 1 for Finding 2's ordering fix) used to return
    /// without dropping `lctx_snapshot`, leaving the memo STALE across
    /// exactly the window it exists to close. Reproduces the review's
    /// own reachability path directly rather than asserting the drop in
    /// isolation: `with_mvar_context` — reachable from
    /// `propagate_expected_type`'s own `is_def_eq` via `whnf.rs`'s
    /// pending-instance-mvar path or `assign.rs`'s `mk_aux_mvar_for`
    /// rescue — REPOPULATES the cache on its way out (`install_lctx`
    /// reads, and so rebuilds and caches, `current_lctx()` on entry,
    /// then reinstalls that exact snapshot on exit), with a snapshot
    /// that predates the instance install below.
    #[test]
    fn install_local_instance_for_last_pushed_drops_a_stale_memo() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let n = const_named(ctx, "N");

            // `propagate_expected_type`'s own shape: push first, WITHOUT
            // installing — the domain is not yet known to be class-typed
            // (an elided binder's domain starts as a fresh mvar; `n`
            // stands in for "not yet Add N" here).
            let fvar = ctx
                .push_local_decl_without_instance(None, n, BinderInfo::Default)
                .expect("push");

            // Anything on `propagate_expected_type`'s own path that
            // enters and leaves a metavariable's context repopulates the
            // memo in between — any DECLARED mvar does.
            let (_, other_mvar) = fresh_mvar(ctx, n);
            ctx.with_mvar_context(other_mvar, |_| {});
            assert!(
                ctx.lctx_snapshot.is_some(),
                "with_mvar_context must have repopulated the memo for \
                 this test to mean anything"
            );

            // NOW the domain is discovered to be class-typed (the
            // oracle's own `isClass? type` test, run AFTER propagation
            // per Finding 2) and installed.
            ctx.install_local_instance_for_last_pushed(fvar, add_n)
                .expect("install");

            // The memo must reflect the just-installed instance, not
            // the stale pre-install snapshot `with_mvar_context` cached.
            let snap = ctx.current_lctx();
            assert_eq!(
                snap.local_instances().len(),
                1,
                "current_lctx() returned a snapshot that predates the \
                 local-instance install"
            );
        });
    }

    /// Binder info does NOT gate installation: the oracle's
    /// `withNewFVar` consults `isClass?` on the TYPE and nothing else,
    /// so a class-typed EXPLICIT binder is a local instance too
    /// (`fun (inst : Add N) => …`). A port that gated on
    /// `BinderInfo::InstImplicit` would silently lose those.
    #[test]
    fn a_class_typed_explicit_binder_is_also_a_local_instance() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let cp = ctx.lctx_checkpoint();
            ctx.push_local_decl(None, add_n, BinderInfo::Default)
                .expect("push");
            assert_eq!(
                ctx.local_instances.entries().len(),
                1,
                "installation keys on the TYPE, never on the binder info"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// oracle: `withLetDeclImp` (`Basic.lean:1905-1911`) routes through
    /// the same `withNewFVar`, so a let-bound instance counts.
    #[test]
    fn pushing_a_class_typed_let_decl_installs_a_local_instance() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let n = const_named(ctx, "N");
            let val = const_named(ctx, "instAddN");
            let cp = ctx.lctx_checkpoint();
            ctx.push_let_decl(None, add_n, val).expect("push");
            assert_eq!(ctx.local_instances.entries().len(), 1);

            // Same discriminator as `push_local_decl`'s own test above:
            // a checkpoint taken immediately AFTER this push, then a
            // restore to it after pushing something else on top, must
            // leave the instance in scope — catches `depth` captured
            // after the push (equal to this checkpoint) rather than
            // before (this decl's own index, strictly less than it).
            let cp_after_inst = ctx.lctx_checkpoint();
            let _another_plain = ctx
                .push_local_decl(None, n, BinderInfo::Default)
                .expect("push");
            ctx.lctx_restore(cp_after_inst);
            assert_eq!(
                ctx.local_instances.entries().len(),
                1,
                "the instance was pushed before this checkpoint, so restoring to it \
                 must leave it in scope"
            );

            ctx.lctx_restore(cp);
            assert!(ctx.local_instances.entries().is_empty());
        });
    }

    /// `mk_forall`/`mk_lambda` (`mk_binding`'s two callers) on an ldecl
    /// (let-bound) fvar is an error, never a silently wrong `lam`/`forallE`
    /// that drops the ldecl's value. Pins the guard added for the
    /// whole-branch-review finding: `mk_binding` is the cdecl-only case
    /// (see its own doc), and unlike the kernel's `subst.rs::mk_binding`
    /// twin it has no `Some(value)` branch, so it must refuse rather than
    /// build a wrong `ExprId`. Mirrors `mk_let_expr_rejects_a_cdecl_fvar`
    /// above, with the roles of ldecl/cdecl swapped.
    #[test]
    fn mk_binding_rejects_an_ldecl_fvar() {
        with_prelude0_ctx(|ctx| {
            let nat = const_named(ctx, "Nat");
            let checkpoint = ctx.lctx_checkpoint();
            let fvar = ctx.push_let_decl(None, nat, nat).expect("push_let_decl");
            let err = ctx.mk_forall(std::slice::from_ref(&fvar), fvar);
            ctx.lctx_restore(checkpoint);
            assert!(err.is_err(), "expected Err for an ldecl fvar, got {err:?}");
        });
    }

    /// oracle: `Expr.instantiateBetaRevRange`'s FIRST short-circuit,
    /// `if e.hasLooseBVars && ..` (`Lean/Meta/InferType.lean:37`). A term
    /// with no loose bvars is returned as-is — even when it is itself a
    /// beta redex and even when `args` contains a lambda (which is what
    /// isolates this guard from the `args.any isLambda` one below).
    ///
    /// Pins the whole-branch-review finding: the previous implementation
    /// substituted and then `head_beta`'d unconditionally, so this exact
    /// input came back as `Nat` instead of `(fun _ => #0) Nat`. Because
    /// `getParamType`/`getArgExpectedType` read the result, that is the
    /// expected type an argument gets elaborated against.
    #[test]
    fn instantiate_beta_rev_range_leaves_a_closed_term_alone() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let nat = const_named(ctx, "Nat");
            let bvar0 = ctx
                .scratch
                .expr_bvar(base, &leanr_kernel::Nat::from(0u64))
                .expect("bvar");
            // `fun (_ : Nat) => #0` — the identity, closed.
            let id_lam = ctx
                .scratch
                .expr_lam(base, None, nat, bvar0, BinderInfo::Default)
                .expect("lam");
            // `(fun (_ : Nat) => #0) Nat` — a redex, but CLOSED.
            let redex = ctx.scratch.expr_app(base, id_lam, nat).expect("app");
            let out = ctx
                .instantiate_beta_rev_range(redex, &[id_lam])
                .expect("instantiate_beta_rev_range");
            assert_eq!(
                out, redex,
                "hasLooseBVars is false, so the oracle returns `e` untouched"
            );
        });
    }

    /// oracle: the SECOND short-circuit — `else instantiateRevRange e
    /// start stop args`, taken when `args.any (·.consumeMData.isLambda)`
    /// is false (`InferType.lean:39-43`, with the oracle's own comment
    /// "If there are no lambdas, then `instantiateRevRange` suffices").
    ///
    /// The term here has a loose bvar (so the first guard does not fire)
    /// and an existing head redex, and the substituted argument is a
    /// constant, not a lambda. The oracle substitutes and stops; the
    /// previous implementation went on to `head_beta` and collapsed the
    /// redex.
    #[test]
    fn instantiate_beta_rev_range_skips_beta_when_no_arg_is_a_lambda() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let nat = const_named(ctx, "Nat");
            let bvar0 = ctx
                .scratch
                .expr_bvar(base, &leanr_kernel::Nat::from(0u64))
                .expect("bvar");
            let id_lam = ctx
                .scratch
                .expr_lam(base, None, nat, bvar0, BinderInfo::Default)
                .expect("lam");
            // `(fun (_ : Nat) => #0) #0` — the OUTER `#0` is loose.
            let e = ctx.scratch.expr_app(base, id_lam, bvar0).expect("app");
            let out = ctx
                .instantiate_beta_rev_range(e, &[nat])
                .expect("instantiate_beta_rev_range");
            match ctx.node(out) {
                Node::App { f, arg } => {
                    assert!(
                        matches!(ctx.node(f), Node::Lam { .. }),
                        "no lambda in `args`, so no beta step: the head stays a Lam"
                    );
                    assert_eq!(arg, nat, "the loose bvar is still substituted");
                }
                other => panic!("expected the redex to survive un-reduced, got {other:?}"),
            }
        });
    }

    /// The case the oracle's `visit` arm exists for, and the reason this
    /// function is not just `instantiateRevRange`: a loose bvar in HEAD
    /// position substituted by a lambda argument produces a redex that
    /// must be reduced (`InferType.lean`'s own docstring example, `motive
    /// n` with `motive := fun x => ..`). `head_beta` covers exactly this
    /// head-position case — see `instantiate_beta_rev_range`'s named
    /// limitation for the nested-redex case it does not.
    #[test]
    fn instantiate_beta_rev_range_betas_a_lambda_substituted_at_the_head() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let nat = const_named(ctx, "Nat");
            let bvar0 = ctx
                .scratch
                .expr_bvar(base, &leanr_kernel::Nat::from(0u64))
                .expect("bvar");
            let id_lam = ctx
                .scratch
                .expr_lam(base, None, nat, bvar0, BinderInfo::Default)
                .expect("lam");
            // `#0 Nat` — head is a loose bvar.
            let e = ctx.scratch.expr_app(base, bvar0, nat).expect("app");
            let out = ctx
                .instantiate_beta_rev_range(e, &[id_lam])
                .expect("instantiate_beta_rev_range");
            assert_eq!(out, nat, "`(fun _ => #0) Nat` must beta-reduce to `Nat`");
        });
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

    #[test]
    fn rollback_restores_assignments_and_postponed() {
        use crate::{LocalCtxSnapshot, MVarDecl, MVarId, MVarKind};
        with_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).expect("level");
            let ty = ctx.scratch.expr_sort(None, z).expect("sort");
            let s = ctx.scratch.intern_str(None, "m").expect("intern");
            let nm = ctx.scratch.name_str(None, None, s).expect("name");
            let m = MVarId(nm);
            ctx.mctx.declare(
                m,
                MVarDecl {
                    user_name: None,
                    ty,
                    lctx: LocalCtxSnapshot::empty(),
                    kind: MVarKind::Natural,
                },
            );

            let snap = ctx.checkpoint();
            ctx.mctx.assign(m, ty).expect("assign");
            ctx.postponed.push((z, z));
            assert!(ctx.mctx.is_assigned(m));
            assert_eq!(ctx.postponed.len(), 1);

            ctx.rollback(snap);
            assert!(!ctx.mctx.is_assigned(m), "assignment must be undone");
            assert!(ctx.postponed.is_empty(), "postponed must be restored");
        });
    }

    /// `instantiate_beta_rev_range` on a forall BODY with one loose bvar:
    /// substituting `Nat` for `#0` yields `Nat` itself. Mirrors what
    /// `ElabAppArgs.State.getFType` does after one argument is consumed.
    #[test]
    fn instantiate_beta_rev_range_substitutes_loose_bvar() {
        with_prelude0_ctx(|ctx| {
            let nat = const_named(ctx, "Nat");
            // `#0` — a loose bvar standing for the consumed argument.
            let bvar = ctx
                .store_mut()
                .expr_bvar(None, &leanr_kernel::Nat::from(0u64))
                .unwrap();
            let got = ctx.instantiate_beta_rev_range(bvar, &[nat]).unwrap();
            assert_eq!(got, nat, "#0 must be replaced by the single argument");
        });
    }

    /// The empty-args fast path is the identity, and must not re-intern.
    #[test]
    fn instantiate_beta_rev_range_empty_is_identity() {
        with_prelude0_ctx(|ctx| {
            let nat = const_named(ctx, "Nat");
            assert_eq!(ctx.instantiate_beta_rev_range(nat, &[]).unwrap(), nat);
        });
    }

    #[test]
    fn process_postponed_levels_drains_an_empty_queue() {
        with_ctx(|ctx| {
            assert_eq!(ctx.postponed_len(), 0);
            // An empty queue is vacuously solvable: the oracle's
            // `processPostponed` returns `true` when there is nothing
            // left to solve (`level.rs::process_postponed`'s own
            // contract), which is what makes the ladder's final
            // `process_postponed_universe_constraints` a no-op on every
            // term that never postponed a level constraint.
            assert!(ctx.process_postponed_levels().expect("no error"));
            assert_eq!(ctx.postponed_len(), 0);
        });
    }

    /// Mirrors `default_instances_finds_the_default_instance`
    /// (instances.rs) through the new public accessor: the same
    /// fixture (`with_instances_ctx` — the task brief's sketched
    /// `with_default_instance_ctx` does not exist; `instances.rs`'s own
    /// test builds its context inline the same way), the same class,
    /// the same expected entry — proving the accessor forwards rather
    /// than reimplementing.
    #[test]
    fn default_instances_of_reads_the_default_instance_table() {
        with_instances_ctx(|ctx| {
            let of_n = const_named(ctx, "OfN");
            let of_n_name = if let Node::Const { name: Some(n), .. } = ctx.node(of_n) {
                n
            } else {
                panic!("OfN is not a bare const")
            };
            let found = ctx.default_instances_of(of_n_name);
            let names: Vec<String> = found.iter().map(|(n, _)| render_name(ctx, *n)).collect();
            assert!(
                names.contains(&"instOfNN".to_string()),
                "default_instances_of(OfN): {names:?}"
            );
        });
    }

    /// `check_occurs` forwards to the crate-private `occurs_check`
    /// exactly: `false` when `mvar_id` occurs inside `e` (here, `?m`
    /// inside the application `Nat ?m`), `true` when it does not. This
    /// is the accessor `leanr_elab::synthetic::resume_postponed`'s
    /// assignment guard needs — it may not assign a resumed result that
    /// mentions the very mvar it is resolving (M4b-3 P2a task 5 review
    /// finding 1).
    #[test]
    fn check_occurs_forwards_to_the_crate_private_occurs_check() {
        with_prelude0_ctx(|ctx| {
            let nat = const_named(ctx, "Nat");
            let (m_expr, m_id) = fresh_mvar(ctx, nat);
            let base = Some(ctx.view.store);
            let app = ctx
                .scratch
                .expr_app(base, nat, m_expr)
                .expect("app: Nat ?m");
            assert!(
                !ctx.check_occurs(m_id, app).expect("no error"),
                "?m occurs inside `Nat ?m` -> not safe to assign"
            );
            assert!(
                ctx.check_occurs(m_id, nat).expect("no error"),
                "?m does not occur in `Nat` -> safe to assign"
            );
        });
    }

    /// `is_coe_decl` reads the `Lean.Meta.coeDeclAttr` name set (M4b-3
    /// P4 task 2), the gate `expand_coe` consults per head
    /// (`Meta/Coe.lean:28-29`, `isCoeDecl`). Over `Synth0.olean`:
    /// `CoeT.coe` is tagged, `CoeT` (the class) and `Add.add` are not.
    #[test]
    fn is_coe_decl_reads_the_tag_set() {
        use crate::test_support::with_synth0_ctx;
        with_synth0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let mut name = |parts: &[&str]| {
                let mut id = None;
                for p in parts {
                    let s = ctx.scratch.intern_str(base, p).expect("intern");
                    id = Some(ctx.scratch.name_str(base, id, s).expect("name"));
                }
                id.expect("non-empty")
            };
            let coe_t_coe = name(&["CoeT", "coe"]);
            let coe_t = name(&["CoeT"]);
            let add_add = name(&["Add", "add"]);
            assert!(ctx.is_coe_decl(coe_t_coe));
            assert!(!ctx.is_coe_decl(coe_t));
            assert!(!ctx.is_coe_decl(add_add));
        });
    }

    /// `with_transparency` restores on the normal path and nests.
    #[test]
    fn with_transparency_restores_the_ambient_mode() {
        use crate::TransparencyMode as T;
        with_prelude0_ctx(|ctx| {
            assert_eq!(ctx.cfg().transparency, T::Default);
            ctx.with_transparency(T::Instances, |ctx| {
                assert_eq!(ctx.cfg().transparency, T::Instances);
                ctx.with_transparency(T::Reducible, |ctx| {
                    assert_eq!(ctx.cfg().transparency, T::Reducible);
                });
                assert_eq!(ctx.cfg().transparency, T::Instances);
            });
            assert_eq!(ctx.cfg().transparency, T::Default);
        });
    }

    /// `with_mvar_context` installs a metavariable's own local context
    /// and restores the ambient one on the way out (oracle:
    /// `withMVarContextImp` = `withLocalContextImp mvarDecl.lctx
    /// mvarDecl.localInstances`, `Meta/Basic.lean:2043-2045`). The
    /// discriminating shape is a variable whose binder scope has CLOSED:
    /// outside the closure it does not resolve, inside it does.
    #[test]
    fn with_mvar_context_reinstalls_a_closed_binder_scope() {
        use crate::test_support::with_prelude0_ctx;
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let x = ctx
                .push_local_decl(None, sort0, leanr_kernel::BinderInfo::Default)
                .expect("decl");
            let (_, mvar_id) = ctx.mk_aux_mvar(sort0).expect("mvar");
            ctx.lctx_restore(cp);

            // The binder is gone: `x` no longer types.
            assert!(
                ctx.infer_type(x).is_err(),
                "the ambient context has dropped the binder"
            );
            // Under the metavariable's own context it does. Also take a
            // checkpoint INSIDE the closure: this is what a caller that
            // goes on to open a further binder there would do, and
            // `lctx_checkpoint` asserts `local_names`/`lctx` are in
            // lockstep — the brief's install_lctx mutation (swap `lctx`
            // but not `local_names`) leaves them 1 vs. 0 here and is
            // otherwise invisible to this test, since neither
            // `infer_type` nor the restore path reads `local_names`.
            let inside = ctx.with_mvar_context(mvar_id, |ctx| {
                let _ = ctx.lctx_checkpoint();
                ctx.infer_type(x).is_ok()
            });
            assert!(inside, "the metavariable's context still has the binder");
            // And the ambient context is restored afterwards.
            assert!(
                ctx.infer_type(x).is_err(),
                "the ambient context was restored on the way out"
            );
        });
    }

    /// oracle: `MVarId.withContext` → `withLocalContextImp`
    /// (`Basic.lean:2002-2004`) swaps `lctx` AND `localInstances`
    /// together. A metavariable minted under an instance binder must see
    /// that instance when its own context is reinstalled — otherwise a
    /// postponed goal resumed after its binder closed would synthesize
    /// against a strictly smaller instance set than the oracle's.
    #[test]
    fn with_mvar_context_reinstalls_local_instances() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let n = const_named(ctx, "N");

            // Mint a metavariable UNDER an instance binder.
            let cp = ctx.lctx_checkpoint();
            ctx.push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push");
            let (_, m) = ctx.mk_aux_mvar(n).expect("mvar");
            ctx.lctx_restore(cp);

            // Back at top level, nothing is in scope.
            assert!(
                ctx.local_instances.entries().is_empty(),
                "the binder closed, so its instance is out of scope here"
            );

            // Inside the metavariable's own context, it is.
            let seen = ctx.with_mvar_context(m, |c| c.local_instances.entries().len());
            assert_eq!(
                seen, 1,
                "the mvar's recorded context carries the instance that was \
                 in scope when it was minted"
            );

            // And the caller's context is restored on the way out.
            assert!(ctx.local_instances.entries().is_empty());
        });
    }

    /// `reduced` erases an fvar from the context; its local instance must
    /// go with it — and ONLY it. oracle: `reduceLocalContext`
    /// (`MetavarContext.lean:1065-1067`) removes the decl, and an
    /// instance whose fvar is no longer declared is a dangling reference
    /// that `get_instances` would offer as a candidate.
    ///
    /// TWO instance binders are pushed, and only one is erased, so this
    /// discriminates selective filtering from wholesale clearing — the
    /// same shape as `reduced_drops_the_named_fvars_from_both_halves`
    /// (`local_snapshot.rs`), which uses three fvars and erases only one
    /// for the identical reason. A version of `reduced` that replaced
    /// the instance filter with an unconditional `Vec::new()` would
    /// still pass a single-instance fixture; it cannot pass this one,
    /// since `inst_b`'s instance must survive.
    #[test]
    fn reduced_drops_only_the_local_instance_of_the_erased_fvar() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let cp = ctx.lctx_checkpoint();
            let inst_a = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push inst_a");
            let inst_b = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push inst_b");
            let snap = ctx.current_lctx();
            ctx.lctx_restore(cp);

            assert_eq!(
                snap.local_instances().len(),
                2,
                "both instance binders were pushed"
            );

            let id_of = |ctx: &MetaCtx, e| match ctx.node(e) {
                Node::FVar { id: Some(id) } => id,
                other => panic!("expected fvar, got {other:?}"),
            };
            let id_a = id_of(ctx, inst_a);

            // Erase only inst_a's declaration.
            let reduced = snap.reduced(&[(inst_a, id_a)], |f| match ctx.node(f) {
                Node::FVar { id } => id,
                _ => None,
            });
            assert_eq!(
                reduced.local_instances().len(),
                1,
                "erasing inst_a's declaration must erase its local instance too — \
                 an instance pointing at an undeclared fvar is a candidate \
                 `get_instances` would hand to the search"
            );
            assert!(
                reduced.local_instances().iter().all(|li| li.fvar != inst_a),
                "the erased instance (inst_a) must not survive"
            );
            assert!(
                reduced.local_instances().iter().any(|li| li.fvar == inst_b),
                "the untouched instance (inst_b) must survive — proves the \
                 filter is selective by `to_remove`, not a wholesale clear"
            );
        });
    }
    /// `reduced` erases a decl from the MIDDLE of `lctx`, and
    /// `LocalContext::erase` (`leanr_kernel/src/local_ctx.rs`) reindexes
    /// every later decl down by one. A surviving instance's `at_depth` —
    /// by its own definition "the index of its own declaration in
    /// `lctx.decls`" (`local_instance.rs`) — therefore has to be
    /// recomputed against the FILTERED decl list, or it names a position
    /// past the end of the context it now travels with.
    ///
    /// The discriminating shape is an ORDINARY (non-class) binder in
    /// FRONT of the instance binder, and only the ordinary one erased:
    /// the instance is recorded at depth 1, the reduced context has one
    /// decl, and a stale `at_depth = 1` is `>=` every checkpoint that
    /// context can produce. So the first ordinary telescope opened under
    /// the installed snapshot — `lctx_checkpoint` / `push_local_decl` /
    /// `lctx_restore`, which is what `local_instance_candidate` and
    /// `forall_bounded_telescope` both do — silently pops a still-in-scope
    /// local instance, and `get_instances` stops offering it for the rest
    /// of the window. Nothing errors; the answer just gets smaller.
    ///
    /// `reduced_drops_only_the_local_instance_of_the_erased_fvar` above
    /// cannot catch this: it erases the FIRST of two instance binders,
    /// so the survivor's recorded depth (1) coincides with the count of
    /// decls it followed in the ORIGINAL context, and it never installs
    /// the result.
    #[test]
    fn reduced_renumbers_a_surviving_instances_depth() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let n = const_named(ctx, "N");

            let cp = ctx.lctx_checkpoint();
            // depth 0: an ordinary binder, no local instance.
            let plain = ctx
                .push_local_decl(None, n, BinderInfo::Default)
                .expect("push plain");
            // depth 1: the instance binder whose entry must survive.
            let inst = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push inst");
            let snap = ctx.current_lctx();
            ctx.lctx_restore(cp);

            let id_of = |ctx: &MetaCtx, e| match ctx.node(e) {
                Node::FVar { id: Some(id) } => id,
                other => panic!("expected fvar, got {other:?}"),
            };
            let id_plain = id_of(ctx, plain);

            // Erase ONLY the ordinary binder in front of the instance.
            let reduced =
                std::sync::Arc::new(snap.reduced(&[(plain, id_plain)], |f| match ctx.node(f) {
                    Node::FVar { id } => id,
                    _ => None,
                }));
            assert_eq!(reduced.entries().len(), 1, "one decl erased, one survivor");
            assert_eq!(
                reduced.local_instances().len(),
                1,
                "the instance's own decl was not erased, so it survives"
            );
            assert_eq!(
                reduced.local_instances()[0].fvar,
                inst,
                "and it is the instance binder's own entry"
            );
            assert_eq!(
                reduced.local_instances()[0].at_depth,
                0,
                "the survivor is now the FIRST decl of the reduced context, \
                 so its recorded depth must be 0 — keeping the original 1 \
                 names a decl index the reduced context does not have"
            );

            // The consequence, stated as behavior rather than as a field
            // value: install the reduced snapshot and open one ordinary
            // telescope under it, exactly as `local_instance_candidate`
            // does for every candidate.
            let saved = ctx.install_lctx(reduced);
            let inner = ctx.lctx_checkpoint();
            ctx.push_local_decl(None, n, BinderInfo::Default)
                .expect("push inside");
            ctx.lctx_restore(inner);
            let survivors = ctx.local_instances.entries().len();
            ctx.install_lctx(saved);

            assert_eq!(
                survivors, 1,
                "the local instance is still in scope after a telescope \
                 opened and closed under it — with a stale `at_depth` the \
                 restore's `truncate_to` pops it and `get_instances` \
                 silently stops offering it"
            );
        });
    }
}
