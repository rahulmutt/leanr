//! All shared `MetaM` state. Each concern module (`whnf`, `infer`, ...)
//! contributes an `impl MetaCtx` block — inherent impls split across
//! files, direct calls, no dynamic dispatch (spec § MetaCtx).
//!
//! Traversal is ExprId-native over the bank, the `tc.rs` idiom: nodes
//! decode one level at a time via `Store::expr_node`, caches key on
//! ids, and `Store::to_expr` is never called on a hot path.

use std::collections::HashMap;

use leanr_kernel::abstract_fvars;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId, Store};
use leanr_kernel::{
    BinderInfo, EnvView, ExprData, FVarIdGen, LocalContext, RecGuard, MAX_REC_DEPTH,
};
use leanr_olean::{
    DefaultInstanceEntry, EntryScope, InstanceEntry, MatcherEntry, ProjectionFnInfo,
    ReducibilityEntry, ReducibilityStatus,
};

use crate::instances::InstanceTable;
use crate::{Config, LMVarId, MVarId, MetaError, MetavarContext, TransparencyMode};

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
    /// `push_local_decl` call (`None` name for an anonymous binder, kept
    /// so the two stay 1:1 in length). Exists ONLY because
    /// `LocalContext`'s `decls`/`index` fields are private even within
    /// `leanr_kernel` (module-private to `local_ctx.rs`) — the kernel's
    /// own public surface is `get(fvar_id)` (by id) and `save`/`restore`
    /// (by count), no by-name scan, and adding one to `LocalContext`
    /// itself would touch the byte-untouched kernel TCB. Every OTHER
    /// internal `self.lctx.mk_local_decl`/`mk_let_decl`/`save`/`restore`
    /// call site (`infer.rs`, `whnf.rs`, `assign.rs`, `defeq.rs`) already
    /// brackets its own additions with an unconditional restore before
    /// returning to its caller (the same `save -> push -> restore` stack
    /// discipline this field's own `lctx_checkpoint`/`lctx_restore`
    /// pairing uses), so `lctx.decls.len()` net-changes, across any span
    /// bracketed by `lctx_checkpoint`/`lctx_restore`, ONLY via
    /// `push_local_decl` — which is this field's sole writer too. The two
    /// therefore stay in lockstep, and `lctx_restore`'s existing
    /// `checkpoint: usize` (already `lctx.save()`'s own return value)
    /// doubles as this field's truncation point with no second
    /// checkpoint API. See `lctx_lookup_by_name` (the reader) below.
    pub(crate) local_names: Vec<(Option<NameId>, ExprId)>,
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

impl<'e> MetaCtx<'e> {
    /// Task B6 adds the 8th (`projection_fn_entries`) decoded-slice
    /// parameter, crossing clippy's default `too_many_arguments`
    /// threshold (7) — same "decoded slices in, private fields out"
    /// constructor shape B3's `instance_entries`/`default_instance_entries`
    /// pair already established (this module's own doc, above); adding a
    /// 9th builder/options-struct layer here would be a bigger refactor
    /// than this task's own scope, for a constructor that already has
    /// exactly one call style (every call site passes all eight slices
    /// positionally, `grep`-verified, no partial-application anywhere).
    ///
    /// **Follow-up, explicitly flagged (opus review round 1): the NEXT
    /// decoded extension makes this 9.** At that point, stop widening
    /// this positional list and instead introduce a `DecodedExtensions`
    /// (or similarly named) params struct bundling every
    /// `&[XyzEntry]` slice this constructor takes, with each call site
    /// building one from a `ModuleData` (`md.reducibility`, `md.matchers`,
    /// ..., `md.projection_fns`, ...) — a mechanical, low-risk refactor
    /// deferred out of THIS task's scope, not an open question about
    /// whether it should happen.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        view: EnvView<'e>,
        scratch: &'e mut Store,
        cfg: Config,
        reducibility: &[ReducibilityEntry],
        matchers: &[MatcherEntry],
        instance_entries: &[InstanceEntry],
        default_instance_entries: &[DefaultInstanceEntry],
        projection_fn_entries: &[ProjectionFnInfo],
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
        let instances = InstanceTable::build(view, instance_entries, default_instance_entries);
        // oracle: `projectionFnInfoExt`'s own `NameMap` (`ProjFns.lean:30,
        // 37-59`) — the extension's own key IS `ProjectionFnInfo.projFn`
        // (see that struct's doc, `leanr_olean::ProjectionFnInfo`), so no
        // filtering/dedup decision is needed here beyond keying by it;
        // a real `.olean` never registers the same projection fn name
        // twice (`mkMapDeclarationExtension`'s own map semantics), so a
        // colliding second entry (last-write-wins) is reachable only via
        // adversarial/malformed bytes, same untrusted-input posture as
        // every other decoder in this crate (never panics either way).
        let projection_fns = projection_fn_entries
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
        debug_assert_eq!(
            self.local_names.len(),
            self.lctx.save(),
            "local_names/lctx lockstep invariant violated"
        );
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
        Ok(fvar)
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
    fn mk_binding(
        &mut self,
        is_lambda: bool,
        fvars: &[ExprId],
        body: ExprId,
    ) -> Result<ExprId, MetaError> {
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
                    (decl.binder_name, decl.ty, decl.binder_info)
                }
                _ => {
                    return Err(MetaError::Infer(
                        "mk_binding: telescope entry is not an fvar".into(),
                    ))
                }
            };
            let ty2 = abstract_fvars(
                self.scratch,
                Some(self.view.store),
                ty,
                &fvars[..i],
                &mut self.guard,
            )?;
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

    pub(crate) fn checkpoint(&self) -> MetaSnapshot {
        let (expr_assignments, level_assignments) = self.mctx.snapshot_assignments();
        MetaSnapshot {
            expr_assignments,
            level_assignments,
            postponed: self.postponed.clone(),
        }
    }

    pub(crate) fn rollback(&mut self, snap: MetaSnapshot) {
        self.mctx
            .restore_assignments(snap.expr_assignments, snap.level_assignments);
        self.postponed = snap.postponed;
    }
}

/// A save point for `checkpointDefEq` (oracle Basic.lean:2438). Holds
/// exactly what a failed trial unification must restore: the expr and
/// level assignment maps and the postponed queue. NOT the permanent
/// cache (it is monotone and shared) and NOT declarations (an mvar stays
/// declared).
///
/// `Clone` (task B5): the tabled-synthesis driver stores one snapshot
/// PER NODE (the oracle's own `GeneratorNode.mctx`/`ConsumerNode.mctx`
/// fields, `SynthInstance.lean:49`/`:57`) and re-enters it repeatedly
/// via a `withMCtx`-equivalent, so it must be able to restore the same
/// snapshot more than once — `rollback` consumes its argument.
#[derive(Clone)]
pub(crate) struct MetaSnapshot {
    expr_assignments: HashMap<MVarId, ExprId>,
    level_assignments: HashMap<LMVarId, LevelId>,
    postponed: Vec<(LevelId, LevelId)>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{const_named, with_ctx, with_prelude0_ctx};
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
        use crate::{MVarDecl, MVarId, MVarKind};
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
                    lctx: Default::default(),
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
}
