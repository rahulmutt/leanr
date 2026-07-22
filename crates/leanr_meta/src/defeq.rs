//! `is_def_eq` — the elaborator's definitional equality (spec plan 3).
//!
//! oracle: `Lean/Meta/ExprDefEq.lean` + `Lean/Meta/Basic.lean`,
//! toolchain leanprover/lean4:v4.33.0-rc1. NOT the kernel's `is_def_eq`
//! (`leanr_kernel::tc`): this one is over open terms, mvar-assigning
//! (task 5+), transparency-gated, and DELIBERATELY INCOMPLETE where the
//! oracle itself is (the `*_approx` flags, `isDefEqStuck`). Lean's
//! source is the specification; every arm below cites the exact region
//! read from the pinned toolchain (never transcribed from memory).
//!
//! # This task's slice of the ladder
//!
//! The full ladder (`isExprDefEqAuxImpl`, ExprDefEq.lean:2285) is:
//! `checkpointDefEq` wrapper -> `isDefEqQuick` (structural + mvar fast
//! paths) -> `isDefEqProofIrrel` -> `whnfCoreAtDefEq` both sides
//! (`proj := yesWithDeltaI`), recurse if either changed ->
//! `instantiateMVars` -> defeq cache -> `isExprDefEqExpensive` (eta,
//! proj, whnfCore-again, native/nat/offset/delta, eta-struct,
//! const-levels/app-args congruence, projInst/stringLit/unitLike,
//! onFailure).
//!
//! Tasks 1-3 built ONLY: the `checkpointDefEq` wrapper (task 2's
//! `checkpoint`/`rollback`/`postponed`), `isDefEqQuick`'s structural
//! leaf cases, the `whnfCoreAtDefEq` loop, and `isExprDefEqExpensive`'s
//! **congruence** arms (Const-with-equal-levels, App head+args,
//! Lam/Forall binder congruence, Sort). Tasks 4-5 added level defeq and
//! expr-mvar assignment. **Task 6** (this task) fills every arm that
//! still needed reduction: `isDefEqProofIrrel` (wired in
//! [`MetaCtx::is_def_eq_core`] below), and `isExprDefEqExpensive`'s
//! eta/eta-struct/proj/native/nat/offset/delta/projInst/stringLit/
//! unitLike arms (wired in [`MetaCtx::is_def_eq_expensive`] below) —
//! all actually IMPLEMENTED in `lazy_delta.rs`, except `isDefEqNative`/
//! `isDefEqOffset` (permanently/plan-3 named seams, `isDefEqProjInst`
//! (class-projection registry, undecoded everywhere in this crate) and
//! `isDefEqOnFailure` (unification hints, task 7), both cited at their
//! call site below and never silently dropped.
//!
//! # A transcription correction (brief vs. pinned source)
//!
//! The task brief filed Lam/Forall binder congruence under
//! `isExprDefEqExpensive`. Reading the pinned source shows this is
//! wrong: the real `isExprDefEqExpensive` (ExprDefEq.lean:2205-2232)
//! has NO Lam/Forall arm at all — binder congruence is decided
//! entirely inside `isDefEqQuick` itself (`.lam .., .lam ..` /
//! `.forallE .., .forallE ..`, ExprDefEq.lean:1827-1828, via
//! `isDefEqBinding`/`isDefEqBindingAux`, :459-477). This module places
//! it in [`MetaCtx::is_def_eq_quick`] to match; see
//! [`MetaCtx::is_def_eq_binding_shallow`]'s doc comment for a second
//! correction (binder-info equality is NOT part of the real check —
//! `isDefEqBindingAux` never compares it) and for how this task's
//! simplified single-binder fvar substitution relates to the oracle's
//! full telescope.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::{instantiate, BinderInfo};

use crate::{MetaCtx, MetaError, ProjReduction};

impl<'e> MetaCtx<'e> {
    /// oracle: `isDefEq`/`isExprDefEq` (Basic.lean:2474-2509) +
    /// `checkpointDefEq` (:2438-2461). Clears the transient cache,
    /// resets postponed, runs the core, and on success processes +
    /// merges postponed; on failure or throw, rolls back.
    ///
    /// One oracle step is deliberately NOT ported here: the `defEqCtx?`
    /// reader bump (:2475-2476), elaborator-context this crate does not
    /// model.
    ///
    /// `resetDefEqPermCaches` (Basic.lean:2477-2495) IS ported, right
    /// below: `self.defeq_cache_perm.clear()`. Fix-wave-1 (Critical
    /// finding on task 8): the permanent-cache eligibility check
    /// (`getDefEqCacheKind`, ExprDefEq.lean:2238-2242, transcribed at
    /// `cache.rs::defeq_cache_kind`) tests only `hasMVar` on `t`/`s`,
    /// never `hasFVar`. That is sound ONLY under the compensating reset
    /// here: an mvar-free `t`/`s` pair can still MENTION an fvar whose
    /// *declared type* in `self.lctx` contains an unassigned mvar `?m`.
    /// A permanent-cache entry for that pair is a verdict computed
    /// under the CURRENT assignment of `?m`; once `?m` gets assigned (a
    /// different `MCtx` state), the identical `(config, t, s)` key would
    /// otherwise serve the STALE pre-assignment verdict on a later
    /// top-level call over the same, reused `MetaCtx` — a wrong verdict,
    /// possibly a wrong `true`. fvar *identity* is permanent in this
    /// crate (`FVarId`s are never reused/mutated, per `cache.rs`'s own
    /// module doc), but fvar *meaning under instantiation* is not, and
    /// that is exactly the oracle's own rationale for
    /// `resetDefEqPermCaches` (Basic.lean:2477-2495: "the map may
    /// contain entries taking for granted a different local context /
    /// assignment"). Clearing it here — at the TOP-LEVEL wrapper only,
    /// never inside the recursive `is_def_eq_core` below — resets the
    /// permanent cache between top-level `is_def_eq` calls (matching
    /// the oracle) while still letting entries populated earlier in
    /// THIS SAME query tree be reused for the rest of it (the
    /// memoization the permanent cache exists for).
    pub fn is_def_eq(&mut self, t: ExprId, s: ExprId) -> Result<bool, MetaError> {
        let snap = self.checkpoint();
        self.defeq_cache_transient.clear();
        self.defeq_cache_perm.clear();
        let saved_postponed = std::mem::take(&mut self.postponed);
        match self.is_def_eq_core(t, s) {
            Ok(true) => {
                if self.process_postponed()? {
                    // merge saved + newly-postponed (level.rs's real
                    // `process_postponed`, task 4).
                    let mut merged = saved_postponed;
                    merged.append(&mut self.postponed);
                    self.postponed = merged;
                    Ok(true)
                } else {
                    self.rollback(snap);
                    Ok(false)
                }
            }
            Ok(false) => {
                self.rollback(snap);
                Ok(false)
            }
            Err(e) => {
                self.rollback(snap);
                Err(e)
            }
        }
    }

    /// oracle: `isExprDefEqAuxImpl` (ExprDefEq.lean:2285-2354). The
    /// `instantiateMVars` + defeq-cache stage (:2333-2354) is wired in
    /// task 8 (`cache.rs`): `instantiateMVars` both sides, look up the
    /// permanent/transient cache (`defeq_cache_kind`/`cache_lookup`),
    /// and on a miss run `is_def_eq_expensive` and store the result
    /// (`cache_store`) ONLY IF the postponed-constraint count did not
    /// change across that call (oracle: `numPostponed == (←
    /// getNumPostponed)`, :2350-2353) — a verdict that leaned on a NEW
    /// postponement is not yet grounded and must be recomputed next
    /// time, not served stale.
    ///
    /// `pub(crate)`, not private (task 5): `assign.rs::
    /// check_types_and_assign` calls this directly (not the
    /// checkpoint-wrapped `is_def_eq`) to avoid double-checkpointing a
    /// nested type comparison — see that function's own doc comment,
    /// which makes the identical point `level.rs::is_level_def_eq`'s
    /// doc comment makes about `isLevelDefEqAux` vs. `isLevelDefEq`.
    pub(crate) fn is_def_eq_core(&mut self, t: ExprId, s: ExprId) -> Result<bool, MetaError> {
        self.step()?;
        self.guarded(|ctx| {
            if let Some(b) = ctx.is_def_eq_quick(t, s)? {
                return Ok(b);
            }
            // oracle: `isDefEqProofIrrel` (ExprDefEq.lean:1766-1780) —
            // task 6, `lazy_delta.rs`.
            if let Some(b) = ctx.is_def_eq_proof_irrel(t, s)? {
                return Ok(b);
            }
            let t2 = ctx.whnf_core_at_defeq(t)?;
            let s2 = ctx.whnf_core_at_defeq(s)?;
            if t2 != t || s2 != s {
                return ctx.is_def_eq_core(t2, s2);
            }
            // oracle :2333-2335: `instantiateMVars` both sides before
            // the cache key is built (see also `cache.rs::cache_store`'s
            // own doc comment for why the TRANSIENT branch instantiates
            // a second time, after `is_def_eq_expensive` below).
            let t3 = ctx.instantiate_mvars(t2)?;
            let s3 = ctx.instantiate_mvars(s2)?;
            // oracle :2336-2338: `mkCacheKey` + `getCachedResult`.
            let kind = ctx.defeq_cache_kind(t3, s3);
            if let Some(cached) = ctx.cache_lookup(kind, t3, s3) {
                return Ok(cached);
            }
            // oracle :2347-2354: the postponed-count guard. A verdict
            // that relied on a NEW postponed constraint during the
            // expensive call is not yet grounded, so it is returned but
            // never cached.
            let num_postponed = ctx.postponed.len();
            let result = ctx.is_def_eq_expensive(t3, s3)?;
            if ctx.postponed.len() == num_postponed {
                ctx.cache_store(kind, t3, s3, result)?;
            }
            Ok(result)
        })
    }

    /// oracle: `whnfCoreAtDefEq` (ExprDefEq.lean:2277-2281): `whnfCore`
    /// with `proj := yesWithDeltaI` for this reduction only (the
    /// `backward.isDefEq.lazyWhnfCore` option gate is not modeled —
    /// this crate has no options table; its `else` branch, plain
    /// `whnfCore`, is the one behavior it would always take if the
    /// option WERE read, so the omission changes nothing observable).
    fn whnf_core_at_defeq(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let saved = self.cfg.proj;
        self.cfg.proj = ProjReduction::YesWithDeltaI;
        let r = self.whnf_core(e);
        self.cfg.proj = saved;
        r
    }

    /// oracle: `isDefEqQuick` / `isDefEqQuickOther` (ExprDefEq.lean:
    /// 1819-1927). This task's subset: pointer equality, same-shape
    /// leaf decisions (`Lit`, `BVar`/`BVarBig`, `Sort` via structural
    /// level compare, `Const` via name + structural level compare),
    /// and Lam/Forall binder congruence. Returns `Ok(None)` to
    /// escalate to `is_def_eq_core`'s `whnf_core` loop, exactly like
    /// the oracle's `LBool.undef`.
    ///
    /// Two placements here are a task-3 SHORTCUT, not literal oracle
    /// structure (see the module doc's transcription-correction note
    /// for why they still are not WRONG):
    /// - `BVar`/`BVarBig`, `Const`: the real `isDefEqQuick` does not
    ///   special-case either — a same-index bvar pair or a same-name/
    ///   same-levels const pair is ALREADY caught by the leading
    ///   `t == s` check (`ExprId`s are hash-consed: identical index /
    ///   identical name+levels interns to the identical `ExprId`), and
    ///   a MISMATCHED pair otherwise falls through
    ///   `isDefEqQuickOther`'s generic mvar-head dispatch to `.undef`
    ///   (:1873, `if !tFn.isMVar && !sFn.isMVar then return
    ///   LBool.undef`) — decided later by `isExprDefEqExpensive`'s
    ///   Const-congruence arm (:2225-2226) for Const, or (for a bvar
    ///   pair, which can never reduce further) by simply never
    ///   matching either congruence arm there and falling to `false`.
    ///   Deciding both directly here just skips a no-op `whnf_core`
    ///   round trip; the verdict is identical either way.
    /// - Lam/Forall: real oracle location, see module doc.
    ///
    /// `pub(crate)`, not private (task 5): `assign.rs::is_def_eq_mvar`
    /// (the oracle's `isDefEqQuickOther`, this function's own catch-all
    /// arm below) re-enters this SAME function after instantiating an
    /// already-assigned mvar-headed side (oracle: `isAssigned tFn =>
    /// let t ← instantiateMVars t; isDefEqQuick t s`), a genuine mutual
    /// recursion across the module boundary.
    pub(crate) fn is_def_eq_quick(
        &mut self,
        t: ExprId,
        s: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        if t == s {
            return Ok(Some(true));
        }
        match (self.node(t), self.node(s)) {
            (Node::LitNat { v: v1 }, Node::LitNat { v: v2 }) => Ok(Some(v1 == v2)),
            (Node::LitStr { v: v1 }, Node::LitStr { v: v2 }) => Ok(Some(v1 == v2)),
            (Node::BVar { idx: i1 }, Node::BVar { idx: i2 }) => Ok(Some(i1 == i2)),
            (Node::BVarBig { idx: i1 }, Node::BVarBig { idx: i2 }) => Ok(Some(i1 == i2)),
            (Node::Sort { level: l1 }, Node::Sort { level: l2 }) => {
                // oracle: the real `.sort u, .sort v` arm calls
                // `isLevelDefEqAux` (LevelDefEq.lean) — task 4's
                // `is_level_def_eq`, a DECISIVE procedure (always true
                // or false, possibly after postponing), so this never
                // needs to escalate/punt.
                Ok(Some(self.is_level_def_eq(l1, l2)?))
            }
            (
                Node::Const {
                    name: n1,
                    levels: ls1,
                },
                Node::Const {
                    name: n2,
                    levels: ls2,
                },
            ) => {
                if n1 != n2 {
                    // Name mismatch escalates to is_def_eq_expensive,
                    // where isDefEqDelta (ExprDefEq.lean:2217) runs BEFORE
                    // the const-congruence arm (:2225-2226), allowing
                    // delta-equal distinct-named consts (e.g. `def a := b`)
                    // to still unify. Task 7 (delta) will implement this;
                    // until then, is_def_eq_expensive returns false for
                    // distinct names, as correct.
                    Ok(None)
                } else {
                    // oracle: `isListLevelDefEqAux` (task 4's
                    // `is_def_eq_levels`) — decisive, so this never
                    // needs to escalate/punt on a levels mismatch.
                    let us = self
                        .scratch
                        .level_list_at(Some(self.view.store), ls1)
                        .to_vec();
                    let vs = self
                        .scratch
                        .level_list_at(Some(self.view.store), ls2)
                        .to_vec();
                    Ok(Some(self.is_def_eq_levels(&us, &vs)?))
                }
            }
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
            ) => Ok(Some(self.is_def_eq_binding_shallow(d1, b1, d2, b2)?)),
            // oracle: `isDefEqQuick`'s own `| t, s => isDefEqQuickOther
            // t s` fallthrough (:1841) — task 5's `assign.rs::
            // is_def_eq_mvar` (the mvar-headed-application dispatch:
            // detects `t`/`s` via `get_app_fn`, not just a literal top-
            // level `MVar` node, since `?m a1 .. an` must be recognized
            // even though its own top node is `App`).
            _ => self.is_def_eq_mvar(t, s),
        }
    }

    /// oracle: `isDefEqBinding`/`isDefEqBindingAux` (ExprDefEq.lean:
    /// 459-477). Domain compared before body, matching the oracle's
    /// order.
    ///
    /// TWO corrections/simplifications vs. the literal source, both
    /// deliberate for this task's scope:
    /// - Binder-info equality is NOT checked: the real
    ///   `isDefEqBindingAux` never compares it (`.lam n d1 b1 _, .lam _
    ///   d2 b2 _` — the trailing `_` discards BOTH sides' info). It
    ///   affects elaboration/pretty-printing only, never definitional
    ///   equality. (The brief's "binder-info equal" wording was wrong;
    ///   fixed here.)
    /// - The real algorithm opens a full fvar TELESCOPE across a chain
    ///   of same-kind binders, instantiating each later domain against
    ///   every earlier fvar before it ever recurses on the bodies
    ///   (`isDefEqBindingAux`'s own loop, :459-472). This task opens
    ///   exactly ONE fresh fvar per call (for THIS binder alone) and
    ///   recurses via `is_def_eq_core` on the substituted bodies — a
    ///   nested Lam/Forall inside those bodies gets its OWN fresh fvar
    ///   from a NEW call to this same function, one recursion level
    ///   at a time, rather than one accumulated telescope. This is
    ///   semantically equivalent for the shapes this task's fixtures
    ///   exercise (no domain in a later binder depends on an
    ///   assignment made while checking an earlier one — there is no
    ///   assignment yet at all, task 5's job) and, critically, it is
    ///   SAFE: substituting a real fvar for the bound variable BEFORE
    ///   recursing means `is_def_eq_core`/`whnf_core` never meet a raw
    ///   loose bvar (which `whnf_easy_cases`, whnf.rs, legitimately
    ///   treats as ill-formed input and errors on) — e.g. a body like
    ///   `f x` (the bound `x` as an application ARGUMENT is fine, but
    ///   `x arg`, the bound variable as an application HEAD, is a
    ///   completely ordinary shape that a naive raw-bvar recursion
    ///   would crash on, since `whnf_core`'s app case peels the spine
    ///   down to its head and calls `whnf_core` on THAT directly).
    fn is_def_eq_binding_shallow(
        &mut self,
        d1: ExprId,
        b1: ExprId,
        d2: ExprId,
        b2: ExprId,
    ) -> Result<bool, MetaError> {
        if !self.is_def_eq_core(d1, d2)? {
            return Ok(false);
        }
        let checkpoint = self.lctx.save();
        let r = self.is_def_eq_binding_shallow_body(d1, b1, b2);
        self.lctx.restore(checkpoint);
        r
    }

    fn is_def_eq_binding_shallow_body(
        &mut self,
        d1: ExprId,
        b1: ExprId,
        b2: ExprId,
    ) -> Result<bool, MetaError> {
        // `binder_name`/`binder_info` are inert placeholders on this
        // fvar's own decl: neither is ever consulted by `is_def_eq`
        // (see this function's doc comment on binder-info), so a
        // fixed `None`/`Default` is exactly as faithful as threading
        // either side's real value through.
        let fvar = self.lctx.mk_local_decl(
            self.scratch,
            Some(self.view.store),
            &mut self.fvar_gen,
            None,
            d1,
            BinderInfo::Default,
        )?;
        let ib1 = instantiate(
            self.scratch,
            Some(self.view.store),
            b1,
            fvar,
            &mut self.guard,
        )?;
        let ib2 = instantiate(
            self.scratch,
            Some(self.view.store),
            b2,
            fvar,
            &mut self.guard,
        )?;
        self.is_def_eq_core(ib1, ib2)
    }

    /// oracle: `isExprDefEqExpensive` (ExprDefEq.lean:2205-2232). Task 6
    /// fills every arm tasks 3-5 left as a named seam — eta (both
    /// directions), projection, the post-eta/proj `whnfCore` recheck,
    /// native/nat/offset/delta, structure eta (both directions) — all
    /// actually implemented in `lazy_delta.rs` except `isDefEqNative`/
    /// `isDefEqOffset`, which stay NAMED SEAMS wired below (never
    /// silently skipped from the sequence — see their own doc comments
    /// in `lazy_delta.rs`). Unchanged from task 3: Const/Const
    /// (:2225-2226) and App/App via `isDefEqApp`'s spine walk
    /// (:2166-2178, simplified). Two arms remain named-but-uncommitted
    /// seams at their call site below, both because the class-
    /// projection registry they would need is undecoded EVERYWHERE
    /// else in this crate too (`whnf.rs`'s own
    /// `unfold_proj_inst_when_instances`/`get_stuck_mvar` notes):
    /// - `isDefEqProjInst` (:2229, `unfoldProjInstWhenInstances?`-gated,
    ///   `.instances`/`.implicit` transparency only).
    /// - `isDefEqOnFailure` (:2232, unification hints :2022-2028) —
    ///   task 7.
    ///
    /// (A `Sort`/`Sort` pair never reaches this function at all, as of
    /// task 4: `is_def_eq_quick`'s `.sort` arm calls the DECISIVE
    /// `is_level_def_eq`, matching the real `isDefEqQuick`, which
    /// always fully resolves `Sort` before `isExprDefEqExpensive` ever
    /// runs.)
    fn is_def_eq_expensive(&mut self, t: ExprId, s: ExprId) -> Result<bool, MetaError> {
        // oracle :2206-2207: `whenUndefDo (isDefEqEta t s) do whenUndefDo
        // (isDefEqEta s t) do ..`.
        if let Some(b) = self.is_def_eq_eta(t, s)? {
            return Ok(b);
        }
        if let Some(b) = self.is_def_eq_eta(s, t)? {
            return Ok(b);
        }
        // oracle :2208: `if (← isDefEqProj t s) then return true`.
        if self.is_def_eq_proj(t, s)? {
            return Ok(true);
        }
        // oracle :2209-2212: a second plain `whnfCore` round, recursing
        // if either side changed. Now a REAL second pass (unlike tasks
        // 3-5's scope cut): delta/eta/proj above can all still leave a
        // `whnfCore`-reducible shape behind.
        let t2 = self.whnf_core(t)?;
        let s2 = self.whnf_core(s)?;
        if t2 != t || s2 != s {
            return self.is_def_eq_core(t2, s2);
        }
        // oracle :2214: `isDefEqNative` — permanent seam.
        if let Some(b) = self.is_def_eq_native(t2, s2)? {
            return Ok(b);
        }
        // oracle :2215: `isDefEqNat`.
        if let Some(b) = self.is_def_eq_nat(t2, s2)? {
            return Ok(b);
        }
        // oracle :2216: `isDefEqOffset` — plan-3 seam.
        if let Some(b) = self.is_def_eq_offset(t2, s2)? {
            return Ok(b);
        }
        // oracle :2217: `isDefEqDelta` — the heart of this task.
        if let Some(b) = self.is_def_eq_delta(t2, s2)? {
            return Ok(b);
        }
        // oracle :2219-2221: structure eta, tried AFTER lazy delta
        // (oracle's own comment: trying it earlier would fire at every
        // step of a reduction chain as soon as one side is a
        // constructor application).
        if self.is_def_eq_eta_struct(t2, s2)? || self.is_def_eq_eta_struct(s2, t2)? {
            return Ok(true);
        }
        match (self.node(t2), self.node(s2)) {
            (
                Node::Const {
                    name: n1,
                    levels: ls1,
                },
                Node::Const {
                    name: n2,
                    levels: ls2,
                },
            ) => {
                if n1 != n2 {
                    Ok(false)
                } else {
                    // oracle: `isListLevelDefEqAux` (task 4's
                    // `is_def_eq_levels`), same as the `is_def_eq_quick`
                    // Const arm above.
                    let us = self
                        .scratch
                        .level_list_at(Some(self.view.store), ls1)
                        .to_vec();
                    let vs = self
                        .scratch
                        .level_list_at(Some(self.view.store), ls2)
                        .to_vec();
                    self.is_def_eq_levels(&us, &vs)
                }
            }
            (Node::App { .. }, Node::App { .. }) => {
                let t_fn = self.get_app_fn(t2);
                let s_fn = self.get_app_fn(s2);
                if !self.is_def_eq_core(t_fn, s_fn)? {
                    return Ok(false);
                }
                let t_args = self.get_app_args(t2);
                let s_args = self.get_app_args(s2);
                // oracle: `isDefEqApp` (:2166-2178) delegates arg
                // comparison to `isDefEqArgs` (:371-421) — task 5's
                // `assign.rs::is_def_eq_args` (extracted from this
                // arm's own former inline pairwise walk so
                // `isDefEqMVarSelf` can share it too, per that
                // function's own citation).
                self.is_def_eq_args(t_fn, &t_args, &s_args)
            }
            // oracle :2229-2231, reached only when `t`/`s` are neither
            // both `Const` nor both `App` (the real oracle's own
            // `if .. then .. else if .. isDefEqApp .. else ..`
            // structure, ExprDefEq.lean:2223-2231).
            _ => {
                // SEAM: isDefEqProjInst (:2229) — see this function's
                // own doc comment.
                if let Some(b) = self.is_def_eq_string_lit(t2, s2)? {
                    return Ok(b);
                }
                if self.is_def_eq_unit_like(t2, s2)? {
                    return Ok(true);
                }
                // SEAM: isDefEqOnFailure (:2232, unification hints) —
                // task 7.
                Ok(false)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::{fresh_fvar, with_ctx};

    #[test]
    fn reflexive_and_structural() {
        with_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap(); // Sort 0
            let s1u = ctx.scratch.level_succ(None, z).unwrap();
            let s1 = ctx.scratch.expr_sort(None, s1u).unwrap(); // Sort 1
            assert!(ctx.is_def_eq(s0, s0).unwrap()); // pointer-eq
            assert!(!ctx.is_def_eq(s0, s1).unwrap()); // Sort 0 != Sort 1
        });
    }

    #[test]
    fn beta_via_whnf_core() {
        with_ctx(|ctx| {
            // (fun (x : Sort 0) => x) Sort0  =?=  Sort0
            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap();
            let bv = ctx
                .scratch
                .expr_bvar(None, &leanr_kernel::Nat::from(0u64))
                .unwrap();
            let lam = ctx
                .scratch
                .expr_lam(None, None, s0, bv, leanr_kernel::BinderInfo::Default)
                .unwrap();
            let app = ctx.scratch.expr_app(None, lam, s0).unwrap();
            assert!(ctx.is_def_eq(app, s0).unwrap());
        });
    }

    /// Task 6 note: `A`/`B` are now real declared `Axiom`s, not bare
    /// undeclared `Const`s — `is_def_eq_proof_irrel` (task 6)
    /// unconditionally calls `infer_type` on every pair before any
    /// other rung runs, and a `Const` naming nothing in the environment
    /// is a genuinely malformed term to the oracle too (`getConstInfo`
    /// throws on an unknown name), not merely an inert placeholder the
    /// way it was while proof irrelevance was still a no-op seam.
    #[test]
    fn distinct_consts_are_not_def_eq() {
        use leanr_kernel::bank::Store;
        use leanr_kernel::{AxiomVal, ConstSource, ConstantInfo, ConstantVal, EnvView};

        let mut base = Store::persistent();
        let z = base.level_zero(None).unwrap();
        let sort0 = base.expr_sort(None, z).unwrap();
        let a_s = base.intern_str(None, "A").unwrap();
        let a_n = base.name_str(None, None, a_s).unwrap();
        let b_s = base.intern_str(None, "B").unwrap();
        let b_n = base.name_str(None, None, b_s).unwrap();
        let empty_levels = base.intern_level_list(None, &[]).unwrap();
        let a = base.expr_const(None, Some(a_n), empty_levels).unwrap();
        let b = base.expr_const(None, Some(b_n), empty_levels).unwrap();

        let mk_axiom = |name| {
            ConstantInfo::Axiom(AxiomVal {
                val: ConstantVal {
                    name,
                    level_params: vec![],
                    ty: sort0,
                },
                is_unsafe: false,
            })
        };
        let mut extra = std::collections::HashMap::new();
        extra.insert(a_n, mk_axiom(a_n));
        extra.insert(b_n, mk_axiom(b_n));

        let empty_consts = leanr_kernel::CheckedConstants::new(std::collections::HashMap::new());
        let view = EnvView {
            consts: ConstSource::Gated(&empty_consts),
            extra: Some(&extra),
            quot_initialized: false,
            store: &base,
        };
        let mut scratch = Store::scratch();
        let mut ctx = crate::MetaCtx::new(view, &mut scratch, crate::Config::default(), &[], &[]);
        assert!(!ctx.is_def_eq(a, b).unwrap());
    }

    /// Task 6 note: `f` is now a properly-declared fvar (via
    /// `fresh_fvar`, of a real `Forall` type), not a bare `Expr::fvar`
    /// reference with no backing `lctx` decl — `is_def_eq_proof_irrel`
    /// (task 6) calls `infer_type` on `lhs`/`rhs` (`f _`, an
    /// application) before any other rung runs, and that needs `f`'s
    /// OWN type to resolve `infer_app_type`'s `Forall` peel.
    #[test]
    fn app_congruence_recurses_into_args() {
        with_ctx(|ctx| {
            // f ((fun (x : Sort 0) => x) Sort0)  =?=  f Sort0 —
            // exercises App congruence (same head `f`) recursing via
            // is_def_eq_core into an arg pair that only agrees after a
            // beta reduction (whnf_core), not by pointer/structural
            // equality alone.
            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap();
            let f_ty = ctx
                .scratch
                .expr_forall(None, None, s0, s0, leanr_kernel::BinderInfo::Default)
                .unwrap();
            let f = fresh_fvar(ctx, f_ty, "f");

            let bv = ctx
                .scratch
                .expr_bvar(None, &leanr_kernel::Nat::from(0u64))
                .unwrap();
            let lam = ctx
                .scratch
                .expr_lam(None, None, s0, bv, leanr_kernel::BinderInfo::Default)
                .unwrap();
            let arg_lhs = ctx.scratch.expr_app(None, lam, s0).unwrap(); // (fun x => x) Sort0

            let lhs = ctx.scratch.expr_app(None, f, arg_lhs).unwrap();
            let rhs = ctx.scratch.expr_app(None, f, s0).unwrap();
            assert!(ctx.is_def_eq(lhs, rhs).unwrap());
        });
    }

    #[test]
    fn lam_congruence_opens_one_fvar_and_recurses_on_bodies() {
        with_ctx(|ctx| {
            // (fun (x : Sort 0) => x) vs (fun (x : Sort 0) => (fun y =>
            // y) x) — same domain; bodies only agree after whnf_core
            // reduces the RHS body's redex. Exercises
            // `is_def_eq_binding_shallow`'s fvar substitution: the
            // RHS body's own bound variable `x` (a bvar referencing the
            // OUTER binder, at the same depth as the inner lambda's
            // application) must be substituted correctly around the
            // untouched inner binder.
            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap();
            let bv0 = ctx
                .scratch
                .expr_bvar(None, &leanr_kernel::Nat::from(0u64))
                .unwrap();
            let lhs = ctx
                .scratch
                .expr_lam(None, None, s0, bv0, leanr_kernel::BinderInfo::Default)
                .unwrap();

            // inner (fun y => y) applied to bvar 0 (the outer `x`).
            let inner_lam = ctx
                .scratch
                .expr_lam(None, None, s0, bv0, leanr_kernel::BinderInfo::Default)
                .unwrap();
            let rhs_body = ctx.scratch.expr_app(None, inner_lam, bv0).unwrap();
            let rhs = ctx
                .scratch
                .expr_lam(None, None, s0, rhs_body, leanr_kernel::BinderInfo::Default)
                .unwrap();
            assert!(ctx.is_def_eq(lhs, rhs).unwrap());
        });
    }

    #[test]
    fn forall_binder_info_mismatch_still_def_eq() {
        with_ctx(|ctx| {
            // {x : Sort 0} -> Sort 0  vs  (x : Sort 0) -> Sort 0 —
            // differ ONLY in binder-info (implicit vs default); must
            // still be def-eq, pinning the module doc's correction
            // that binder-info is never part of the check.
            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap();
            let lhs = ctx
                .scratch
                .expr_forall(None, None, s0, s0, leanr_kernel::BinderInfo::Implicit)
                .unwrap();
            let rhs = ctx
                .scratch
                .expr_forall(None, None, s0, s0, leanr_kernel::BinderInfo::Default)
                .unwrap();
            assert!(ctx.is_def_eq(lhs, rhs).unwrap());
        });
    }

    #[test]
    fn forall_domain_mismatch_is_not_def_eq() {
        with_ctx(|ctx| {
            // (x : Sort 0) -> Sort 0  vs  (x : Sort 1) -> Sort 0 —
            // domains differ (and are not structurally-equal-level
            // Sorts), so binder congruence must reject the pair, not
            // fall through to a vacuous "bodies matched" true. Pins
            // that `is_def_eq_binding_shallow` actually threads `d2`
            // into the domain check (a real bug this test caught: the
            // first draft of this function silently dropped `d2`).
            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap();
            let one = ctx.scratch.level_succ(None, z).unwrap();
            let s1 = ctx.scratch.expr_sort(None, one).unwrap();
            let lhs = ctx
                .scratch
                .expr_forall(None, None, s0, s0, leanr_kernel::BinderInfo::Default)
                .unwrap();
            let rhs = ctx
                .scratch
                .expr_forall(None, None, s1, s0, leanr_kernel::BinderInfo::Default)
                .unwrap();
            assert!(!ctx.is_def_eq(lhs, rhs).unwrap());
        });
    }
}
