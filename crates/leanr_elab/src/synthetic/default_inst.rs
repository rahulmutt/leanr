//! Rung 3 of the escalation ladder: default instances. Oracle:
//! `Lean/Elab/SyntheticMVars.lean:113-221`.
//!
//! P2a shipped `synthesize_using_default` as a shape-guarded seam that
//! ERRORED when a pending typeclass mvar's class had default instances
//! registered. This module is that seam's replacement (design spec
//! § Amendment 2, item 2): `num` is the first construct in leanr's
//! grammar that creates such a goal from source, so the rung and its
//! producer land together.
//!
//! Two orderings are transliterated verbatim because they are
//! fidelity-critical and invisible on simple corpus terms:
//!
//!   * the priority set is walked DESCENDING (`:215-221`, with the
//!     oracle's own "Recall that `prioSet` is stored in descending
//!     order" at `:217`);
//!   * within a priority, `synthesizeSomeUsingDefaultPrio` walks
//!     `pendingMVars.reverse` — REVERSE CREATION ORDER — with the
//!     oracle's own comment explaining why (`:207-209`: otherwise
//!     `toString 0` fails with an `OfNat String ?_` error). On success
//!     the queue is rebuilt as `pendingMVars.reverse ++
//!     pendingMVarsNew` (`:202`).
//!
//! Both have direct unit tests in `tests/synthetic_smoke.rs`; the
//! corpus cannot be relied on to catch them.
//!
//! **Termination.** The two loops are well-founded: `synthesize_pending`
//! shrinks its goal list by at least one on every iteration (its own
//! doc), and `synthesize_using_instances` returns as soon as a pass
//! closes nothing. The MUTUAL RECURSION through
//! `synthesize_using_default_instance` -> `synthesize_pending` ->
//! `synthesize_some_using_default_qm` -> `synthesize_using_default_for`
//! -> `synthesize_using_default_prio` ->
//! `synthesize_using_default_instance` is not: it is bounded only by the
//! default-instance graph being well-founded, exactly as in the oracle,
//! whose `synthesizeUsingDefaultPrio` is declared `partial` (`:113`) for
//! this reason. A cyclic set of default instances would recurse until
//! the Rust stack is exhausted where the oracle would loop forever;
//! neither is a behavior leanr can produce from its fixture, and adding
//! a depth cap the oracle does not have would be a divergence, not a
//! fix.
//!
//! **`mvarId.withContext` (`:114`, `:135`) is ported; it was a seam
//! until the elimMVarDeps slice, and it went live the day that slice
//! landed.** The scoping re-enters the goal's OWN local context, which
//! every mvar carries since the metavariable-local-contexts slice
//! (`mk_fresh_expr_mvar_of_kind`'s own doc). Both sites are wrapped in
//! `ladder.rs::with_mvar_local_context` below: the whole of
//! `synthesize_using_default_prio` (oracle `:114`, so
//! `synthesize_using_default_instance` inherits the scope rather than
//! opening its own), and the inside of
//! `synthesize_pending_inst_mvar_committed`'s `commit_when` (oracle
//! `:135`, whose `commitWhen <| mvarId.withContext do` has the same
//! nesting).
//!
//! **The history, because a reader will otherwise wonder why rung 3 got
//! this and rung 1 always had it.** This rung shipped without the
//! scoping, documented here as a seam on the argument that "no
//! default-instance goal in today's corpus depends on a binder that
//! closed before rung 3 ran". That stopped being true when
//! `elimMVarDeps` (`leanr_meta/src/mk_binding.rs`) was wired into
//! `MetaCtx::mk_binding`: its PLAIN-ASSIGN branch rewrites an
//! unassigned non-opaque mvar whose context holds the abstracted
//! binders into `?a := ?aux n`, so rung 3's `is_def_eq` against a
//! default-instance candidate then dereferences `n` — a binder that
//! closed before the fixpoint ran — against whatever context happened
//! to be ambient. Measured: `fun (n : Nat) => 0` and
//! `fun (n : Nat) => useFresh` elaborated to the oracle's answer before
//! that wiring and failed with `unknown free variable` after, with no
//! corpus record to notice. Both are corpus records now
//! (`num/zeroUnderBinder`, `dflt/polyInstImplicitUnderBinder`) and are
//! this fix's measured kill. Rungs 1-2 were never affected: their
//! dispatch has gone through `with_mvar_local_context` since M4b-3 P2a.
//!
//! `withRef mvarDecl.stx` (`:201`) positions error messages, and
//! leanr's error type carries no position (design spec § Amendment,
//! item 2). That one IS still unaddressed, and is not a behavior
//! difference on any term leanr can elaborate.

use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;
use leanr_meta::MVarId;
use leanr_syntax::kind::KindInterner;

use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::synthetic::SyntheticMVarKind;

impl<'e> TermElabM<'e> {
    /// oracle: `synthesizeUsingDefault` (`SyntheticMVars.lean:215-221`)
    /// — the ladder's rung 3. Walk the GLOBAL priority set in
    /// descending order; the first priority that makes progress wins.
    ///
    /// **`kinds` is unused by every function in this module today, not
    /// merely by the leaf** — stated plainly here because the earlier
    /// wording implied it was consumed somewhere along the way and was
    /// corrected by M4b-3 P3 task 8's audit. It is threaded through all
    /// eight helpers and read by none of them: the only leaf this family
    /// calls is `synthesize_inst_mvar_core`, which takes no interner
    /// because an instance goal is solved by SYNTHESIS, never by
    /// re-elaborating syntax.
    ///
    /// It is kept rather than deleted, and the reason is the public
    /// signature, not a forward bet on its own. `kinds` is part of this
    /// method's contract (design spec § P3; `ladder.rs`'s rung 3 and
    /// `synthesize_using_default_loop` both pass the interner they
    /// already hold), and it is there for the ladder's convention that
    /// every fixpoint entry point takes the interner rather than storing
    /// it (`SyntheticMVarDecl`'s own doc, which cites `TermElabM`'s
    /// module doc for the underlying rule). Dropping it from the private
    /// helpers alone would leave that public parameter with NO consumer
    /// at all — a `_kinds` on the crate's API surface, which is a louder
    /// falsehood than a threaded-but-unread argument, and would have to
    /// be re-threaded through this exact cycle if a future `.postponed`
    /// arm ever lands inside `synthesize_pending_inst_mvar_committed`,
    /// since that WOULD re-elaborate syntax. **P5 did not land one
    /// there** — its own postponement work (M4b-3 P5 task 6, the
    /// `useImplicitLambda` third-result finding) dispatches through a
    /// different mechanism, `elab.rs`'s `UseImplicitLambda::Postpone`,
    /// to a named `UnsupportedSyntax` seam owned by M4b-4, not through
    /// this fixpoint's `.typeClass` walk. (M4b-3 P4 shipped the `.coe`
    /// producer and its two consumer arms, but neither lands here: this
    /// rung's own walk skips every non-`.typeClass` kind by construction
    /// — see the oracle citation on `synthesize_some_using_default_prio`
    /// above — so the `.coe` half of this speculation resolved without
    /// touching this function.) So this parameter's `.postponed`
    /// justification is STILL speculative, unclaimed by any landed
    /// slice — recorded as a deliberate call, so a future reader does
    /// not have to re-derive it or wonder whether P5 already closed it.
    pub fn synthesize_using_default(&mut self, kinds: &KindInterner) -> Result<bool, ElabError> {
        // oracle: "Recall that `prioSet` is stored in descending order".
        // `MetaCtx::default_instance_priorities` guarantees that
        // (M4b-3 P3 task 4); the ordering test asserts it independently
        // rather than trusting the accessor.
        for prio in self.mctx.default_instance_priorities() {
            if self.synthesize_some_using_default_prio(prio, kinds)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// oracle: `synthesizeSomeUsingDefaultPrio` (`:193-210`).
    ///
    /// `pending_mvars`' head is the MOST RECENT (P2a's invariant), and
    /// the oracle walks `pendingMVars.reverse` (`:210`), so this
    /// iterates the REVERSED list — oldest first. `pending_new`
    /// accumulates the skipped entries in the oracle's own consing order
    /// (`visit pendingMVars (mvarId :: pendingMVarsNew)`), so the
    /// rebuilt queue is `remainder.reverse() ++ pending_new` and stays
    /// head-is-most-recent: every entry in the remainder is NEWER than
    /// every skipped one, because the walk runs oldest-first.
    fn synthesize_some_using_default_prio(
        &mut self,
        prio: usize,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        let mut walk: Vec<MVarId> = self.pending_mvars.clone();
        walk.reverse();
        let mut pending_new: Vec<MVarId> = Vec::new();
        for i in 0..walk.len() {
            let mvar_id = walk[i];
            walk_log::push(mvar_id);
            // oracle: `let some mvarDecl ← getSyntheticMVarDecl? mvarId
            // | visit ..` then `match mvarDecl.kind with | .typeClass ..`
            // (`:198-206`) — a missing decl and a non-typeclass kind take
            // the same skip branch.
            let is_tc = matches!(
                self.synthetic_mvar_decl(mvar_id).map(|d| &d.kind),
                Some(SyntheticMVarKind::TypeClass)
            );
            if is_tc && self.synthesize_using_default_prio(mvar_id, prio, kinds)? {
                // oracle: `pendingMVars := pendingMVars.reverse ++
                // pendingMVarsNew` (`:202`) — `pendingMVars` there is
                // what is LEFT of the walk after the successful entry.
                let mut rest: Vec<MVarId> = walk[i + 1..].to_vec();
                rest.reverse();
                rest.extend(pending_new);
                self.pending_mvars = rest;
                return Ok(true);
            }
            // oracle: `visit pendingMVars (mvarId :: pendingMVarsNew)`.
            pending_new.insert(0, mvar_id);
        }
        Ok(false)
    }

    /// oracle: `synthesizeUsingDefaultPrio` (`:113-126`).
    ///
    /// The oracle's `isClass? mvarType` early-out is FUSED with the
    /// `getDefaultInstances className` one: both `return false`, and a
    /// head constant with a non-empty default-instance list is
    /// necessarily a class, so `pending_class_name` plus an empty-list
    /// test decides both (plan § Measured facts, item 3). This is a
    /// fusion, not a seam — no oracle behavior is skipped.
    ///
    /// One narrowing that comes with `pending_class_name` (P2a's, not
    /// new here): the oracle's `isClass?` whnfs the goal and telescopes
    /// through `forallE` binders before reading its head, where
    /// `pending_class_name` walks the SYNTACTIC application spine of the
    /// instantiated type. Every `.typeClass` goal leanr registers is a
    /// class applied to arguments — `mk_inst_mvar`'s and
    /// `process_inst_implicit_arg`'s goals are both an instImplicit
    /// binder's domain — so the two agree on everything reachable. A
    /// goal whose head is a definition unfolding to a class, or a
    /// `∀`-wrapped one, would be classified by the oracle and skipped
    /// here; no leanr slice can build one yet.
    fn synthesize_using_default_prio(
        &mut self,
        mvar_id: MVarId,
        prio: usize,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        // oracle: `mvarId.withContext do` wraps the WHOLE body (`:114`),
        // so `synthesizeUsingDefaultInstance` below inherits the scope
        // rather than opening its own. See this module's doc for why
        // this is not optional. `with_mvar_local_context` is the ladder's
        // existing helper, the same one `synthesize_synthetic_mvar`
        // (`ladder.rs:149`) and the stuck reporter (`report.rs:105`) use.
        self.with_mvar_local_context(mvar_id, |elab| {
            let Some(class) = elab.pending_class_name(mvar_id)? else {
                return Ok(false);
            };
            for (inst, inst_prio) in elab.mctx.default_instances_of(class) {
                if inst_prio != prio {
                    continue;
                }
                if elab.synthesize_using_default_instance(mvar_id, inst, kinds)? {
                    return Ok(true);
                }
            }
            Ok(false)
        })
    }

    /// oracle: `synthesizeUsingDefaultInstance` (`:155-173`).
    ///
    /// Mint the default instance with fresh universe mvars, telescope
    /// its type into argument mvars, unify the goal against the applied
    /// candidate under `withAssignableSyntheticOpaque`, and — on
    /// success — recursively synthesize the instance-implicit binders
    /// the candidate introduced. That recursion is a NESTED FIXPOINT,
    /// not a single pass.
    ///
    /// `withAssignableSyntheticOpaque` (`:164`) is required because
    /// `coeAtOutParam` may mark a local instance's output parameter
    /// `syntheticOpaque`, which ordinary unification refuses to assign.
    /// M4b-3 P2b-ii's local-instance outParam feature (`args.rs`'s
    /// `is_next_out_param_of_local_instance_and_result`) does not itself
    /// mint a `syntheticOpaque` mvar, but M4b-3 P4's `coe.rs::mk_coe`
    /// does — its `.undef` arm mints exactly `MVarKind::SyntheticOpaque`
    /// on a stuck coercion — so the scope is no longer unconditionally a
    /// no-op. Whether `mk_coe`'s mint can coincide with a local
    /// instance's own outParam mvar on a reachable term is the
    /// missing-`MVarKind::SyntheticOpaque`-discriminator gap already
    /// triaged as a deferred minor (not this task's to resolve); the
    /// scope is kept ported regardless, so the day that gap closes this
    /// line does not have to move.
    fn synthesize_using_default_instance(
        &mut self,
        mvar_id: MVarId,
        inst: NameId,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        self.commit_when(|s| {
            let candidate = s.mk_default_instance_candidate(inst)?;
            let cand_type = s.mctx.infer_type(candidate)?;
            let (mvars, bis, _body) = s.mctx.forall_meta_telescope_reducing(cand_type)?;
            // oracle: `mkAppN candidate mvars` (`:159`).
            let base = s.view.store;
            let mut applied = candidate;
            for m in &mvars {
                applied = s
                    .mctx
                    .store_mut()
                    .expr_app(Some(base), applied, *m)
                    .map_err(leanr_meta::MetaError::from)?;
            }
            let goal = s
                .mctx
                .store_mut()
                .expr_mvar(None, Some(mvar_id.0))
                .map_err(leanr_meta::MetaError::from)?;
            // oracle: `isDefEqGuarded` (`:164`) — a FAILED unification is
            // `false`, not an error. leanr's `is_def_eq` already reports
            // failure as `Ok(false)`; the oracle's `catch` additionally
            // swallows genuine exceptions, which leanr does NOT do here
            // (a `MetaError` — a blown step budget, a malformed term —
            // propagates and is caught one level up by `commit_when`'s
            // own error path in `synthesize_pending_inst_mvar_committed`,
            // or surfaces to the ladder). Erring toward a visible error
            // over a silent rejection is this crate's standing choice.
            let ok = s
                .mctx
                .with_assignable_synthetic_opaque(|m| m.is_def_eq(goal, applied))?;
            if !ok {
                return Ok(false);
            }
            // oracle: `:167-171` — collect the instImplicit binders as
            // new pending goals, CONSED (so the resulting list is
            // reverse binder order), then `synthesizePending`.
            let mut pending: Vec<MVarId> = Vec::new();
            for (m, bi) in mvars.iter().zip(bis.iter()) {
                if *bi == BinderInfo::InstImplicit {
                    pending.insert(0, s.mvar_id_of(*m)?);
                }
            }
            s.synthesize_pending(pending, kinds)
        })
    }

    /// oracle: `mkConstWithFreshMVarLevels defaultInstance` (`:157`).
    ///
    /// Two steps, because `MetaCtx::mk_const_with_fresh_mvar_levels`
    /// takes an already-built `Expr.const` and REFRESHES the levels it
    /// carries (that method's own doc records the deliberate signature
    /// difference from the oracle's name-taking version): build the
    /// constant at its declared level PARAMS first — the oracle's
    /// `mkConstWithLevelParams` — then refresh. Building it at the empty
    /// level list instead would silently no-op the refresh for every
    /// universe-polymorphic default instance, leaving its levels as
    /// rigid params that cannot unify with the goal's.
    ///
    /// A missing declaration yields the empty parameter list, and the
    /// caller's `infer_type` then raises the real "unknown constant".
    /// Unreachable by construction — every name here came out of the
    /// environment's own default-instance table.
    fn mk_default_instance_candidate(&mut self, inst: NameId) -> Result<ExprId, ElabError> {
        let base = self.view.store;
        let params: Vec<NameId> = self
            .view
            .get(inst)
            .map(|info| info.constant_val().level_params.clone())
            .unwrap_or_default();
        let mut levels = Vec::with_capacity(params.len());
        for p in params {
            levels.push(
                self.mctx
                    .store_mut()
                    .level_param(Some(base), Some(p))
                    .map_err(leanr_meta::MetaError::from)?,
            );
        }
        // `intern_level_list`'s `base` is dedup-only and never resolves a
        // child id, so `None` is safe for a mixed-region list — the same
        // reasoning `app/head.rs`'s `mk_const` records at length.
        let levels = self
            .mctx
            .store_mut()
            .intern_level_list(None, &levels)
            .map_err(leanr_meta::MetaError::from)?;
        let raw = self
            .mctx
            .store_mut()
            .expr_const(Some(base), Some(inst), levels)
            .map_err(leanr_meta::MetaError::from)?;
        Ok(self.mctx.mk_const_with_fresh_mvar_levels(raw)?)
    }

    /// oracle: `synthesizePending` (`:186-190`) — the nested fixpoint:
    /// solve what ordinary instance synthesis can, then apply ONE
    /// default instance, then repeat. Returns `false` if any goal is
    /// left that neither can close.
    ///
    /// Terminates: `synthesize_using_instances` only ever shrinks its
    /// argument, and `synthesize_some_using_default_qm` returns either
    /// `None` (immediate `false`) or a list exactly one shorter — so
    /// `ids.len()` strictly decreases on every iteration.
    fn synthesize_pending(
        &mut self,
        mvar_ids: Vec<MVarId>,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        let mut ids = self.synthesize_using_instances(mvar_ids, kinds)?;
        loop {
            if ids.is_empty() {
                return Ok(true);
            }
            let Some(next) = self.synthesize_some_using_default_qm(ids, kinds)? else {
                return Ok(false);
            };
            ids = self.synthesize_using_instances(next, kinds)?;
        }
    }

    /// oracle: `synthesizeUsingInstances` (`:148-153`) over
    /// `synthesizeUsingInstancesStep` (`:141-146`) — repeatedly filter
    /// out the goals ordinary synthesis can close, until a pass closes
    /// none.
    fn synthesize_using_instances(
        &mut self,
        mvar_ids: Vec<MVarId>,
        kinds: &KindInterner,
    ) -> Result<Vec<MVarId>, ElabError> {
        let mut cur = mvar_ids;
        loop {
            let before = cur.len();
            let mut next = Vec::with_capacity(before);
            for id in cur {
                if !self.synthesize_pending_inst_mvar_committed(id, kinds)? {
                    next.push(id);
                }
            }
            // oracle: `if mvarIds'.length < mvarIds.length then recurse`
            // — a pass that closes nothing is the fixpoint.
            if next.len() == before {
                return Ok(next);
            }
            cur = next;
        }
    }

    /// oracle: `synthesizePendingInstMVar'` (`:134-139`) —
    /// `commitWhen <| try synthesizeInstMVarCore catch _ => false`. A
    /// synthesis ERROR is swallowed into `false` here, unlike the
    /// ladder's own `synthesize_pending_inst_mvar`, because a default
    /// instance's subgoal that cannot be solved is a reason to reject
    /// the candidate, not to fail the elaboration.
    fn synthesize_pending_inst_mvar_committed(
        &mut self,
        mvar_id: MVarId,
        _kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        // oracle: `commitWhen <| mvarId.withContext do …` (`:135`) —
        // the context swap is INSIDE the `commitWhen`, matching the
        // oracle's own nesting.
        self.commit_when(|s| {
            Ok(
                s.with_mvar_local_context(mvar_id, |elab| elab.synthesize_inst_mvar_core(mvar_id))
                    .unwrap_or(false),
            )
        })
    }

    /// oracle: `synthesizeSomeUsingDefault?` (`:175-184`) — apply a
    /// default instance to the FIRST goal that accepts one, returning
    /// the remaining goals with that one removed; `None` if none does.
    ///
    /// The oracle's recursion rebuilds the survivors as `mvarId ::
    /// mvarIds'`, i.e. the original order minus the solved entry, which
    /// is what removing at the index does here.
    fn synthesize_some_using_default_qm(
        &mut self,
        mvar_ids: Vec<MVarId>,
        kinds: &KindInterner,
    ) -> Result<Option<Vec<MVarId>>, ElabError> {
        for (i, id) in mvar_ids.iter().enumerate() {
            if self.synthesize_using_default_for(*id, kinds)? {
                let mut rest = mvar_ids.clone();
                rest.remove(i);
                return Ok(Some(rest));
            }
        }
        Ok(None)
    }

    /// oracle: the inner `synthesizeUsingDefault` (`:128-132`) — the
    /// per-MVAR priority walk, distinct from the top-level per-QUEUE
    /// walk above. Deliberately NOT logged: `walk_log` records the
    /// pending-queue walk's order, and mixing this recursive per-mvar
    /// walk into the same log would make the recorded sequence depend on
    /// how deep a candidate's subgoals go.
    fn synthesize_using_default_for(
        &mut self,
        mvar_id: MVarId,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        for prio in self.mctx.default_instance_priorities() {
            if self.synthesize_using_default_prio(mvar_id, prio, kinds)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// The `MVarId` an `Expr.mvar` node refers to.
    ///
    /// oracle: `mvars[i]!.mvarId!` (`:170`) — a partial function that
    /// PANICS on anything else. Unreachable by contract here too: every
    /// element of `forall_meta_telescope_reducing`'s first result is an
    /// `Expr.mvar` node it just minted (`mk_aux_mvar`).
    ///
    /// LOUD rather than silent all the same (M4b-3 P3 task 5 review,
    /// minor 2). This started life returning `Option` and SKIPPING a
    /// binder it could not read, which is the one failure mode
    /// named-seam discipline forbids: skipping an `instImplicit` binder
    /// drops it from `synthesizePending`'s goal list, so the candidate
    /// would be ACCEPTED with an unsynthesized instance argument left
    /// in the emitted term — a wrong `Expr`, not an error. A
    /// `debug_assert!` catches it in the dev loop and the error arm
    /// catches it in release; the message names the invariant, the same
    /// shape `report_stuck_synthetic_mvars` uses for the oracle's
    /// `| _ => unreachable!`.
    ///
    /// It named "M4b-3 P3 invariant" until task 8's seam audit. That
    /// read as a DEFERRAL under this crate's named-seam discipline —
    /// "P3 owes an implementation here" — which was false the moment
    /// task 5 landed the body around it, so the slice label was dropped
    /// rather than retargeted at a later slice that owes nothing either.
    /// See `builtin::lit::inst_mvar_id`, the other message this applied
    /// to, and `tests/seam_audit.rs`'s
    /// `no_seam_message_names_the_completed_p3_slice`.
    fn mvar_id_of(&self, e: ExprId) -> Result<MVarId, ElabError> {
        let base = self.view.store;
        let node = self.mctx.store().expr_node(Some(base), e);
        if let leanr_kernel::bank::terms::Node::MVar { id: Some(n) } = node {
            return Ok(MVarId(n));
        }
        debug_assert!(
            false,
            "forallMetaTelescopeReducing yielded a non-metavariable telescope entry: {node:?}"
        );
        Err(ElabError::UnsupportedSyntax(
            "internal invariant: forallMetaTelescopeReducing yielded a non-metavariable \
             telescope entry (synthetic::default_inst — not a deferred construct)"
                .to_string(),
        ))
    }
}

/// Visit-order instrumentation for `tests/synthetic_smoke.rs`'s
/// reverse-creation-order test. The corpus cannot express that ordering
/// (on a term with one numeral both orders agree), and asserting it
/// through the public API alone would only observe the OUTCOME, not the
/// order — so the walk records which mvars it considered.
///
/// Not `#[cfg(test)]`: integration tests link this crate as an external
/// consumer, where `#[cfg(test)]` items do not exist. The log is inert
/// unless [`default_walk_log_reset`] has armed it — `push` allocates
/// nothing and stores nothing while `LOG` is `None` — so the cost in
/// production is, per visited mvar, one thread-local access plus one
/// `RefCell` mutable borrow (a counter write, its check, and the
/// matching release) and a discriminant test. Not free, but O(1) and
/// off the defeq/synthesis hot path: `push` runs once per mvar the
/// default-instance walk CONSIDERS, not once per unification step.
///
/// **THREAD-LOCAL, not a global `Mutex<Vec<_>>`.** `cargo test` runs the
/// tests in one binary on a thread pool, and several tests in
/// `synthetic_smoke.rs` drive rung 3 — so a process-wide log would
/// collect another test's visited mvars into the middle of the ordering
/// assertion, and a process-wide `ARMED` flag would let one test disarm
/// another's recording. Both are order-dependent, so the failure would
/// be an intermittent one that passes locally. The walk always runs
/// synchronously on its caller's own thread (nothing under
/// `synthesize_using_default` spawns or joins), so a thread-local log
/// sees exactly the walk the arming test drove, and nothing else.
mod walk_log {
    use leanr_meta::MVarId;
    use std::cell::RefCell;

    thread_local! {
        /// `None` = disarmed (the production state): `push` does nothing
        /// and no allocation is ever made. `Some(log)` = armed by
        /// `reset`, drained by `take`. One `Option` carries both the
        /// flag and the buffer, so the two can never disagree.
        static LOG: RefCell<Option<Vec<MVarId>>> = const { RefCell::new(None) };
    }

    pub fn push(id: MVarId) {
        LOG.with(|log| {
            if let Some(entries) = log.borrow_mut().as_mut() {
                entries.push(id);
            }
        });
    }

    pub fn reset() {
        LOG.with(|log| *log.borrow_mut() = Some(Vec::new()));
    }

    pub fn take() -> Vec<MVarId> {
        LOG.with(|log| log.borrow_mut().take().unwrap_or_default())
    }
}

/// Arm the default-instance walk's visit log on THIS thread and clear
/// it. See [`walk_log`] for why the log is thread-local.
pub fn default_walk_log_reset() {
    walk_log::reset();
}

/// Take and disarm this thread's default-instance walk log. Returns the
/// mvars [`TermElabM::synthesize_using_default`] considered since the
/// matching [`default_walk_log_reset`], in visit order — empty if the
/// log was never armed on this thread.
pub fn default_walk_log_take() -> Vec<MVarId> {
    walk_log::take()
}
