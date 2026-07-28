//! M4b-3 P2a: Rust-level tests for the scheduler's state and orderings.
//! These live here, not in `oracle_elab.rs`, because every term that
//! exercises the ladder ends in an ERROR in the oracle too, and
//! `dump_elab.lean` drops a throwing query rather than recording it
//! (plan § Measured facts, item 2).

mod support;

use leanr_elab::synthetic::{PostponeBehavior, SyntheticMVarKind};

#[test]
fn registering_a_synthetic_mvar_makes_it_pending_and_findable() {
    support::with_app_harness("Nat.zero", |app| {
        let ty = app.st.f_type;
        let (_e, mvar_id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(ty, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        assert!(app.elab.pending_mvars.is_empty(), "nothing pending yet");

        let stx = support::any_syn_elem();
        app.elab
            .register_synthetic_mvar(stx, mvar_id, SyntheticMVarKind::TypeClass);

        // oracle: `registerSyntheticMVar` (`TermElabM.lean:864-865`) —
        // inserts into `syntheticMVars` AND conses onto `pendingMVars`,
        // head-is-most-recent.
        assert_eq!(app.elab.pending_mvars, vec![mvar_id]);
        assert!(app.elab.synthetic_mvar_decl(mvar_id).is_some());

        // oracle: `markAsResolved` (`SyntheticMVars.lean:417-418`) erases
        // from `syntheticMVars` only — `pendingMVars` is managed by the
        // step's own filter, not here.
        app.elab.mark_as_resolved(mvar_id);
        assert!(app.elab.synthetic_mvar_decl(mvar_id).is_none());
        assert_eq!(app.elab.pending_mvars, vec![mvar_id]);
    });
}

#[test]
fn without_postponing_restores_the_flag_on_both_paths() {
    support::with_app_harness("Nat.zero", |app| {
        // oracle: `withoutPostponing` (`TermElabM.lean:1049-1050`) is a
        // READER modification — `mayPostpone := false` for the duration,
        // restored afterwards. leanr's is a field, so the restore is
        // explicit and must survive an early return.
        app.elab.may_postpone = true;
        let ok: Result<u8, leanr_elab::ElabError> = app.elab.without_postponing(|e| {
            assert!(!e.may_postpone);
            Ok(1)
        });
        assert_eq!(ok.expect("ok path"), 1);
        assert!(app.elab.may_postpone, "restored after the ok path");

        let err: Result<u8, leanr_elab::ElabError> = app.elab.without_postponing(|e| {
            assert!(!e.may_postpone);
            Err(leanr_elab::ElabError::UnsupportedSyntax("probe".into()))
        });
        assert!(err.is_err());
        assert!(app.elab.may_postpone, "restored after the error path");
    });
}

#[test]
fn postpone_behavior_is_three_valued() {
    // oracle: `inductive PostponeBehavior` (`SyntheticMVars.lean:423-441`)
    // — `yes` / `no` / `partial`. The third value is not decorative:
    // `let`'s type elaboration uses it (`Binders.lean:775`), and the
    // ladder's rungs 2-5 are gated on `postpone != .yes`, which is a
    // DIFFERENT test from `postpone == .no`.
    assert_ne!(PostponeBehavior::Partial, PostponeBehavior::Yes);
    assert_ne!(PostponeBehavior::Partial, PostponeBehavior::No);
}

/// The step visits pending mvars in CREATION order, not list order.
///
/// `pending_mvars` is head-is-most-recent, and the oracle walks it with
/// `filterRevM` (`SyntheticMVars.lean:584`), which visits right-to-left
/// — oldest first. `filterM` would visit newest first and still
/// terminate, which is why this needs a direct test.
#[test]
fn step_processes_pending_mvars_in_creation_order() {
    support::with_app_harness("Nat.zero", |app| {
        let ids = support::register_n_typeclass_mvars(app, 3);
        // Registered oldest..newest, so the list is newest..oldest.
        assert_eq!(
            app.elab.pending_mvars,
            vec![ids[2], ids[1], ids[0]],
            "head is most recent"
        );

        let seen = support::step_recording_visit_order(app);
        assert_eq!(
            seen,
            vec![ids[0], ids[1], ids[2]],
            "visited oldest-first (creation order)"
        );
    });
}

/// Survivors keep their ORIGINAL order (head still most recent), and
/// mvars created DURING the step land BEFORE them.
///
/// oracle: `pendingMVars := s.pendingMVars ++ remainingPendingMVars`
/// (`SyntheticMVars.lean:593`). Reversing that merge still terminates
/// and still looks green on simple terms, then diverges on nested
/// applications.
///
/// Also asserts progress here (not just merge order): 2 pre-existing
/// pending mvars, 0 solved, 1 created mid-step must still report NO
/// progress. If progress were computed off the post-merge list length
/// (3) instead of the snapshot (2) vs. survivor count (2), this would
/// wrongly report progress — see `step_reports_progress_by_snapshot_count`
/// for the case that comparison alone cannot distinguish.
#[test]
fn step_merges_new_pending_before_still_unsolved() {
    support::with_app_harness("Nat.zero", |app| {
        let old = support::register_n_typeclass_mvars(app, 2);
        let (fresh, progress) = support::step_creating_one_mvar_solving_none(app);
        assert_eq!(
            app.elab.pending_mvars,
            vec![fresh, old[1], old[0]],
            "new pending first, then still-unsolved in original order"
        );
        assert!(
            !progress,
            "2 snapshot vs 2 survivors (mid-step creation must not count \
             as merged-list growth) -> no progress"
        );
    });
}

/// `Err(IsDefEqStuck)` from synthesis means POSTPONE, never fail.
///
/// oracle: `trySynthInstance`'s `.undef` -> `return false -- we will try
/// later` (`TermElabM.lean:1274`). This is the distinction the whole
/// postponement scheme rests on: `Ok(None)` is a real failure that
/// throws, `Err(IsDefEqStuck)` is "not ready yet" that survives to the
/// next rung.
///
/// STILL IGNORED after Task 7, for a reason the Elab0 fixture cannot
/// fix: `MetaError::IsDefEqStuck` (`leanr_meta::error`) is never
/// constructed anywhere in `leanr_meta/src` today — confirmed by
/// grep and by a direct probe (`app.elab.mctx.synth_instance(Wrap ?m)`
/// returns `Ok(Some(instWrapNat))`, not `Err(IsDefEqStuck)`). The real
/// oracle DOES report this stuck (verified against the pinned
/// v4.33.0-rc1 toolchain: `useWrap` alone elaborates to "typeclass
/// instance problem is stuck / Wrap ?m.1 / ... the type argument to
/// `Wrap` is a metavariable"), via `SynthInstance.lean`'s
/// `withNewMCtxDepth` around the whole search (`:978`) making an
/// OUTER-scope mvar read-only mid-search — a general MCtx-depth /
/// read-only-mvar model `leanr_meta` does not have yet, by its own
/// documented design (`synth.rs`, `whnf.rs`, `level.rs`'s "Depth /
/// read-only seam" — explicitly deferred to a later `leanr_meta` plan,
/// out of scope for `leanr_meta/src unchanged by this task`). Fixing
/// this needs that model, not a different fixture shape.
#[test]
#[ignore = "needs leanr_meta MCtx-depth / read-only-mvar support so \
            synth_instance can ever produce IsDefEqStuck — leanr_meta/src \
            is out of scope for M4b-3 P2a"]
fn stuck_synthesis_is_not_ready_rather_than_failure() {
    support::with_app_harness("Nat.zero", |app| {
        // `Wrap ?m` — a class goal whose type argument is an unassigned
        // mvar, which is exactly what `synth_instance` reports stuck.
        let goal = support::wrap_of_fresh_mvar(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        let ready = app
            .elab
            .synthesize_inst_mvar_core(id)
            .expect("stuck is not an error");
        assert!(!ready, "stuck -> not ready yet");
        assert!(
            !app.elab.mctx.mctx().is_assigned(id),
            "a stuck goal assigns nothing"
        );
    });
}

/// A solvable goal is synthesized and ASSIGNED.
#[test]
fn solvable_instance_is_synthesized_and_assigned() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::wrap_of_nat(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        assert!(app.elab.synthesize_inst_mvar_core(id).expect("no error"));
        assert!(app.elab.mctx.mctx().is_assigned(id));
    });
}

/// A class with no instance is a real failure, not a postponement.
///
/// oracle: `trySynthInstance`'s `.none` arm throws
/// (`TermElabM.lean:1275+`).
#[test]
fn unsolvable_instance_is_a_synthesis_failure() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::no_inst_of_nat(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        assert!(matches!(
            app.elab.synthesize_inst_mvar_core(id),
            Err(leanr_elab::ElabError::InstanceSynthesisFailed { .. })
        ));
    });
}

/// A pre-existing assignment that IS defeq to the synthesized instance is
/// RECONCILED, not overwritten: `synthesizeInstMVarCore` confirms it and
/// leaves it in place.
///
/// oracle: `synthesizeInstMVarCore`'s `isAssigned` branch, defeq path
/// (`TermElabM.lean:1240-1242`). This is the "already assigned" half of
/// the trichotomy's downstream handling, exercised by nothing else in
/// this file: the other three tests all synthesize into a still-
/// unassigned mvar, so only this test (and the mismatch test below) ever
/// take the `is_assigned(inst_mvar)` branch at all — including its
/// `contains_pending_mvar` retry-later escape hatch, which the design
/// spec's Global Constraints single out as "not optional".
#[test]
fn already_assigned_and_defeq_is_reconciled_not_overwritten() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::wrap_of_nat(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        // Pre-assign to exactly the value real synthesis will produce, so
        // the reconciliation's `is_def_eq` succeeds.
        let val = app
            .elab
            .mctx
            .synth_instance(goal)
            .expect("synth_instance succeeds")
            .expect("Wrap Nat is solvable");
        app.elab
            .mctx
            .mctx_mut()
            .assign(id, val)
            .expect("assign a freshly-declared, unassigned mvar");

        assert!(
            app.elab
                .synthesize_inst_mvar_core(id)
                .expect("a defeq pre-existing assignment reconciles, it does not error"),
            "already-assigned + defeq -> Ok(true)"
        );
        assert_eq!(
            app.elab.mctx.mctx().assignment(id),
            Some(val),
            "reconciliation must not overwrite the pre-existing assignment"
        );
    });
}

/// A pre-existing assignment that is NOT defeq to the synthesized
/// instance is a real mismatch, not a silent overwrite and not a
/// postponement.
///
/// oracle: `synthesizeInstMVarCore`'s two assignment-mismatch throws
/// (`TermElabM.lean:1265-1272`). Neither side of this test's comparison
/// mentions a pending mvar, so this exercises the throwing path, not the
/// `contains_pending_mvar` retry-later escape hatch (see
/// `already_assigned_and_defeq_is_reconciled_not_overwritten`'s doc for
/// why that branch otherwise goes untested).
#[test]
fn already_assigned_and_not_defeq_is_a_mismatch() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::wrap_of_nat(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        // Pre-assign to something that cannot be the synthesized `Wrap
        // Nat` instance: the harness's own elaborated `Nat.zero` head,
        // whose head symbol no `Wrap` instance term shares.
        let wrong = app.st.f;
        app.elab
            .mctx
            .mctx_mut()
            .assign(id, wrong)
            .expect("assign a freshly-declared, unassigned mvar");

        assert!(matches!(
            app.elab.synthesize_inst_mvar_core(id),
            Err(leanr_elab::ElabError::InstanceMismatch { .. })
        ));
    });
}

/// Progress is a COUNT comparison, not "any succeeded".
///
/// oracle: `return numSyntheticMVars != remainingPendingMVars.length`
/// (`SyntheticMVars.lean:594`). The comparison is SNAPSHOT length vs
/// SURVIVOR count — never the post-merge list — so mvars created during
/// the step can never mask progress. Two pending with one solved is
/// `2 != 1`, progress, however many new ones the step created.
#[test]
fn step_reports_progress_by_snapshot_count() {
    support::with_app_harness("Nat.zero", |app| {
        support::register_n_typeclass_mvars(app, 2);
        let progress = support::step_solving_exactly_one(app);
        assert!(progress, "2 pending, 1 solved -> progress");

        support::register_n_typeclass_mvars(app, 1);
        let progress = support::step_solving_none(app);
        assert!(!progress, "nothing solved -> no progress");
    });
}

/// The ladder terminates and reports a stuck typeclass problem.
///
/// Measured against the pinned oracle (plan § Measured facts, item 2):
/// `useWrap` with no expected type leaves `Wrap ?m` stuck, and the
/// oracle's own `synthesizeSyntheticMVarsNoPostponing` throws
/// "typeclass instance problem is stuck". leanr must do the same rather
/// than emitting a term with a dangling mvar.
///
/// STILL IGNORED after Task 7 — same `leanr_meta` MCtx-depth gap as
/// `stuck_synthesis_is_not_ready_rather_than_failure` (see that test's
/// own doc for the full finding). Measured directly against this exact
/// query: `elab_and_synthesize("useWrap")` currently returns
/// `Ok(@useWrap Nat instWrapNat)` — leanr's `synth_instance` resolves
/// `Wrap ?a` via the sole candidate instead of reporting it stuck, so
/// the fixpoint never reaches `report_stuck_synthetic_mvars` at all.
/// The pinned oracle genuinely does throw "typeclass instance problem
/// is stuck" for this exact source text (re-confirmed against
/// v4.33.0-rc1 while investigating this gap) — the fixture and the
/// assertion are both right; `leanr_meta` cannot yet reproduce the
/// oracle's refusal.
#[test]
#[ignore = "needs leanr_meta MCtx-depth / read-only-mvar support (see \
            stuck_synthesis_is_not_ready_rather_than_failure's doc) — \
            leanr_meta/src is out of scope for M4b-3 P2a"]
fn bare_typeclass_application_is_reported_stuck() {
    let err = support::elab_and_synthesize("useWrap").expect_err("stuck");
    assert!(matches!(
        err,
        leanr_elab::ElabError::StuckSyntheticMVar { .. }
    ));
}

/// `postpone == .yes` does NOT report stuck — it leaves the mvar
/// pending for an outer scheduler.
///
/// oracle: rungs 2-5 and the stuck report are all under
/// `else if postpone != .yes` / `else if postpone == .no`
/// (`SyntheticMVars.lean:617,642`).
///
/// STILL IGNORED after Task 7 — same `leanr_meta` MCtx-depth gap as
/// `stuck_synthesis_is_not_ready_rather_than_failure`'s own doc:
/// `wrap_of_fresh_mvar`'s goal is genuinely solved by
/// `synthesize_inst_mvar_core` (not left pending), so this test's own
/// "still pending" assertion fails on the FIRST call, before
/// `postpone == .yes` is even exercised.
#[test]
#[ignore = "needs leanr_meta MCtx-depth / read-only-mvar support (see \
            stuck_synthesis_is_not_ready_rather_than_failure's doc) — \
            leanr_meta/src is out of scope for M4b-3 P2a"]
fn postpone_yes_leaves_the_mvar_pending() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::wrap_of_fresh_mvar(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        app.elab.register_synthetic_mvar(
            support::any_syn_elem(),
            id,
            leanr_elab::synthetic::SyntheticMVarKind::TypeClass,
        );
        let kinds = support::any_kinds();
        app.elab
            .synthesize_synthetic_mvars(leanr_elab::synthetic::PostponeBehavior::Yes, &kinds)
            .expect("postpone := .yes never reports stuck");
        assert_eq!(app.elab.pending_mvars, vec![id], "still pending");
    });
}

/// The default-instance seam fires only when default instances could
/// actually apply.
///
/// Rung 3 is P3's `synthesizeUsingDefault`. P2a supplies a SHAPE-GUARDED
/// stand-in: it errors when a pending `TypeClass` mvar's class has
/// default instances registered — the state in which the real rung would
/// have done something — and reports no progress otherwise. A blanket
/// `false` would silently skip a rung the oracle runs.
#[test]
fn synthesize_using_default_is_a_shape_guarded_seam() {
    support::with_app_harness("Nat.zero", |app| {
        // No pending mvars at all: no-op, no progress, no error.
        assert!(!app
            .elab
            .synthesize_using_default()
            .expect("no pending mvars -> no-op"));
    });
}

/// The positive case the shape guard exists FOR: a pending `TypeClass`
/// mvar whose class HAS a registered `@[default_instance]` must error
/// naming the P3 seam, not silently return `Ok(false)`.
///
/// Review finding (M4b-3 P2a task 5 review, finding 2):
/// `synthesize_using_default_is_a_shape_guarded_seam` above only ever
/// exercised the vacuous "no pending mvars" path — the guard's own
/// reason for existing (erroring rather than silently skipping rung 3
/// when a default instance really is registered) was untested. This
/// test drives that branch directly, against a class the fixture must
/// keep separate from `Wrap`/`Pair`/`NoInst` — see `support::dflt_of_nat`'s
/// own doc for why.
#[test]
fn synthesize_using_default_errors_when_a_default_instance_is_registered() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::dflt_of_nat(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        app.elab.register_synthetic_mvar(
            support::any_syn_elem(),
            id,
            leanr_elab::synthetic::SyntheticMVarKind::TypeClass,
        );
        assert!(
            matches!(
                app.elab.synthesize_using_default(),
                Err(leanr_elab::ElabError::UnsupportedSyntax(_))
            ),
            "a registered default instance must fire the P3 seam, not silently no-op"
        );
    });
}

/// The stuck report drains `pending_mvars` before reporting.
///
/// oracle: `let pendingMVars ← modifyGet fun s => (s.pendingMVars,
/// { s with pendingMVars := [] })` (`SyntheticMVars.lean:323`).
#[test]
fn stuck_report_drains_the_pending_list() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::wrap_of_fresh_mvar(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        app.elab.register_synthetic_mvar(
            support::any_syn_elem(),
            id,
            leanr_elab::synthetic::SyntheticMVarKind::TypeClass,
        );
        let _ = app.elab.report_stuck_synthetic_mvars();
        assert!(
            app.elab.pending_mvars.is_empty(),
            "drained before reporting"
        );
    });
}

/// `with_synthesize` restores the caller's pending list by APPENDING,
/// on both the ok and the error path — not by overwriting it.
///
/// oracle: `withSynthesizeImp` (`SyntheticMVars.lean:662-672`) — save,
/// clear, run, synthesize, then `finally` restore as
/// `s.pendingMVars ++ pendingMVarsSaved`. The `finally` is why leanr's
/// restore must survive an early return.
///
/// Review finding (M4b-3 P2a task 6 review, finding 3): the first
/// version of this test left `k`'s own pending list empty in both
/// calls, so `self.pending_mvars.extend(saved)` onto `[]` was
/// indistinguishable from `self.pending_mvars = saved` — an
/// implementation that OVERWROTE instead of APPENDED would have passed
/// unchanged. `k` here registers its own `Tactic`-kind synthetic mvar
/// and leaves it deliberately UNRESOLVED (`synthesize_synthetic_mvar`
/// reports `Ok(false)` for a `Tactic` decl whenever `run_tactics` is
/// false, which is every rung `with_synthesize`'s own
/// `synthesize_synthetic_mvars` call reaches under `postpone == Yes` —
/// the loop breaks before ever reaching rung 5's `run_tactics: true`),
/// so the restored list has a real, non-empty survivor to check the
/// MERGE ORDER against, not just the presence of the caller's saved
/// entry.
#[test]
fn with_synthesize_saves_clears_and_restores_pending() {
    support::with_app_harness("Nat.zero", |app| {
        let outer = support::register_n_typeclass_mvars(app, 1);
        let kinds = support::any_kinds();
        let ty = app.st.f_type;

        let inner_seen = std::cell::Cell::new(usize::MAX);
        let mut inner_id = None;
        let ok_outcome = app
            .elab
            .with_synthesize(PostponeBehavior::Yes, &kinds, |e| {
                // The caller's pending mvars are invisible inside.
                inner_seen.set(e.pending_mvars.len());
                let (_expr, id) = e
                    .mk_fresh_expr_mvar_of_kind(ty, leanr_meta::MVarKind::Synthetic)
                    .expect("fresh mvar");
                e.register_synthetic_mvar(support::any_syn_elem(), id, SyntheticMVarKind::Tactic);
                inner_id = Some(id);
                Ok(())
            });
        assert_eq!(inner_seen.get(), 0, "cleared for the duration");
        assert!(
            ok_outcome.is_ok(),
            "an unresolved Tactic mvar postpones under postpone == Yes, it does not error"
        );
        let inner_id = inner_id.expect("k registered its own mvar");
        assert_eq!(
            app.elab.pending_mvars,
            vec![inner_id, outer[0]],
            "restored by APPENDING: k's own unresolved survivor stays first, \
             the caller's saved mvar is appended after (oracle's \
             `s.pendingMVars ++ pendingMVarsSaved` — `s.pendingMVars` there is \
             what the call itself leaves behind, not the saved list)"
        );

        // Reset to the same outer-only baseline the first call started
        // from, so the error-path call below is symmetric with it.
        app.elab.pending_mvars = outer.clone();

        let mut inner_id2 = None;
        let err_outcome: Result<(), _> =
            app.elab
                .with_synthesize(PostponeBehavior::Yes, &kinds, |e| {
                    let (_expr, id) = e
                        .mk_fresh_expr_mvar_of_kind(ty, leanr_meta::MVarKind::Synthetic)
                        .expect("fresh mvar");
                    e.register_synthetic_mvar(
                        support::any_syn_elem(),
                        id,
                        SyntheticMVarKind::Tactic,
                    );
                    inner_id2 = Some(id);
                    Err(leanr_elab::ElabError::UnsupportedSyntax("probe".into()))
                });
        assert!(err_outcome.is_err());
        let inner_id2 = inner_id2.expect("k registered its own mvar before erroring");
        assert_eq!(
            app.elab.pending_mvars,
            vec![inner_id2, outer[0]],
            "restored on the error path too, same APPEND order: k's own mvar \
             (never touched by `synthesize_synthetic_mvars` — the error path \
             returns before that call) stays first, the caller's saved mvar \
             is appended after"
        );
    });
}

/// M4b-3 P2a task 9: the top-level entry point,
/// `TermElabM::elab_term_and_synthesize`, runs `elab_term`, then the
/// fixpoint, then `instantiate_mvars` (oracle: `elabTermAndSynthesize`,
/// `SyntheticMVars.lean:696-698`).
///
/// **This is NOT the brief's original test.** The brief's own
/// `entry_point_runs_the_fixpoint` asserted that `useWrap` (bare)
/// elaborates fine under `elab_term` alone but is reported
/// `StuckSyntheticMVar` under the real entry point — exactly the
/// oracle's own behavior for that source text (re-confirmed against
/// v4.33.0-rc1 during Task 7's investigation). It cannot pass today:
/// `leanr_meta` declares `MetaError::IsDefEqStuck` but constructs it
/// NOWHERE (`synth.rs:1636-1650` names the missing mctx-depth /
/// read-only-mvar model as a later `leanr_meta` plan's own scope, out
/// of reach here), so `synth_instance(Wrap ?m)` solves eagerly from the
/// sole candidate instead of refusing — the ladder's stuck report is
/// unreachable from any typeclass goal today. That exact scenario is
/// already recorded, `#[ignore]`d with this same evidenced reason, as
/// `bare_typeclass_application_is_reported_stuck` above — and since
/// `elab_and_synthesize` (this file's own support helper) is re-pointed
/// at the real `elab_term_and_synthesize` by this task rather than the
/// hand-chained stand-in it used to be, that ignored test now already
/// exercises the REAL entry point. It needs no changes here to go green
/// the day the `leanr_meta` gap above closes — writing a second,
/// differently-shaped ignored test for the identical scenario would
/// only be duplicate bookkeeping.
///
/// So this test instead pins the piece of `elab_term_and_synthesize`
/// that IS observable on today's grammar: an ordinary application with
/// an implicit argument, `id Nat.zero`. Two things are asserted, each
/// standing in for one half of the pipeline:
///
/// - **Instantiation matters.** `elab_term` alone elaborates `id
///   Nat.zero` to `@id ?α Nat.zero` with `?α := Nat` ASSIGNED (by
///   `finalize`'s own unification) but never SUBSTITUTED — the raw
///   term still carries a bare `Expr.mvar` reference, which
///   `elab_only`'s canonical encoding below still shows as a `"mvar"`
///   node. `elab_term_and_synthesize`'s own `instantiate_mvars` call is
///   what erases it. A version of the entry point that dropped that
///   call would make the two encodings AGREE, so this comparison would
///   catch it.
/// - **The fixpoint's call is exercised, even though it cannot yet be
///   shown to have any effect.** Every term in today's reachable
///   grammar resolves its instance goals eagerly inside `finalize`'s
///   own `synthesize_app_inst_mvars` (`app/state.rs`), so
///   `pending_mvars` is already empty by the time
///   `elab_term_and_synthesize` reaches
///   `synthesize_synthetic_mvars_no_postponing` — the call runs (it is
///   real code on the path, not skipped), but it is a measured no-op
///   on `id Nat.zero` and on every other term this corpus can produce.
///   Once the `leanr_meta` gap above closes, the case that WOULD tell
///   "the fixpoint ran" apart from "the fixpoint was skipped" is
///   `bare_typeclass_application_is_reported_stuck`'s own `useWrap`.
#[test]
fn entry_point_runs_the_fixpoint() {
    let raw =
        support::elab_only("id Nat.zero").expect("elab_term alone succeeds on today's grammar");
    let full = support::elab_and_synthesize("id Nat.zero")
        .expect("the entry point succeeds on the same, ordinary application");

    assert_ne!(
        raw, full,
        "elab_term alone (uninstantiated) and the entry point (instantiated) \
         must differ on a term with an implicit argument — if they agree, \
         `elab_term_and_synthesize` dropped its `instantiate_mvars` call"
    );
    assert!(
        raw.to_string().contains("\"mvar\""),
        "elab_term alone: expected an uninstantiated `?α` mvar node, got {raw}"
    );
    assert!(
        !full.to_string().contains("\"mvar\""),
        "the entry point: expected a fully-instantiated term with no \
         surviving mvar node, got {full}"
    );
}
