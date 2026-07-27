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
#[test]
#[ignore = "needs the Elab0 class scaffold (Task 7)"]
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
#[ignore = "needs the Elab0 class scaffold (Task 7)"]
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
#[ignore = "needs the Elab0 class scaffold (Task 7)"]
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
