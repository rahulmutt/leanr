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
/// UN-IGNORED by M4b-3 P3 task 2. It was ignored through P2a because
/// `MetaError::IsDefEqStuck` is constructed nowhere in `leanr_meta/src`
/// (still true) and `synth_instance(Wrap ?m)` therefore answered
/// `Ok(Some(..))` — it treated the CALLER's `?m` as assignable and chose
/// the class's type parameter on the caller's behalf. The real oracle
/// reports this stuck (verified against the pinned v4.33.0-rc1
/// toolchain: `useWrap` alone gives "typeclass instance problem is
/// stuck / Wrap ?m.1 / ... the type argument to `Wrap` is a
/// metavariable"), via `SynthInstance.lean:978`'s `withNewMCtxDepth`
/// making an OUTER-scope mvar read-only for the whole search.
///
/// `leanr_meta` still has no MCtx-depth / read-only-mvar model — that
/// gap and its owner are unchanged. What changed is that the
/// ELABORATOR no longer depends on it for this decision:
/// `TermElabM::try_synth_instance` (`synthetic/ladder.rs`) reconstructs
/// `trySynthInstance`'s `.undef` from the goal type, so a goal that
/// still mentions an unassigned expr mvar is "not ready" instead of
/// being answered by a guessed candidate. See that function's doc for
/// exactly how much of the oracle's dynamic condition this covers.
#[test]
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
/// UN-IGNORED by M4b-3 P3 task 2, together with
/// `stuck_synthesis_is_not_ready_rather_than_failure` (see that test's
/// doc for the finding). Through P2a this returned
/// `Ok(@useWrap Nat instWrapNat)` — `Wrap ?a` was resolved from the
/// then-sole candidate instead of being reported stuck, so the fixpoint
/// never reached `report_stuck_synthetic_mvars` at all. It is the
/// END-TO-END counterpart of that test: it proves the `.undef` reaches
/// the ladder's stuck report through the whole fixpoint, not just that
/// `synthesize_inst_mvar_core` returns `false`.
#[test]
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
/// UN-IGNORED by M4b-3 P3 task 2 (see
/// `stuck_synthesis_is_not_ready_rather_than_failure`'s doc). Through
/// P2a `wrap_of_fresh_mvar`'s goal was genuinely SOLVED by
/// `synthesize_inst_mvar_core` rather than left pending, so the "still
/// pending" assertion failed on the first call, before
/// `postpone == .yes` was exercised at all. This is the only test in
/// this file that distinguishes rung-gating by `postpone` from the
/// stuck report, and it needs a genuinely unsolvable-for-now goal to do
/// it.
#[test]
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

/// **Residue 1 of `try_synth_instance`'s pre-test, retired (M4b-3
/// P2b-ii).** A goal whose only unassigned mvar sits in an
/// OUTPUT-PARAMETER position is answered by the oracle
/// (`preprocessOutParam` + `assignOutParams`, `SynthInstance.lean:775-861`,
/// ported in P2b-i) and must now reach the real search here too — with
/// the caller's mvar ASSIGNED as a result, which is the whole feature.
///
/// Before this task the pre-test answered `Undef` on any expr mvar at
/// all, and the ladder eventually raised `StuckSyntheticMVar` on a goal
/// the oracle solves. Corpus record `outParam/getFst` pins the same fact
/// end-to-end.
#[test]
fn out_param_position_mvar_reaches_the_real_search() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::get_cell_nat_of_fresh_mvar(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        assert!(
            app.elab
                .synthesize_inst_mvar_core(id)
                .expect("an outParam goal is not an error"),
            "`Get Cell Nat ?e` must be SOLVED, not postponed: the only mvar is \
             in an output-parameter position"
        );
        assert!(
            app.elab.mctx.mctx().is_assigned(id),
            "the instance mvar is assigned"
        );
        // The outParam mvar itself must have been assigned by
        // `assign_out_params` — read it back off the goal.
        let goal = app.elab.mctx.instantiate_mvars(goal).expect("instantiate");
        let base = app.elab.view.store;
        assert!(
            !app.elab
                .mctx
                .store()
                .expr_data(Some(base), goal)
                .has_expr_mvar(),
            "`?e := Unit` is assigned as a RESULT of synthesis, got {goal:?}"
        );
    });
}

/// The exemption is POSITIONAL, not class-level (design spec
/// § Amendment 4 item 6): `Get Cell ?i ?e` has an unassigned mvar in a
/// NON-output position (`idx`), so it must still postpone. This is
/// load-bearing for the `GetElem` worked example — `?i` is fixed only
/// when the `OfNat` default instance fires, and sending the goal to the
/// search early would answer `.none` and fail the headline record.
#[test]
fn non_out_param_position_mvar_still_postpones() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::get_cell_of_two_fresh_mvars(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        assert!(
            !app.elab
                .synthesize_inst_mvar_core(id)
                .expect("a stuck goal is not an error"),
            "`Get Cell ?i ?e` must be POSTPONED: `?i` is not an output parameter"
        );
        assert!(
            !app.elab.mctx.mctx().is_assigned(id),
            "nothing is committed on a postponed goal"
        );
    });
}

/// Rung 3 with nothing pending is a no-progress no-op — unchanged
/// behavior from P2a's seam, but now for the real reason (the priority
/// walk finds no pending `TypeClass` mvar) rather than a shape guard.
#[test]
fn synthesize_using_default_is_a_no_op_with_nothing_pending() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        assert!(!app
            .elab
            .synthesize_using_default(&kinds)
            .expect("no pending mvars -> no-op"));
    });
}

/// The case P2a's seam existed for, now solved rather than refused: a
/// pending `Dflt ?a` goal is closed by applying `@[default_instance]
/// instDfltNat`, which assigns `?a := Nat`.
///
/// oracle: `synthesizeUsingDefaultPrio` (`SyntheticMVars.lean:113-126`)
/// -> `synthesizeUsingDefaultInstance` (`:155-173`).
#[test]
fn synthesize_using_default_applies_a_default_instance() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        let goal = support::dflt_of_fresh_mvar(app);
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
            app.elab
                .synthesize_using_default(&kinds)
                .expect("rung 3 runs"),
            "a registered default instance must make progress"
        );
        assert!(
            app.elab.mctx.mctx().is_assigned(id),
            "the goal mvar is assigned by the default instance"
        );
    });
}

/// `commit_when` is a `Term.SavedState` bracket, not a mctx one.
///
/// oracle: `commitWhen` (`Lean/Util/MonadBacktrack.lean:50-60`) over the
/// `MonadBacktrack SavedState TermElabM` instance
/// (`TermElabM.lean:458-460`), whose `SavedState` is
/// `Meta.SavedState × Term.State` (`:206-209`). Driven directly rather
/// than through rung 3 because no default instance in `Elab0` assigns
/// anything before being rejected — the fixture cannot reach the
/// restore, so the bracket is tested at its own boundary.
#[test]
fn commit_when_restores_the_mctx_and_the_elaborator_tables() {
    support::with_app_harness("Nat.zero", |app| {
        let ty = app.st.f_type;
        let val = app.st.f;
        let (_e, outer) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(ty, leanr_meta::MVarKind::Natural)
            .expect("fresh mvar");

        // A rejected attempt: every effect below is rolled back.
        let mut inner = None;
        let kept = app
            .elab
            .commit_when(|s| {
                let (_e2, id) =
                    s.mk_fresh_expr_mvar_of_kind(ty, leanr_meta::MVarKind::Synthetic)?;
                inner = Some(id);
                s.register_synthetic_mvar(
                    support::any_syn_elem(),
                    id,
                    SyntheticMVarKind::TypeClass,
                );
                s.register_mvar_error_hole_info(id, support::any_syn_elem());
                s.mctx
                    .mctx_mut()
                    .assign(outer, val)
                    .map_err(leanr_elab::ElabError::from)?;
                Ok(false)
            })
            .expect("the closure itself does not error");
        let inner = inner.expect("the closure ran");
        assert!(!kept);
        assert!(
            app.elab.pending_mvars.is_empty(),
            "pending_mvars restored: a rejected candidate strands no subgoal"
        );
        assert!(
            app.elab.synthetic_mvar_decl(inner).is_none(),
            "synthetic_mvars restored"
        );
        assert!(
            app.elab.mvar_error_infos.is_empty(),
            "mvar_error_infos restored"
        );
        assert!(
            !app.elab.mctx.mctx().is_assigned(outer),
            "the mctx assignment is rolled back"
        );

        // The error path restores identically (the oracle's `catch ex =>
        // restoreState s; throw ex`).
        let err = app.elab.commit_when(|s| {
            s.mctx
                .mctx_mut()
                .assign(outer, val)
                .map_err(leanr_elab::ElabError::from)?;
            Err(leanr_elab::ElabError::UnsupportedSyntax("probe".into()))
        });
        assert!(err.is_err());
        assert!(
            !app.elab.mctx.mctx().is_assigned(outer),
            "restored on the error path too"
        );

        // A COMMITTING attempt keeps everything.
        let kept = app
            .elab
            .commit_when(|s| {
                s.mctx
                    .mctx_mut()
                    .assign(outer, val)
                    .map_err(leanr_elab::ElabError::from)?;
                Ok(true)
            })
            .expect("ok");
        assert!(kept);
        assert!(
            app.elab.mctx.mctx().is_assigned(outer),
            "a committing attempt keeps its effects"
        );
    });
}

/// A REJECTED default instance leaves no trace.
///
/// oracle: `synthesizeUsingDefaultInstance` runs inside `commitWhen`
/// (`SyntheticMVars.lean:156`), so a candidate whose `isDefEqGuarded`
/// fails must restore the state it unified into. `Dflt Unit` is the
/// minimal shape: `Dflt`'s only `@[default_instance]` is
/// `instDfltNat : Dflt Nat`, and `Dflt Unit =?= Dflt Nat` cannot hold.
///
/// `pending_mvars` is checked as well as the assignment, because
/// `commit_when` restores `Term.State`'s tables and not only the mctx —
/// see its own doc for why a mctx-only rollback would strand a rejected
/// candidate's subgoals on the pending list forever.
#[test]
fn a_rejected_default_instance_is_rolled_back() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        let goal = support::dflt_of_unit(app);
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
            !app.elab
                .synthesize_using_default(&kinds)
                .expect("rung 3 runs"),
            "instDfltNat does not apply to `Dflt Unit`"
        );
        assert!(
            !app.elab.mctx.mctx().is_assigned(id),
            "the rejected candidate must not stay assigned"
        );
        assert_eq!(
            app.elab.pending_mvars,
            vec![id],
            "a failed priority walk leaves the pending queue untouched"
        );
    });
}

/// **Ordering test 1 of 2 (design spec § Verification, tier 2).**
/// `synthesizeSomeUsingDefaultPrio` walks `pendingMVars.reverse` —
/// REVERSE CREATION ORDER — and the oracle's own comment
/// (`SyntheticMVars.lean:207-209`) explains why: otherwise `toString 0`
/// fails with an `OfNat String ?_` error. `pending_mvars`' head is the
/// MOST RECENT (P2a's invariant), so the walk must visit the OLDEST
/// first.
///
/// The corpus cannot catch this: on a term with one numeral both orders
/// agree.
///
/// The three goals are `OfNat ?a ?n` (oldest), `Wrap ?m`, `NoInst Nat`,
/// and only the OLDEST has a class with default instances — so under
/// `pending_mvars` order (newest first) the walk would reach it LAST.
/// `OfNat` rather than `Dflt` deliberately: its default instances sit
/// at priorities 100/50, strictly below `instDfltNat`'s bare
/// `@[default_instance]`, so the TOP priority applies to nothing and
/// the walk visits all three before dropping a rung. That makes the
/// recorded order a full three-element sequence
/// (`[oldest, middle, newest]`) instead of a single entry, and pins the
/// descending-priority drop in the same log.
#[test]
fn default_instance_walk_visits_pending_mvars_in_reverse_creation_order() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        let prios = app.elab.mctx.default_instance_priorities();
        assert_eq!(
            prios.len(),
            4,
            "Elab0's four default-instance priorities (1000 / 100 / 75 / 50), got {prios:?}"
        );
        // The TOP priority must apply to none of the three goals (so the
        // walk visits all of them before dropping a rung), and the
        // SECOND must be where `OfNat`'s winning default sits —
        // `instOfNatNat` at 100 since the task-6 review re-prioritised
        // `instOfNatTag` from 500 down to 50. M4b-3 P2b-ii added a
        // fourth priority (`instFreshSeed` at 75) BELOW 100: the walk
        // stops at the first priority that makes progress, so the
        // recorded order below is unchanged — three visits at the top,
        // one at 100 — and only this count moved.
        assert!(prios[0] > 100 && prios[1] == 100, "got {prios:?}");
        let ids = support::register_three_goals_oldest_defaultable(app);
        let order = support::visit_order_of_default_walk(app, &kinds);
        // Two properties ride on the single `assert_eq!` below — the
        // within-priority order and the descending drop — so the LENGTH
        // is checked first to say which one broke. A newest-first walk
        // makes this 6 (both priorities exhausted); an ascending
        // priority walk makes it 1 (the oldest solves at once at 100).
        assert_eq!(
            order.len(),
            4,
            "three visits at the top priority, then one at 100: got {order:?}"
        );
        assert_eq!(
            order,
            vec![ids[0], ids[1], ids[2], ids[0]],
            "reverse creation order: oldest pending mvar first, at every \
             priority, and the top priority applies to none of the three"
        );
        // oracle: `pendingMVars := pendingMVars.reverse ++
        // pendingMVarsNew` (`:202`) — the successful entry leaves the
        // queue, the rest are restored head-is-most-recent.
        assert_eq!(
            app.elab.pending_mvars,
            vec![ids[2], ids[1]],
            "the solved goal leaves the queue; the rest keep their order"
        );
    });
}

/// The queue rebuild's OTHER half: when the successful entry is not the
/// first one visited, `pendingMVarsNew` (the skipped prefix, consed) is
/// appended AFTER the reversed remainder.
///
/// oracle: `visit`'s `modify fun s => { s with pendingMVars :=
/// pendingMVars.reverse ++ pendingMVarsNew }` (`:202`) — with the
/// defaultable goal FIRST, `pendingMVarsNew` is empty and the append is
/// invisible, so this drives the middle position.
#[test]
fn default_instance_walk_rebuilds_the_pending_queue_newest_first() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        let goals = vec![
            support::wrap_of_fresh_mvar(app),
            support::of_nat_of_fresh_mvars(app),
            support::no_inst_of_nat(app),
        ];
        let ids = support::register_typeclass_goals(app, goals);
        assert!(app
            .elab
            .synthesize_using_default(&kinds)
            .expect("rung 3 runs"));
        assert_eq!(
            app.elab.pending_mvars,
            vec![ids[2], ids[0]],
            "remainder (newest first) then the skipped prefix"
        );
    });
}

/// The FIXTURE PREMISE the walk test rests on, plus the accessor's
/// storage order — NOT the walk itself.
///
/// `synthesizeUsingDefault` (`SyntheticMVars.lean:215-221`) relies on
/// `getDefaultInstancesPriorities` already being descending ("Recall
/// that `prioSet` is stored in descending order", `:217`;
/// `PrioritySet := Std.TreeSet Nat (fun x y => compare y x)`,
/// `Instances.lean:383`), and rung 3 iterates that order as given. This
/// test pins the "as given" half only: that `Elab0` really carries
/// THREE distinct default-instance priorities, that the two the fixture
/// writes explicitly are 100 and 50, and that `instDfltNat`'s bare
/// `@[default_instance]` outranks both.
///
/// **It does not test the walk, and is not meant to** (M4b-3 P3 task 5
/// review, important 1). The descending-order `assert_eq!` below is a
/// tautology over `MetaCtx::default_instance_priorities`, whose body IS
/// `sort_unstable(); dedup(); reverse()` (`leanr_meta/src/instances.rs:
/// 541-547`, unit-tested at `:644`); a rung-3 walk that iterated the
/// priority set BACKWARDS would leave it green. What pins the walk is
/// `default_instance_walk_visits_pending_mvars_in_reverse_creation_order`
/// above, whose expected log (`[old, mid, new, old]`) is only reachable
/// if the top priority is tried before 100 — and that test consumes the
/// three premises this one establishes.
#[test]
fn default_instance_priorities_are_stored_in_descending_order() {
    support::with_app_harness("Nat.zero", |app| {
        let prios = app.elab.mctx.default_instance_priorities();
        assert!(
            prios.len() >= 4,
            "Elab0 must carry four distinct default-instance priorities, got {prios:?}"
        );
        let mut descending = prios.clone();
        descending.sort_unstable();
        descending.reverse();
        assert_eq!(prios, descending);
        // The two priorities the fixture writes EXPLICITLY are pinned;
        // the bare `@[default_instance]` on `instDfltNat` is only
        // required to outrank both. Lean's own default for the bare
        // attribute is not restated here — it is the oracle's to
        // choose, and pinning it would make this test fail on a
        // toolchain bump for a reason unrelated to the ordering it
        // exists to check.
        assert!(
            prios.contains(&100),
            "instOfNatNat's priority, got {prios:?}"
        );
        assert!(
            prios.contains(&50),
            "instOfNatTag's priority, got {prios:?}"
        );
        assert!(
            prios.contains(&75),
            "instFreshSeed's priority (M4b-3 P2b-ii), got {prios:?}"
        );
        assert!(
            prios[0] > 100,
            "instDfltNat's bare @[default_instance] outranks both explicit ones, got {prios:?}"
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

/// M4b-3 P3 task 3: the literal scaffold is reachable in the fixture
/// env. Every constant the three literal elaborators mint by NAME must
/// resolve — an unresolvable name would surface as `UnknownIdent` deep
/// inside `elab_num` in task 6, far from its cause.
///
/// `Char`/`Char.ofNat` are opaque carriers (`axiom`), not the real
/// definitions: `elabCharLit` (`BuiltinTerm.lean:248-252`) never reads
/// `Char`'s shape, and the real `Char.ofNat` is `dite` over
/// `BitVec.ofNatLT`/`UInt32` (`Init/Prelude.lean:2886-2890`), which a
/// prelude-mode fixture cannot reach. The emitted `Expr` is identical
/// either way (plan § Measured facts, item 8).
#[test]
fn literal_scaffold_constants_resolve_in_the_fixture_env() {
    support::with_app_harness("Nat.zero", |app| {
        for name in [
            "Bool",
            "OfNat",
            "OfNat.ofNat",
            "instOfNatNat",
            "OfScientific",
            "OfScientific.ofScientific",
            "instOfScientificTag",
            "Char",
            "Char.ofNat",
            "Tag",
            "instOfNatTag",
        ] {
            assert!(
                support::fixture_declares(app, name),
                "Elab0 must declare {name} for M4b-3 P3"
            );
        }
    });
}

/// The `natVal` literal is viable against the fixture's own `Nat`.
///
/// Lean's kernel special-cases literals by the NAME `Nat` with
/// `Nat.zero`/`Nat.succ` constructors, which `Elab0.lean:113-116`
/// matches — but this is the first literal the elab fixture mints, so
/// it is MEASURED here rather than assumed (design spec § P3).
#[test]
fn a_nat_literal_infers_as_the_fixture_nat() {
    support::with_app_harness("Nat.zero", |app| {
        let base = app.elab.view.store;
        let lit = app
            .elab
            .mctx
            .store_mut()
            .expr_lit_nat(Some(base), &leanr_kernel::Nat::from(42u64))
            .expect("nat literal interns");
        let ty = app.elab.mctx.infer_type(lit).expect("literal has a type");
        let nat = support::fixture_const(app, "Nat");
        assert!(
            app.elab.mctx.is_def_eq(ty, nat).expect("defeq runs"),
            "Expr.lit (.natVal 42) must infer as the fixture's own Nat"
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

/// `42` with no expected type elaborates to
/// `@OfNat.ofNat.{?u} ?α 42 ?inst`, with the instance goal PENDING
/// (nothing determines `?α` yet) — and the ladder then closes it at
/// rung 3, assigning `?α := Nat` from `instOfNatNat`.
///
/// oracle: `elabNumLit` (`BuiltinTerm.lean:210-229`) followed by the
/// entry point's `synthesizeSyntheticMVarsNoPostponing`. This is the
/// first term in leanr's grammar for which rung 3 does real work.
///
/// Asserting the winning instance BY NAME is what makes this a rung-3
/// test rather than merely a "some instance was found" test: an eager
/// `mkInstMVar` on `OfNat ?α 42` cannot pick a candidate at all (task
/// 2's stuck predicate), so `instOfNatNat` in the output can only have
/// come from the default-instance rung. `Elab0.lean` puts
/// `instOfNatTag` BELOW it (50 vs 100) precisely so that a bare
/// numeral defaults to `Nat`, as in real Lean, while three distinct
/// priorities keep the descending walk observable. Cross-checked
/// against the pinned oracle: corpus record `num/bare` in
/// `tests/fixtures/elab/elab-queries.jsonl` carries exactly this term.
#[test]
fn a_bare_numeral_defaults_to_nat_through_rung_three() {
    let got = support::elab_and_synthesize("42").expect("42 elaborates");
    let rendered = got.to_string();
    assert!(
        rendered.contains("OfNat.ofNat"),
        "emits an OfNat.ofNat application, got {rendered}"
    );
    assert!(
        rendered.contains("instOfNatNat"),
        "the instance goal is closed by the highest-priority applicable \
         default instance, got {rendered}"
    );
    assert!(
        !rendered.contains("mvar"),
        "the fixpoint leaves no dangling metavariable, got {rendered}"
    );
}

/// The contrast case: an expected type pins `?α` inside
/// `mkFreshTypeMVarFor`'s own `isDefEq`, so the `OfNat Tag 42` goal is
/// GROUND by the time `Term.mkInstMVar` runs and eager synthesis closes
/// it — the default rung never fires, and `instOfNatTag` is reached even
/// though it LOSES the priority walk (50, below `instOfNatNat`'s 100).
///
/// `Tag` rather than `Nat` deliberately: ascribing `Nat` would reach the
/// same instance defaulting already picks, so the record could not tell
/// propagation from defaulting. Corpus records `num/ascribedTag` /
/// `num/bare` pin the same pair against the oracle; this states the
/// mechanism the pair is evidence for.
#[test]
fn an_ascribed_numeral_follows_the_expected_type_not_the_priority_walk() {
    let bare = support::elab_and_synthesize("42").expect("42 elaborates");
    let ascribed = support::elab_and_synthesize("(42 : Tag)").expect("(42 : Tag) elaborates");
    assert!(
        ascribed.to_string().contains("instOfNatTag"),
        "the propagated expected type selects instOfNatTag, got {ascribed}"
    );
    assert_ne!(
        bare, ascribed,
        "defaulting and propagation must reach DIFFERENT carriers — if they \
         agree, the expected type is not reaching the numeral"
    );
}

/// `elabNumLit`'s `getDecLevel` FAILURE branch, `Prop` arm — oracle
/// `BuiltinTerm.lean:215-224`, whose `catch` splits into two DISTINCT
/// errors: "the expected type is a proposition" (`:221`) and "…is
/// universe polymorphic and may be a proposition" (`:223`).
/// `ElabError::NumeralIsNotData` keeps them apart with its `is_prop`
/// field rather than collapsing them, and the POLARITY of that field is
/// the whole reason the field exists — so this asserts it, not merely
/// the variant.
///
/// `Eq Nat.zero Nat.zero` is the fixture's reachable `Prop`:
/// `Elab0.lean:28` declares `inductive Eq : α → α → Prop`, so the
/// ascription makes `mkFreshTypeMVarFor` assign `?α := Eq Nat.zero
/// Nat.zero : Prop`, `getDecLevel` cannot decrement `Sort 0`, and
/// `is_prop` is then `true`.
///
/// **The `is_prop: false` arm is not asserted, because nothing in this
/// fixture reaches it.** It needs `getDecLevel` to fail on an expected
/// type that is NOT a `Prop`, i.e. a `Sort u` whose `u` can be neither
/// decremented nor assigned. leanr's `dec_level` may assign its
/// top-level argument (`canAssignMVars` is `true` there), so an
/// unresolved level METAVARIABLE succeeds instead of failing —
/// `(42 : PUnit)`, the fixture's only `Sort u`-polymorphic carrier,
/// gets past `getDecLevel` and fails later at instance synthesis
/// (measured, not assumed). Reaching the arm needs a universe
/// PARAMETER in scope, which no `Elab0` term can put there until the
/// declaration layer lands. Recorded rather than asserted: an
/// unreachable arm with a fabricated test would be worse than none.
#[test]
fn a_numeral_ascribed_to_a_prop_is_not_data() {
    let err = support::elab_and_synthesize("(42 : Eq Nat.zero Nat.zero)")
        .expect_err("a numeral cannot inhabit a Prop");
    match err {
        leanr_elab::ElabError::NumeralIsNotData { is_prop, .. } => assert!(
            is_prop,
            "the expected type IS a Prop, so the oracle's `:221` branch \
             is the one that applies — `is_prop` must be true"
        ),
        other => panic!("expected NumeralIsNotData, got {other:?}"),
    }
}

/// oracle: `synthesizeSyntheticMVarsUsingDefault`
/// (`SyntheticMVars.lean:658-660`) — `synthesizeSyntheticMVars
/// (postpone := .yes)` then `synthesizeUsingDefaultLoop`. The composite
/// exists for `finalize`'s outParam branch (M4b-3 P2b-ii); this pins
/// that it (a) applies a default instance to a stuck goal and (b) does
/// NOT report stuck goals it cannot close — `postpone := .yes` means a
/// goal with no applicable default stays pending rather than erroring.
#[test]
fn synthesize_synthetic_mvars_using_default_defaults_and_keeps_the_rest_pending() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        // `Dflt ?a` — closable by `instDfltNat`; `Wrap ?m` — stuck with
        // no default instance, so it must SURVIVE the call.
        let goals = vec![
            support::dflt_of_fresh_mvar(app),
            support::wrap_of_fresh_mvar(app),
        ];
        let ids = support::register_typeclass_goals(app, goals);
        app.elab
            .synthesize_synthetic_mvars_using_default(&kinds)
            .expect("postpone := .yes never reports a stuck goal");
        assert!(
            app.elab.mctx.mctx().is_assigned(ids[0]),
            "`Dflt ?a` is closed by the default rung"
        );
        assert!(
            !app.elab.mctx.mctx().is_assigned(ids[1]),
            "`Wrap ?m` has no default instance and stays open"
        );
        assert_eq!(
            app.elab.pending_mvars,
            vec![ids[1]],
            "the unclosable goal stays PENDING — not reported, not dropped"
        );
    });
}

/// End-to-end confirmation that `Elab0.lean`'s `Lean.Internal.coeM`
/// turns the feature ON through `app::elab_app_aux`'s own
/// `env_contains_coe_m` (`App.lean:1355`), with no harness override:
/// `elab_term` ALONE — no enclosing fixpoint — on the worked example
/// runs the default rung inside `finalize`, so the walk log is non-empty
/// and the result is fully determined before anything else elaborates.
/// The oracle's motivating example (`App.lean:150-166`) is exactly this
/// property; corpus record `outParam/getElemUnderDflt` pins its
/// consequence against the oracle.
#[test]
fn coe_m_gate_enables_eager_defaulting_from_source() {
    leanr_elab::synthetic::default_walk_log_reset();
    support::elab_only("Get.get cell 0").expect("elab_term alone succeeds");
    let visited = leanr_elab::synthetic::default_walk_log_take();
    assert!(
        !visited.is_empty(),
        "with coeM declared, finalize's outParam branch ran rung 3 inside elab_term"
    );
}

/// A synthetic metavariable registered inside a binder is resumed by the
/// fixpoint AFTER that binder's scope has closed, so the ladder must run
/// each arm under the metavariable's own context — the oracle wraps
/// every arm in `mvarId.withContext` (`SyntheticMVars.lean:32-36`, and
/// the `.coe` arm's own at `:545`).
///
/// **Why a `let`, not a plain binder.** The brief's own shape (`?m : a`
/// for a plain `a : Type`) turns out NOT to discriminate: neither
/// `synthesize_inst_mvar_core` nor anything it calls ever needs to
/// resolve `a`'s OWN local declaration to fail an instance search on a
/// bare free variable — `try_synth_instance` just reports "no instance"
/// without consulting the ambient `lctx` at all (confirmed empirically:
/// the brief's literal test still passes with BOTH the ladder wrapper
/// removed and `mk_fresh_expr_mvar_of_kind` reverted to
/// `LocalCtxSnapshot::empty()`). A `let`-bound `a := Nat` makes the
/// dependency observable instead of merely asserted: `whnf`'s `FVar`
/// arm (`leanr_meta/src/whnf.rs`) only unfolds a let-bound fvar to its
/// VALUE by looking it up in the AMBIENT `lctx` (`self.lctx.get(id)`),
/// under `cfg.zeta_delta` (on by default). So `Wrap a` unifies with the
/// registered `Wrap Nat` instance if and only if `a` is back in the
/// ambient context when the search runs — which is exactly, and only,
/// what resuming under the mvar's own local context provides once its
/// binder has closed.
///
/// Kill 1: drop the `with_mvar_local_context` wrapper in
/// `synthesize_synthetic_mvar` — `a` is never reinstalled, so `Wrap a`'s
/// own instance search dereferences `a` against an `lctx` that no
/// longer declares it. Kill 2: revert `mk_fresh_expr_mvar_of_kind` to
/// `LocalCtxSnapshot::empty()` — the wrapper then reinstalls a context
/// with NO `a` in it at all, same underlying cause. Empirically, BOTH
/// mutations panic at this test's own `out.is_ok()` assertion with
/// `Err(Meta(Infer("unknown free variable")))` — `synthesize_pending_
/// inst_mvar` (via `infer_type`/`is_def_eq` somewhere in the search)
/// hits the missing fvar and errors out before `synth_instance` ever
/// gets to report "no instance", so `is_assigned(mvar_id)` is never
/// even reached, let alone left `false`.
#[test]
fn a_synthetic_mvar_resumes_under_its_own_local_context() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        let nat = support::fixture_const(app, "Nat");
        // `Nat : Type`, so inferring gives the sort to bind `a` at.
        let type_sort = app.elab.mctx.infer_type(nat).expect("Type");
        let cp = app.elab.mctx.lctx_checkpoint();
        // `a := Nat : Type` — a let-bound local whose VALUE only comes
        // back into view through the ambient `lctx`.
        let a = app
            .elab
            .mctx
            .push_let_decl(None, type_sort, nat)
            .expect("let decl");

        // `Wrap` — the fixture class `wrap_of_nat`/`wrap_of_fresh_mvar`
        // already use, applied here to `a` instead of a literal `Nat`
        // or a fresh mvar.
        let wrap_src = {
            use leanr_syntax::{builtin, parse_term};
            let snap = builtin::snapshot();
            let parsed = parse_term("Wrap", &snap);
            assert!(
                parsed.errors.is_empty(),
                "parse `Wrap`: {:?}",
                parsed.errors
            );
            let term_elem: leanr_elab::dispatch::SynElem = parsed
                .tree
                .root()
                .first_child_or_token()
                .expect("Wrap has a term child");
            app.elab
                .elab_term(&term_elem, &parsed.tree.kinds, None)
                .expect("Wrap elaborates")
        };
        let base = app.elab.view.store;
        let goal = app
            .elab
            .mctx
            .store_mut()
            .expr_app(Some(base), wrap_src, a)
            .expect("Wrap a");

        // `?m : Wrap a` — its type mentions the let-bound binder, so
        // resolving the instance goal at all requires `a` (and its
        // value) to be back in scope.
        let (_mvar_expr, mvar_id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("mvar");
        app.elab.register_synthetic_mvar(
            support::any_syn_elem(),
            mvar_id,
            leanr_elab::synthetic::SyntheticMVarKind::TypeClass,
        );
        // The `let`'s scope closes before the fixpoint runs.
        app.elab.mctx.lctx_restore(cp);

        let out = app.elab.synthesize_synthetic_mvars_no_postponing(&kinds);
        assert!(
            out.is_ok(),
            "resuming `Wrap a` under its own context must succeed: {:?}",
            out.err()
        );
        assert!(
            app.elab.mctx.mctx().is_assigned(mvar_id),
            "`Wrap a` should resolve to `instWrapNat` once `a := Nat` is back in scope \
             under the mvar's own local context, even though `a`'s let has closed \
             in the ambient context"
        );
    });
}

/// The `.coe` ladder arm's FIRST branch (`SyntheticMVars.lean:546-551`,
/// M4b-3 P4): when the types have become defeq under `withDefault`
/// since the coercion was postponed, the mvar is assigned `e` ITSELF —
/// no synthesis, no expansion. `Nat` vs `NatAlias` (a semireducible
/// alias) is the discriminating shape: defeq at `Default`, NOT at
/// `Instances`, so the second branch's `CoeT Nat e NatAlias` search
/// would answer `.none` (design spec § Amendment 5 item 10). Kill:
/// drop the first branch and this mvar stays unassigned / the ladder
/// reports `StuckCoercion`.
#[test]
fn coe_arm_assigns_e_itself_when_types_became_defeq() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        let zero = support::fixture_const(app, "Nat.zero");
        let alias = support::fixture_const(app, "NatAlias");
        let (mv, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(alias, leanr_meta::MVarKind::SyntheticOpaque)
            .expect("mvar");
        app.elab.register_synthetic_mvar(
            support::any_syn_elem(),
            id,
            leanr_elab::synthetic::state::SyntheticMVarKind::Coe {
                expected_type: alias,
                e: zero,
            },
        );
        app.elab
            .synthesize_synthetic_mvars_no_postponing(&kinds)
            .expect("the arm assigns without searching");
        let got = app.elab.mctx.instantiate_mvars(mv).expect("inst");
        assert_eq!(got, zero, "assigned to `e` itself, not to an expansion");
    });
}

/// The `.coe` arm's SECOND branch (`:552-560`) coerces once the
/// expected type is known, and the reporter's `.coe` arm (`:304-310`)
/// names a coercion that never became solvable. `pairW n` alone leaves
/// `?a` unassigned forever: `CoeT Nat n (Wrapper ?a)` is `.undef` at
/// registration AND at every retry, so the fixpoint ends with the
/// `.coe` mvar pending and the reporter raises `StuckCoercion` — the
/// oracle's `throwTypeMismatchError … "failed to create type class
/// instance for …"`. The dumper drops this query on the oracle side —
/// measured against the pin, `dump_elab` prints `elaboration failed for
/// … Application type mismatch: the argument n has type Nat but is
/// expected to have type Wrapper (?m n)` and emits nothing — which is
/// why it is a smoke test and not a record.
#[test]
fn stuck_coercion_is_reported_by_the_coe_reporter_arm() {
    match support::elab_and_synthesize("fun (n : Nat) => pairW n") {
        Err(leanr_elab::ElabError::StuckCoercion { .. }) => {}
        other => panic!("expected StuckCoercion, got {other:?}"),
    }
}
