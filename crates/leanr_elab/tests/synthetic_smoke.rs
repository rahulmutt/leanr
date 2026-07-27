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
