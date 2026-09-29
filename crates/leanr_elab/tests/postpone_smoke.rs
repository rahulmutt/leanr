//! M4b-4a P2: term-level postponement mechanics — the producers
//! (`postpone.rs`), the catch (`elab.rs`'s `elab_using_elab_fns`) and
//! the resume (`synthetic/ladder.rs`'s `resume_postponed`). The corpus
//! (`oracle_elab.rs`, `p2/*` records) pins the TERMS postponement
//! produces; this file pins the state transitions the corpus cannot
//! see.

mod support;

use leanr_elab::synthetic::SyntheticMVarKind;
use leanr_elab::{ElabError, TermElabM};
use leanr_meta::{MVarId, MVarKind};

/// Pending synthetic mvars of kind `.postponed`, head-is-most-recent.
fn postponed_ids(elab: &TermElabM) -> Vec<MVarId> {
    elab.pending_mvars
        .iter()
        .copied()
        .filter(|id| {
            matches!(
                elab.synthetic_mvar_decl(*id).map(|d| &d.kind),
                Some(SyntheticMVarKind::Postponed { .. })
            )
        })
        .collect()
}

/// oracle: `tryPostpone` (`TermElabM.lean:1370-1372`) throws only
/// while `mayPostpone` holds, and `withoutPostponing` (`:1049-1050`)
/// clears it. `tryPostponeIfNoneOrMVar none` is plain `tryPostpone`
/// (`:1384-1387`).
#[test]
fn try_postpone_reads_may_postpone() {
    support::with_elab("Nat.zero", |elab, _, _| {
        assert!(matches!(elab.try_postpone(), Err(ElabError::Postpone)));
        assert!(matches!(
            elab.try_postpone_if_none_or_mvar(None),
            Err(ElabError::Postpone)
        ));
        assert!(elab.without_postponing(|e| e.try_postpone()).is_ok());
        assert!(elab
            .without_postponing(|e| e.try_postpone_if_none_or_mvar(None))
            .is_ok());
    });
}

/// oracle: `isMVarApp` is `(← whnfR e).getAppFn.isMVar`
/// (`TermElabM.lean:1375-1376`). `outParam` is `@[reducible]`
/// (`Elab0.lean:341`), so `outParam ?m` whnfR-reduces to `?m` — an
/// instantiate-then-spine-walk (leanr's pre-P2 approximation) sees the
/// constant `outParam` instead.
#[test]
fn is_mvar_app_sees_through_reducible_definitions() {
    support::with_elab("outParam _", |elab, term, kinds| {
        let e = elab
            .elab_term(term, kinds, None)
            .expect("outParam _ elaborates");
        assert!(
            elab.is_mvar_app(e).unwrap(),
            "outParam ?m whnfR-reduces to ?m"
        );
        assert!(matches!(
            elab.try_postpone_if_mvar(e),
            Err(ElabError::Postpone)
        ));
        assert!(elab
            .without_postponing(|el| el.try_postpone_if_mvar(e))
            .is_ok());
    });
    support::with_elab("Prod Nat _", |elab, term, kinds| {
        let e = elab
            .elab_term(term, kinds, None)
            .expect("Prod Nat _ elaborates");
        assert!(
            !elab.is_mvar_app(e).unwrap(),
            "the head is the constant Prod"
        );
        assert!(elab.try_postpone_if_mvar(e).is_ok());
    });
}

/// `whnfR` instantiates an ASSIGNED head mvar, so an mvar that has been
/// solved no longer counts.
#[test]
fn is_mvar_app_instantiates_an_assigned_head() {
    support::with_elab("Nat", |elab, term, kinds| {
        let nat = elab.elab_term(term, kinds, None).unwrap();
        let ty = elab.mctx.infer_type(nat).unwrap();
        let (m, id) = elab
            .mk_fresh_expr_mvar_of_kind(ty, MVarKind::Natural)
            .unwrap();
        assert!(elab.is_mvar_app(m).unwrap());
        elab.mctx.mctx_mut().assign(id, nat).unwrap();
        assert!(!elab.is_mvar_app(m).unwrap());
    });
}

/// oracle: `postponeElabTermCore` (`TermElabM.lean:1449-1453`) —
/// `mkFreshExprMVar expectedType? .syntheticOpaque`, registered
/// `.postponed (← saveContext)`. With no expected type,
/// `mkFreshExprMVarImpl`'s `none` arm (`Meta/Basic.lean:872-875`)
/// mints a fresh type mvar first.
#[test]
fn postpone_elab_term_registers_a_synthetic_opaque_postponed_mvar() {
    support::with_elab("Nat.zero", |elab, term, _| {
        let before = elab.pending_mvars.len();
        elab.postpone_elab_term(term, None).unwrap();
        assert_eq!(elab.pending_mvars.len(), before + 1);
        let id = elab.pending_mvars[0];
        assert!(matches!(
            elab.synthetic_mvar_decl(id).unwrap().kind,
            SyntheticMVarKind::Postponed { .. }
        ));
        let decl = elab.mctx.mctx().decl(id).unwrap();
        assert_eq!(decl.kind, MVarKind::SyntheticOpaque);
        let ty = decl.ty;
        assert!(
            elab.is_mvar_app(ty).unwrap(),
            "no expected type: a fresh type mvar"
        );
        assert_eq!(postponed_ids(elab), vec![id]);
    });
}

/// oracle: `elabTermAux`'s `.postpone` arm (`TermElabM.lean:1843-1850`)
/// — with `mayPostpone` and `catchExPostpone`, it calls
/// `postponeElabTerm` DIRECTLY, registering the term as a `.postponed`
/// synthetic mvar. No `Exception.postpone` is thrown, so this does NOT
/// exercise `elabUsingElabFnsAux`'s catch (`:1635-1651`); that catch is
/// pinned by `a_postpone_discards_what_the_failed_attempt_registered`.
/// The postponed syntax is `x` — the local whose implicit-lambda
/// treatment is postponed — not the enclosing ascription.
#[test]
fn the_implicit_lambda_postpone_arm_registers_the_term() {
    support::with_elab("fun x => (x : {a : Type} -> Nat)", |elab, term, kinds| {
        elab.elab_term(term, kinds, None)
            .expect("the `.postpone` arm turns the term into an mvar");
        let ids = postponed_ids(elab);
        assert_eq!(ids.len(), 1, "exactly the one postponed `x`");
        let decl = elab.synthetic_mvar_decl(ids[0]).unwrap();
        assert_eq!(kinds.name(decl.stx.kind()), "<ident>");
    });
}

/// oracle: `.postpone` with `mayPostpone == false` elaborates WITHOUT
/// implicit lambdas (`TermElabM.lean:1853-1854`) — no postponement.
#[test]
fn without_postponing_the_implicit_lambda_arm_elaborates_directly() {
    support::with_elab("fun x => (x : {a : Type} -> Nat)", |elab, term, kinds| {
        elab.without_postponing(|e| e.elab_term(term, kinds, None))
            .expect("elaborates without the wrap");
        assert!(postponed_ids(elab).is_empty());
    });
}

/// Review Focus 1. oracle: `resumeElabTerm` elaborates with
/// `catchExPostpone := false` (`SyntheticMVars.lean:23-26`), and
/// `resumePostponed` turns a postponement into "not ready yet"
/// (`:61-65`). At rung 1 `x`'s type is still unknown, so the resume
/// postpones again: the step makes NO progress and the SAME mvar stays
/// pending. Catching it instead would assign the old mvar to a fresh
/// one — "progress" the fixpoint would chase forever.
#[test]
fn resuming_does_not_catch_its_own_postpone() {
    support::with_elab("fun x => (x : {a : Type} -> Nat)", |elab, term, kinds| {
        elab.elab_term(term, kinds, None).unwrap();
        let before = postponed_ids(elab);
        let progressed = elab
            .synthesize_synthetic_mvars_step(false, false, kinds)
            .unwrap();
        assert!(!progressed, "a re-postponed resume is not progress");
        assert_eq!(postponed_ids(elab), before);
    });
}

/// oracle: `resumePostponed`'s `.error` arm with `postponeOnError`
/// restores the saved state (`SyntheticMVars.lean:68-71`). `(_ : Nat).1`
/// registers a hole (`registerMVarErrorHoleInfo`,
/// `BuiltinTerm.lean:67`), then fails: `#check (_ : Nat).1` on the
/// pinned oracle reports "Invalid projection: Projections extract
/// constructor fields for one-constructor inductive types. The
/// expression ?m.1 has type `Nat` which is not a one-constructor
/// inductive type."
#[test]
fn a_failed_resume_under_postpone_on_error_rolls_its_state_back() {
    support::with_elab("(_ : Nat).1", |elab, term, kinds| {
        elab.postpone_elab_term(term, None).unwrap();
        let id = elab.pending_mvars[0];
        let infos = elab.mvar_error_infos.len();
        let r = elab.without_postponing(|e| e.synthesize_synthetic_mvar(id, true, false, kinds));
        assert!(matches!(r, Ok(false)), "{r:?}");
        assert_eq!(
            elab.mvar_error_infos.len(),
            infos,
            "the hole's registration is rolled back"
        );
        let r = elab.without_postponing(|e| e.synthesize_synthetic_mvar(id, false, false, kinds));
        assert!(
            matches!(
                r,
                Err(ElabError::InvalidProjection {
                    reason: leanr_elab::InvalidProjectionReason::NotOneCtor,
                    ..
                })
            ),
            "{r:?}"
        );
    });
}

/// oracle: the catch restores the saved state before postponing
/// (`TermElabM.lean:1635-1651`). Elaborating `(x.1).1` postpones the
/// inner `x.1` first (a registered mvar `?m`), then the outer `.1`
/// postpones on `?m`'s unknown type; the restore drops `?m`, so exactly
/// ONE postponed mvar — the whole `(x.1).1` — is pending.
#[test]
fn a_postpone_discards_what_the_failed_attempt_registered() {
    support::with_elab("fun x => (x.1).1", |elab, term, kinds| {
        elab.elab_term(term, kinds, None).unwrap();
        let ids = postponed_ids(elab);
        assert_eq!(ids.len(), 1, "the inner postponement is discarded");
        let decl = elab.synthetic_mvar_decl(ids[0]).unwrap();
        assert_eq!(
            u32::from(decl.stx.text_range().len()),
            "(x.1).1".len() as u32,
            "the postponed syntax is the whole projection chain"
        );
    });
}

/// oracle: a resume that postpones again restores its saved state
/// (`SyntheticMVars.lean:61-65`). `(_ : _).1`'s head registers two holes
/// (the type and the value), THEN `.1` postpones on `?T`.
#[test]
fn a_resume_that_postpones_again_rolls_its_state_back() {
    support::with_elab("(_ : _).1", |elab, term, kinds| {
        elab.postpone_elab_term(term, None).unwrap();
        let id = elab.pending_mvars[0];
        let infos = elab.mvar_error_infos.len();
        let pending = elab.pending_mvars.clone();
        let r = elab.synthesize_synthetic_mvar(id, false, false, kinds);
        assert!(matches!(r, Ok(false)), "{r:?}");
        assert_eq!(elab.mvar_error_infos.len(), infos, "both holes rolled back");
        assert_eq!(elab.pending_mvars, pending);
    });
}
