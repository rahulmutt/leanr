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
