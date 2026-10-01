mod support;
use support::{elab_and_synthesize, fixture_in, name_id, with_elab};

use leanr_elab::app::elim::elab_as_elim_info;
use leanr_elab::app::expand::{expand_app, Arg, NamedArg};
use leanr_elab::error::EliminatorErrorReason;
use leanr_elab::ElabError;

/// Expand `term` if it is an application node; a bare identifier is an
/// application with no arguments.
fn parts(
    term: &leanr_elab::dispatch::SynElem,
    kinds: &leanr_syntax::kind::KindInterner,
) -> (Vec<NamedArg>, Vec<Arg>, bool) {
    match term.as_node() {
        Some(node) if kinds.name(node.kind()) == "Lean.Parser.Term.app" => {
            let (_head, named, args, ellipsis) = expand_app(node, kinds).expect("expand");
            (named, args, ellipsis)
        }
        _ => (Vec::new(), Vec::new(), false),
    }
}

/// `(head constant, source)` → does the gate divert?
fn gate(head: &str, src: &str) -> bool {
    with_elab(src, |elab, term, kinds| {
        let (named, args, ellipsis) = parts(term, kinds);
        let c = name_id(elab, head);
        let f = elab
            .mk_const_with_fresh_mvar_levels_of(c)
            .expect("declared");
        elab_as_elim_info(elab, f, &named, &args, false, ellipsis, kinds)
            .expect("gate")
            .is_some()
    })
}

#[test]
fn every_should_elab_as_elim_disjunct_diverts() {
    assert!(gate("Nat.rec", "Nat.rec z s n"), "isRec");
    assert!(
        gate("Nat.casesOn", "Nat.casesOn n z s"),
        "isCasesOnRecursor"
    );
    assert!(gate("Nat.brecOn", "Nat.brecOn n s"), "isBRecOnRecursor");
    assert!(gate("Nat.recOn", "Nat.recOn n z s"), "isRecOnRecursor");
    assert!(gate("natElim", "natElim z s"), "elabAsElim tag");
    assert!(!gate("Nat.succ", "Nat.succ n"), "not an eliminator");
}

#[test]
fn a_supplied_motive_takes_the_standard_path() {
    assert!(
        !gate("Nat.rec", "Nat.rec (motive := m) z s n"),
        "named motive"
    );
    // `False.rec`'s motive is EXPLICIT: a positional `_` counts as missing,
    // any other positional is the motive (App.lean:1421-1431).
    assert!(gate("False.rec", "False.rec _ h"), "positional hole");
    assert!(
        !gate("False.rec", "False.rec (fun _ => Nat) h"),
        "positional motive"
    );
    assert!(!gate("False.rec", "False.rec h"), "positional non-hole");
    assert!(gate("False.rec", "False.rec"), "no positional at all");
    // `Nat.rec`'s motive is implicit, so the `_` is the zero minor.
    assert!(
        gate("Nat.rec", "Nat.rec _ s n"),
        "implicit motive ignores `_`"
    );
}

#[test]
fn binders_before_the_motive_consume_their_arguments() {
    // `preElim (k : Nat) {motive}`: `k` eats one positional, motive implicit.
    assert!(gate("preElim", "preElim k z n"));
    // A named argument for a pre-motive binder is erased, not counted.
    assert!(gate("Eq.subst'", "Eq.subst' (α := Nat) h p"));
}

#[test]
fn explicit_and_ellipsis_opt_out() {
    with_elab("Nat.rec z s n", |elab, term, kinds| {
        let (named, args, _e) = parts(term, kinds);
        let c = name_id(elab, "Nat.rec");
        let f = elab.mk_const_with_fresh_mvar_levels_of(c).unwrap();
        assert!(
            elab_as_elim_info(elab, f, &named, &args, true, false, kinds)
                .unwrap()
                .is_none()
        );
        assert!(
            elab_as_elim_info(elab, f, &named, &args, false, true, kinds)
                .unwrap()
                .is_none()
        );
    });
}

/// A non-`.const` head (here an fvar) is never an eliminator head.
#[test]
fn a_local_head_is_not_gated() {
    with_elab("Nat.rec z s n", |elab, term, kinds| {
        let (named, args, e) = parts(term, kinds);
        let c = name_id(elab, "Nat.rec");
        let rec = elab.mk_const_with_fresh_mvar_levels_of(c).unwrap();
        let ty = elab.mctx.infer_type(rec).unwrap();
        let x = elab
            .mctx
            .push_local_decl(None, ty, leanr_kernel::BinderInfo::Default)
            .unwrap();
        assert!(elab_as_elim_info(elab, x, &named, &args, false, e, kinds)
            .unwrap()
            .is_none());
    });
}

/// The oracle behavior that replaced the old M4b-4c recursor seam.
/// `Nat.rec`, postponed with no expected type and resumed, is an ORACLE
/// error (`App.lean:1376`, "expected type is not available"):
/// `resumePostponed` swallows it under `postponeOnError`
/// (`SyntheticMVars.lean:68-71`). Without that flag the oracle logs it
/// (`:73`); leanr, which does not log-and-continue, propagates it.
#[test]
fn a_resumed_eliminator_without_expected_type_is_an_oracle_error() {
    with_elab("Nat.rec", |elab, term, kinds| {
        elab.postpone_elab_term(term, None).unwrap();
        let id = elab.pending_mvars[0];
        let soft = elab.without_postponing(|e| e.synthesize_synthetic_mvar(id, true, false, kinds));
        assert!(
            matches!(soft, Ok(false)),
            "postponeOnError swallows an oracle error: {soft:?}"
        );
        let hard =
            elab.without_postponing(|e| e.synthesize_synthetic_mvar(id, false, false, kinds));
        assert!(
            matches!(
                hard,
                Err(ElabError::Eliminator {
                    reason: EliminatorErrorReason::NoExpectedType
                })
            ),
            "{hard:?}"
        );
    });
}

/// KNOWN DIVERGENCE (executable record of the `instantiate_beta_rev_range`
/// nested-redex gap, `metactx.rs`; spec § Landed follow-ups). The minor's
/// type keeps `(fun _x => Nat) n` under its arrow, so leanr elaborates the
/// unannotated `ih` with binder type `(fun _x => Nat) n`, where the oracle
/// (whose `instantiateBetaRevRange` betas nested redexes) gives `Nat`.
///
/// The oracle's encoding of this exact source was dumped with a scratch
/// copy of `dump_elab.lean` and is byte-identical to the committed
/// `elim/namedMotive` record's `exp` (that record annotates `(ih : Nat)`
/// so it does not hit the gap; the canonical encoder erases binder names).
/// So the expectation is read from that record, not written by hand.
///
/// This test must FLIP when `instantiateBetaRevRange` is fully ported: at
/// that point replace it with a corpus record in `dump_elab.lean` and
/// delete it.
#[test]
fn known_divergence_nested_redex_under_arrow_is_not_reduced() {
    let src = "fun (n : Nat) => Nat.rec (motive := fun _x => Nat) Nat.zero (fun _k ih => ih) n";
    let corpus = std::fs::read_to_string(fixture_in("elab", "elab-queries.jsonl")).unwrap();
    let oracle = corpus
        .lines()
        .map(|l| serde_json::from_str::<serde_json::Value>(l).unwrap())
        .find(|q| q["id"] == "elim/namedMotive")
        .expect("elim/namedMotive record")["exp"]
        .clone();
    // Control: the annotated spelling (the corpus record's own source) matches,
    // so the difference below is the nested redex and nothing else.
    let control =
        "fun (n : Nat) => Nat.rec (motive := fun _x => Nat) Nat.zero (fun _k (ih : Nat) => ih) n";
    assert_eq!(elab_and_synthesize(control).expect("control"), oracle);
    let ours = elab_and_synthesize(src).expect("leanr elaborates it, wrongly");
    assert_ne!(
        ours, oracle,
        "the nested-redex gap is closed: turn this into a corpus record"
    );
}
