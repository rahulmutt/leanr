mod support;
use support::{name_id, with_elab};

use leanr_elab::app::elim::elab_as_elim_info;
use leanr_elab::app::expand::{expand_app, Arg, NamedArg};

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
    // any other positional is the motive (App.lean:1422-1430).
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
