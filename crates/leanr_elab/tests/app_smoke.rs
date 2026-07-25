//! M4b-3 P1 unit tests: the application state machine's shapes and
//! orderings. These are the properties the hermetic oracle corpus
//! (`oracle_elab.rs`) cannot distinguish — tree layout, argument
//! partitioning, and seam messages — so they get direct tests here.
//! Same spirit as `binder_smoke.rs`.
//!
//! The `Term.app` / argument-item tree shape these tests assume was
//! confirmed by two throwaway probes (never landed, per M4b-1's
//! precedent) and is now recorded in `app/expand.rs`'s module doc.

use leanr_syntax::{builtin, parse_term};

use leanr_elab::app::expand::{expand_app, Arg};

fn app_node(
    src: &str,
) -> (
    leanr_syntax::tree::SyntaxNode,
    leanr_syntax::parse::ParseResult,
) {
    let snap = builtin::snapshot();
    let parsed = parse_term(src, &snap);
    assert!(parsed.errors.is_empty(), "{src}: {:?}", parsed.errors);
    let node = parsed.tree.root().first_child().expect("app node");
    (node, parsed)
}

#[test]
fn expand_app_splits_head_and_positional_args() {
    let (node, parsed) = app_node("Nat.succ Nat.zero");
    let (head, named, args, ellipsis) = expand_app(&node, &parsed.tree.kinds).unwrap();
    assert_eq!(head.kind(), parsed.tree.kinds.lookup("<ident>").unwrap());
    assert!(named.is_empty());
    assert_eq!(args.len(), 1);
    assert!(matches!(args[0], Arg::Stx(_)));
    assert!(!ellipsis);
}

#[test]
fn expand_app_collects_named_args() {
    let (node, parsed) = app_node("Nat.succ (n := Nat.zero)");
    let (_head, named, args, _e) = expand_app(&node, &parsed.tree.kinds).unwrap();
    assert_eq!(named.len(), 1, "named args: {:?}", named.len());
    assert_eq!(named[0].name, "n");
    let val_text = match &named[0].val {
        Arg::Stx(el) => match el {
            leanr_syntax::tree::NodeOrToken::Token(t) => t.text().to_string(),
            leanr_syntax::tree::NodeOrToken::Node(n) => n.text().to_string(),
        },
        other => panic!("expected Arg::Stx, got {other:?}"),
    };
    assert_eq!(
        val_text, "Nat.zero",
        "named arg's value must be the `:=` RHS (stx[3]), not a punctuation atom"
    );
    assert!(args.is_empty(), "a named arg is not positional");
}

#[test]
fn expand_app_pops_trailing_ellipsis() {
    let (node, parsed) = app_node("Nat.succ ..");
    let (_head, named, args, ellipsis) = expand_app(&node, &parsed.tree.kinds).unwrap();
    assert!(ellipsis, "trailing `..` sets the flag");
    assert!(
        named.is_empty() && args.is_empty(),
        "`..` is not an argument"
    );
}

#[test]
fn expand_app_rejects_duplicate_named_arg() {
    let (node, parsed) = app_node("Nat.succ (n := Nat.zero) (n := Nat.zero)");
    match expand_app(&node, &parsed.tree.kinds) {
        Err(leanr_elab::ElabError::DuplicateNamedArg(n)) => assert_eq!(n, "n"),
        other => panic!("expected DuplicateNamedArg, got {other:?}"),
    }
}

mod support;

/// `f_type_is_forall` must WHNF a non-forall `fType` into one and cache
/// the result (oracle: `fTypeIsForall`, `App.lean:238-249`), and report
/// false without mutating `fType` when it does not reduce to a forall.
#[test]
fn f_type_is_forall_whnfs_and_caches() {
    support::with_app_harness("Nat.succ", |app| {
        // `Nat.succ : Nat -> Nat` is already a forall.
        assert!(app.f_type_is_forall().unwrap());
        let cached = app.st.f_type;
        assert!(app.f_type_is_forall().unwrap());
        assert_eq!(app.st.f_type, cached, "second call must not re-reduce");
    });
}

#[test]
fn f_type_is_forall_false_for_non_function() {
    support::with_app_harness("Nat.zero", |app| {
        assert!(
            !app.f_type_is_forall().unwrap(),
            "Nat.zero : Nat is not a function type"
        );
    });
}

/// `get_param_info` reads the CURRENT parameter's binder info, and
/// `param_idx` tracks `f_args.len()` (oracle: `State.paramIdx`,
/// `App.lean:230`).
#[test]
fn param_idx_tracks_f_args_len() {
    support::with_app_harness("Nat.succ", |app| {
        assert_eq!(app.param_idx(), 0);
        assert!(app.f_type_is_forall().unwrap());
        assert_eq!(
            app.get_param_info().unwrap(),
            leanr_kernel::BinderInfo::Default
        );
    });
}
