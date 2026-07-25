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
