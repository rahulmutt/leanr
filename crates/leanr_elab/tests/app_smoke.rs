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

/// Fix round 1, Critical 1 regression: the Forall reconstruction inside
/// `f_type_is_forall`'s `d != binder_type` branch (`state.rs`) must
/// route through `Some(base)`, not `None`. `body` there is the ORIGINAL
/// Forall's child, and for any function type inferred straight off the
/// environment — exactly `Nat.succ`'s own `Nat -> Nat`, since
/// `infer_const`'s `instantiate_level_params` short-circuits to `Ok(e)`
/// for a constant with no level params (`leanr_kernel/src/
/// subst.rs:754-756`) — that child is a PERSISTENT-region `ExprId`.
/// `base = None` on the scratch store either panics the
/// `debug_assert!` in `Store::store_for`
/// (`leanr_kernel/src/bank/mod.rs:143-146`, this is a debug build) or
/// silently reads the wrong row in release.
///
/// Elab0 has no dependently-typed declaration until Task 7, so this
/// builds a synthetic dependent `fType` by hand — `∀ (_ : #0), <Nat.succ's
/// own persistent codomain>`, domain = `BVar 0` — the same
/// "construct `State` directly" technique Task 5's brief uses for its
/// strict-implicit test. With `f_args = [<persistent arg>]`,
/// `instantiate_beta_rev_range` substitutes `#0` with that persistent
/// arg, so `d != binder_type` and the reconstruction genuinely runs.
///
/// Before/after evidence (fix round 1 report has the actual command
/// output): reverting `state.rs`'s `Some(base)` back to `None` makes
/// this test PANIC (the `debug_assert!` above fires, since both `d`
/// and `body` are persistent-region ids passed with `base = None` on a
/// scratch store) rather than merely fail an assertion — this test
/// could not pass against the pre-fix code.
#[test]
fn f_type_is_forall_reconstructs_dependent_domain_with_correct_base() {
    support::with_app_harness("Nat.succ", |app| {
        let (persistent_dom, persistent_body) = match app.node(app.st.f_type) {
            leanr_kernel::bank::terms::Node::Forall {
                binder_type, body, ..
            } => (binder_type, body),
            other => panic!("Nat.succ's inferred type must be a Forall, got {other:?}"),
        };
        assert!(
            !persistent_dom.is_scratch() && !persistent_body.is_scratch(),
            "test precondition: Nat.succ's `Nat -> Nat` must be entirely \
             persistent-region (infer_const's no-level-params short circuit) \
             for this regression to be meaningful"
        );

        let base = app.elab.view.store;
        let bvar0 = app
            .elab
            .mctx
            .store_mut()
            .expr_bvar(None, &leanr_kernel::Nat::from(0u64))
            .unwrap();
        let dep_forall = app
            .elab
            .mctx
            .store_mut()
            .expr_forall(
                Some(base),
                None,
                bvar0,
                persistent_body,
                leanr_kernel::BinderInfo::Default,
            )
            .unwrap();

        app.st.f_type = dep_forall;
        app.st.f_args = vec![persistent_dom];

        assert!(app.f_type_is_forall().unwrap());
        match app.node(app.st.f_type) {
            leanr_kernel::bank::terms::Node::Forall { binder_type, .. } => {
                assert_eq!(
                    binder_type, persistent_dom,
                    "reconstructed domain must be the substituted (persistent) arg, \
                     not the unsubstituted BVar"
                );
            }
            other => panic!("expected Forall after reconstruction, got {other:?}"),
        }
    });
}

/// Fix round 1, Important 2: exercises `f_type_is_forall`'s WHNF
/// reduction path, which `f_type_is_forall_whnfs_and_caches` (Task 3's
/// original, brief-verbatim test) never reaches — `Nat.succ`'s type is
/// already syntactically a `Forall`, so that test takes the fast path.
/// Here `fType` starts as `(fun (_ : Sort 0) => #0) (Nat.succ's own
/// `Nat -> Nat`)` — an `App`, not a `Forall` — so `f_type_is_forall`
/// must fall through to `get_f_type` + `whnf_forall`, whose beta
/// reduction produces the underlying Forall, which then gets cached
/// into `st.f_type`.
#[test]
fn f_type_is_forall_whnfs_non_forall_into_forall() {
    support::with_app_harness("Nat.succ", |app| {
        let nat_to_nat = app.st.f_type;
        let base = app.elab.view.store;

        let zero = app.elab.mctx.store_mut().level_zero(None).unwrap();
        let sort0 = app.elab.mctx.store_mut().expr_sort(None, zero).unwrap();
        let bvar0 = app
            .elab
            .mctx
            .store_mut()
            .expr_bvar(None, &leanr_kernel::Nat::from(0u64))
            .unwrap();
        let id_lam = app
            .elab
            .mctx
            .store_mut()
            .expr_lam(None, None, sort0, bvar0, leanr_kernel::BinderInfo::Default)
            .unwrap();
        let redex = app
            .elab
            .mctx
            .store_mut()
            .expr_app(Some(base), id_lam, nat_to_nat)
            .unwrap();
        assert!(
            !matches!(
                app.node(redex),
                leanr_kernel::bank::terms::Node::Forall { .. }
            ),
            "the redex must NOT be syntactically a Forall — that's the whole point"
        );

        app.st.f_type = redex;
        assert!(app.f_type_is_forall().unwrap());
        assert_eq!(
            app.st.f_type, nat_to_nat,
            "WHNF must beta-reduce the redex down to the original Forall and cache it"
        );
    });
}

/// A strict-implicit parameter with NO remaining arguments finalizes
/// instead of inserting an mvar (oracle: `processStrictImplicitArg`,
/// `App.lean:887-895`). The corpus cannot show this: Elab0 declares no
/// strict-implicit constant, and the difference from `processImplicitArg`
/// (which inserts UNCONDITIONALLY) only appears at the end of the
/// argument list — task 5's own module doc on `process_strict_implicit_arg`
/// makes the same point.
#[test]
fn strict_implicit_without_args_finalizes() {
    support::with_app_harness("id", |app| {
        // `with_app_harness("id", ..)` already ran bare "id" through
        // `main` once (a bare identifier is a zero-argument application,
        // `head.rs`'s own module doc): `id`'s own single parameter (`α`)
        // is plain `Implicit`, which `process_implicit_arg` inserts
        // UNCONDITIONALLY, so `app.st.f` arrives here already applied —
        // `id ?m`, not the bare constant. Peel the application back
        // apart to recover the underlying `id` constant this test wants
        // as `f`; it is the exact same universe-mvar-carrying `Const`
        // either way, so nothing is lost.
        let id_const = match app.node(app.st.f) {
            leanr_kernel::bank::terms::Node::App { f, .. } => f,
            _ => app.st.f,
        };

        // Force `f_type` to a SYNTHETIC strict-implicit forall — the
        // same "construct `State` directly" technique
        // `f_type_is_forall_reconstructs_dependent_domain_with_correct_base`
        // uses above, `Some(base)` throughout (that test's own doc
        // comment has the full store-routing citation). Domain/body are
        // two concrete, non-dependent `Sort 0`s: their identity doesn't
        // matter to this test, only that the Forall's `binder_info` is
        // `StrictImplicit`.
        let base = app.elab.view.store;
        let zero = app.elab.mctx.store_mut().level_zero(None).unwrap();
        let sort0 = app.elab.mctx.store_mut().expr_sort(None, zero).unwrap();
        let strict_forall = app
            .elab
            .mctx
            .store_mut()
            .expr_forall(
                Some(base),
                None,
                sort0,
                sort0,
                leanr_kernel::BinderInfo::StrictImplicit,
            )
            .unwrap();

        app.st.f = id_const;
        app.st.f_type = strict_forall;
        app.st.f_args = Vec::new();
        app.st.args = Vec::new();

        let f_before = app.st.f;
        let snap = leanr_syntax::builtin::snapshot();
        let kinds = snap.kinds();
        let got = leanr_elab::app::args::main(app, &kinds).unwrap();
        assert_eq!(
            got, f_before,
            "a strict-implicit parameter with no remaining arguments must \
             finalize `f` unchanged, not insert a fresh mvar"
        );
        assert!(
            app.st.f_args.is_empty(),
            "finalize must not have consumed/added any argument"
        );
    });
}
