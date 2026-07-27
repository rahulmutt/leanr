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

use leanr_elab::app::expand::{expand_app, Arg, NamedArg};

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

// ===== M4b-3 P1 task 7: named arguments and eta-expansion =====
//
// The corpus (`app/namedBoth`, `app/namedFirst`, `app/namedEta`,
// `app/namedDep`) already discriminates the named-argument lookup in
// `main`, `find_named_arg_depends_on_current`'s `Some` (implicit) vs
// `None` (eta) fork, `add_eta_arg`, and `finalize`'s `mkLambdaFVars`.
// What it CANNOT see is everything below: `found_named_args` (pure
// diagnostic bookkeeping, never part of the emitted term), the eta
// binder's NAME (the oracle encoder erases binder names —
// `dump_elab.lean`'s "binder names erased" rule), the ellipsis arm (no
// `..` query exists), and the reducing half of `has_opt_auto_params`
// (Elab0 declares no `optParam`/`autoParam` parameter at all).

/// `pushFoundNamedArg` (`App.lean:940-941`) records a binder name only
/// when `findNamedArg?` MISSED it, and `addEtaArg` (`App.lean:734-740`)
/// then makes the missing parameter a lambda binder carrying the
/// PARAMETER's name — not the fresh name `push_local_decl` was given.
/// Neither is visible in the oracle corpus: `found_named_args` never
/// reaches the emitted `Expr`, and the canonical encoder erases binder
/// names on both sides.
#[test]
fn eta_records_found_named_args_and_restores_the_parameter_name() {
    let snap = builtin::snapshot();
    let parsed = parse_term("Nat.zero", &snap);
    let val = parsed
        .tree
        .root()
        .first_child_or_token()
        .expect("Nat.zero term");
    support::with_app_harness("pick", |app| {
        // `pick (y := Nat.zero)`: `x` is missing, `y` is named.
        app.st.named_args = vec![NamedArg {
            name: "y".to_string(),
            val: Arg::Stx(val.clone()),
            num_implicit_params: 0,
        }];
        let got = leanr_elab::app::args::main(app, &parsed.tree.kinds).unwrap();

        assert_eq!(
            app.st.found_named_args,
            vec!["x".to_string()],
            "only the binder `findNamedArg?` MISSED is recorded — `y` matched \
             a named argument, so `main` takes the erase/elaborate branch and \
             never reaches `pushFoundNamedArg`"
        );

        let (binder_name, body) = match app.node(got) {
            leanr_kernel::bank::terms::Node::Lam {
                binder_name, body, ..
            } => (binder_name, body),
            other => panic!("eta expansion must emit a lambda, got {other:?}"),
        };
        let base = app.elab.view.store;
        let rendered = app
            .elab
            .mctx
            .store()
            .to_name(Some(base), binder_name)
            .to_string();
        assert_eq!(
            rendered, "x",
            "`finalize`'s `updateBinderNames` step (App.lean:623) must put the \
             PARAMETER's name back on the binder — `add_eta_arg` declares the \
             fvar under a fresh `_leanr_elab_binder_fresh` name so later \
             arguments cannot capture it, and that name must not survive"
        );
        assert!(
            matches!(app.node(body), leanr_kernel::bank::terms::Node::App { .. }),
            "the lambda's body is the saturated application `pick #0 Nat.zero`"
        );
    });
}

/// `elab_app_aux` brackets the whole `main` loop with
/// `lctx_checkpoint`/`lctx_restore`, so the fvars `add_eta_arg` pushes
/// are gone by the time the caller resumes. The oracle gets this from
/// `withLocalDeclD`'s scoping; leanr's `push_local_decl` is unscoped, so
/// a missing bracket would leak an eta fvar into every subsequent
/// `lctx_lookup_by_name` — invisible to the corpus, which elaborates
/// each query in a fresh `MetaCtx`.
#[test]
fn eta_expansion_leaves_no_fvar_in_the_ambient_lctx() {
    support::with_app_harness("Nat.zero", |app| {
        let before = app.elab.mctx.lctx_checkpoint();
        let snap = builtin::snapshot();
        let parsed = parse_term("pick (y := Nat.zero)", &snap);
        let elem = parsed
            .tree
            .root()
            .first_child_or_token()
            .expect("application term");
        let got = app
            .elab
            .elab_term(&elem, &parsed.tree.kinds, None)
            .expect("pick (y := Nat.zero) elaborates");
        assert!(
            matches!(app.node(got), leanr_kernel::bank::terms::Node::Lam { .. }),
            "end-to-end: a named argument with an earlier missing parameter \
             elaborates to a LAMBDA, not an application"
        );
        assert_eq!(
            before,
            app.elab.mctx.lctx_checkpoint(),
            "the eta fvar must not outlive the application elaborator"
        );
    });
}

/// oracle: `if (← read).ellipsis then addImplicitArg argName`
/// (`App.lean:856-857`) — with `..`, eta-expansion is DISABLED and every
/// missing argument becomes `_` (`App.lean:202-204`). No corpus query
/// uses `..` (it is otherwise M4b-3 P5's), so the arm is only reachable
/// from here: without it `pick ..` would finalize as the bare partial
/// application, a silently different term.
#[test]
fn ellipsis_fills_missing_explicit_args_with_implicit_mvars() {
    support::with_app_harness("pick", |app| {
        app.ctx.ellipsis = true;
        let snap = builtin::snapshot();
        let kinds = snap.kinds();
        let got = leanr_elab::app::args::main(app, &kinds).unwrap();
        assert!(
            app.st.eta_args.is_empty(),
            "`..` disables eta-expansion entirely"
        );
        // `pick ?m ?n` — two `App` spine nodes, both arguments mvars.
        let mut spine = Vec::new();
        let mut cur = got;
        while let leanr_kernel::bank::terms::Node::App { f, arg } = app.node(cur) {
            spine.push(arg);
            cur = f;
        }
        assert_eq!(spine.len(), 2, "both explicit parameters must be filled");
        for arg in spine {
            assert!(
                matches!(app.node(arg), leanr_kernel::bank::terms::Node::MVar { .. }),
                "`..` fills a missing argument with a fresh mvar"
            );
        }
    });
}

/// `has_opt_auto_params` is the oracle's `hasOptAutoParams`
/// (`App.lean:121-127`), which walks the telescope with
/// `forallTelescopeReducing` — it REDUCES as it goes. Task 4's version
/// walked the already-instantiated spine without reducing, so a binder
/// only revealed by WHNF was missed, and `main` finalized a bare partial
/// application where the oracle eta-expands.
///
/// Elab0 declares no `optParam` parameter (and no declaration whose type
/// hides a telescope behind a redex), so the type is built by hand:
/// `∀ (x : Nat), (fun (_ : Sort 0) => ∀ (y : optParam Nat Nat), Nat) (Sort 0)`.
/// Only a REDUCING walk sees `y`'s wrapper. With it, `x` becomes an eta
/// argument and the loop then hits `y`'s own P5 optParam seam; without
/// it, `main` would return the unchanged `pick`.
#[test]
fn has_opt_auto_params_reduces_to_find_a_hidden_optparam() {
    support::with_app_harness("pick", |app| {
        let base = app.elab.view.store;
        // `pick : ∀ (x : Nat), ∀ (y : Nat), Nat` — reuse its own
        // persistent `Nat` rather than re-resolving the constant.
        let nat = match app.node(app.st.f_type) {
            leanr_kernel::bank::terms::Node::Forall { binder_type, .. } => binder_type,
            other => panic!("pick's type must be a Forall, got {other:?}"),
        };
        let opt_name = {
            let store = app.elab.mctx.store_mut();
            let s = store.intern_str(Some(base), "optParam").unwrap();
            store.name_str(Some(base), None, s).unwrap()
        };
        let no_levels = app
            .elab
            .mctx
            .store_mut()
            .intern_level_list(None, &[])
            .unwrap();
        let opt_const = app
            .elab
            .mctx
            .store_mut()
            .expr_const(Some(base), Some(opt_name), no_levels)
            .unwrap();
        // `optParam Nat Nat` — `consume_type_annotations` reads the head
        // constant's name and takes the FIRST spine argument, so the
        // default value's own type is irrelevant to this test and never
        // inferred on the path it exercises.
        let opt_nat = {
            let partial = app
                .elab
                .mctx
                .store_mut()
                .expr_app(Some(base), opt_const, nat)
                .unwrap();
            app.elab
                .mctx
                .store_mut()
                .expr_app(Some(base), partial, nat)
                .unwrap()
        };
        let inner = app
            .elab
            .mctx
            .store_mut()
            .expr_forall(
                Some(base),
                None,
                opt_nat,
                nat,
                leanr_kernel::BinderInfo::Default,
            )
            .unwrap();
        let zero = app.elab.mctx.store_mut().level_zero(None).unwrap();
        let sort0 = app.elab.mctx.store_mut().expr_sort(None, zero).unwrap();
        let hidden = {
            let lam = app
                .elab
                .mctx
                .store_mut()
                .expr_lam(
                    Some(base),
                    None,
                    sort0,
                    inner,
                    leanr_kernel::BinderInfo::Default,
                )
                .unwrap();
            app.elab
                .mctx
                .store_mut()
                .expr_app(Some(base), lam, sort0)
                .unwrap()
        };
        app.st.f_type = app
            .elab
            .mctx
            .store_mut()
            .expr_forall(
                Some(base),
                None,
                nat,
                hidden,
                leanr_kernel::BinderInfo::Default,
            )
            .unwrap();

        let snap = builtin::snapshot();
        let kinds = snap.kinds();
        match leanr_elab::app::args::main(app, &kinds) {
            Err(leanr_elab::ElabError::UnsupportedSyntax(msg)) => assert!(
                msg.contains("optParam default"),
                "expected the P5 optParam seam once the eta argument exposed \
                 the hidden binder, got {msg:?}"
            ),
            other => panic!(
                "a non-reducing `has_opt_auto_params` would finalize the bare \
                 partial application instead of eta-expanding; got {other:?}"
            ),
        }
        assert_eq!(
            app.st.eta_args.len(),
            1,
            "the first parameter must have become an eta argument"
        );
    });
}

/// `getResultingTypeCore?`'s `findNamedArgDependsOn?` ESCAPE
/// (`App.lean:477-479`): when named arguments remain, the simulation
/// continues past the current parameter (`processImplicit' ()`) if one of
/// them DETERMINES it, and only postpones (`return none`) otherwise.
///
/// This is the branch Task 6 collapsed onto the postponement and Task 7
/// restored, so it gets a direct test on top of `app/namedDepPropagate2`:
/// the corpus record discriminates it only through the
/// `Unit`-is-a-reducible-abbrev-of-`PUnit` coincidence
/// (`app/propagateAbbrev`'s mechanism), which is a real but indirect
/// signal. Here the branch's own return value is the assertion —
/// `Some(?a)` with the escape, `None` without it — so a future
/// re-collapse fails on the shape rather than on an unfolding accident.
#[test]
fn get_resulting_type_escapes_past_a_parameter_a_named_arg_determines() {
    let snap = builtin::snapshot();
    let w = parse_term("PUnit.unit", &snap);
    let z = parse_term("Nat.zero", &snap);
    let w_elem = w.tree.root().first_child_or_token().expect("PUnit.unit");
    let z_elem = z.tree.root().first_child_or_token().expect("Nat.zero");
    support::with_app_harness("dpick", |app| {
        // `dpick {a : Type} (w : a) (x : Type) (z : x) : a` — the harness
        // already inserted `a`'s implicit mvar, so `f_type` is
        // `∀ (w : ?a) (x : Type) (z : x), ?a`.
        app.st.args = vec![Arg::Stx(w_elem.clone())];
        app.st.named_args = vec![NamedArg {
            name: "z".to_string(),
            val: Arg::Stx(z_elem.clone()),
            num_implicit_params: 0,
        }];

        let got = leanr_elab::app::propagate::get_resulting_type(app).unwrap();
        let resulting = got.expect(
            "the simulation must reach the result type: `w` consumes the positional \
             argument, then `x` is missing but `z : x` DEPENDS on it, so \
             `findNamedArgDependsOn?` returns `some` and the walk continues \
             (App.lean:478) instead of postponing",
        );
        assert!(
            matches!(
                app.node(resulting),
                leanr_kernel::bank::terms::Node::MVar { .. }
            ),
            "the resulting type is `dpick`'s own result parameter `?a` — an \
             UNASSIGNED mvar, which is exactly why the escape is observable: \
             propagating unifies the expected type with it here rather than \
             letting a later argument assign it"
        );
    });
}
