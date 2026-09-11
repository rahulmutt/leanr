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
/// argument and the loop then finds `y`'s own `optParam` wrapper (real
/// code since M4b-3 P5 task 8, not a seam); without it, `main` would
/// return the unchanged `pick`.
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
        // A non-reducing `has_opt_auto_params` would fail to see `y`'s
        // optParam through the beta-redex, leave `eta_args` empty, and
        // finalize the bare partial application instead of eta-expanding
        // `x` and then filling `y`'s default (Task 8) — so success alone
        // does not discriminate; the `eta_args` assertion below does.
        leanr_elab::app::args::main(app, &kinds).expect(
            "the reducing eta escape must expose `y`'s optParam default, \
             which Task 8 now fills",
        );
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

// ================================================================
// M4b-3 P1 task 8: `@` explicit mode, `.{u}` explicit universes, and
// the implicit-lambda guard.
// ================================================================

/// Elaborate `src` as a whole term, in the fixture environment, and
/// return the raw `Result`. `with_app_harness`'s head is irrelevant
/// here (`Nat.zero`, the cheapest constant) — only its `TermElabM` is
/// used. Mirrors `eta_expansion_leaves_no_fvar_in_the_ambient_lctx`'s
/// own in-harness `elab_term` call.
fn elab_src(src: &str) -> Result<leanr_kernel::bank::ExprId, leanr_elab::ElabError> {
    support::with_app_harness("Nat.zero", |app| {
        let snap = builtin::snapshot();
        let parsed = parse_term(src, &snap);
        assert!(parsed.errors.is_empty(), "{src}: {:?}", parsed.errors);
        let elem = parsed
            .tree
            .root()
            .first_child_or_token()
            .unwrap_or_else(|| panic!("{src}: no term child"));
        app.elab.elab_term(&elem, &parsed.tree.kinds, None)
    })
}

/// oracle: `mkConst` (`TermElabM.lean:2128-2136`) — "too many explicit
/// universe levels" is an ERROR, not a truncation. Elab0's `List` has
/// exactly one level parameter, so `List.{0, 0}` is the case.
///
/// Task 4 added the `TooManyUniverseLevels` check with no producer for
/// `explicit_levels`; this task is the producer, so this is the first
/// test that can reach it at all. The corpus cannot: a query whose
/// oracle side is an ERROR is never emitted by `dump_elab.lean` (it
/// logs to stderr and writes no record), so an over-long `.{..}` has no
/// possible corpus row.
#[test]
fn too_many_explicit_universe_levels_is_an_error() {
    match elab_src("List.{0, 0}") {
        Err(leanr_elab::ElabError::TooManyUniverseLevels(n)) => assert_eq!(n, "List"),
        other => panic!("expected TooManyUniverseLevels(\"List\"), got {other:?}"),
    }
}

/// The `.{u, v}` suffix's levels are the sepBy1 wrapper's EVEN-indexed
/// children (the oracle's `Syntax.getSepArgs`). Taking every child
/// instead would hand the `,` atom to `elab_level`; taking only the
/// first would silently drop `v`. `List.{0, 0}` discriminates both:
/// with `getSepArgs` it reaches `mkConst` with TWO levels and errors as
/// above, with a naive `first()` it would reach it with one and
/// succeed, and with no filtering at all it would fail inside
/// `elab_level` on the `<atom>` kind instead.
#[test]
fn explicit_univ_list_uses_sep_args_not_every_child() {
    // Single level: no separator involved, must succeed.
    assert!(elab_src("List.{0}").is_ok());
    // Two levels: both are seen (hence "too many"), and neither the
    // `,` atom nor a dropped second level is what surfaced.
    assert!(matches!(
        elab_src("List.{0, 0}"),
        Err(leanr_elab::ElabError::TooManyUniverseLevels(_))
    ));
}

/// oracle: `elabExplicit`'s `` `(@($t)) ``/`` `(@$t) `` arms
/// (`App.lean:2269-2270`) do NOT enter explicit mode — they elaborate `t`
/// with `implicitLambda := false`. Implemented by the M4b-3 close-out
/// (`elab.rs`'s `elab_term_without_implicit_lambda`); the corpus records
/// `closeout/explicit-*` pin the terms. This pins the retired seam's own
/// example as a success.
#[test]
fn at_on_a_parenthesised_term_elaborates_it() {
    assert!(
        elab_src("@(Nat.succ Nat.zero)").is_ok(),
        "`@(t)` must elaborate `t`, not raise a seam"
    );
}

/// `@0` is the `` `(@$t) `` arm with a non-`paren` `t`. Pinned binary:
/// `(@0 : {a : Type} → Nat)` fails with "failed to synthesize instance of
/// type class OfNat ({a : Type} → Nat) 0", while `(0 : {a : Type} → Nat)`
/// elaborates to `fun {a : Type} => 0`. So the `@` really does switch off
/// implicit-lambda insertion for a non-parenthesised term. The corpus
/// cannot hold this — an oracle error emits no record.
///
/// "failed to synthesize" is `synthesizeInstMVarCore`'s `.none` arm, which
/// is `ElabError::InstanceSynthesisFailed`. If leanr reports a different
/// variant here, stop and compare against the oracle; do not widen the
/// match.
#[test]
fn at_on_a_numeral_disables_implicit_lambda() {
    match support::elab_and_synthesize("(@0 : {a : Type} -> Nat)") {
        Err(leanr_elab::ElabError::InstanceSynthesisFailed { .. }) => {}
        other => panic!("expected InstanceSynthesisFailed, got {other:?}"),
    }
}

/// `@(e : T)` is the `` `(@$t) `` arm with a type ascription. Pinned
/// binary: `(@(Nat.zero : Nat) : {a : Type} → Nat)` is a type mismatch.
#[test]
fn at_on_an_ascription_is_a_type_mismatch() {
    match support::elab_result("(@(Nat.zero : Nat) : {a : Type} -> Nat)") {
        Err(leanr_elab::ElabError::TypeMismatch { .. }) => {}
        other => panic!("expected TypeMismatch, got {other:?}"),
    }
}

/// oracle: `elabAppFn`'s `` `(@$_) => throwUnsupportedSyntax ``
/// (`App.lean:2118`) — in a FUNCTION position `@` on anything outside
/// the seven `elabAtom` shapes is simply invalid; it is NOT the
/// implicit-lambda-disabling form (that one is only reachable when the
/// `@..` node is the whole term). Two different oracle arms; only this
/// one is still a seam (the other is implemented by the M4b-3
/// close-out).
#[test]
fn at_on_a_non_atom_head_is_an_invalid_occurrence() {
    match elab_src("@(Nat.succ) Nat.zero") {
        Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => {
            assert!(
                m.contains("invalid occurrence of `@`"),
                "a head-position `@` seam must cite App.lean:2118, got {m:?}"
            );
        }
        other => panic!("expected the head-position `@` seam, got {other:?}"),
    }
}

/// Pins spec § Design 5's first bullet: "`false` skips
/// `use_implicit_lambda` entirely, including its `.postpone` arm."
/// oracle: `useImplicitLambda`'s local-identifier-with-mvar-type special
/// case, `TermElabM.lean:1753-1778` (`return .postpone` at `:1778`),
/// consulted by `elabTermAux`'s `| .postpone =>` dispatch arm
/// (`:1843`) — but only when `elabTermAux` is called with
/// `implicitLambda := true`; `elab_term_core`'s `false` path never
/// calls `use_implicit_lambda` at all (`elab.rs`, above), so this local
/// never reaches the postpone check in the first place.
///
/// `@(f)`'s inner `f` is exactly the shape `useImplicitLambda`'s
/// special case exists for: a bare local identifier whose own type is
/// still an unassigned metavariable (`fun f => ..` gives `f` no
/// annotation). Confirmed against the pinned `lean` binary: `fun f =>
/// (@(f) : {a : Type} -> Nat)` elaborates to `fun (f : {a : Type} →
/// Nat) => f` — `f`'s mvar type unifies directly against the
/// ascription's expected type, with no implicit-lambda wrapping and no
/// postponement.
///
/// Without the guard this test exists to pin, a caller could
/// reintroduce a `use_implicit_lambda` consultation into the `false`
/// path (e.g. ahead of dispatch) and every other `leanr_elab` test
/// still passes, because nothing else drives an `@`-disabled term
/// through a local whose type is an unassigned mvar. Asserting on the
/// JSON shape (not just `is_ok`) also rules out a version that
/// succeeds for the wrong reason (e.g. an implicit lambda silently
/// re-inserted around `f`).
#[test]
fn at_on_a_local_with_mvar_type_skips_the_postpone_arm() {
    let j = support::elab_and_synthesize("(fun f => (@(f) : {a : Type} -> Nat))")
        .unwrap_or_else(|e| panic!("expected Ok, got {e:?}"));
    assert_eq!(
        j["k"], "lam",
        "must be `fun (f : {{a : Type}} -> Nat) => f`"
    );
    assert_eq!(
        j["b"],
        serde_json::json!({"k": "bvar", "i": 0}),
        "the body must be plain `f` (a bvar into the outer binder) — an \
         implicit lambda around it, or a postpone-arm error, would both \
         show `use_implicit_lambda` was consulted for `f` despite the \
         `false` (no-implicit-lambda) path"
    );
}

/// Under `@`, `processImplicitArg` delegates to `processExplicitArg`
/// (`App.lean:882-886`), so an implicit parameter is filled from the
/// POSITIONAL arguments. The corpus record `app/atId` covers the
/// success shape; this covers the complementary one the corpus cannot:
/// WITHOUT `@`, the same positional argument list is one too many, and
/// the oracle's `explicit` flag is the only thing that tells the two
/// apart.
#[test]
fn explicit_mode_consumes_implicit_params_positionally() {
    // `id {α : Sort u} (a : α) : α`. With `@`, `Nat` fills `α`.
    assert!(
        elab_src("@id Nat Nat.zero").is_ok(),
        "`@id Nat Nat.zero` must fill the implicit `α` positionally"
    );
    // Without `@`, `α` is inserted as an mvar, `Nat` fills the single
    // explicit parameter `a` (assigning `α := Nat` along the way), and
    // `Nat.zero` is left over with no parameter to fill: `id`'s result
    // type is `α`, which instantiates to the now-concrete `Nat` — a
    // genuinely non-function type, so `main`'s
    // `synthesize_pending_and_normalize_fun_type` reports
    // `FunctionExpected` rather than a seam (M4b-3 P2a task 8).
    match elab_src("id Nat Nat.zero") {
        Err(leanr_elab::ElabError::FunctionExpected { .. }) => {}
        other => panic!("expected FunctionExpected without `@`, got {other:?}"),
    }
}

/// oracle: `useImplicitLambda` (`TermElabM.lean:1743-1779`) fires only
/// when the whnf'd expected type is a `forallE` whose binder info is
/// IMPLICIT or INST-IMPLICIT — `unless c.isImplicit || c.isInstImplicit
/// do return .no` (`:1751`), with the function's own doc comment
/// spelling out the exclusion: "implicit lambdas are not triggered by
/// the strict implicit binder annotation `{{a : α}} → β`".
///
/// Was `implicit_lambda_guard_fires_only_for_implicit_and_inst_implicit`,
/// asserting the P1 guard's `Err(UnsupportedSyntax("implicit lambda
/// insertion"))`. M4b-3 P5 task 5 turned that guard into a real wrap
/// (`elab.rs`'s `use_implicit_lambda` + `elab_implicit_lambda`), so
/// "fires" now means "produces a `Lam`", not "errors" — updated in
/// place rather than left pinning behaviour that no longer exists.
///
/// The corpus cannot discriminate this at all: no committed record has
/// an implicit-`forall` expected type (source ascription is the only
/// expected-type source, and no fixture declaration is ascribed to one),
/// so a guard that tested all three implicit flavours — the shape this
/// task's own brief paraphrased — would keep every record green while
/// diverging from the oracle. Each binder info is asserted directly.
#[test]
fn implicit_lambda_wraps_only_for_implicit_and_inst_implicit() {
    use leanr_kernel::BinderInfo::*;
    for (bi, should_wrap) in [
        (Implicit, true),
        (InstImplicit, true),
        (StrictImplicit, false),
        (Default, false),
    ] {
        support::with_app_harness("Nat.zero", |app| {
            // `∀ (_ : Nat) , Nat` at binder info `bi`, built from
            // `Nat.zero`'s own PERSISTENT type — `base = Some(..)`
            // throughout, per `Store::store_for`'s misrouting hazard.
            let nat = app.elab.mctx.infer_type(app.st.f).unwrap();
            let base = app.elab.view.store;
            let expected = app
                .elab
                .mctx
                .store_mut()
                .expr_forall(Some(base), None, nat, nat, bi)
                .unwrap();

            let snap = builtin::snapshot();
            let parsed = parse_term("Nat.zero", &snap);
            let elem = parsed.tree.root().first_child_or_token().unwrap();
            let got = app
                .elab
                .elab_term(&elem, &parsed.tree.kinds, Some(expected))
                .unwrap_or_else(|e| panic!("binder info {bi:?}: elaboration failed: {e:?}"));
            let wrapped = matches!(
                app.node(got),
                leanr_kernel::bank::terms::Node::Lam { binder_info, .. } if binder_info == bi
            );
            assert_eq!(
                wrapped,
                should_wrap,
                "binder info {bi:?}: got {:?}",
                app.node(got)
            );
        });
    }
}

/// oracle: `blockImplicitLambda` (`TermElabM.lean:1716-1720`) runs
/// BEFORE the expected type is examined, and its exclusion list is what
/// keeps the guard above from firing on shapes the oracle elaborates
/// normally. Each entry is checked against the SAME implicit-`forall`
/// expected type that makes the guard fire for a bare identifier — so a
/// missing disjunct is a test failure, not a silent widening.
///
/// This is the property the full corpus gate can only test negatively
/// (a guard that over-fires turns green records red); here it is tested
/// positively, one disjunct at a time.
#[test]
fn block_implicit_lambda_covers_the_oracles_exclusion_list() {
    // `None` = must elaborate; `Some(needle)` = the guard is suppressed
    // but a DIFFERENT named seam is reached, identified by its message.
    for (src, seam) in [
        // isExplicit — `@f`
        ("@Nat.succ", None::<&str>),
        // isExplicitApp — `@f a`
        ("@id Nat Nat.zero", None),
        // isHole — `_`
        ("_", None),
        // isTypeAscription — `(e : T)`
        ("(Nat.zero : Nat)", None),
        // isLambdaWithImplicit — `fun {α} => ..`. `fun`'s own
        // implicit-binder arm (`builtin::binder`) now elaborates (M4b-3
        // P5 task 1), so this source positively demonstrates guard
        // suppression via full success, like the other disjuncts.
        ("fun {a : Nat} => Nat.zero", None),
        // dropParens: the disjuncts see through leading `(..)`
        ("(@Nat.succ)", None),
    ] {
        support::with_app_harness("Nat.zero", |app| {
            let nat = app.elab.mctx.infer_type(app.st.f).unwrap();
            let base = app.elab.view.store;
            let expected = app
                .elab
                .mctx
                .store_mut()
                .expr_forall(
                    Some(base),
                    None,
                    nat,
                    nat,
                    leanr_kernel::BinderInfo::Implicit,
                )
                .unwrap();

            let snap = builtin::snapshot();
            let parsed = parse_term(src, &snap);
            assert!(parsed.errors.is_empty(), "{src}: {:?}", parsed.errors);
            let elem = parsed.tree.root().first_child_or_token().unwrap();
            let got = app
                .elab
                .elab_term(&elem, &parsed.tree.kinds, Some(expected));
            match seam {
                // The guard was suppressed and elaboration ran to
                // completion. Asserted POSITIVELY: an `is_ok()` test
                // cannot pass on a `TypeMismatch`, on an unrelated
                // `UnsupportedSyntax`, or on a re-introduced implicit
                // lambda error, which is exactly what the earlier
                // `if let Err(UnsupportedSyntax(m)) = &got` shape did.
                None => assert!(
                    got.is_ok(),
                    "{src}: blockImplicitLambda must suppress the guard, got {got:?}"
                ),
                // The guard was suppressed, but elaboration then hit a
                // DIFFERENT, named seam. Pinned by its own message, so
                // this arm is equally unable to pass on `Ok` or on the
                // implicit-lambda error.
                Some(needle) => match &got {
                    Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => {
                        assert!(
                            m.contains(needle),
                            "{src}: expected the {needle:?} seam, got {m:?}"
                        );
                        assert!(
                            !m.contains("implicit lambda insertion"),
                            "{src}: blockImplicitLambda must suppress the guard, got {m:?}"
                        );
                    }
                    other => panic!("{src}: expected the {needle:?} seam, got {other:?}"),
                },
            }
        });
    }
}

/// oracle: `processStrictImplicitArg` (`App.lean:891-897`) — under `@`
/// it delegates to `processExplicitArg`, so a strict-implicit parameter
/// is filled from the POSITIONAL arguments; without `@` (and with
/// arguments left) it inserts an mvar instead and the positional
/// argument survives with no parameter to fill. The synthetic `fType`
/// here is `∀ {{_ : Nat}}, Nat` — non-dependent, so once the mvar is
/// inserted the result type is the concrete `Nat`, a genuinely
/// non-function type: `synthesize_pending_and_normalize_fun_type`
/// reports `FunctionExpected` (M4b-3 P2a task 8), not a seam.
///
/// Newly live in P1 task 8 (a different task 8 from the P2a one cited
/// above): `ctx.explicit` was permanently `false` when this arm was
/// written, so its `explicit` half had never executed.
/// The corpus still cannot reach it (Elab0 declares no strict-implicit
/// constant), hence the synthetic `fType` — the same technique
/// `strict_implicit_without_args_finalizes` above uses, `Some(base)`
/// throughout per that test's store-routing citation.
#[test]
fn explicit_mode_fills_a_strict_implicit_from_positional_args() {
    for explicit in [false, true] {
        support::with_app_harness("pick", |app| {
            let base = app.elab.view.store;
            let nat = match app.node(app.st.f_type) {
                leanr_kernel::bank::terms::Node::Forall { binder_type, .. } => binder_type,
                other => panic!("pick's type must be a Forall, got {other:?}"),
            };
            // `∀ {{_ : Nat}}, Nat`.
            app.st.f_type = app
                .elab
                .mctx
                .store_mut()
                .expr_forall(
                    Some(base),
                    None,
                    nat,
                    nat,
                    leanr_kernel::BinderInfo::StrictImplicit,
                )
                .unwrap();
            app.st.f_args = Vec::new();

            let snap = builtin::snapshot();
            let parsed = parse_term("Nat.zero", &snap);
            let elem = parsed.tree.root().first_child_or_token().unwrap();
            app.st.args = vec![Arg::Stx(elem)];
            app.ctx.explicit = explicit;

            let kinds = snap.kinds();
            let got = leanr_elab::app::args::main(app, &kinds);
            if explicit {
                let got = got.expect("under `@` the positional argument fills the parameter");
                let arg = match app.node(got) {
                    leanr_kernel::bank::terms::Node::App { arg, .. } => arg,
                    other => panic!("expected an application, got {other:?}"),
                };
                assert!(
                    matches!(app.node(arg), leanr_kernel::bank::terms::Node::Const { .. }),
                    "under `@` the argument is the ELABORATED `Nat.zero`, not a fresh mvar"
                );
            } else {
                match got {
                    Err(leanr_elab::ElabError::FunctionExpected { .. }) => {}
                    other => panic!(
                        "without `@` the strict implicit takes an mvar, the result type \
                         `Nat` is concrete, and the leftover positional argument should \
                         report FunctionExpected, got {other:?}"
                    ),
                }
            }
        });
    }
}

/// `optParam <ty> <default>` built by hand — Elab0 declares no
/// `optParam` parameter. `ty` and `default` are taken SEPARATELY (not a
/// single `nat` reused for both) so a test built from this can tell
/// `opt_param_default` apart from a broken sibling that returns
/// `args[0]` (the annotated type) instead of `args[1]` (the default) —
/// passing the same `ExprId` for both would make that swap invisible.
/// `Some(base)` throughout, per
/// `f_type_is_forall_reconstructs_dependent_domain_with_correct_base`'s
/// store-routing citation.
fn opt_param_of(
    app: &mut leanr_elab::app::state::AppElab,
    ty: leanr_kernel::bank::ExprId,
    default: leanr_kernel::bank::ExprId,
) -> leanr_kernel::bank::ExprId {
    let base = app.elab.view.store;
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
    let partial = app
        .elab
        .mctx
        .store_mut()
        .expr_app(Some(base), opt_const, ty)
        .unwrap();
    app.elab
        .mctx
        .store_mut()
        .expr_app(Some(base), partial, default)
        .unwrap()
}

/// `pick`'s own persistent `Nat` (its first binder's domain).
fn nat_of(app: &leanr_elab::app::state::AppElab) -> leanr_kernel::bank::ExprId {
    match app.node(app.st.f_type) {
        leanr_kernel::bank::terms::Node::Forall { binder_type, .. } => binder_type,
        other => panic!("pick's type must be a Forall, got {other:?}"),
    }
}

/// oracle: `processExplicitArg`'s optParam/autoParam block
/// (`App.lean:826-854`) is `match (← read).explicit, ..` whose every
/// default-filling arm has `false` as its first scrutinee — under `@`
/// none of them match and control falls through to `App.lean:855`'s
/// `| _, _, _ =>` arm. `fType` here is `∀ (y : optParam Nat Nat), Nat`,
/// so the CURRENT parameter is the wrapped one:
///   * `explicit = false` — Task 8's `optParam` default arm fires:
///     `y`'s default (the synthetic `nat` built by `opt_param_of`) is
///     appended as the argument.
///   * `explicit = true`  — falls through to `finalize`, `f` unchanged.
///
/// Was written in Task 4/5, while `ctx.explicit` was permanently
/// `false` and the default arm itself was still the deferred P5 seam;
/// updated by Task 8 now that the arm is implemented. The corpus still
/// cannot reach this shape (Elab0 declares no bare `optParam` parameter
/// on a two-`Nat`-arg function), hence the direct test.
#[test]
fn explicit_mode_skips_the_optparam_default() {
    for explicit in [false, true] {
        support::with_app_harness("pick", |app| {
            let base = app.elab.view.store;
            let nat = nat_of(app);
            // A default DISTINCT from the annotated type — `Nat.zero`,
            // not `nat` again — so this test can tell `opt_param_default`
            // apart from a broken sibling that returns `args[0]` (the
            // type) instead of `args[1]` (the default).
            let default = support::fixture_const(app, "Nat.zero");
            let opt_nat = opt_param_of(app, nat, default);
            app.st.f_type = app
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
            app.st.f_args = Vec::new();
            app.st.args = Vec::new();
            app.ctx.explicit = explicit;

            let f_before = app.st.f;
            let snap = builtin::snapshot();
            let kinds = snap.kinds();
            let got = leanr_elab::app::args::main(app, &kinds);
            if explicit {
                assert_eq!(
                    got.expect("under `@` the default is not filled — finalize"),
                    f_before,
                    "under `@` the optParam default arm does not match \
                     (App.lean:827-828)"
                );
            } else {
                let expected = app
                    .elab
                    .mctx
                    .store_mut()
                    .expr_app(Some(base), f_before, default)
                    .unwrap();
                assert_eq!(
                    got.expect("without `@` the declared default fills the argument"),
                    expected,
                    "without `@` the optParam default (App.lean:827-828) must be \
                     appended to `f` directly, not left unfilled"
                );
            }
        });
    }
}

/// oracle: the eta escape at `App.lean:870-873` — `else if !(← read)
/// .explicit then if (← hasOptAutoParams (← getFType)) then addEtaArg`.
/// A LATER parameter carrying a default eta-expands the application,
/// but only when `@` was NOT used; under `@` control reaches
/// `finalize` (`App.lean:877`) instead. `fType` here is
/// `∀ (x : Nat) (y : optParam Nat Nat), Nat`, so the current parameter
/// (`x`) is unwrapped and only `hasOptAutoParams` can see `y`:
///   * `explicit = false` — `x` becomes an eta argument, and the loop
///     then reaches `y`'s own optParam default arm (Task 8), which fills
///     it and finalizes successfully;
///   * `explicit = true`  — finalizes `f` unchanged, no eta argument.
///
/// A separate test from `explicit_mode_skips_the_optparam_default`
/// above because the two `!`s are separate gates: measured, each shape
/// discriminates only its own (the current-parameter shape leaves the
/// eta gate unreached, and this shape leaves the default gate's `if`
/// body unreached).
#[test]
fn explicit_mode_skips_the_optparam_eta_escape() {
    for explicit in [false, true] {
        support::with_app_harness("pick", |app| {
            let base = app.elab.view.store;
            let nat = nat_of(app);
            // Distinct from `nat` for the same reason as
            // `explicit_mode_skips_the_optparam_default`, even though
            // this test doesn't assert the filled value's identity —
            // keeping `opt_param_of`'s two arguments genuinely distinct
            // everywhere is what makes the helper itself trustworthy.
            let default = support::fixture_const(app, "Nat.zero");
            let opt_nat = opt_param_of(app, nat, default);
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
            app.st.f_type = app
                .elab
                .mctx
                .store_mut()
                .expr_forall(
                    Some(base),
                    None,
                    nat,
                    inner,
                    leanr_kernel::BinderInfo::Default,
                )
                .unwrap();
            app.st.f_args = Vec::new();
            app.st.args = Vec::new();
            app.ctx.explicit = explicit;

            let f_before = app.st.f;
            let snap = builtin::snapshot();
            let kinds = snap.kinds();
            let got = leanr_elab::app::args::main(app, &kinds);
            if explicit {
                assert_eq!(
                    got.expect("under `@` the application finalizes as-is"),
                    f_before,
                    "under `@` the `hasOptAutoParams` eta escape is skipped"
                );
                assert!(
                    app.st.eta_args.is_empty(),
                    "under `@` no eta argument is added"
                );
            } else {
                got.expect(
                    "without `@` the eta escape exposes `y`'s optParam default, \
                     which Task 8 now fills",
                );
                assert_eq!(
                    app.st.eta_args.len(),
                    1,
                    "without `@` `x` becomes an eta argument (App.lean:873)"
                );
            }
        });
    }
}

// =======================================================================
// `app::propagate`'s two PURE functions. Oracle: `Expr.isProp`
// (`Lean/Expr.lean:837-839`) and `shouldPropagateExpectedTypeFor`
// (`App.lean:516-523`). Both decide, syntactically, whether expected-type
// propagation runs at all, and both were transcribed wrong at least once
// while this plan was written — hence direct tests rather than relying on
// the corpus, which reaches neither predicate's interesting inputs.
// =======================================================================

/// oracle: `Expr.isProp` — `| sort .zero => true | _ => false`.
///
/// Five cases, each of which kills a specific plausible wrong
/// implementation (measured; see the plan's fix report):
///   - `Sort 0` true kills the SEMANTIC `Lean.Meta.isProp` ("does `e`
///     have type `Sort 0`"), for which `Sort 0 : Sort 1` is false.
///   - `Sort 1` false and `Sort ?u` false kill `Node::Sort { .. } => true`.
///   - a non-`Sort` node false kills "anything at all is Prop".
///   - `Sort (max 0 0)` false kills a level-NORMALIZING check. leanr's
///     `LevelRow` is non-normalizing and so is `Expr.isProp`: the oracle
///     matches the `Level` constructor, and `.max .zero .zero` is not
///     `.zero`. This is the case a `whnf`-flavoured or `Level.normalize`-
///     flavoured reading would get wrong.
#[test]
fn is_prop_is_the_syntactic_sort_zero_test() {
    support::with_app_harness("Nat.zero", |app| {
        let base = app.elab.view.store;

        let zero = app.elab.mctx.store_mut().level_zero(Some(base)).unwrap();
        let one = app
            .elab
            .mctx
            .store_mut()
            .level_succ(Some(base), zero)
            .unwrap();
        let max00 = app
            .elab
            .mctx
            .store_mut()
            .level_max(Some(base), zero, zero)
            .unwrap();
        let umvar = app.elab.mk_fresh_level_mvar().unwrap();

        let mk_sort = |app: &mut leanr_elab::app::state::AppElab, l| {
            app.elab.mctx.store_mut().expr_sort(Some(base), l).unwrap()
        };
        let sort0 = mk_sort(app, zero);
        let sort1 = mk_sort(app, one);
        let sort_max00 = mk_sort(app, max00);
        let sort_mvar = mk_sort(app, umvar);

        // `Sort 0` is `Prop`, the ONLY true case.
        assert!(
            leanr_elab::app::propagate::is_prop(app, sort0),
            "Sort 0 is Prop"
        );
        // `Sort 1` is `Type`.
        assert!(
            !leanr_elab::app::propagate::is_prop(app, sort1),
            "Sort 1 is Type, not Prop"
        );
        // A `Sort` over an unassigned level mvar is not syntactically
        // `Sort .zero`, whatever it may later be assigned.
        assert!(
            !leanr_elab::app::propagate::is_prop(app, sort_mvar),
            "Sort ?u is not syntactically Sort 0"
        );
        // `Sort (max 0 0)` is `Prop` up to level normalization, and the
        // oracle still says false.
        assert!(
            !leanr_elab::app::propagate::is_prop(app, sort_max00),
            "Expr.isProp matches the Level CONSTRUCTOR; max 0 0 is not .zero"
        );
        // A non-`Sort` node. `app.st.f` is the elaborated head `Nat.zero`
        // — a `Const`, and the closest thing the fixture env has to the
        // "expected type is a proposition-valued application" shape whose
        // syntactic/semantic disagreement `is_prop`'s doc calls out.
        let head = app.st.f;
        assert!(
            !leanr_elab::app::propagate::is_prop(app, head),
            "a Const is not Sort 0"
        );
    });
}

/// oracle: `shouldPropagateExpectedTypeFor` (`App.lean:516-523`) —
/// `false` for an already-elaborated `Arg.expr`, and for the three
/// syntax kinds whose elaboration is DEFERRED; `true` otherwise.
///
/// Discrimination (measured): dropping any ONE of the three excluded
/// kinds flips that kind's case, and returning `true` for `Arg::Expr`
/// flips the first case — so this test cannot pass on a partial
/// exclusion list, which is exactly how the plan first wrote it.
#[test]
fn should_propagate_expected_type_for_excludes_deferred_kinds() {
    use leanr_elab::app::propagate::should_propagate_expected_type_for;

    let snap = builtin::snapshot();

    // `Arg.expr` — already elaborated, nothing left to inform. Needs a
    // genuine `ExprId` (the id newtype has no public constructor), so it
    // borrows the harness's elaborated head.
    support::with_app_harness("Nat.zero", |app| {
        let parsed = parse_term("Nat.zero", &snap);
        let arg = Arg::Expr(app.st.f);
        assert!(
            !should_propagate_expected_type_for(&arg, &parsed.tree.kinds),
            "Arg::Expr is already elaborated"
        );
    });

    for (src, expected) in [
        // `_` — becomes an mvar.
        ("_", false),
        // `?x` — becomes a synthetic-opaque mvar.
        ("?x", false),
        // `by ..` — becomes a tactic mvar.
        ("by skip", false),
        // Everything else propagates.
        ("Nat.zero", true),
        ("(Nat.zero)", true),
        ("fun x => x", true),
        ("Nat.succ Nat.zero", true),
    ] {
        let parsed = parse_term(src, &snap);
        // `by skip` deliberately carries a parse error (`Elab0` registers
        // no tactics); only the KIND matters to this predicate, and the
        // kind is asserted below so a parser change cannot silently turn
        // this case vacuous.
        let elem = parsed
            .tree
            .root()
            .first_child_or_token()
            .unwrap_or_else(|| panic!("{src}: no term element"));
        let kind = parsed.tree.kinds.name(elem.kind()).to_string();
        let want_kind = match src {
            "_" => "Lean.Parser.Term.hole",
            "?x" => "Lean.Parser.Term.syntheticHole",
            "by skip" => "Lean.Parser.Term.byTactic",
            "Nat.zero" => "<ident>",
            "(Nat.zero)" => "Lean.Parser.Term.paren",
            "fun x => x" => "Lean.Parser.Term.fun",
            _ => "Lean.Parser.Term.app",
        };
        assert_eq!(kind, want_kind, "{src}: unexpected syntax kind");
        assert_eq!(
            should_propagate_expected_type_for(&Arg::Stx(elem), &parsed.tree.kinds),
            expected,
            "{src} (kind {kind})"
        );
    }
}

/// oracle: `isNextOutParamOfLocalInstanceAndResult` (`App.lean:681-727`)
/// — the `resultTypeOutParam?` PRODUCER (M4b-3 P2b-ii). `Get.get`'s
/// `{elem}` is the result type AND the outParam of the local instance
/// `[self : Get cont idx elem]`, so processing it marks the mvar and
/// disables expected-type propagation (`App.lean:747-755`).
///
/// Driven with the flag FORCED on because this test calls
/// `app::args::main` directly rather than through `elab_app_aux`, which
/// is the only thing that computes `result_is_out_param_support`
/// (`app/mod.rs:413`). It is not a stand-in for an environment that
/// cannot reach the flag: `Elab0.lean` has declared
/// `Lean.Internal.coeM` since M4b-3 P4 task 5, so end-to-end the flag
/// is `true` for a non-`@` application — pinned by
/// `synthetic_smoke.rs`'s `coe_m_gate_enables_eager_defaulting_from_source`.
///
/// `main` finalizes the bare partial application (no arguments), which
/// takes the branch's ELSE arm
/// (`eType` is `?idx → ?elem`, not the outParam mvar itself) — so this
/// also pins that the else arm returns without error.
#[test]
fn producer_marks_the_result_type_out_param_of_a_local_instance() {
    support::with_app_args("Get.get", &[], |app, kinds| {
        app.ctx.result_is_out_param_support = true;
        app.st.propagate_expected = true;
        leanr_elab::app::args::main(app, kinds).expect("bare `Get.get` finalizes");
        let out = app
            .st
            .result_type_out_param
            .expect("`elem` is the outParam of `[Get cont idx elem]` and the result type");
        assert!(
            !app.st.propagate_expected,
            "marking the result type as an outParam disables propagation (App.lean:753)"
        );
        assert!(
            !app.elab.mctx.mctx().is_assigned(out),
            "nothing determines `?elem` on a bare partial application"
        );
    });
}

/// The producer's THREE false directions, each of which a constant-`true`
/// mutation of one clause would flip (design spec § Amendment 4 item 7,
/// `Elab0.lean`'s `getFst` comment):
///
///   * `useWrap` — `Wrap` has no outParams, so
///     `hasLocalInstanceWithOutParams` (`:700-706`) is false;
///   * `getFst`'s `{cont}` — the result type, but position 0 of `Get`
///     is not an `outParam` position, so `isOutParamOf` (`:718-727`)
///     is false;
///   * `getFst`'s `{elem}` — an outParam of the local instance, but not
///     the result type, so `isResultType` (`:693-697`) is false.
///
/// `getFst` covers the last two at once: if EITHER clause were a
/// constant `true`, one of its two implicits would be marked.
///
/// Caveat, measured rather than assumed: a constant-`true` mutation of
/// `has_local_instance_with_out_params` is NOT killed by any test in
/// this crate (the positional clause re-checks it independently), so
/// this test's own name overstates that one direction; only the
/// `useWrap` row here kills that clause's `→ false` mutation.
#[test]
fn producer_answers_false_on_each_of_its_three_gates() {
    for head in ["useWrap", "getFst"] {
        support::with_app_args(head, &[], |app, kinds| {
            app.ctx.result_is_out_param_support = true;
            app.st.propagate_expected = true;
            leanr_elab::app::args::main(app, kinds)
                .unwrap_or_else(|e| panic!("bare `{head}` finalizes: {e:?}"));
            assert!(
                app.st.result_type_out_param.is_none(),
                "{head}: no implicit is the outParam of a local instance AND the result type"
            );
            assert!(
                app.st.propagate_expected,
                "{head}: propagation stays enabled when the producer answers false"
            );
        });
    }
}

/// `Context.resultIsOutParamSupport = false` short-circuits the producer
/// (`App.lean:682-683`, "if `resultIsOutParamSupport` is `false`, this
/// method returns `false`") — under `@`, and in every env without
/// `Lean.Internal.coeM`, `Get.get` is elaborated with no special support.
#[test]
fn producer_is_inert_when_the_context_flag_is_off() {
    support::with_app_args("Get.get", &[], |app, kinds| {
        assert!(!app.ctx.result_is_out_param_support, "harness default");
        app.st.propagate_expected = true;
        leanr_elab::app::args::main(app, kinds).expect("bare `Get.get` finalizes");
        assert!(app.st.result_type_out_param.is_none());
        assert!(app.st.propagate_expected);
    });
}

/// oracle: `finalize`'s outParam branch, INTERESTING arm
/// (`App.lean:641-644`): the outParam mvar is still unassigned after
/// `synthesizeAppInstMVars` and `eType` IS that mvar, so
/// `synthesizeSyntheticMVarsUsingDefault` runs HERE, inside the
/// application elaborator, and the `OfNat` default instance fires before
/// any enclosing fixpoint gets a chance.
///
/// Observed through P3's `default_walk_log`: the walk visits mvars only
/// when rung 3 runs, and nothing but this branch runs rung 3 inside
/// `args::main`. The `Get Cell ?α ?elem` goal is then solved by the
/// loop's interleaved `synthesizeSyntheticMVars`, so `?elem := Unit`
/// is assigned by the time `main` returns — which is the entire point of
/// the feature (`App.lean:150-166`).
#[test]
fn finalize_applies_default_instances_when_the_out_param_is_still_open() {
    support::with_app_args("Get.get", &["cell", "0"], |app, kinds| {
        app.ctx.result_is_out_param_support = true;
        app.st.propagate_expected = true;
        leanr_elab::synthetic::default_walk_log_reset();
        let e = leanr_elab::app::args::main(app, kinds).expect("`Get.get cell 0` elaborates");
        let visited = leanr_elab::synthetic::default_walk_log_take();
        assert!(
            !visited.is_empty(),
            "rung 3 must run INSIDE finalize on the open-outParam shape"
        );
        let out = app.st.result_type_out_param.expect("producer fired");
        assert!(
            app.elab.mctx.mctx().is_assigned(out),
            "`?elem` is assigned as a RESULT of the eager default (Unit, via instGetCellNat)"
        );
        let ty = app.elab.mctx.infer_type(e).expect("infer");
        let ty = app.elab.mctx.instantiate_mvars(ty).expect("instantiate");
        let base = app.elab.view.store;
        let carrier = match app.node(ty) {
            leanr_kernel::bank::terms::Node::Const { name: Some(n), .. } => app
                .elab
                .mctx
                .store()
                .to_name(Some(base), Some(n))
                .to_string(),
            other => panic!("the application's type is not a constant: {other:?}"),
        };
        assert_eq!(
            carrier, "Unit",
            "the application's type is the fixed carrier"
        );
        assert!(
            app.elab.pending_mvars.is_empty(),
            "the interleaved synthesizeSyntheticMVars closed the instance goal too"
        );
    });
}

/// oracle: the branch's ELSE arm (`App.lean:645-646`) — "If `eType !=
/// mkMVar outParamMVarId`, then the function is partially applied, and
/// we do not apply default instances." Design spec § Amendment 4 item
/// 10: this is a smoke test, not a corpus record, because on a green
/// term the arm's effect is invisible in the emitted `Expr` and the
/// oracle's dumper drops a partially-applied query (its instance goal
/// stays stuck through the fixpoint).
///
/// The discriminator is the walk log again: with `Get Cell ?idx ?elem`
/// PENDING and the arm taken, rung 3 must NOT run; a mutation that
/// always applies defaults visits that goal and the log is non-empty.
#[test]
fn finalize_skips_default_instances_on_a_partial_application() {
    support::with_app_args("Get.get", &["cell"], |app, kinds| {
        app.ctx.result_is_out_param_support = true;
        app.st.propagate_expected = true;
        leanr_elab::synthetic::default_walk_log_reset();
        leanr_elab::app::args::main(app, kinds).expect("`Get.get cell` finalizes");
        let visited = leanr_elab::synthetic::default_walk_log_take();
        assert!(
            visited.is_empty(),
            "partially applied: no default-instance walk, got {visited:?}"
        );
        assert_eq!(
            app.elab.pending_mvars.len(),
            1,
            "the stuck `Get Cell ?idx ?elem` goal is registered pending, not solved or reported"
        );
        let out = app.st.result_type_out_param.expect("producer fired");
        assert!(!app.elab.mctx.mctx().is_assigned(out));
    });
}

/// The producer disables expected-type propagation (`App.lean:753`), so
/// with an expected type in hand `?elem` must be assigned by the DEFAULT
/// rung, not by `propagateExpectedType`: the walk log is non-empty.
/// Leaving propagation on assigns `?elem := Unit` at the first explicit
/// argument, the guard's `isAssigned` then sees it, and the log stays
/// EMPTY — which is how this test kills that mutation.
///
/// What it does NOT discriminate, stated so nobody claims it later: the
/// branch's early `return e` (`App.lean:644,646`) also skips `finalize`'s
/// own `isDefEq expectedType eType` (design spec § Amendment 4 item 5),
/// but by the time control would reach that block the default rung has
/// already assigned `?elem`, so falling through changes nothing a leanr
/// term can observe. The early return is transliterated because the
/// oracle has it, not because a test needs it.
#[test]
fn finalize_under_an_expected_type_still_defaults_rather_than_unifies() {
    support::with_app_args("Get.get", &["cell", "0"], |app, kinds| {
        app.ctx.result_is_out_param_support = true;
        app.st.propagate_expected = true;
        app.st.expected_type = Some(support::fixture_const(app, "Unit"));
        leanr_elab::synthetic::default_walk_log_reset();
        leanr_elab::app::args::main(app, kinds).expect("`(Get.get cell 0 : Unit)` elaborates");
        let visited = leanr_elab::synthetic::default_walk_log_take();
        assert!(
            !visited.is_empty(),
            "with propagation off and the finalize unification skipped, only rung 3 can fix `?elem`"
        );
    });
}

/// The `($e :)` ascription arm (`ascription.rs`'s `None` branch,
/// `BuiltinNotation.lean:434-435`) — the third of M4b-3 P4's rewire
/// sites (design spec § Amendment 5 item 8) and the one no corpus
/// record reaches: `($e : $type)` delegates to
/// `elab_term_ensuring_type` instead, so only a BARE ascription
/// exercises this arm's own `ensureHasType`.
///
/// `takesInt (Nat.zero :)` elaborates `Nat.zero` with NO expected type
/// (the arm deliberately withholds the caller's), then coerces the
/// result against the caller's `Int`. Its `($e : $type)` twin is the
/// assertion's yardstick, and both shapes were confirmed against the
/// oracle as `takesInt (Int.ofNat Nat.zero)` (throwaway `dump_elab`
/// probes, per M4b-1's precedent — not landed, because the corpus
/// floor for this task is pinned at 111).
///
/// Kill: revert the arm to the M4b-1 posture (infer, `isDefEq`, else
/// `TypeMismatch`) and the bare form errors with `TypeMismatch` while
/// the annotated one still succeeds.
#[test]
fn bare_ascription_coerces_against_the_callers_expected_type() {
    let bare = support::elab_and_synthesize("takesInt (Nat.zero :)")
        .expect("`(e :)` under an expected type coerces rather than erroring");
    let annotated =
        support::elab_and_synthesize("takesInt (Nat.zero : Int)").expect("its `($e : $type)` twin");
    assert_eq!(
        bare, annotated,
        "both ascription arms must insert the same coercion"
    );
    assert!(
        bare.to_string().contains("Int.ofNat"),
        "the coercion is present, not merely a defeq pass: {bare}"
    );
}

/// oracle: `App.lean:828`'s `| false, some defVal, _ => addNewArg
/// argName defVal`. `withDefault (n : Nat := Nat.zero) : Nat := n`
/// (`Elab0.lean`) — an omitted argument takes the DECLARED default
/// value directly, not a fresh mvar.
#[test]
fn opt_param_default_is_the_declared_value() {
    let j = support::elab_and_synthesize("withDefault")
        .expect("an omitted optParam argument fills with the declared default");
    assert_eq!(j["k"], "app");
    assert_eq!(j["f"]["n"], "withDefault");
    assert_eq!(j["a"]["k"], "const");
    assert_eq!(j["a"]["n"], "Nat.zero");
}

/// The oracle's match scrutinee is `(← read).explicit` — under `@` the
/// arm is not reached at all, so `withDefault`'s parameter must still
/// be supplied positionally rather than defaulted.
#[test]
fn opt_param_explicit_mode_does_not_fill() {
    let j = support::elab_and_synthesize("@withDefault Nat.zero")
        .expect("`@withDefault` supplies the optParam positionally");
    assert_eq!(j["k"], "app");
    assert_eq!(j["f"]["n"], "withDefault");
    assert_eq!(j["a"]["k"], "const");
    assert_eq!(j["a"]["n"], "Nat.zero");
}

/// M4b-3 P5 Task 9. `def withTactic (n : autoParam Nat p5AutoTac) : Nat
/// := n` (`Elab0.lean`). Supplying the argument bypasses the tactic
/// entirely — `process_explicit_arg`'s positional-argument branch
/// (`App.lean:803-808`) consumes `Nat.zero` and returns before the
/// `!explicit`/`getAutoParamTactic?` arms this task adds are ever
/// reached, exactly as `opt_param_explicit_mode_does_not_fill` above
/// pins for the `optParam` sibling.
#[test]
fn auto_param_explicit_argument_elaborates_normally() {
    let j = support::elab_and_synthesize("withTactic Nat.zero")
        .expect("an explicitly supplied autoParam argument elaborates normally");
    assert_eq!(j["k"], "app");
    assert_eq!(j["f"]["n"], "withTactic");
    assert_eq!(j["a"]["k"], "const");
    assert_eq!(j["a"]["n"], "Nat.zero");
}

/// M4b-3 P5 Task 9. This test's own history is the point: it used to be
/// `opt_param_arm_falls_through_for_autoparam`, pinned to Task 8's
/// placeholder — an omitted `autoParam` argument still hit the OLD
/// combined `UnsupportedSyntax` seam Task 8 deliberately left erroring
/// (`args.rs`'s `"optParam default / autoParam tactic argument — M4b-3
/// P5"`). This task deletes that seam and gives `autoParam` its own real
/// body: mint a `.tactic` synthetic mvar (oracle `App.lean:846`,
/// `mkTacticMVar`) and let the ladder report it unsolved, because
/// EXECUTING the tactic needs the `by` elaborator and the tactic
/// framework — a later M4 slice, not this one.
/// `seam_audit.rs`'s `omitted_auto_param_is_a_reported_tactic_mvar`
/// asserts the same fact from that file's own seam-audit angle; this
/// one keeps the coverage where Task 8 first put it.
#[test]
fn omitted_auto_param_mints_a_reported_tactic_mvar() {
    match support::elab_and_synthesize("withTactic") {
        Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => {
            assert!(m.contains("tactic"), "must name the tactic mvar: {m:?}");
            assert!(
                m.contains("parameter `n`"),
                "must name the stuck parameter: {m:?}"
            );
            assert!(m.contains("M4"), "must name the deferring slice: {m:?}");
        }
        other => {
            panic!("an omitted autoParam argument must never silently elaborate, got {other:?}")
        }
    }
}

// -- Whole-branch review, item 11: a `.typeClass` synthetic mvar --------
// -- registered under an instance-implicit binder, deferred past its --
// -- closing, resolved at the top-level fixpoint against the LOCAL -----
// -- instance -------------------------------------------------------

/// Coverage gap the review named: every existing test that resolves a
/// `.typeClass` mvar minted under an instance-implicit `fun [inst : C]`
/// binder either resolves it at `finalize` WHILE STILL IN SCOPE
/// (`binder_smoke.rs`'s `fun_elided_binder_registers_as_a_local_instance_only_after_propagation`)
/// or crosses the binder and lands on a GLOBAL instance. The mechanism
/// that reinstalls a closed binder's local instances for a mvar
/// resolved after the fact is covered at unit level
/// (`leanr_meta::metactx`'s `with_mvar_context_reinstalls_local_instances`,
/// which drives `with_mvar_context` directly on a hand-built `MetaCtx`)
/// but not end-to-end through `synthesize_app_inst_mvars`
/// (`app/state.rs:459-473`) and the real fixpoint. This closes that gap.
///
/// **Why `useWrap` used BARE forces genuine deferral.** `useWrap {a :
/// Type} [Wrap a] (x : a) : a := Wrap.wrap x` (`Elab0.lean`). A bare
/// `useWrap` (no explicit args supplied) auto-inserts `{a}` and
/// `[Wrap a]` as fresh mvars, then FINALIZES without ever reaching the
/// explicit `x` param (no more args, no expected type to eta-expand
/// against) — so `a` stays unassigned when `synthesize_app_inst_mvars`
/// commits, `Wrap ?a` is genuinely stuck (`try_synth_instance` answers
/// `LOption::Undef`, not a candidate list), and the `[Wrap a]` mvar is
/// registered as a PENDING `.typeClass` synthetic mvar rather than
/// resolved inline. Confirmed in isolation: `(fun [inst : Wrap Nat] =>
/// useWrap)` alone (nothing left to fix `a`) elaborates to
/// `ElabError::StuckSyntheticMVar` — the same deferral this test
/// exploits, just left permanently unresolved there.
///
/// **What supplies the LATER fix for `a`, after the binder has
/// closed.** `let g := useWrap; g Nat.zero` gives the bare `useWrap`
/// (still inside `inst`'s scope, since it is the `let`'s VALUE) its own
/// separate finalize — deferred exactly as above — and then applies the
/// let-bound `g` to `Nat.zero` in a SEPARATE application unit. That
/// unit's own argument check (`ensure_has_type`, `Nat.zero`'s type
/// against `g`'s domain `?a`) assigns `?a := Nat` — the assignment that
/// finally makes the pending mvar's type ground. Both units are still
/// textually inside the outer `fun [inst : Wrap Nat] => …`'s body, but
/// neither the elaborator nor this test needs them to be: the whole
/// point is that resolution happens through the TOP-LEVEL fixpoint
/// (`elab_term_and_synthesize`, called once after the ENTIRE term —
/// including the outer binder's own `lctx_restore` — has already been
/// built), not through any in-scope retry. By fixpoint time `inst` is
/// off the ambient `lctx`; the mvar's own RECORDED context (captured at
/// mint time, still carrying `inst`) is what `with_mvar_context`
/// reinstalls to find it.
///
/// A bare identifier as an application HEAD that is itself a `fun` is
/// unavailable here — `elabAppFn` is scoped to the identifier case only
/// in this slice (M4b-1 P1; the general-term-in-function-position arm
/// is M4b-4's LVal machinery) — so this cannot be written as
/// `(fun [inst : Wrap Nat] => useWrap) Nat.zero`. Naming the
/// intermediate value with `let` sidesteps that restriction; it is not
/// load-bearing for what this test demonstrates; wrapping `useWrap`
/// itself in a second `fun` before the `let` was also tried and hits an
/// unrelated pre-existing limitation (`let g := (fun (z : Nat) => id);
/// g Nat.zero Nat.zero` fails the same way, with no instance or local
/// context involved at all) — worth a future look, but out of scope
/// here since this construction does not need it.
///
/// **Mutation-discriminating by construction, not by an added check**:
/// the LOCAL `inst` and the GLOBAL `instWrapNat` (also in scope,
/// `Elab0.lean`) both solve `Wrap Nat` and are individually sufficient,
/// but they encode to DIFFERENT terms — a bound-variable reference vs.
/// a `const` — so a version of `with_mvar_context` that failed to
/// reinstall the mvar's recorded local instances would make this
/// resolve to the global `instWrapNat` instead, and the assertion below
/// would fail. Confirmed directly: `let g := useWrap; g Nat.zero` with
/// NO enclosing instance binder (same deferral, no local instance in
/// scope at fixpoint time) resolves to `instWrapNat`, not a bvar — the
/// contrasting case that shows this test is reading the local/global
/// choice, not some other property.
#[test]
fn deferred_typeclass_mvar_under_a_closed_binder_resolves_to_the_local_instance() {
    let j = support::elab_and_synthesize("fun [inst : Wrap Nat] => let g := useWrap; g Nat.zero")
        .expect("the pending .typeClass mvar must resolve once `a` is grounded");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "c", "the outer binder is instance-implicit");
    let let_value = &j["b"]["v"];
    assert_eq!(let_value["k"], "app", "@useWrap Nat <instance>");
    assert_eq!(let_value["f"]["f"]["n"], "useWrap");
    assert_eq!(
        let_value["a"],
        serde_json::json!({"k": "bvar", "i": 0}),
        "must be the LOCAL `inst` (a bound-variable reference into the \
         closed binder's recorded context), not the global `instWrapNat` \
         — proves `with_mvar_context` reinstalled the local instance \
         table for a mvar resolved after its binder closed"
    );
}
