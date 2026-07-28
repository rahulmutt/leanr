//! Cross-crate include of `leanr_meta`'s canonical decode/encode scheme
//! (`decode_expr`/`encode_expr`/`EncSt`/`fixture_in`/`replay_fixture_in`)
//! — ONE source of truth (`crates/leanr_meta/tests/support/mod.rs`),
//! extended by `leanr_meta`'s own tasks, never copied here. See that
//! file's own module doc for the scheme itself; this file contributes
//! nothing but the `#[path]` include.
// Each integration-test binary that does `mod support;`
// (`oracle_elab.rs`, `binder_smoke.rs`, `app_smoke.rs`) compiles this
// whole file but uses only the part its own gate needs — same
// per-binary-dead-code situation `meta_support`'s own module doc
// documents for itself, one level up. `with_app_harness` below is only
// called from `app_smoke.rs`, so it reads as dead code to the other
// two binaries without this.
#![allow(dead_code)]

#[path = "../../../leanr_meta/tests/support/mod.rs"]
mod meta_support;
pub use meta_support::*;

/// Run `k` with an `AppElab` whose head is `head_src`, elaborated
/// against the committed `Elab0.olean` fixture environment. A
/// closure-taking helper rather than a struct-returning one:
/// `AppElab` borrows `TermElabM`, which borrows the `Store`, so a
/// struct-returning harness would need the env/store to outlive it —
/// this closure form keeps every borrow's owner alive for exactly the
/// duration `k` runs (Task 3 brief's own resolved ambiguity #1).
///
/// Construction mirrors `oracle_elab.rs:29-93` verbatim: replay the
/// fixture env, build a scratch `Store` + `MetaCtx` + `TermElabM`,
/// parse `head_src` through leanr's own parser, and elaborate it via
/// `elab_term` — which for a bare identifier routes through
/// `app::elab_atom` (a zero-argument application) since Task 4 retired
/// M4b-1's leaf `builtin::ident`. The elaborated head's inferred type
/// seeds `State.f_type`.
pub fn with_app_harness<R>(
    head_src: &str,
    k: impl FnOnce(&mut leanr_elab::app::state::AppElab) -> R,
) -> R {
    use leanr_elab::app::state::{AppElab, Context, State};
    use leanr_elab::TermElabM;
    use leanr_kernel::bank::Store;
    use leanr_kernel::EnvView;
    use leanr_meta::{Config, MetaCtx};
    use leanr_syntax::{builtin, parse_term};

    let Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
    } = replay_fixture_in("elab", "Elab0.olean");
    let snap = builtin::snapshot();

    let view: EnvView = env.view();
    let parsed = parse_term(head_src, &snap);
    assert!(
        parsed.errors.is_empty(),
        "app_harness: leanr parse errors for {head_src:?}: {:?}",
        parsed.errors
    );
    let root = parsed.tree.root();
    let term_elem: leanr_elab::dispatch::SynElem = root
        .first_child_or_token()
        .unwrap_or_else(|| panic!("app_harness: no term child for {head_src:?}"));

    let mut scratch = Store::scratch();
    let mctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        &reducibility,
        &matchers,
        &instances,
        &default_instances,
        &projection_fns,
    );
    let mut elab = TermElabM::new(mctx, view);
    let f = elab
        .elab_term(&term_elem, &parsed.tree.kinds, None)
        .unwrap_or_else(|e| panic!("app_harness: elab_term failed for {head_src:?}: {e:?}"));
    let f_type = elab
        .mctx
        .infer_type(f)
        .unwrap_or_else(|e| panic!("app_harness: infer_type failed for {head_src:?}: {e:?}"));

    let ctx = Context {
        ellipsis: false,
        explicit: false,
        result_is_out_param_support: false,
        num_implicit_params: 0,
        stx: term_elem.clone(),
    };
    let st = State {
        f,
        f_type,
        f_args: Vec::new(),
        args: Vec::new(),
        named_args: Vec::new(),
        expected_type: None,
        eta_args: Vec::new(),
        to_set_error_ctx: Vec::new(),
        inst_mvars: Vec::new(),
        propagate_expected: false,
        result_type_out_param: None,
        found_named_args: Vec::new(),
    };
    let mut app = AppElab {
        ctx,
        st,
        elab: &mut elab,
    };
    k(&mut app)
}

/// A syntax reference for tests that need one but do not care which.
/// `SynElem` is an owned rowan handle, so the parse tree it points into
/// stays alive through the returned value.
pub fn any_syn_elem() -> leanr_elab::dispatch::SynElem {
    use leanr_syntax::{builtin, parse_term};
    let snap = builtin::snapshot();
    let parsed = parse_term("Nat.zero", &snap);
    assert!(parsed.errors.is_empty());
    parsed
        .tree
        .root()
        .first_child_or_token()
        .expect("term child")
}

/// A `KindInterner` for tests that need one but do not care which
/// `GrammarSnapshot` backed it. Every snapshot's interner carries the
/// same builtin-grammar kinds, so any parse's own interner (cloned —
/// `KindInterner::Clone` is cheap, an `Arc<str>` per name) works as a
/// stand-in wherever a caller just needs `&KindInterner` and not a
/// specific tree's own.
pub fn any_kinds() -> leanr_syntax::kind::KindInterner {
    use leanr_syntax::{builtin, parse_term};
    let snap = builtin::snapshot();
    let parsed = parse_term("Nat.zero", &snap);
    assert!(parsed.errors.is_empty());
    (*parsed.tree.kinds).clone()
}

/// Register `n` `TypeClass` synthetic mvars, oldest first, returning
/// their ids in creation order.
pub fn register_n_typeclass_mvars(
    app: &mut leanr_elab::app::state::AppElab,
    n: usize,
) -> Vec<leanr_meta::MVarId> {
    use leanr_elab::synthetic::SyntheticMVarKind;
    let ty = app.st.f_type;
    let mut ids = Vec::new();
    for _ in 0..n {
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(ty, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        app.elab
            .register_synthetic_mvar(any_syn_elem(), id, SyntheticMVarKind::TypeClass);
        ids.push(id);
    }
    ids
}

/// Drive `step_with` recording the order in which mvars are visited,
/// resolving none of them. Used to test the creation-order walk in
/// isolation from any real synthesis.
pub fn step_recording_visit_order(
    app: &mut leanr_elab::app::state::AppElab,
) -> Vec<leanr_meta::MVarId> {
    let mut seen = Vec::new();
    app.elab
        .step_with(|_elab, mvar_id| {
            seen.push(mvar_id);
            Ok(false)
        })
        .expect("step_with: stub outcome is infallible");
    seen
}

/// Drive `step_with` registering one fresh `TypeClass` mvar mid-walk
/// (as real synthesis can) and resolving none of the pre-existing
/// pending mvars. Returns the id of the mvar created during the step
/// AND the step's progress bool, so callers can assert both the merge
/// order and that the mid-step-created mvar does not get counted into
/// the progress comparison (progress is snapshot length vs. survivor
/// count, never the post-merge list length).
pub fn step_creating_one_mvar_solving_none(
    app: &mut leanr_elab::app::state::AppElab,
) -> (leanr_meta::MVarId, bool) {
    use leanr_elab::synthetic::SyntheticMVarKind;
    let ty = app.st.f_type;
    let mut fresh_id = None;
    let progress = app
        .elab
        .step_with(|elab, _mvar_id| {
            if fresh_id.is_none() {
                let (_e, id) = elab
                    .mk_fresh_expr_mvar_of_kind(ty, leanr_meta::MVarKind::Synthetic)
                    .expect("fresh mvar");
                elab.register_synthetic_mvar(any_syn_elem(), id, SyntheticMVarKind::TypeClass);
                fresh_id = Some(id);
            }
            Ok(false)
        })
        .expect("step_with: stub outcome is infallible");
    (
        fresh_id.expect("step visited at least one pending mvar"),
        progress,
    )
}

/// Drive `step_with` resolving exactly the first-visited (oldest)
/// pending mvar and none of the rest.
pub fn step_solving_exactly_one(app: &mut leanr_elab::app::state::AppElab) -> bool {
    let mut first = true;
    app.elab
        .step_with(|_elab, _mvar_id| {
            let succeeded = first;
            first = false;
            Ok(succeeded)
        })
        .expect("step_with: stub outcome is infallible")
}

/// Drive `step_with` resolving none of the pending mvars.
pub fn step_solving_none(app: &mut leanr_elab::app::state::AppElab) -> bool {
    app.elab
        .step_with(|_elab, _mvar_id| Ok(false))
        .expect("step_with: stub outcome is infallible")
}

// === Task 4's `synthesize_inst_mvar_core` fixtures (real, Task 7) ===
//
// `synthetic_smoke.rs`'s trichotomy tests need real class goals — `Wrap`,
// solvable only for `Nat`, and `NoInst`, solvable for nothing. Both (plus
// `Pair` and `Dflt`) live in `Elab0.lean` as of M4b-3 P2a Task 7 (see that
// file's own "M4b-3 P2a corpus" section).

/// Parse `src` and elaborate it through `app`'s own `elab` — the SAME
/// committed `Elab0.olean` environment `app` was itself built over
/// (`with_app_harness`'s own construction). Used by `wrap_of_nat`,
/// `no_inst_of_nat` and `dflt_of_nat`: each of those goals (`Wrap Nat`,
/// `NoInst Nat`, `Dflt Nat`) is a CLOSED term with no mvar, so the
/// ordinary end-to-end entry point (parse -> `elab_term`) builds it
/// directly, through the very `app::elab_app` path this task adds
/// instance-implicit support to — `Wrap`/`NoInst`/`Dflt` are each
/// `Type -> Type` classes with no instance-implicit parameter of their
/// OWN, so applying one to `Nat` is a plain explicit application, not a
/// typeclass goal itself.
fn elab_type_expr(
    app: &mut leanr_elab::app::state::AppElab,
    src: &str,
) -> leanr_kernel::bank::ExprId {
    use leanr_syntax::{builtin, parse_term};
    let snap = builtin::snapshot();
    let parsed = parse_term(src, &snap);
    assert!(
        parsed.errors.is_empty(),
        "elab_type_expr: leanr parse errors for {src:?}: {:?}",
        parsed.errors
    );
    let term_elem: leanr_elab::dispatch::SynElem = parsed
        .tree
        .root()
        .first_child_or_token()
        .unwrap_or_else(|| panic!("elab_type_expr: no term child for {src:?}"));
    app.elab
        .elab_term(&term_elem, &parsed.tree.kinds, None)
        .unwrap_or_else(|e| panic!("elab_type_expr: elab_term failed for {src:?}: {e:?}"))
}

/// `Wrap Nat` — a solvable instance goal.
pub fn wrap_of_nat(app: &mut leanr_elab::app::state::AppElab) -> leanr_kernel::bank::ExprId {
    elab_type_expr(app, "Wrap Nat")
}

/// `Wrap ?m` — the same class goal as `wrap_of_nat`, but applied to a
/// freshly-minted unassigned mvar so `synth_instance` reports the goal
/// stuck rather than solved or failed.
///
/// Built by hand rather than parsed: no surface syntax can write an
/// unassigned mvar. `elab_type_expr(app, "Wrap")` elaborates the bare
/// class constant unapplied (zero args, so `main` finalizes with the
/// still-unconsumed `Type -> Type` forall in place — the same "no
/// positional argument, not explicit, no opt/auto param, no ellipsis,
/// no named args, no further opt/auto param in the remaining telescope"
/// path `process_explicit_arg` takes for any bare polymorphic head);
/// the domain of ITS OWN inferred type is the exact type a fresh mvar
/// for `Wrap`'s parameter must carry, so it is read off that type
/// rather than re-elaborating a separate `"Type"` term.
pub fn wrap_of_fresh_mvar(app: &mut leanr_elab::app::state::AppElab) -> leanr_kernel::bank::ExprId {
    use leanr_kernel::bank::terms::Node;
    let wrap = elab_type_expr(app, "Wrap");
    let wrap_ty = app
        .elab
        .mctx
        .infer_type(wrap)
        .expect("Wrap's own type infers");
    let Node::Forall { binder_type, .. } = app.node(wrap_ty) else {
        panic!("wrap_of_fresh_mvar: Wrap's type is not a forall: {wrap_ty:?}");
    };
    let (mvar, _id) = app
        .elab
        .mk_fresh_expr_mvar_of_kind(binder_type, leanr_meta::MVarKind::Natural)
        .expect("fresh mvar");
    let base = app.elab.view.store;
    app.elab
        .mctx
        .store_mut()
        .expr_app(Some(base), wrap, mvar)
        .expect("Wrap ?m applies")
}

/// `NoInst Nat` — a class goal with no instance, exercising the real
/// synthesis-failure (`.none`) arm.
pub fn no_inst_of_nat(app: &mut leanr_elab::app::state::AppElab) -> leanr_kernel::bank::ExprId {
    elab_type_expr(app, "NoInst Nat")
}

/// `Dflt Nat` — a class goal whose class HAS a registered
/// `@[default_instance]` (`Elab0.lean`'s `instDfltNat`), exercising
/// `synthesize_using_default`'s SHAPE GUARD positive case
/// (`synthesize_using_default_errors_when_a_default_instance_is_registered`,
/// Task 5's review fix). `Wrap`/`Pair`/`NoInst` never gain a default
/// instance — see `Elab0.lean`'s own doc comment on why that would
/// break the stuck-path tests.
pub fn dflt_of_nat(app: &mut leanr_elab::app::state::AppElab) -> leanr_kernel::bank::ExprId {
    elab_type_expr(app, "Dflt Nat")
}

/// Shared plumbing for `elab_only`/`elab_and_synthesize` below: replay
/// the committed `Elab0.olean` fixture, parse `src` through leanr's own
/// parser, and hand the caller a fresh `TermElabM` plus the parsed term
/// and its `KindInterner` to elaborate however it needs. Mirrors
/// `with_app_harness`/`oracle_elab.rs`'s own replay construction.
///
/// A closure-taking helper, not a struct-returning one, for the same
/// reason `with_app_harness` is one: the `Store`/`EnvView`/`MetaCtx`
/// borrow chain does not outlive this function, so the result must be
/// fully computed (encoded to a self-contained JSON value, for both
/// callers below) before it returns.
fn with_elab_harness<R>(
    caller: &str,
    src: &str,
    k: impl FnOnce(
        &mut leanr_elab::TermElabM,
        &leanr_elab::dispatch::SynElem,
        &leanr_syntax::kind::KindInterner,
    ) -> R,
) -> R {
    use leanr_elab::TermElabM;
    use leanr_kernel::bank::Store;
    use leanr_kernel::EnvView;
    use leanr_meta::{Config, MetaCtx};
    use leanr_syntax::{builtin, parse_term};

    let Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
    } = replay_fixture_in("elab", "Elab0.olean");
    let snap = builtin::snapshot();
    let view: EnvView = env.view();

    let parsed = parse_term(src, &snap);
    assert!(
        parsed.errors.is_empty(),
        "{caller}: leanr parse errors for {src:?}: {:?}",
        parsed.errors
    );
    let term_elem: leanr_elab::dispatch::SynElem = parsed
        .tree
        .root()
        .first_child_or_token()
        .unwrap_or_else(|| panic!("{caller}: no term child for {src:?}"));

    let mut scratch = Store::scratch();
    let mctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        &reducibility,
        &matchers,
        &instances,
        &default_instances,
        &projection_fns,
    );
    let mut elab = TermElabM::new(mctx, view);
    k(&mut elab, &term_elem, &parsed.tree.kinds)
}

/// Elaborate `src` through `elab_term` ALONE — no fixpoint, no
/// instantiation — and return its canonical encoding (the same
/// `encode_expr`/`EncSt` scheme `oracle_elab.rs`'s own gate uses). The
/// `Store` this mints into does not outlive the call, so the result is
/// encoded to a self-contained JSON value rather than an `ExprId`,
/// which lets a caller compare this against `elab_and_synthesize`'s
/// output even though the two calls build entirely separate stores.
pub fn elab_only(src: &str) -> Result<serde_json::Value, leanr_elab::ElabError> {
    with_elab_harness("elab_only", src, |elab, term_elem, kinds| {
        let e = elab.elab_term(term_elem, kinds, None)?;
        let base = elab.view.store;
        let mut st = EncSt::default();
        Ok(encode_expr(elab.mctx.store(), Some(base), e, &mut st))
    })
}

/// Elaborate `src` through the real top-level entry point,
/// `TermElabM::elab_term_and_synthesize` (Task 9) — `elab_term`, the
/// fixpoint, then `instantiate_mvars` — and return its canonical
/// encoding, same scheme as `elab_only` above.
///
/// Before Task 9 this helper stood in for the entry point by chaining
/// `elab_term_ensuring_type` / `synthesize_synthetic_mvars_no_postponing`
/// / `instantiate_mvars` by hand; it now calls the real method, so
/// there is one implementation of the entry point, not two.
pub fn elab_and_synthesize(src: &str) -> Result<serde_json::Value, leanr_elab::ElabError> {
    with_elab_harness("elab_and_synthesize", src, |elab, term_elem, kinds| {
        let e = elab.elab_term_and_synthesize(term_elem, kinds, None)?;
        let base = elab.view.store;
        let mut st = EncSt::default();
        Ok(encode_expr(elab.mctx.store(), Some(base), e, &mut st))
    })
}
