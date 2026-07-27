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

// === Task 4's `synthesize_inst_mvar_core` fixtures (placeholders until
// Task 7) ===
//
// `synthetic_smoke.rs`'s trichotomy tests need real class goals — `Wrap`,
// solvable only for `Nat`, and `NoInst`, solvable for nothing — neither of
// which exists in `Elab0.lean` yet (M4b-3 P2a Task 7 adds that scaffold and
// regenerates `Elab0.olean`; growing the fixture is that task's own scope,
// not this one's). The three helpers below exist purely so those tests
// compile NOW under `#[ignore]`: each panics if actually called, since
// there is no `Wrap`/`NoInst` constant to resolve yet. Task 7 replaces
// these bodies with real term construction and removes the callers'
// `#[ignore]` in the same step.

/// `Wrap Nat` — a solvable instance goal, once `Wrap`/`Wrap.instWrapNat`
/// exist. See the module section doc above.
pub fn wrap_of_nat(_app: &mut leanr_elab::app::state::AppElab) -> leanr_kernel::bank::ExprId {
    unimplemented!("Wrap Nat needs the Elab0 class scaffold — M4b-3 P2a Task 7")
}

/// `Wrap ?m` — the same class goal as `wrap_of_nat`, but applied to a
/// freshly-minted unassigned mvar so `synth_instance` reports the goal
/// stuck rather than solved or failed. See the module section doc above.
pub fn wrap_of_fresh_mvar(
    _app: &mut leanr_elab::app::state::AppElab,
) -> leanr_kernel::bank::ExprId {
    unimplemented!("Wrap ?m needs the Elab0 class scaffold — M4b-3 P2a Task 7")
}

/// `NoInst Nat` — a class goal with no instance, exercising the real
/// synthesis-failure (`.none`) arm. See the module section doc above.
pub fn no_inst_of_nat(_app: &mut leanr_elab::app::state::AppElab) -> leanr_kernel::bank::ExprId {
    unimplemented!("NoInst Nat needs the Elab0 class scaffold — M4b-3 P2a Task 7")
}
