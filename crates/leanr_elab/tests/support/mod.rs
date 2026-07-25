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
/// `elab_term` — which for a bare identifier still routes to M4b-1's
/// `builtin::ident` until Task 4 rewires application heads through
/// `AppElab::main`. The elaborated head's inferred type seeds
/// `State.f_type`.
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
