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
    use leanr_meta::{Config, EnvExtensions, MetaCtx};
    use leanr_syntax::{builtin, parse_term};

    let Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
        classes,
        coe_decls,
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
        EnvExtensions {
            reducibility: &reducibility,
            matchers: &matchers,
            instances: &instances,
            default_instances: &default_instances,
            projection_fns: &projection_fns,
            classes: &classes,
            coe_decls: &coe_decls,
        },
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

/// `with_app_harness` plus POSITIONAL ARGUMENTS, on the RAW head: each
/// entry of `arg_srcs` is parsed through leanr's own parser and queued
/// as an `Arg::Stx`, so `args::main` elaborates it exactly as
/// `elab_app_aux` would — the way `app_smoke.rs`'s ellipsis test drives
/// `main` on `pick`, but with arguments to consume.
///
/// "Raw head", because `with_app_harness` has already run `head_src`
/// through `main` once as a zero-argument application (its own doc, and
/// `strict_implicit_without_args_finalizes`'s comment): for a head with
/// implicit parameters, `app.st.f` arrives as `@Get.get ?c ?i ?e ?inst`
/// with `f_type` already `?c → ?i → ?e`, and the instance goal that
/// elaboration registered is sitting in `pending_mvars`. This helper
/// peels the spine back to the constant (the same universe-mvar-carrying
/// `Const` either way), re-infers its FULL type, resets the per-application
/// state, and retires the harness's leftover pending goals — so the
/// caller's `main` walks every binder itself, from the first implicit.
///
/// The `KindInterner` handed to `k` is `any_kinds()` (every
/// builtin-snapshot parse carries the same kinds, per that helper's
/// doc), which is what `elab_and_add_new_arg` reads.
///
/// `result_is_out_param_support` and `propagate_expected` are left at
/// `with_app_harness`'s defaults (`false`), and `expected_type` is
/// left at ITS harness default too (`None`); a caller that wants the
/// oracle's `elabAppArgs` defaults sets any of the three itself before
/// calling `main`. `with_app_harness`'s own `State` literal (above, in
/// this file) is the source of truth for what a new field would need:
/// a field added there without a matching default here would silently
/// leave callers of `with_app_args` exercising the wrong starting
/// state.
pub fn with_app_args<R>(
    head_src: &str,
    arg_srcs: &[&str],
    k: impl FnOnce(&mut leanr_elab::app::state::AppElab, &leanr_syntax::kind::KindInterner) -> R,
) -> R {
    use leanr_elab::app::expand::Arg;
    use leanr_kernel::bank::terms::Node;
    use leanr_syntax::{builtin, parse_term};
    let snap = builtin::snapshot();
    let parses: Vec<_> = arg_srcs
        .iter()
        .map(|src| {
            let parsed = parse_term(src, &snap);
            assert!(
                parsed.errors.is_empty(),
                "with_app_args: leanr parse errors for {src:?}: {:?}",
                parsed.errors
            );
            parsed
        })
        .collect();
    let args: Vec<Arg> = parses
        .iter()
        .map(|p| {
            Arg::Stx(
                p.tree
                    .root()
                    .first_child_or_token()
                    .expect("with_app_args: no term child"),
            )
        })
        .collect();
    let kinds = any_kinds();
    with_app_harness(head_src, |app| {
        let mut f = app.st.f;
        while let Node::App { f: inner, .. } = app.node(f) {
            f = inner;
        }
        let f_type =
            app.elab.mctx.infer_type(f).unwrap_or_else(|e| {
                panic!("with_app_args: infer_type of the raw head failed: {e:?}")
            });
        app.st.f = f;
        app.st.f_type = f_type;
        app.st.f_args = Vec::new();
        app.st.args = args;
        app.st.named_args = Vec::new();
        app.st.eta_args = Vec::new();
        app.st.to_set_error_ctx = Vec::new();
        app.st.inst_mvars = Vec::new();
        app.st.result_type_out_param = None;
        app.st.found_named_args = Vec::new();
        for id in std::mem::take(&mut app.elab.pending_mvars) {
            app.elab.mark_as_resolved(id);
        }
        k(app, &kinds)
    })
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

/// `Get Cell Nat ?e` — a class goal whose ONLY unassigned mvar sits in
/// an OUTPUT-PARAMETER position (`Get`'s third parameter is
/// `outParam (Type w)`). The oracle answers this goal — `preprocessOutParam`
/// swaps `?e` for a search-local mvar and `assignOutParams` assigns the
/// caller's `?e := Unit` afterwards (M4b-3 P2b-i ported both) — so the
/// ladder pre-test must let it reach the real search.
///
/// Built like `wrap_of_fresh_mvar`: the fresh mvar's type is read off the
/// partial application's own inferred type rather than re-elaborated.
pub fn get_cell_nat_of_fresh_mvar(
    app: &mut leanr_elab::app::state::AppElab,
) -> leanr_kernel::bank::ExprId {
    use leanr_kernel::bank::terms::Node;
    let get_cell_nat = elab_type_expr(app, "Get Cell Nat");
    let ty = app
        .elab
        .mctx
        .infer_type(get_cell_nat)
        .expect("Get Cell Nat's own type infers");
    let Node::Forall { binder_type, .. } = app.node(ty) else {
        panic!("get_cell_nat_of_fresh_mvar: `Get Cell Nat` is not a forall: {ty:?}");
    };
    let (mvar, _id) = app
        .elab
        .mk_fresh_expr_mvar_of_kind(binder_type, leanr_meta::MVarKind::Natural)
        .expect("fresh mvar");
    let base = app.elab.view.store;
    app.elab
        .mctx
        .store_mut()
        .expr_app(Some(base), get_cell_nat, mvar)
        .expect("Get Cell Nat ?e applies")
}

/// `Get Cell ?i ?e` — the same class with an unassigned mvar in a
/// NON-output position too (`idx`). This is the shape the `GetElem`
/// worked example depends on staying POSTPONED: `?i` is fixed only when
/// the `OfNat` default instance fires, and an exemption keyed on the
/// class rather than the position would send this goal to a search that
/// answers `.none` (design spec § Amendment 4 item 6).
pub fn get_cell_of_two_fresh_mvars(
    app: &mut leanr_elab::app::state::AppElab,
) -> leanr_kernel::bank::ExprId {
    use leanr_kernel::bank::terms::Node;
    let get_cell = elab_type_expr(app, "Get Cell");
    let ty = app
        .elab
        .mctx
        .infer_type(get_cell)
        .expect("Get Cell's own type infers");
    let Node::Forall {
        binder_type: idx_ty,
        body,
        ..
    } = app.node(ty)
    else {
        panic!("get_cell_of_two_fresh_mvars: `Get Cell` is not a forall: {ty:?}");
    };
    let (idx, _) = app
        .elab
        .mk_fresh_expr_mvar_of_kind(idx_ty, leanr_meta::MVarKind::Natural)
        .expect("fresh idx mvar");
    // The `elem` binder's type is closed only once `idx` is substituted
    // in (the telescope is `∀ (idx : Type v), outParam (Type w) → ...`,
    // non-dependent here, but instantiating is the general shape).
    let rest = app
        .elab
        .mctx
        .instantiate_beta_rev_range(body, &[idx])
        .expect("instantiate");
    let Node::Forall {
        binder_type: elem_ty,
        ..
    } = app.node(rest)
    else {
        panic!("get_cell_of_two_fresh_mvars: `Get Cell ?i` is not a forall: {rest:?}");
    };
    let (elem, _) = app
        .elab
        .mk_fresh_expr_mvar_of_kind(elem_ty, leanr_meta::MVarKind::Natural)
        .expect("fresh elem mvar");
    let base = app.elab.view.store;
    let with_idx = app
        .elab
        .mctx
        .store_mut()
        .expr_app(Some(base), get_cell, idx)
        .expect("Get Cell ?i applies");
    app.elab
        .mctx
        .store_mut()
        .expr_app(Some(base), with_idx, elem)
        .expect("Get Cell ?i ?e applies")
}

/// `NoInst Nat` — a class goal with no instance, exercising the real
/// synthesis-failure (`.none`) arm.
pub fn no_inst_of_nat(app: &mut leanr_elab::app::state::AppElab) -> leanr_kernel::bank::ExprId {
    elab_type_expr(app, "NoInst Nat")
}

/// `Dflt Nat` — a GROUND class goal whose class HAS a registered
/// `@[default_instance]` (`Elab0.lean`'s `instDfltNat`).
///
/// Ordinary instance synthesis already closes this one at rung 1, so it
/// is NOT what rung 3 acts on; `dflt_of_fresh_mvar` below is. Kept as
/// the ground half of that contrast — `Wrap`/`Pair`/`NoInst` never gain
/// a default instance, see `Elab0.lean`'s own doc comment on why that
/// would break the stuck-path tests.
pub fn dflt_of_nat(app: &mut leanr_elab::app::state::AppElab) -> leanr_kernel::bank::ExprId {
    elab_type_expr(app, "Dflt Nat")
}

/// `Dflt Unit` — a goal whose class HAS a default instance
/// (`instDfltNat`) that does NOT apply to it: `Dflt Unit =?= Dflt Nat`
/// fails, so `synthesizeUsingDefaultInstance`'s `commitWhen` must roll
/// the attempt back. `Dflt`'s other instance (`instDfltUnit`) carries no
/// `@[default_instance]`, so rung 3 has nothing else to try.
pub fn dflt_of_unit(app: &mut leanr_elab::app::state::AppElab) -> leanr_kernel::bank::ExprId {
    elab_type_expr(app, "Dflt Unit")
}

/// `Dflt ?a` with a FRESH type mvar — the shape rung 3 actually closes,
/// unlike `dflt_of_nat`'s ground `Dflt Nat` (which ordinary synthesis
/// already solves at rung 1).
pub fn dflt_of_fresh_mvar(app: &mut leanr_elab::app::state::AppElab) -> leanr_kernel::bank::ExprId {
    let base = app.elab.view.store;
    let dflt = fixture_const(app, "Dflt");
    // `Dflt (a : Type)`, and `Type` is `Sort 1` — a SORT, not a
    // declared constant, so it is built rather than resolved.
    let ty = {
        let store = app.elab.mctx.store_mut();
        let zero = store.level_zero(None).expect("zero");
        let one = store.level_succ(None, zero).expect("succ");
        store.expr_sort(None, one).expect("Sort 1")
    };
    let (a, _) = app
        .elab
        .mk_fresh_expr_mvar_of_kind(ty, leanr_meta::MVarKind::Natural)
        .expect("fresh type mvar");
    app.elab
        .mctx
        .store_mut()
        .expr_app(Some(base), dflt, a)
        .expect("Dflt ?a")
}

/// `OfNat ?a ?n` — a class goal whose class has default instances at
/// TWO priorities (`instOfNatNat` at 100, `instOfNatTag` at 50), both
/// strictly below the bare `@[default_instance]` on `instDfltNat`.
///
/// That is what makes the reverse-creation-order walk observable across
/// a whole priority: at the highest priority NOTHING applies, so the
/// walk visits every pending mvar before dropping a rung — and the log
/// records the full three-element order rather than stopping at the
/// first entry, which is what a `Dflt ?a` goal (whose default instance
/// sits at the TOP priority) would do.
///
/// Built by peeling `OfNat`'s own inferred telescope, the same way
/// `wrap_of_fresh_mvar` reads `Wrap`'s domain off its type rather than
/// re-elaborating a separate `"Type"` term: `OfNat` is universe
/// polymorphic (`OfNat (α : Type u) (_ : Nat)`), so the domain of its
/// first binder is `Type ?u` for the fresh level mvar `elab_type_expr`
/// already minted, not a hand-built `Sort 1`.
pub fn of_nat_of_fresh_mvars(
    app: &mut leanr_elab::app::state::AppElab,
) -> leanr_kernel::bank::ExprId {
    use leanr_kernel::bank::terms::Node;
    let mut cur = elab_type_expr(app, "OfNat");
    for _ in 0..2 {
        let ty = app
            .elab
            .mctx
            .infer_type(cur)
            .expect("OfNat's partial application infers");
        let Node::Forall { binder_type, .. } = app.node(ty) else {
            panic!("of_nat_of_fresh_mvars: OfNat's type is not a forall: {ty:?}");
        };
        let (m, _) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(binder_type, leanr_meta::MVarKind::Natural)
            .expect("fresh mvar");
        let base = app.elab.view.store;
        cur = app
            .elab
            .mctx
            .store_mut()
            .expr_app(Some(base), cur, m)
            .expect("OfNat applies");
    }
    cur
}

/// Register each of `goals` as a pending `TypeClass` synthetic mvar, in
/// the order given — so index 0 is the OLDEST — and return their ids in
/// that same CREATION order.
///
/// `pending_mvars` itself is head-is-most-recent, so the returned vector
/// is the REVERSE of the pending list. Ordering tests compare against
/// this vector precisely because the two disagree.
pub fn register_typeclass_goals(
    app: &mut leanr_elab::app::state::AppElab,
    goals: Vec<leanr_kernel::bank::ExprId>,
) -> Vec<leanr_meta::MVarId> {
    let mut ids = Vec::new();
    for g in goals {
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(g, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        app.elab.register_synthetic_mvar(
            any_syn_elem(),
            id,
            leanr_elab::synthetic::SyntheticMVarKind::TypeClass,
        );
        ids.push(id);
    }
    ids
}

/// Three pending `TypeClass` goals registered oldest-first, where only
/// the OLDEST has a class carrying default instances. Returns their ids
/// in CREATION order.
pub fn register_three_goals_oldest_defaultable(
    app: &mut leanr_elab::app::state::AppElab,
) -> Vec<leanr_meta::MVarId> {
    let goals = vec![
        of_nat_of_fresh_mvars(app),
        wrap_of_fresh_mvar(app),
        no_inst_of_nat(app),
    ];
    register_typeclass_goals(app, goals)
}

/// The order in which the default-instance walk CONSIDERS pending
/// mvars. Drives the real `synthesize_using_default` and reads the
/// visit log the implementation records; see
/// `synthetic/default_inst.rs`'s `walk_log`.
pub fn visit_order_of_default_walk(
    app: &mut leanr_elab::app::state::AppElab,
    kinds: &leanr_syntax::kind::KindInterner,
) -> Vec<leanr_meta::MVarId> {
    leanr_elab::synthetic::default_walk_log_reset();
    let _ = app.elab.synthesize_using_default(kinds);
    leanr_elab::synthetic::default_walk_log_take()
}

/// The `ExprId` of a fixture constant with no universe arguments,
/// resolved by dotted source name exactly as `app::head::elab_ident_head`
/// does. Panics if the fixture does not declare it — a test helper's
/// contract, not elaborator code.
pub fn fixture_const(
    app: &mut leanr_elab::app::state::AppElab,
    name: &str,
) -> leanr_kernel::bank::ExprId {
    let base = app.elab.view.store;
    let mut id: Option<leanr_kernel::bank::NameId> = None;
    for part in name.split('.') {
        let store = app.elab.mctx.store_mut();
        let s = store.intern_str(Some(base), part).expect("intern");
        id = Some(store.name_str(Some(base), id, s).expect("name"));
    }
    let cname = id.expect("non-empty name");
    assert!(
        app.elab.view.get(cname).is_some(),
        "fixture must declare {name}"
    );
    let levels = app
        .elab
        .mctx
        .store_mut()
        .intern_level_list(None, &[])
        .expect("empty level list");
    app.elab
        .mctx
        .store_mut()
        .expr_const(Some(base), Some(cname), levels)
        .expect("const")
}

/// Whether the fixture env declares `name` (dotted source form).
pub fn fixture_declares(app: &mut leanr_elab::app::state::AppElab, name: &str) -> bool {
    let base = app.elab.view.store;
    let mut id: Option<leanr_kernel::bank::NameId> = None;
    for part in name.split('.') {
        let store = app.elab.mctx.store_mut();
        let s = store.intern_str(Some(base), part).expect("intern");
        id = Some(store.name_str(Some(base), id, s).expect("name"));
    }
    app.elab.view.get(id.expect("non-empty name")).is_some()
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
    use leanr_meta::{Config, EnvExtensions, MetaCtx};
    use leanr_syntax::{builtin, parse_term};

    let Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
        classes,
        coe_decls,
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
        EnvExtensions {
            reducibility: &reducibility,
            matchers: &matchers,
            instances: &instances,
            default_instances: &default_instances,
            projection_fns: &projection_fns,
            classes: &classes,
            coe_decls: &coe_decls,
        },
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
