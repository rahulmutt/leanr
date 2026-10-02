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
        aux_recs,
        elab_as_elim,
        structures,
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
            aux_recs: &aux_recs,
            elab_as_elim: &elab_as_elim,
            structures: &structures,
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

/// The `ExprId` of a fixture constant with no universe arguments, looked
/// up by its WHOLE dotted source name: every component is interned and
/// the resulting name must be declared. Unlike `app::head::elab_app_fn_id`
/// there is no local lookup, no namespace or prefix search and no field
/// split, so `"Nat.zero.succ"` panics rather than resolving. Panics if the fixture does not declare it — a test helper's
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
    with_doctored_elab_harness(caller, src, |_| {}, k)
}

/// `with_elab_harness`, but `doctor` may rewrite the decoded
/// `structureExt` rows first — standing in for a malformed `.olean`
/// whose `StructureInfo` disagrees with the environment.
fn with_doctored_elab_harness<R>(
    caller: &str,
    src: &str,
    doctor: impl FnOnce(&mut Vec<leanr_olean::StructureInfo>),
    k: impl FnOnce(
        &mut leanr_elab::TermElabM,
        &leanr_elab::dispatch::SynElem,
        &leanr_syntax::kind::KindInterner,
    ) -> R,
) -> R {
    use leanr_syntax::{builtin, parse_term};

    let snap = builtin::snapshot();
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
    with_doctored_elab_env(doctor, |elab| k(elab, &term_elem, &parsed.tree.kinds))
}

/// Replay `Elab0` and hand `k` a fresh `TermElabM` over it, with no
/// syntax — for gates that drive a `TermElabM` entry point directly
/// (`elim_info_oracle.rs`).
pub fn with_elab_env<R>(k: impl FnOnce(&mut leanr_elab::TermElabM) -> R) -> R {
    with_doctored_elab_env(|_| {}, k)
}

/// The `TermElabM` construction behind `with_elab_env` and
/// `with_doctored_elab_harness`: replay `Elab0`, let `doctor` rewrite
/// the decoded `structureExt` rows, build a scratch `Store` + `MetaCtx`.
fn with_doctored_elab_env<R>(
    doctor: impl FnOnce(&mut Vec<leanr_olean::StructureInfo>),
    k: impl FnOnce(&mut leanr_elab::TermElabM) -> R,
) -> R {
    use leanr_elab::TermElabM;
    use leanr_kernel::bank::Store;
    use leanr_kernel::EnvView;
    use leanr_meta::{Config, EnvExtensions, MetaCtx};

    let Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
        classes,
        coe_decls,
        aux_recs,
        elab_as_elim,
        mut structures,
    } = replay_fixture_in("elab", "Elab0.olean");
    doctor(&mut structures);
    let view: EnvView = env.view();

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
            aux_recs: &aux_recs,
            elab_as_elim: &elab_as_elim,
            structures: &structures,
        },
    );
    let mut elab = TermElabM::new(mctx, view);
    k(&mut elab)
}

/// The `NameId` of a name printed by `Name.toString (escape := false)`
/// (the oracle dumps' `"n"` field). Like `decode_name`, but an all-digit
/// component is a `Name.num` (`_private.Elab0.0.PrivMk.mk`): with
/// `decode_name` such a name would not resolve.
pub fn name_id(elab: &mut leanr_elab::TermElabM, s: &str) -> leanr_kernel::bank::NameId {
    let base = Some(elab.view.store);
    let store = elab.mctx.store_mut();
    let mut id: Option<leanr_kernel::bank::NameId> = None;
    for part in s.split('.') {
        id = Some(match part.parse::<u64>() {
            Ok(n) => {
                let nid = store
                    .intern_nat(base, &leanr_kernel::Nat::from(n))
                    .expect("intern nat");
                store.name_num(base, id, nid).expect("name")
            }
            Err(_) => {
                let sid = store.intern_str(base, part).expect("intern");
                store.name_str(base, id, sid).expect("name")
            }
        });
    }
    id.expect("name_id: empty name")
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

/// `elab_and_synthesize` over `structureExt` rows rewritten by
/// `doctor` (malformed-`.olean` guards no well-formed fixture reaches).
pub fn elab_and_synthesize_doctored(
    src: &str,
    doctor: impl FnOnce(&mut Vec<leanr_olean::StructureInfo>),
) -> Result<serde_json::Value, leanr_elab::ElabError> {
    with_doctored_elab_harness(
        "elab_and_synthesize_doctored",
        src,
        doctor,
        |elab, term_elem, kinds| {
            let e = elab.elab_term_and_synthesize(term_elem, kinds, None)?;
            let base = elab.view.store;
            let mut st = EncSt::default();
            Ok(encode_expr(elab.mctx.store(), Some(base), e, &mut st))
        },
    )
}

/// Elaborate `src` through `elab_term_ensuring_type` then
/// `instantiate_mvars`, returning the raw `Result` rather than
/// panicking on failure or encoding to JSON — for tests asserting a
/// specific `ElabError` variant rather than a successful shape.
///
/// Moved here from `binder_smoke.rs` (M4b-3 P5 Task 6): that file,
/// `oracle_elab.rs` and `seam_audit.rs` all build the same shape of
/// `MetaCtx` (this file's `with_elab_harness`, above, is that
/// construction), and a fourth copy of this small helper is where drift
/// starts.
pub fn elab_result(src: &str) -> Result<leanr_kernel::bank::ExprId, leanr_elab::ElabError> {
    with_elab_harness("elab_result", src, |elab, term_elem, kinds| {
        elab.elab_term_ensuring_type(term_elem, kinds, None)
            .and_then(|e| {
                elab.mctx
                    .instantiate_mvars(e)
                    .map_err(leanr_elab::ElabError::from)
            })
    })
}

/// Replay `Elab0`, parse `src`, and hand `k` a fresh `TermElabM` with
/// the parsed term — for tests that drive the elaborator step by step
/// (elaborate, then inspect `pending_mvars`, then run one fixpoint
/// step) rather than through a single entry point.
pub fn with_elab<R>(
    src: &str,
    k: impl FnOnce(
        &mut leanr_elab::TermElabM,
        &leanr_elab::dispatch::SynElem,
        &leanr_syntax::kind::KindInterner,
    ) -> R,
) -> R {
    with_elab_harness("with_elab", src, k)
}

/// Parse `src` with leanr's own parser, assert it parses cleanly and the
/// term spans the WHOLE source (`parse_term` stops silently at an unknown
/// token), build a fresh `TermElabM` over `r`'s environment, and run `k`
/// on it. The one place the per-record elaboration setup lives; shared by
/// `run_elab_corpus` and `elab_src_in`.
///
/// The `KindInterner` handed to `k` is the parsed tree's own, never a
/// separately held snapshot handle. The term is the root's
/// `first_child_or_token`, not `first_child`: a bare identifier is an
/// unwrapped leaf token (`crate::dispatch`'s module doc).
pub fn with_record_elab<R>(
    r: &Replayed,
    src: &str,
    snap: &leanr_syntax::grammar::GrammarSnapshot,
    k: impl FnOnce(
        &mut leanr_elab::TermElabM,
        &leanr_elab::dispatch::SynElem,
        &leanr_syntax::kind::KindInterner,
    ) -> R,
) -> R {
    use leanr_elab::TermElabM;
    use leanr_kernel::bank::Store;
    use leanr_meta::{Config, EnvExtensions, MetaCtx};

    let parsed = leanr_syntax::parse_term(src, snap);
    assert!(
        parsed.errors.is_empty(),
        "leanr parse errors for {src:?}: {:?}",
        parsed.errors
    );
    let term_elem: leanr_elab::dispatch::SynElem = parsed
        .tree
        .root()
        .first_child_or_token()
        .unwrap_or_else(|| panic!("parse_term produced no term child for {src:?}"));
    let range = term_elem.text_range();
    assert_eq!(
        (usize::from(range.start()), usize::from(range.end())),
        (0, src.trim_end().len()),
        "the parsed term does not span the whole source {src:?} \
         (`parse_term` stops silently at an unknown token)"
    );
    let view = r.env.view();
    let mut scratch = Store::scratch();
    let mctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        EnvExtensions {
            reducibility: &r.reducibility,
            matchers: &r.matchers,
            instances: &r.instances,
            default_instances: &r.default_instances,
            projection_fns: &r.projection_fns,
            classes: &r.classes,
            coe_decls: &r.coe_decls,
            aux_recs: &r.aux_recs,
            elab_as_elim: &r.elab_as_elim,
            structures: &r.structures,
        },
    );
    let mut elab = TermElabM::new(mctx, view);
    k(&mut elab, &term_elem, &parsed.tree.kinds)
}

/// Replay `tests/fixtures/elab/<fixture>`, then elaborate every
/// `{id, src, exp|err}` record of `<queries>` against it, parsing with
/// `snap`. Panics listing every divergence. Returns the number of records
/// replayed, for the caller's floor.
pub fn run_elab_corpus(
    fixture: &str,
    queries: &str,
    snap: &leanr_syntax::grammar::GrammarSnapshot,
) -> usize {
    use leanr_kernel::EnvView;

    let r = replay_fixture_in("elab", fixture);

    let queries = std::fs::read_to_string(fixture_in("elab", queries))
        .unwrap_or_else(|e| panic!("committed elab corpus {queries}: {e}"));
    let mut failures = Vec::new();
    // Fix 2 of the M4b-3 P4 whole-branch fix wave: the WHOLE-CLASS
    // detector for an unabstracted `fvar` leaking into a closed-term
    // answer. See the assertion below.
    let mut leaked_fvars = Vec::new();
    let mut replayed = 0usize;
    for line in queries.lines().filter(|l| !l.trim().is_empty()) {
        replayed += 1;
        let q: serde_json::Value = serde_json::from_str(line).expect("committed JSONL is valid");
        let id = q["id"].as_str().expect("id field");
        let src = q["src"].as_str().expect("src field");

        // Fresh EnvView/Store/MetaCtx per query: queries never share
        // state with each other. `with_record_elab` parses `src`,
        // asserts it spans the whole source, and builds the `TermElabM`.
        let view: EnvView = r.env.view();
        with_record_elab(&r, src, snap, |elab, term_elem, kinds| {
            // The pinned entry point, matching `dump_elab.lean`'s own module
            // doc (M4b-3 P2a task 9): `TermElabM::elab_term_and_synthesize`
            // (`elab.rs`) — `elab_term`, then
            // `synthesize_synthetic_mvars_no_postponing`, then
            // `instantiate_mvars` internally — mirroring the oracle's own
            // `elabTermAndSynthesize` (`SyntheticMVars.lean:696-698`).
            // `expected := None`: the committed corpus carries no
            // expected-type field, so the inner `elab_term`'s `is_def_eq`
            // branch never runs.
            let got = elab.elab_term_and_synthesize(term_elem, kinds, None);

            // M4b-4c P2: an `err` record is a query the ORACLE rejects. leanr
            // must reject it too, with the same first line. Only errors with
            // an `oracle_first_line` can match, which today is
            // `ElabError::Eliminator`.
            if let Some(want) = q.get("err").and_then(|v| v.as_str()) {
                match got {
                    Err(e) => {
                        let line = e.oracle_first_line();
                        if line.as_deref() != Some(want) {
                            failures.push(format!(
                                "{id}: leanr error {e:?} (first line {line:?}); oracle {want:?}"
                            ));
                        }
                    }
                    Ok(_) => failures.push(format!(
                        "{id}: leanr elaborated; oracle errors with {want:?}"
                    )),
                }
                return;
            }

            match got {
                Ok(g) => {
                    // `base = Some(view.store)` (Task 5 reconciliation,
                    // mirroring `oracle_fast.rs`'s own `let base =
                    // Some(view.store);`): `g` can now embed a
                    // PERSISTENT-region `NameId` (`ident`'s resolved global
                    // constant name), which `elab.mctx.store()` — the
                    // elaborator's own SCRATCH store — cannot resolve on its
                    // own; `encode_expr`'s internal `to_name` needs the
                    // persistent store as a fallback base, exactly like
                    // every kernel-side `Store` method with a `base`
                    // parameter.
                    let mut st = EncSt::default();
                    let got_json = encode_expr(elab.mctx.store(), Some(view.store), g, &mut st);
                    // EVERY term this corpus elaborates is CLOSED — the
                    // queries are standalone terms with no ambient local
                    // context (`replay_fixture_in` installs an environment,
                    // never an `lctx`), so after `elab_term_and_synthesize`'s
                    // internal `instantiate_mvars` the finished `Expr` must
                    // contain no `fvar` NODE AT ALL. `EncSt` is fresh per
                    // record and `encode_expr` interns every `Node::FVar` it
                    // walks into `st.fvars`, so a non-empty map is an exact
                    // "this term leaked a free variable" answer, not a
                    // heuristic.
                    //
                    // WHY THIS GUARDS A REAL CLASS, not a hypothetical.
                    // Every corpus query is a CLOSED term (no ambient
                    // `lctx` — see above), so an `fvar` in a finished answer
                    // is a bug, full stop: it means some subterm's free
                    // variable never got abstracted before its binder
                    // closed. `MetaCtx::mk_binding`
                    // (`leanr_meta/src/metactx.rs`) runs the oracle's
                    // `elimMVarDeps` (`MetavarContext.lean`,
                    // `leanr_meta/src/mk_binding.rs`'s port) over the body
                    // and over each binder type before abstracting, at the
                    // oracle's own two insertion points — an unassigned
                    // metavariable whose own local context holds the fvars
                    // being abstracted is rewritten to a fresh metavariable
                    // APPLIED to them, so it abstracts like any other
                    // argument instead of leaking. Before that port landed
                    // (the `elimMVarDeps` slice), a postponed synthetic mvar
                    // registered under a binder and resumed by the fixpoint
                    // AFTER that binder closed had its value spliced in
                    // unabstracted: leanr emitted an `fvar` where the oracle
                    // emits a `bvar`, a WRONG `ExprId` with NO error — silent
                    // divergence, which this repo's cardinal rule forbids.
                    // `seam_audit.rs`'s
                    // `postponed_coe_under_a_binder_abstracts_via_elim_mvar_deps`
                    // pins that one shape by hand; this assertion turns the
                    // whole class loud across the corpus: any future
                    // regression fails HERE, named, instead of quietly
                    // shifting bytes.
                    //
                    // PLACEMENT: deliberately here, in the record replay,
                    // and NOT inside the shared `elab_and_synthesize`
                    // helper (it lives in this corpus runner) — a corpus regression should fail loudly at the
                    // corpus, not inside a shared helper other tests also
                    // call for unrelated shapes.
                    if !st.fvars.is_empty() {
                        leaked_fvars.push(format!("{id}: {got_json}"));
                    }
                    // The dumper (`dump_elab.lean`) only catches THROWN
                    // errors; a LOGGED one becomes `sorryAx` in an
                    // apparently successful record (errToSorry). Such a
                    // record pins an oracle error as a term (macro/binop% P3).
                    assert!(
                        !q["exp"].to_string().contains("\"sorryAx\""),
                        "{id}: the oracle record contains sorryAx -- the \
                         query is an oracle ERROR; move it to the err queries"
                    );
                    if got_json != q["exp"] {
                        failures.push(format!("{id}: leanr={got_json} oracle={}", q["exp"]));
                    }
                }
                Err(e) => failures.push(format!("{id}: leanr errored: {e:?}")),
            }
        });
    }
    // Asserted BEFORE the byte-comparison below: a leaked `fvar` also
    // shows up there as an ordinary divergence, and this message is the
    // one that says which class it belongs to.
    assert!(
        leaked_fvars.is_empty(),
        "{} record(s) finished with an UNABSTRACTED `fvar` in the term. Every \
         corpus query is a closed term, so an `fvar` in an answer is a bug: \
         `MetaCtx::mk_binding` (`leanr_meta/src/metactx.rs`) runs \
         `elim_mvar_deps` (`leanr_meta/src/mk_binding.rs`, the oracle's \
         `MkBinding.elimMVarDeps`) over the body and over each binder type \
         before abstracting, and `seam_audit.rs`'s \
         `postponed_coe_under_a_binder_abstracts_via_elim_mvar_deps` pins the \
         shape that used to leak. Do NOT relax this assertion and do NOT edit \
         the corpus — track down why a metavariable's value is reaching this \
         point unabstracted; a new record that trips this is a real \
         regression, not a known gap. Offenders:\n{}",
        leaked_fvars.len(),
        leaked_fvars.join("\n")
    );
    assert!(
        failures.is_empty(),
        "{} divergences:\n{}",
        failures.len(),
        failures.join("\n")
    );
    replayed
}

/// Elaborate `src` against an already-replayed environment, with the
/// same entry point `run_elab_corpus` uses, and discard the term. For
/// tests that only care whether, and how, elaboration fails.
pub fn elab_src_in(
    r: &Replayed,
    src: &str,
    snap: &leanr_syntax::grammar::GrammarSnapshot,
) -> Result<(), leanr_elab::ElabError> {
    with_record_elab(r, src, snap, |elab, term, kinds| {
        elab.elab_term_and_synthesize(term, kinds, None).map(|_| ())
    })
}

/// The grammar of the generated `ElabOp` fixture (macro/binop% P2): the
/// builtin grammar plus ElabOp's own notations. Shared by `oracle_op.rs`
/// and `op_helpers.rs`.
pub fn elab_op_grammar() -> leanr_syntax::grammar::GrammarSnapshot {
    let bytes = std::fs::read(fixture_in("elab", "ElabOp.olean")).expect("committed ElabOp.olean");
    let mut st = leanr_kernel::bank::Store::persistent();
    let md = leanr_olean::ModuleData::parse(&bytes, &mut st).expect("decode ElabOp.olean");
    assert!(md.imports.is_empty(), "ElabOp must stay import-free");
    let name = std::sync::Arc::new(leanr_kernel::Name::Anonymous); // display-only
    leanr_grammar::assemble(&[(name, md)], &st).snapshot
}

/// `f a`, built directly in the elaborator's scratch store.
pub fn mk_app(
    elab: &mut leanr_elab::TermElabM,
    f: leanr_kernel::bank::ExprId,
    a: leanr_kernel::bank::ExprId,
) -> leanr_kernel::bank::ExprId {
    let base = elab.view.store;
    elab.mctx
        .store_mut()
        .expr_app(Some(base), f, a)
        .expect("expr_app")
}

/// The `NameId` of a `Node::Const`; panics on any other node.
pub fn const_name(
    elab: &leanr_elab::TermElabM,
    c: leanr_kernel::bank::ExprId,
) -> leanr_kernel::bank::NameId {
    match elab.mctx.store().expr_node(Some(elab.view.store), c) {
        leanr_kernel::bank::terms::Node::Const { name: Some(n), .. } => n,
        other => panic!("const_name: not a named constant: {other:?}"),
    }
}

/// A fresh natural mvar whose type is a sort (`mkFreshTypeMVar`).
pub fn fresh_type_mvar(elab: &mut leanr_elab::TermElabM) -> leanr_kernel::bank::ExprId {
    elab.mk_fresh_type_mvar().expect("mk_fresh_type_mvar")
}

/// Elaborate the type `src` (builtin grammar) with this `elab`.
pub fn parse_type(elab: &mut leanr_elab::TermElabM, src: &str) -> leanr_kernel::bank::ExprId {
    let snap = leanr_syntax::builtin::snapshot();
    let parsed = leanr_syntax::parse_term(src, &snap);
    assert!(
        parsed.errors.is_empty(),
        "parse_type: {src:?}: {:?}",
        parsed.errors
    );
    let elem: leanr_elab::dispatch::SynElem = parsed
        .tree
        .root()
        .first_child_or_token()
        .unwrap_or_else(|| panic!("parse_type: no term child for {src:?}"));
    elab.elab_term(&elem, &parsed.tree.kinds, None)
        .unwrap_or_else(|e| panic!("parse_type: {src:?}: {e:?}"))
}
