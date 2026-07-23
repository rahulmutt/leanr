//! Shared `#[cfg(test)]` helpers for building a `MetaCtx` over the
//! replayed `Prelude0` fixture. Moved out of `infer.rs`'s own tests
//! module (task 5): `whnf.rs`'s tests need the exact same idiom, and
//! task 4's brief flagged duplicating it per module as the worse
//! option ("reuse — move it to a shared `#[cfg(test)]` module if
//! cleaner rather than duplicating").

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use leanr_kernel::bank::{ExprId, NameId, Store};
use leanr_kernel::{
    BinderInfo, CheckedConstants, ConstSource, ConstantInfo, EnvView, Environment, Nat,
};
use leanr_olean::ModuleData;

use crate::{Config, MVarDecl, MVarId, MVarKind, MetaCtx};

pub(crate) fn fixture_path(name: &str) -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

/// The empty-environment idiom (no `.olean`, no constants, `Config::
/// default`) — promoted from `metactx.rs::tests::with_ctx` (task 3):
/// `defeq.rs`'s tests need the exact same tiny scaffold, and per-module
/// duplication is precisely what this file exists to avoid (see the
/// module doc). Reconcile against `schedule.rs:324` — the shape, not
/// the letter: an `EnvView` over an empty persistent store and no
/// constants.
pub(crate) fn with_ctx<R>(f: impl FnOnce(&mut MetaCtx) -> R) -> R {
    let base = Store::persistent();
    let mut scratch = Store::scratch();
    let empty = CheckedConstants::new(std::collections::HashMap::new());
    let view = EnvView {
        consts: ConstSource::Gated(&empty),
        extra: None,
        quot_initialized: false,
        store: &base,
    };
    let mut ctx = MetaCtx::new(view, &mut scratch, Config::default(), &[], &[], &[], &[]);
    f(&mut ctx)
}

/// Mint a fresh, declared (but unassigned) expr metavariable of type
/// `ty` and return both its `Expr::mvar` reference and its `MVarId`
/// (task 5). Promoted here rather than defined privately in `assign.rs`
/// per task 5's own brief: task 8's plan text is expected to tell a
/// later implementer to reuse this exact helper, so a private copy in
/// `assign.rs` would force that later duplication instead of avoiding
/// it. Name uniqueness is via a process-wide monotone counter (mirrors
/// `level.rs::fresh_level_mvar`'s "fixed prefix + counter" idiom,
/// scoped to the whole test binary rather than one `MetaCtx` since
/// there is no production-code counter field to reuse for this
/// test-only need); every caller uses its own fresh `Store` (`with_ctx`
/// et al. each build one), so cross-test collisions cannot arise
/// either way — the counter is just cheap insurance against two calls
/// within the SAME test/`Store` colliding.
pub(crate) fn fresh_mvar(ctx: &mut MetaCtx, ty: ExprId) -> (ExprId, MVarId) {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let idx = COUNTER.fetch_add(1, Ordering::Relaxed);
    let base = Some(ctx.view.store);
    let prefix_str = ctx
        .scratch
        .intern_str(base, "_leanr_test_mvar")
        .expect("interning a tiny fixed name is infallible");
    let prefix = ctx
        .scratch
        .name_str(base, None, prefix_str)
        .expect("interning a tiny fixed name is infallible");
    let idx_id = ctx
        .scratch
        .intern_nat(base, &Nat::from(idx))
        .expect("interning a small nat is infallible");
    let name = ctx
        .scratch
        .name_num(base, Some(prefix), idx_id)
        .expect("interning a tiny fixed name is infallible");
    let id = MVarId(name);
    ctx.mctx_mut().declare(
        id,
        MVarDecl {
            user_name: None,
            ty,
            lctx: Default::default(),
            kind: MVarKind::Natural,
        },
    );
    let expr = ctx
        .scratch
        .expr_mvar(base, Some(name))
        .expect("interning a fresh mvar reference is infallible");
    (expr, id)
}

/// Mint a fresh free variable of type `ty`, declared directly in
/// `ctx.lctx` (task 6, promoted here per the task brief: `defeq.rs`'s
/// own `is_def_eq_binding_shallow_body` is the production-code idiom
/// this mirrors — `LocalContext::mk_local_decl`, reconciled against
/// `crates/leanr_kernel/src/local_ctx.rs`'s bank-native signature —
/// but that path opens a fvar mid-recursion and restores the context
/// on exit; a *test* fvar is meant to outlive the single call that
/// mints it, so this does not bracket it in a `save`/`restore` pair).
/// Interns `name` as the fvar's (purely cosmetic, never consulted by
/// `is_def_eq`) `binder_name` and returns the `Expr::fvar` reference.
pub(crate) fn fresh_fvar(ctx: &mut MetaCtx, ty: ExprId, name: &str) -> ExprId {
    let base = Some(ctx.view.store);
    let s = ctx
        .scratch
        .intern_str(base, name)
        .expect("interning a tiny fixed name is infallible");
    let n = ctx
        .scratch
        .name_str(base, None, s)
        .expect("interning a tiny fixed name is infallible");
    ctx.lctx
        .mk_local_decl(
            ctx.scratch,
            base,
            &mut ctx.fvar_gen,
            Some(n),
            ty,
            BinderInfo::Default,
        )
        .expect("declaring a test fvar is infallible")
}

/// Replay `Prelude0.olean` (import-free — see
/// `crates/leanr_olean/tests/check_fixtures.rs::prelude0_replays_from_empty_env`)
/// into a fresh `Environment`, then build a `MetaCtx` over its
/// `EnvView` (`Environment::view()`, the same shape
/// `crates/leanr_check/src/schedule.rs:316-329`'s `run_task` builds
/// by hand) plus a fresh scratch store — mirroring
/// `metactx.rs::tests::with_ctx`'s empty-env idiom, populated
/// instead of empty.
pub(crate) fn with_prelude0_ctx<R>(f: impl FnOnce(&mut MetaCtx) -> R) -> R {
    let bytes = std::fs::read(fixture_path("Prelude0.olean")).expect("Prelude0.olean fixture");
    let mut env = Environment::default();
    let md = ModuleData::parse(&bytes, env.store_mut()).expect("Prelude0 decodes");
    let reducibility = md.reducibility;
    let matchers = md.matchers;
    let instances = md.instances;
    let default_instances = md.default_instances;
    let constants: HashMap<NameId, ConstantInfo> =
        md.constants.into_iter().map(|c| (c.name(), c)).collect();
    leanr_kernel::replay(&mut env, constants).expect("Prelude0 replays");

    let view = env.view();
    let mut scratch = Store::scratch();
    let mut ctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        &reducibility,
        &matchers,
        &instances,
        &default_instances,
    );
    f(&mut ctx)
}

/// Replay `Instances.olean` (PR-A's decode fixture for the typeclass-
/// synthesis extensions: `instanceExtension`/`defaultInstanceExtension`/
/// `projectionFnInfoExt`; task B2's own fixture). Same shape as
/// [`with_matcher_ctx`] just above — `prelude`-mode, import-free, replayed
/// into a fresh empty `Environment` (see `Instances.lean`'s own module doc
/// for the fixture's classes/instances: `Add`/`Mul`/`Semigroup extends
/// Mul`/`Monoid extends Semigroup`, `inductive N`, `instAddN`/`instMulN`/
/// `instSemigroupN`/`instMonoidN`, the parametrized `instAddProd {a b}
/// [Add a] [Add b] : Add (Prod a b)`, and `OfN`/`@[default_instance]
/// instOfNN`).
pub(crate) fn with_instances_ctx<R>(f: impl FnOnce(&mut MetaCtx) -> R) -> R {
    let bytes = std::fs::read(fixture_path("Instances.olean")).expect("Instances.olean fixture");
    let mut env = Environment::default();
    let md = ModuleData::parse(&bytes, env.store_mut()).expect("Instances.olean decodes");
    assert!(
        md.imports.is_empty(),
        "Instances.olean must be import-free (prelude-mode fixture) — \
         with_instances_ctx replays it into an empty Environment with no \
         dependency loading"
    );
    let reducibility = md.reducibility;
    let matchers = md.matchers;
    let instances = md.instances;
    let default_instances = md.default_instances;
    let constants: HashMap<NameId, ConstantInfo> =
        md.constants.into_iter().map(|c| (c.name(), c)).collect();
    leanr_kernel::replay(&mut env, constants).expect("Instances.olean replays");

    let view = env.view();
    let mut scratch = Store::scratch();
    let mut ctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        &reducibility,
        &matchers,
        &instances,
        &default_instances,
    );
    f(&mut ctx)
}

/// Build an `Expr.const` for `name`, filling its universe-level
/// arguments with `Level.zero` repeated once per the constant's OWN
/// declared `level_params` arity (mirrors `infer.rs::tests::
/// const_type_instantiates_levels`'s idiom: a bare empty level list is
/// only valid for a level-param-free constant, and every class/instance
/// in `Instances.lean` is declared with at least one `u`, so a real
/// `MetaCtx::infer_type` call on the result — which `discr_path.rs`'s
/// `ignoreArg`/`isType`/`isProof` machinery makes constantly — would
/// otherwise fail `infer_const`'s own level-arity check). `Level.zero`
/// is an arbitrary-but-safe placeholder: nothing this task's tests probe
/// (binder info, `Sort`-headedness, `Prop`-headedness) depends on which
/// universe is actually chosen.
fn const_expr_for(ctx: &mut MetaCtx, name: NameId) -> ExprId {
    let base = Some(ctx.view.store);
    let arity = ctx
        .view
        .get(name)
        .map(|info| info.constant_val().level_params.len())
        .unwrap_or(0);
    let z = ctx.scratch.level_zero(base).expect("level");
    let levels = vec![z; arity];
    let levels = ctx
        .scratch
        .intern_level_list(base, &levels)
        .expect("levels");
    ctx.scratch
        .expr_const(base, Some(name), levels)
        .expect("const")
}

/// An `Expr.const` for a root (single-component) name, interned against
/// the CURRENT store's persistent base — the `infer.rs::tests::single`+
/// `const_expr` idiom, promoted here (task B2) since `discr_path.rs`'s
/// tests need the exact same "look up a fixture-declared constant by its
/// plain name" shape, and per this file's own module doc, duplication
/// per module is what it exists to avoid. See [`const_expr_for`] for why
/// this fills in real (`Level.zero`) universe arguments rather than an
/// empty list.
pub(crate) fn const_named(ctx: &mut MetaCtx, name: &str) -> ExprId {
    let base = Some(ctx.view.store);
    let s = ctx.scratch.intern_str(base, name).expect("intern");
    let n = ctx.scratch.name_str(base, None, s).expect("name");
    const_expr_for(ctx, n)
}

/// An `Expr.const` for a two-component dotted name (`"Add.add"`,
/// `"N.zero"`, ...), same interning/level-filling convention as
/// [`const_named`] above.
pub(crate) fn const_dotted(ctx: &mut MetaCtx, a: &str, b: &str) -> ExprId {
    let base = Some(ctx.view.store);
    let a_str = ctx.scratch.intern_str(base, a).expect("intern");
    let a_name = ctx.scratch.name_str(base, None, a_str).expect("name");
    let b_str = ctx.scratch.intern_str(base, b).expect("intern");
    let n = ctx
        .scratch
        .name_str(base, Some(a_name), b_str)
        .expect("name");
    const_expr_for(ctx, n)
}

/// Build a goal expression from a space-separated spec: the head is a
/// bare (root-name) constant, each remaining token another bare
/// constant applied as an argument — e.g. `"Add N"` builds `@Add N`
/// (task B3's own `instance_table_finds_add_n` test; brief's suggested
/// helper name, reimplemented here as a free function per this file's
/// existing style rather than a `MetaCtx` method — see [`const_named`]
/// for the same level-filling convention this reuses per token).
pub(crate) fn parse_goal(ctx: &mut MetaCtx, spec: &str) -> ExprId {
    let mut tokens = spec.split_whitespace();
    let head_name = tokens.next().expect("parse_goal: empty spec");
    let head = const_named(ctx, head_name);
    let args: Vec<ExprId> = tokens.map(|t| const_named(ctx, t)).collect();
    ctx.mk_app_spine(head, &args)
        .expect("parse_goal: mk_app_spine")
}

/// Find one instance by its bare declaration name (task B3's own
/// `instance_named` brief helper, reimplemented as a free function per
/// this file's existing style — see [`parse_goal`]'s doc for why).
/// Returns an owned clone (`Instance: Clone`) since `MetaCtx::
/// instance_named`'s borrow cannot outlive the `&str`-interning calls
/// this needs to make first.
pub(crate) fn instance_named(ctx: &mut MetaCtx, name: &str) -> Option<crate::instances::Instance> {
    let base = Some(ctx.view.store);
    let s = ctx.scratch.intern_str(base, name).expect("intern");
    let n = ctx.scratch.name_str(base, None, s).expect("name");
    ctx.instance_named(n).cloned()
}

/// Render a `NameId` to its plain dotted string, resolved through the
/// CURRENT store's persistent base — the assertion-readability helper
/// `discr_path.rs`'s tests use to check a `DiscrKey::Const { name, .. }`
/// against a name like `"Add"` without hand-rolling `NameId` equality at
/// every call site.
pub(crate) fn render_name(ctx: &MetaCtx, name: NameId) -> String {
    ctx.scratch
        .to_name(Some(ctx.view.store), Some(name))
        .to_string()
}

/// Replay `Matcher.olean` (task 1's decode fixture; prelude-mode,
/// import-free, replays from an empty environment exactly like
/// `Prelude0` — see `Matcher.lean`'s own module doc for why a
/// hermetic scaffold was needed to declare `match` under bare
/// `prelude`). Same shape as [`with_prelude0_ctx`] above, just a
/// different fixture and `&md.matchers` actually populated (task 6's
/// first real consumer of that field, over `isZero`/`both`/`plainId`).
pub(crate) fn with_matcher_ctx<R>(f: impl FnOnce(&mut MetaCtx) -> R) -> R {
    let bytes = std::fs::read(fixture_path("Matcher.olean")).expect("Matcher.olean fixture");
    let mut env = Environment::default();
    let md = ModuleData::parse(&bytes, env.store_mut()).expect("Matcher.olean decodes");
    // Hermeticity check (final-review item 3): `Matcher.olean` must be
    // import-free, exactly like `Prelude0.olean` (see
    // `crates/leanr_olean/src/loader.rs:666`'s equivalent assert for
    // that fixture). `leanr_kernel::replay` below replays into a FRESH
    // empty `Environment` — if `Matcher.olean` ever gained a real
    // import, replaying it here without also replaying its
    // dependencies first would silently produce a wrong/incomplete
    // environment instead of failing loudly.
    assert!(
        md.imports.is_empty(),
        "Matcher.olean must be import-free (prelude-mode fixture) — \
         with_matcher_ctx replays it into an empty Environment with no \
         dependency loading"
    );
    let reducibility = md.reducibility;
    let matchers = md.matchers;
    let instances = md.instances;
    let default_instances = md.default_instances;
    let constants: HashMap<NameId, ConstantInfo> =
        md.constants.into_iter().map(|c| (c.name(), c)).collect();
    leanr_kernel::replay(&mut env, constants).expect("Matcher.olean replays");

    let view = env.view();
    let mut scratch = Store::scratch();
    let mut ctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        &reducibility,
        &matchers,
        &instances,
        &default_instances,
    );
    f(&mut ctx)
}
