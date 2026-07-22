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
    let mut ctx = MetaCtx::new(view, &mut scratch, Config::default(), &[], &[]);
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
    );
    f(&mut ctx)
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
    );
    f(&mut ctx)
}
