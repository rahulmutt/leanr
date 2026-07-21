//! Shared `#[cfg(test)]` helpers for building a `MetaCtx` over the
//! replayed `Prelude0` fixture. Moved out of `infer.rs`'s own tests
//! module (task 5): `whnf.rs`'s tests need the exact same idiom, and
//! task 4's brief flagged duplicating it per module as the worse
//! option ("reuse — move it to a shared `#[cfg(test)]` module if
//! cleaner rather than duplicating").

use std::collections::HashMap;

use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{CheckedConstants, ConstSource, ConstantInfo, EnvView, Environment};
use leanr_olean::ModuleData;

use crate::{Config, MetaCtx};

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
