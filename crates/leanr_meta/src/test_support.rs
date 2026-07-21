//! Shared `#[cfg(test)]` helpers for building a `MetaCtx` over the
//! replayed `Prelude0` fixture. Moved out of `infer.rs`'s own tests
//! module (task 5): `whnf.rs`'s tests need the exact same idiom, and
//! task 4's brief flagged duplicating it per module as the worse
//! option ("reuse — move it to a shared `#[cfg(test)]` module if
//! cleaner rather than duplicating").

use std::collections::HashMap;

use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{ConstantInfo, Environment};
use leanr_olean::ModuleData;

use crate::{Config, MetaCtx};

pub(crate) fn fixture_path(name: &str) -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
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
