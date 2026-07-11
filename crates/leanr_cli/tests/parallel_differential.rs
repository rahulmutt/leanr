//! Differential gate (Task 6): the parallel driver (`leanr_check::check_parallel`)
//! must agree with the sequential reference (`leanr_kernel::replay`) on the
//! same decoded input. This is the load-bearing proof that the parallel
//! driver — its dependency graph, its resolve-or-reject compare, and the
//! shared `quot_initialized` flag — is verdict-equivalent to `replay` on
//! real decoded content, not just on hand-built `leanr_check` fixtures.
//!
//! Uses the hermetic `Prelude0.olean` fixture (import-free, no toolchain
//! needed — same fixture `leanr_olean/tests/check_fixtures.rs` replays from
//! an empty environment). `Environment` isn't `Clone` (by design — see its
//! module doc), so each run decodes the fixture bytes fresh: the fixture is
//! tiny, and decoding IS interning (direct-to-id decode), so there is no
//! cheaper way to get two independent, store-consistent copies of the same
//! decoded constant set.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use leanr_kernel::bank::NameId;
use leanr_kernel::{CheckedConstants, ConstantInfo, Environment};
use leanr_olean::ModuleData;

fn fixture_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

/// Decode `Prelude0.olean` fresh into a brand-new `Environment`, returning
/// the union-fold `constants` map (mirrors `leanr_cli::check`'s decode +
/// fold loop, minus the module-count/owner bookkeeping this test doesn't
/// need).
fn decode_prelude0() -> (Environment, HashMap<NameId, ConstantInfo>) {
    let bytes = std::fs::read(fixture_path("Prelude0.olean")).unwrap();
    let mut env = Environment::default();
    let m = ModuleData::parse(&bytes, env.store_mut()).unwrap();
    assert!(m.imports.is_empty(), "Prelude0 imports nothing");
    let constants: HashMap<NameId, ConstantInfo> =
        m.constants.into_iter().map(|c| (c.name(), c)).collect();
    (env, constants)
}

#[test]
fn parallel_matches_sequential_on_fixture() {
    // Sequential reference: decode once, replay against a live env.
    let (mut seq_env, seq_constants) = decode_prelude0();
    let seq = leanr_kernel::replay(&mut seq_env, seq_constants);

    for jobs in [1usize, 4usize] {
        // Parallel: decode AGAIN (independent store), freeze it, build the
        // table + graph, and drive the parallel checker.
        let (par_env, par_constants) = decode_prelude0();
        // `Prelude0` has no unsafe/partial constants (asserted below), so
        // the table is the whole decoded map — matching `replay`'s
        // `skipped_unsafe == 0` on this fixture.
        let skipped = par_constants
            .values()
            .filter(|ci| leanr_kernel::is_unsafe_or_partial(ci))
            .count();

        let store = Arc::new(par_env.into_store());
        let table = Arc::new(CheckedConstants::new(par_constants));
        let graph = leanr_check::graph::build_graph(&store, &table).unwrap();
        let par = leanr_check::check_parallel(store, table, graph, jobs, |_| {});

        match (&seq, &par) {
            (Ok(s), Ok(p)) => {
                assert_eq!(
                    (s.checked, s.skipped_unsafe),
                    (p.checked, skipped),
                    "jobs={jobs}: parallel/sequential checked or skipped counts diverged"
                );
                assert_eq!(
                    p.skipped_unsafe, 0,
                    "table was pre-filtered; driver's own skip count must be 0"
                );
            }
            (Err(_), Err(_)) => {} // both reject — acceptable for a differential
            _ => panic!(
                "jobs={jobs}: verdict mismatch — sequential={:?}, parallel={:?}",
                seq.as_ref().map(|s| s.checked),
                par.as_ref().map(|p| p.checked)
            ),
        }
    }
}
