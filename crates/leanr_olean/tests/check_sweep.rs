//! Full-stdlib `leanr check --all` sweep, mirroring the `check:stdlib` mise
//! task at the library level so it is runnable under `cargo test` tooling
//! too (M1a sweep convention: `stdlib_sweep.rs`'s `every_stdlib_olean_decodes`
//! does the same for the decoder alone). Ignored by default: it needs the
//! pinned Lean toolchain on disk, which CI does not have. Run via
//! `mise run check:stdlib` or directly:
//! `LEANR_SWEEP_DIR="$(lean --print-libdir)" cargo test --release --package leanr_olean --test check_sweep -- --ignored --nocapture`
//!
//! STATUS (M1b Task 14): a full run is expected to currently fail with
//! `KernelError::DeepRecursion` on `Nat.Linear.ExprCnstr.denote_toNormPoly`
//! (module `Init.Data.Nat.Linear`) — a real stdlib definition whose
//! dependency recursion exceeds `RecGuard::MAX_REC_DEPTH` during replay.
//! That is a pre-existing `leanr_kernel` limitation, out of this task's
//! scope, deferred to Task 16 hardening/acceptance. This test documents and
//! exercises the full-closure `load_closure` + `replay` path (the same path
//! `leanr check --all` drives) so the sweep goes green the moment that
//! blocker is lifted.

use std::collections::HashMap;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

use leanr_kernel::bank::NameId;
use leanr_kernel::{ConstantInfo, Environment, Name};
use leanr_olean::{load_closure, SearchPath};

/// Recursively collect every base `.olean` under `dir`. Companion parts
/// (`Foo.olean.server`/`Foo.olean.private`) have extension `server`/
/// `private`, not `olean`, so this filter naturally excludes them — they
/// load automatically as part of their base module (Task 13a).
fn collect_oleans(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_oleans(&path, out);
        } else if path.extension().is_some_and(|e| e == "olean") {
            out.push(path);
        }
    }
}

/// Map a root-relative path (extension already stripped) to a module
/// `Name`, e.g. `Init/Data/Nat` -> `Init.Data.Nat`.
fn path_to_module_name(rel: &Path) -> Option<Arc<Name>> {
    let mut n = Arc::new(Name::Anonymous);
    for comp in rel.components() {
        match comp {
            Component::Normal(s) => {
                n = Arc::new(Name::Str {
                    parent: n,
                    part: s.to_str()?.to_string(),
                });
            }
            _ => return None,
        }
    }
    Some(n)
}

#[test]
#[ignore = "needs the pinned Lean toolchain; run via `mise run check:stdlib`"]
fn check_all_stdlib_oleans() {
    let dir = std::env::var("LEANR_SWEEP_DIR")
        .expect("LEANR_SWEEP_DIR must point at the toolchain lib/lean dir");
    let root = PathBuf::from(&dir);

    let mut files = Vec::new();
    collect_oleans(&root, &mut files);
    files.sort();
    assert!(
        files.len() > 1000,
        "suspiciously few .olean files ({}) under {dir} — wrong directory?",
        files.len()
    );

    let targets: Vec<Arc<Name>> = files
        .iter()
        .filter_map(|f| {
            let rel = f.strip_prefix(&root).unwrap().with_extension("");
            path_to_module_name(&rel)
        })
        .collect();

    let sp = SearchPath::new(vec![root]);
    let modules = load_closure(&sp, &targets).expect("closure loads");
    let module_count = modules.len();

    // Bridge-intern every module's constants into the environment's
    // persistent bank one module at a time, dropping each decoded
    // module's Arc graph before the next (the id-native kernel's
    // memory-win line — spec:
    // docs/superpowers/specs/2026-07-06-term-bank-kernel-migration-design.md
    // §2 "Load"). Module oleans carry only their own module's constants,
    // so the closure's constant sets are disjoint; first-seen wins on
    // the rare cross-module name collision, matching the pre-migration
    // Arc `HashMap::entry(...).or_insert(...)` fold this replaces.
    let mut env = Environment::default();
    let mut constants: HashMap<NameId, ConstantInfo> = HashMap::new();
    for (_, md) in modules {
        let interned = env
            .intern_module(md.constants)
            .unwrap_or_else(|e| panic!("stdlib interning failed: {e}"));
        for (name, ci) in interned {
            constants.entry(name).or_insert(ci);
        }
    }

    let stats = leanr_kernel::replay(&mut env, constants)
        .unwrap_or_else(|e| panic!("stdlib replay failed: {e}"));
    println!(
        "checked {} modules, {} declarations (skipped {} unsafe/partial)",
        module_count, stats.checked, stats.skipped_unsafe
    );
}
