//! Decodes every base `.olean` shipped with the pinned toolchain
//! (~2,400 modules — all of Init/Std/Lean). Ignored by default: it
//! needs the oracle toolchain on disk, which CI does not have. Run via
//! `mise run sweep:stdlib`.

use std::path::{Path, PathBuf};

use leanr_olean::ModuleData;

fn collect_oleans(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_oleans(&path, out);
        } else if path.extension().is_some_and(|e| e == "olean") {
            // `Foo.olean.server`/`.olean.private` have extension
            // "server"/"private", so this filter keeps base parts only
            // (multi-part modules share a compactor; only the base
            // part is self-contained — see the plan's layout notes).
            out.push(path);
        }
    }
}

#[test]
#[ignore = "needs the pinned Lean toolchain; run via `mise run sweep:stdlib`"]
fn every_stdlib_olean_decodes() {
    let dir = std::env::var("LEANR_SWEEP_DIR")
        .expect("LEANR_SWEEP_DIR must point at the toolchain lib/lean dir");
    let mut files = Vec::new();
    collect_oleans(Path::new(&dir), &mut files);
    files.sort();
    assert!(
        files.len() > 1000,
        "suspiciously few .olean files ({}) under {dir} — wrong directory?",
        files.len()
    );

    let mut failures = Vec::new();
    let mut constants = 0usize;
    for path in &files {
        let bytes = std::fs::read(path).unwrap();
        match ModuleData::parse(&bytes) {
            Ok(md) => constants += md.constants.len(),
            Err(err) => failures.push(format!("{}: {err}", path.display())),
        }
    }
    println!(
        "swept {} modules, {} constants, {} failures",
        files.len(),
        constants,
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "decoder incomplete for {} of {} modules:\n{}",
        failures.len(),
        files.len(),
        failures.join("\n")
    );
}
