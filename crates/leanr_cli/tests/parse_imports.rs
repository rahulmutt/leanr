//! Import-aware `leanr parse`: `--path` resolves the header's imports
//! through the same root-discovery as `check`, folding the closure's
//! parser extensions onto the builtin grammar before parsing. No
//! resolvable roots (or no imports) keeps the M3a builtin-only behavior
//! byte-identical.
//!
//! Hermeticity: `discover_roots` also shells out to `lean --print-libdir`
//! and, if a real toolchain happens to be on `PATH` (as it is in dev
//! sandboxes via elan), that would silently add the real Lean core
//! library as an extra search root — turning "unresolvable hermetically"
//! into a multi-minute load of the real stdlib. Every command below
//! blanks `PATH` so root discovery only ever sees `--path`/`LEAN_PATH`.

use assert_cmd::Command;
use std::path::{Path, PathBuf};

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/syntax/import")
}

#[test]
fn parse_with_path_uses_imported_notation() {
    let dir = fixture_dir();
    let want = std::fs::read_to_string(dir.join("ImportMixfix.stx.jsonl")).unwrap();
    let out = Command::cargo_bin("leanr")
        .unwrap()
        .args(["parse", "--dump", "--path"])
        .arg(&dir)
        .arg(dir.join("ImportMixfix.lean"))
        .env_remove("LEAN_PATH")
        .env("PATH", "")
        .assert()
        .success();
    let stdout = String::from_utf8(out.get_output().stdout.clone()).unwrap();
    // Dump includes the header line; oracle dump includes it too.
    assert_eq!(stdout, want);
}

#[test]
fn parse_without_path_keeps_builtin_behavior() {
    // No --path and no LEAN_PATH containing NotaDep: import unresolved →
    // must still exit successfully IF the file parses under builtins;
    // ImportMixfix does NOT (uses ⊕⊕), so expect parse errors reported.
    let dir = fixture_dir();
    Command::cargo_bin("leanr")
        .unwrap()
        .args(["parse"])
        .arg(dir.join("ImportMixfix.lean"))
        .env_remove("LEAN_PATH")
        .env("PATH", "")
        .assert()
        .failure();
}

#[test]
fn verbose_lists_skipped_entries() {
    let dir = fixture_dir();
    // NotaDepMeta has a raw @[term_parser]; importing it must WARN, not
    // fail — but NotaDepMeta itself imports Lean, which is unresolvable
    // hermetically. This test pins that ERROR path: exit failure with a
    // module-not-found message naming Lean, not a panic.
    let tmp = tempfile::TempDir::new().unwrap();
    let file = tmp.path().join("ImportRawTmp.lean");
    std::fs::write(&file, "import NotaDepMeta\n#check 1\n").unwrap();
    let out = Command::cargo_bin("leanr")
        .unwrap()
        .args(["parse", "--verbose", "--path"])
        .arg(&dir)
        .arg(&file)
        .env_remove("LEAN_PATH")
        .env("PATH", "")
        .assert()
        .failure();
    let stderr = String::from_utf8(out.get_output().stderr.clone()).unwrap();
    assert!(stderr.contains("Lean"), "stderr: {stderr}");
}
