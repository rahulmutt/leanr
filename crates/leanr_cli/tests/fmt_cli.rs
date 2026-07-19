//! `leanr fmt` / `leanr fmt --check`.
//!
//! Hermeticity: `load_snapshot` (shared with `parse`) calls `discover_roots`,
//! which shells out to `lean --print-libdir`. In a dev sandbox with a real
//! toolchain on `PATH` (via elan) that would add the real Lean core library
//! as a search root and turn "Foo.A"/"Foo.B" into a multi-minute stdlib
//! load / a hard "module not found" error instead of the intended
//! builtin-only fallback. Every command below blanks `PATH` and removes
//! `LEAN_PATH`, matching `tests/parse_imports.rs`.

use std::process::Command;

fn leanr() -> Command {
    let mut c = Command::new(env!("CARGO_BIN_EXE_leanr"));
    c.env_remove("LEAN_PATH").env("PATH", "");
    c
}

#[test]
fn fmt_check_flags_unformatted_file() {
    let dir = tempfile::tempdir().unwrap();
    let f = dir.path().join("A.lean");
    std::fs::write(&f, "import Foo.B\nimport Foo.A\n").unwrap();
    let out = leanr().arg("fmt").arg("--check").arg(&f).output().unwrap();
    assert!(
        !out.status.success(),
        "check should fail on unformatted file"
    );
}

#[test]
fn fmt_rewrites_in_place() {
    let dir = tempfile::tempdir().unwrap();
    let f = dir.path().join("A.lean");
    std::fs::write(&f, "import Foo.B\nimport Foo.A\n").unwrap();
    let out = leanr().arg("fmt").arg(&f).output().unwrap();
    assert!(out.status.success());
    assert_eq!(
        std::fs::read_to_string(&f).unwrap(),
        "import Foo.A\nimport Foo.B\n"
    );
}
