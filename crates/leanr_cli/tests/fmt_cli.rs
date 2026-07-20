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

#[test]
fn fmt_with_no_args_walks_project_and_respects_gitignore() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    std::fs::create_dir_all(root.join("src/nested")).unwrap();
    std::fs::create_dir_all(root.join("vendored")).unwrap();
    std::fs::create_dir_all(root.join(".lake/packages")).unwrap();
    std::fs::write(root.join(".gitignore"), "vendored/\n").unwrap();

    let unformatted = "import Foo.B\nimport Foo.A\n";
    let formatted = "import Foo.A\nimport Foo.B\n";
    std::fs::write(root.join("src/A.lean"), unformatted).unwrap();
    std::fs::write(root.join("src/nested/B.lean"), unformatted).unwrap();
    std::fs::write(root.join("vendored/C.lean"), unformatted).unwrap();
    std::fs::write(root.join(".lake/packages/D.lean"), unformatted).unwrap();

    let out = leanr().arg("fmt").current_dir(root).output().unwrap();
    assert!(out.status.success(), "project walk should succeed");

    // Walked and rewritten, including nested.
    assert_eq!(
        std::fs::read_to_string(root.join("src/A.lean")).unwrap(),
        formatted
    );
    assert_eq!(
        std::fs::read_to_string(root.join("src/nested/B.lean")).unwrap(),
        formatted
    );
    // Gitignored: untouched.
    assert_eq!(
        std::fs::read_to_string(root.join("vendored/C.lean")).unwrap(),
        unformatted
    );
    // Hidden directory (.lake, .git, .mathlib): untouched.
    assert_eq!(
        std::fs::read_to_string(root.join(".lake/packages/D.lean")).unwrap(),
        unformatted
    );
}

#[test]
fn fmt_with_no_args_and_no_lean_files_succeeds() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("README.md"), "# nothing here\n").unwrap();
    let out = leanr().arg("fmt").current_dir(dir.path()).output().unwrap();
    assert!(
        out.status.success(),
        "an empty project is not an error: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}
