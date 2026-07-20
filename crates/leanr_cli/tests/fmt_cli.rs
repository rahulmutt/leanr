//! `leanr fmt` / `leanr fmt --check`.
//!
//! Hermeticity: `load_snapshot` (shared with `parse`) calls `discover_roots`,
//! which shells out to `lean --print-libdir`. In a dev sandbox with a real
//! toolchain on `PATH` (via elan) that would add the real Lean core library
//! as a search root and turn "Foo.A"/"Foo.B" into a multi-minute stdlib
//! load / a hard "module not found" error instead of the intended
//! builtin-only fallback. Every command below blanks `PATH` and removes
//! `LEAN_PATH`, matching `tests/parse_imports.rs`.

use std::io::Write;
use std::process::{Command, Stdio};

fn leanr() -> Command {
    let mut c = Command::new(env!("CARGO_BIN_EXE_leanr"));
    c.env_remove("LEAN_PATH").env("PATH", "");
    c
}

/// Assert a unified diff body (after the `---`/`+++` headers) contains the
/// expected content, not merely the shape of a diff. Every call site in
/// this file uses the same two-line-swap fixture:
/// `"import Foo.B\nimport Foo.A\n"` -> `"import Foo.A\nimport Foo.B\n"`.
///
/// For that fixture, `similar` (the diff engine `leanr` actually uses,
/// pinned in `Cargo.lock`) picks `import Foo.B` as the unchanged context
/// line and treats `import Foo.A` as moved: it emits `+import Foo.A`
/// followed by unchanged ` import Foo.B` followed by `-import Foo.A`. This
/// was verified by directly executing the production call
/// (`TextDiff::from_lines(before, after).unified_diff().context_radius(3)`)
/// against the fixture, not assumed. Do not "fix" this to also assert on
/// `import Foo.B` — GNU `diff -u` would pick the opposite, equally minimal,
/// tie-break, but `similar` does not, and this assertion must match what
/// the code under test actually produces.
///
/// Skipping the first two lines is REQUIRED, not cosmetic: the unified
/// diff's own header lines (`--- name` / `+++ name`) themselves start with
/// `-`/`+`, so without the skip a shape-only check would pass even on the
/// header alone, with no real diff body at all. Do not simplify this away.
fn assert_shows_a_change(stdout: &str) {
    let body: Vec<&str> = stdout.lines().skip(2).collect();
    assert!(
        body.iter().any(|l| l.starts_with('-')),
        "diff must show a removed line: {stdout}"
    );
    assert!(
        body.iter().any(|l| l.starts_with('+')),
        "diff must show an added line: {stdout}"
    );
    // Content, not just shape: pin the actual swapped line, verified
    // against the real `similar`-backed production output (see doc
    // comment above).
    assert!(
        body.iter().any(|l| l == &"-import Foo.A"),
        "diff must remove the moved line `import Foo.A`: {stdout}"
    );
    assert!(
        body.iter().any(|l| l == &"+import Foo.A"),
        "diff must add the moved line `import Foo.A`: {stdout}"
    );
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

#[test]
fn fmt_check_prints_unified_diff_naming_the_file() {
    let dir = tempfile::tempdir().unwrap();
    let f = dir.path().join("A.lean");
    let unformatted = "import Foo.B\nimport Foo.A\n";
    std::fs::write(&f, unformatted).unwrap();

    let out = leanr().arg("fmt").arg("--check").arg(&f).output().unwrap();
    assert!(
        !out.status.success(),
        "check must fail on a would-change file"
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("A.lean"),
        "diff must name the input: {stdout}"
    );
    assert_shows_a_change(&stdout);
    // Check mode never writes the file.
    assert_eq!(std::fs::read_to_string(&f).unwrap(), unformatted);
}

#[test]
fn fmt_check_stdin_diffs_and_fails_without_emitting_formatted_text() {
    let mut child = leanr()
        .arg("fmt")
        .arg("--check")
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(b"import Foo.B\nimport Foo.A\n")
        .unwrap();
    let out = child.wait_with_output().unwrap();

    assert!(
        !out.status.success(),
        "check on would-change stdin must exit non-zero"
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("<stdin>"),
        "diff must name the input as <stdin>: {stdout}"
    );
    assert_shows_a_change(&stdout);
    // The formatted text itself must NOT be emitted — that is the
    // non-check behavior and would be indistinguishable from it.
    assert!(
        !stdout.contains("\nimport Foo.A\nimport Foo.B\n"),
        "check mode must not emit the formatted output: {stdout}"
    );
}

#[test]
fn fmt_check_is_silent_and_succeeds_on_formatted_input() {
    let dir = tempfile::tempdir().unwrap();
    let f = dir.path().join("A.lean");
    std::fs::write(&f, "import Foo.A\nimport Foo.B\n").unwrap();
    let out = leanr().arg("fmt").arg("--check").arg(&f).output().unwrap();
    assert!(out.status.success(), "already-formatted input must pass");
    assert!(
        out.stdout.is_empty(),
        "no diff for unchanged input: {}",
        String::from_utf8_lossy(&out.stdout)
    );
}
