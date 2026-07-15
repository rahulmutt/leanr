//! `leanr parse` surface: dump matches the library canon; parse errors
//! exit nonzero with coded diagnostics; invalid UTF-8 is E0305.

use assert_cmd::Command;

fn setup() -> tempfile::TempDir {
    tempfile::TempDir::new().unwrap()
}

fn leanr(tmp: &tempfile::TempDir) -> Command {
    let mut c = Command::cargo_bin("leanr").unwrap();
    c.current_dir(tmp.path());
    c
}

#[test]
fn parse_dump_emits_canonical_jsonl() {
    let tmp = setup();
    let f = tmp.path().join("T.lean");
    std::fs::write(&f, "prelude\n\ndef x := 42\n").unwrap();
    let out = leanr(&tmp)
        .args(["parse", "--dump"])
        .arg(&f)
        .output()
        .unwrap();
    assert!(out.status.success(), "{:?}", out);
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(stdout.lines().count() >= 2, "header + command lines");
    assert!(stdout.contains("\"k\":\"Lean.Parser.Module.header\""));
}

#[test]
fn parse_errors_exit_nonzero_with_codes() {
    let tmp = setup();
    let f = tmp.path().join("Bad.lean");
    std::fs::write(&f, "def := :=").unwrap();
    let out = leanr(&tmp).arg("parse").arg(&f).output().unwrap();
    assert!(!out.status.success());
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert!(stderr.contains("error[E03"), "{stderr}");
}

#[test]
fn invalid_utf8_is_e0305_not_a_panic() {
    let tmp = setup();
    let f = tmp.path().join("bin.lean");
    std::fs::write(&f, [0xFF, 0xFE, 0x00]).unwrap();
    let out = leanr(&tmp).arg("parse").arg(&f).output().unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8(out.stderr).unwrap().contains("E0305"));
}
