use assert_cmd::Command;

#[test]
fn version_prints_name_and_semver() {
    Command::cargo_bin("leanr")
        .unwrap()
        .arg("--version")
        .assert()
        .success()
        .stdout(predicates::str::starts_with("leanr 0.1.0"));
}

use std::path::PathBuf;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

#[test]
fn olean_info_prints_header_fields() {
    let githash = std::fs::read_to_string(fixture("oracle-githash.txt")).unwrap();
    Command::cargo_bin("leanr")
        .unwrap()
        .args(["olean", "info"])
        .arg(fixture("Sample.olean"))
        .assert()
        .success()
        .stdout(predicates::str::contains(githash.trim()))
        .stdout(predicates::str::contains("base address"));
}

#[test]
fn olean_info_on_missing_file_fails_with_helpful_error() {
    Command::cargo_bin("leanr")
        .unwrap()
        .args(["olean", "info", "does-not-exist.olean"])
        .assert()
        .failure()
        .stderr(predicates::str::contains("does-not-exist.olean"));
}

#[test]
fn olean_info_on_garbage_fails_without_panicking() {
    let dir = std::env::temp_dir().join("leanr-cli-test");
    std::fs::create_dir_all(&dir).unwrap();
    let garbage = dir.join("garbage.olean");
    std::fs::write(&garbage, b"definitely not an olean").unwrap();

    Command::cargo_bin("leanr")
        .unwrap()
        .args(["olean", "info"])
        .arg(&garbage)
        .assert()
        .failure()
        .stderr(predicates::str::contains("not an olean file"));
}
