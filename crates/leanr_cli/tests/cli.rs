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
