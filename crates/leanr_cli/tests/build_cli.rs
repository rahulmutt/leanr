use assert_cmd::Command;
use predicates::prelude::*;

// Reuse the synthetic-workspace shape from leanr_build's integration
// tests, minus the git dep (no require, no deps) so the CLI test needs
// no git and no manifest entries.
fn setup() -> tempfile::TempDir {
    let tmp = tempfile::TempDir::new().unwrap();
    let write = |rel: &str, text: &str| {
        let p = tmp.path().join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    };
    write(
        "lakefile.toml",
        "name = \"app\"\ndefaultTargets = [\"App\"]\n\n[[lean_lib]]\nname = \"App\"\n",
    );
    write("App.lean", "import App.Sub\n");
    write("App/Sub.lean", "");
    write(
        "lake-manifest.json",
        r#"{"version": "1.2.0", "packages": []}"#,
    );
    // Fake toolchain dir for --toolchain-dir: a real toolchain always ships
    // Init.olean, implicitly imported by every non-prelude module (see
    // leanr_build::graph::add_implicit_init).
    let fake_toolchain = tmp.path().join("fake-toolchain");
    std::fs::create_dir_all(&fake_toolchain).unwrap();
    std::fs::write(fake_toolchain.join("Init.olean"), "").unwrap();
    tmp
}

fn leanr(tmp: &tempfile::TempDir) -> Command {
    let mut c = Command::cargo_bin("leanr").unwrap();
    c.current_dir(tmp.path())
        .env("XDG_CACHE_HOME", tmp.path().join("xdg-cache"))
        .args(["build", "--dry-run"])
        .args([
            "--toolchain-dir",
            tmp.path().join("fake-toolchain").to_str().unwrap(),
        ]);
    c
}

#[test]
fn dry_run_prints_plan() {
    let tmp = setup();
    leanr(&tmp)
        .assert()
        .success()
        .stdout(predicate::str::contains("App.Sub"))
        .stdout(predicate::str::contains("2 modules"));
}

#[test]
fn json_output_is_workspace_relative_and_wave_ordered() {
    let tmp = setup();
    let out = leanr(&tmp)
        .arg("--json")
        .assert()
        .success()
        .get_output()
        .stdout
        .clone();
    let v: serde_json::Value = serde_json::from_slice(&out).unwrap();
    assert_eq!(v["root"], "app");
    assert_eq!(v["targets"][0], "App");
    let mods = v["modules"].as_array().unwrap();
    assert_eq!(mods.len(), 2);
    assert_eq!(mods[0]["name"], "App.Sub");
    assert_eq!(mods[0]["wave"], 0);
    assert_eq!(mods[0]["file"], "App/Sub.lean"); // relative, forward slashes
    assert_eq!(mods[1]["name"], "App");
    assert_eq!(mods[1]["wave"], 1);
}

#[test]
fn build_without_dry_run_is_a_clear_not_yet_error() {
    let tmp = setup();
    Command::cargo_bin("leanr")
        .unwrap()
        .current_dir(tmp.path())
        .env("XDG_CACHE_HOME", tmp.path().join("xdg-cache"))
        .args(["build"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("M2b"));
}

#[test]
fn resolution_error_is_reported_not_panicked() {
    let tmp = setup();
    std::fs::remove_file(tmp.path().join("lake-manifest.json")).unwrap();
    leanr(&tmp)
        .assert()
        .failure()
        .stderr(predicate::str::contains("lake update"));
}

#[test]
fn json_without_dry_run_is_a_clap_error() {
    let tmp = setup();
    Command::cargo_bin("leanr")
        .unwrap()
        .current_dir(tmp.path())
        .env("XDG_CACHE_HOME", tmp.path().join("xdg-cache"))
        .args(["build", "--json"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("--dry-run"));
}

/// A real path dependency: a sibling `dep/` directory (its own
/// lakefile.toml + one module), wired via `[[require]]` in the root
/// lakefile and a `"type": "path"` entry in lake-manifest.json. Exercises
/// the frozen `packages[]` JSON schema's actual field content — every
/// other CLI test workspace has `"packages": []`.
fn setup_with_path_dependency() -> tempfile::TempDir {
    let tmp = tempfile::TempDir::new().unwrap();
    let write = |rel: &str, text: &str| {
        let p = tmp.path().join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    };
    write(
        "app/lakefile.toml",
        "name = \"app\"\ndefaultTargets = [\"App\"]\n\n[[require]]\nname = \"dep\"\n\n\
         [[lean_lib]]\nname = \"App\"\n",
    );
    write("app/App.lean", "import Dep\n");
    write(
        "dep/lakefile.toml",
        "name = \"dep\"\ndefaultTargets = [\"Dep\"]\n\n[[lean_lib]]\nname = \"Dep\"\n",
    );
    write("dep/Dep.lean", "");
    write(
        "app/lake-manifest.json",
        r#"{"version": "1.2.0", "packagesDir": ".lake/packages",
            "packages": [{"type": "path", "name": "dep", "dir": "../dep",
                          "manifestFile": "lake-manifest.json", "inherited": false,
                          "configFile": "lakefile.toml"}]}"#,
    );
    let fake_toolchain = tmp.path().join("app/fake-toolchain");
    std::fs::create_dir_all(&fake_toolchain).unwrap();
    std::fs::write(fake_toolchain.join("Init.olean"), "").unwrap();
    tmp
}

#[test]
fn json_output_carries_path_dependency_package_and_module() {
    let tmp = setup_with_path_dependency();
    let app = tmp.path().join("app");
    let out = Command::cargo_bin("leanr")
        .unwrap()
        .current_dir(&app)
        .env("XDG_CACHE_HOME", tmp.path().join("xdg-cache"))
        .args(["build", "--dry-run", "--json"])
        .args([
            "--toolchain-dir",
            app.join("fake-toolchain").to_str().unwrap(),
        ])
        .assert()
        .success()
        .get_output()
        .stdout
        .clone();
    let v: serde_json::Value = serde_json::from_slice(&out).unwrap();

    let packages = v["packages"].as_array().unwrap();
    assert_eq!(packages.len(), 1);
    assert_eq!(packages[0]["name"], "dep");
    // Path-source packages carry no manifest rev.
    assert_eq!(packages[0]["rev"], serde_json::Value::Null);
    // Workspace-relative (from `app/`), forward slashes, `..`-form kept
    // as-is (not resolved) rather than leaked as an absolute path.
    assert_eq!(packages[0]["dir"], "../dep");

    let modules = v["modules"].as_array().unwrap();
    let dep_module = modules
        .iter()
        .find(|m| m["name"] == "Dep")
        .expect("Dep module present");
    assert_eq!(dep_module["package"], "dep");
    assert_eq!(dep_module["file"], "Dep.lean");
}
