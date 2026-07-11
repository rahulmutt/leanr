//! End-to-end resolve() over a synthetic two-package workspace with a
//! real local git dependency — no lake, no network, no toolchain.

use std::path::{Path, PathBuf};

use leanr_build::bridge::LakeInvoker;
use leanr_build::{find_workspace_root, resolve, BuildError, ResolveOptions};

fn sh(dir: &Path, cmd: &str) {
    let out = std::process::Command::new("sh")
        .arg("-c")
        .arg(cmd)
        .current_dir(dir)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{cmd}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

fn write(dir: &Path, rel: &str, text: &str) {
    let p = dir.join(rel);
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(p, text).unwrap();
}

/// dep repo: lib `Dep`, one module. app: lib `App` importing Dep + a
/// toolchain module. Returns (tempdir, app_dir).
fn setup() -> (tempfile::TempDir, PathBuf) {
    let tmp = tempfile::TempDir::new().unwrap();

    let dep = tmp.path().join("dep-origin");
    std::fs::create_dir_all(&dep).unwrap();
    write(
        &dep,
        "lakefile.toml",
        "name = \"dep\"\ndefaultTargets = [\"Dep\"]\n\n[[lean_lib]]\nname = \"Dep\"\n",
    );
    write(&dep, "Dep.lean", "module\npublic import Init.Core\n");
    sh(
        &dep,
        "git init -q -b main && git add -A && git -c user.email=t@t -c user.name=t commit -qm dep",
    );
    let rev = {
        let out = std::process::Command::new("git")
            .args(["rev-parse", "HEAD"])
            .current_dir(&dep)
            .output()
            .unwrap();
        String::from_utf8(out.stdout).unwrap().trim().to_string()
    };

    let app = tmp.path().join("app");
    std::fs::create_dir_all(&app).unwrap();
    write(&app, "lakefile.toml", "name = \"app\"\ndefaultTargets = [\"App\"]\n\n[[require]]\nname = \"dep\"\n\n[[lean_lib]]\nname = \"App\"\n");
    write(&app, "App.lean", "import App.Sub\nimport Dep\n");
    write(&app, "App/Sub.lean", "import Init.Core\n");
    write(
        &app,
        "lake-manifest.json",
        &format!(
            r#"{{"version": "1.2.0", "packagesDir": ".lake/packages",
                "packages": [{{"type": "git", "name": "dep", "url": "{}",
                               "rev": "{rev}", "manifestFile": "lake-manifest.json",
                               "inherited": false, "configFile": "lakefile.toml"}}]}}"#,
            dep.display()
        ),
    );
    (tmp, app)
}

/// Fake toolchain: a dir containing Init.olean and Init/Core.olean — a
/// real toolchain always ships the former (every non-prelude module
/// implicitly imports it; see `graph::add_implicit_init`), not just
/// submodules under it.
fn fake_toolchain(tmp: &Path) -> PathBuf {
    let dir = tmp.join("toolchain-lib");
    std::fs::create_dir_all(dir.join("Init")).unwrap();
    std::fs::write(dir.join("Init.olean"), "").unwrap();
    std::fs::write(dir.join("Init/Core.olean"), "").unwrap();
    dir
}

fn opts(tmp: &Path) -> ResolveOptions {
    ResolveOptions {
        targets: Vec::new(), // defaultTargets
        lake: LakeInvoker {
            program: PathBuf::from("/no/lake/needed"),
            ..LakeInvoker::default()
        },
        toolchain_olean_dir: fake_toolchain(tmp),
    }
}

/// Same as `setup()`, but the dep's lakefile lives in a subdirectory of
/// the git repo (`subDir` in the manifest) — exercises the
/// `base.join(sub_dir)` composition in `resolve()`'s dependency-config
/// step (Finding 1) end-to-end with a real local git repo, not just the
/// manifest-parser unit tests.
fn setup_with_sub_dir() -> (tempfile::TempDir, PathBuf) {
    let tmp = tempfile::TempDir::new().unwrap();

    let dep = tmp.path().join("dep-origin");
    std::fs::create_dir_all(&dep).unwrap();
    write(
        &dep,
        "sub/lakefile.toml",
        "name = \"dep\"\ndefaultTargets = [\"Dep\"]\n\n[[lean_lib]]\nname = \"Dep\"\n",
    );
    write(&dep, "sub/Dep.lean", "module\npublic import Init.Core\n");
    sh(
        &dep,
        "git init -q -b main && git add -A && git -c user.email=t@t -c user.name=t commit -qm dep",
    );
    let rev = {
        let out = std::process::Command::new("git")
            .args(["rev-parse", "HEAD"])
            .current_dir(&dep)
            .output()
            .unwrap();
        String::from_utf8(out.stdout).unwrap().trim().to_string()
    };

    let app = tmp.path().join("app");
    std::fs::create_dir_all(&app).unwrap();
    write(&app, "lakefile.toml", "name = \"app\"\ndefaultTargets = [\"App\"]\n\n[[require]]\nname = \"dep\"\n\n[[lean_lib]]\nname = \"App\"\n");
    write(&app, "App.lean", "import Dep\n");
    write(
        &app,
        "lake-manifest.json",
        &format!(
            r#"{{"version": "1.2.0", "packagesDir": ".lake/packages",
                "packages": [{{"type": "git", "name": "dep", "url": "{}",
                               "rev": "{rev}", "subDir": "sub", "manifestFile": "lake-manifest.json",
                               "inherited": false, "configFile": "lakefile.toml"}}]}}"#,
            dep.display()
        ),
    );
    (tmp, app)
}

#[test]
fn legitimate_sub_dir_resolves_end_to_end() {
    let (tmp, app) = setup_with_sub_dir();
    let ws = resolve(&app, &opts(tmp.path())).unwrap();

    assert_eq!(ws.deps.len(), 1);
    assert_eq!(ws.deps[0].name, "dep");
    assert!(ws.deps[0].dir.ends_with("sub"));
    // Materialized the whole repo, then resolved the config from the
    // subDir within it.
    assert!(app.join(".lake/packages/dep/sub/Dep.lean").is_file());
    assert!(ws.warnings.is_empty());

    let names: Vec<Vec<String>> = ws
        .waves
        .iter()
        .map(|w| {
            w.iter()
                .map(|id| ws.graph.modules[id.0 as usize].name.to_string())
                .collect()
        })
        .collect();
    assert_eq!(names, [vec!["Dep".to_string()], vec!["App".to_string()]]);
}

#[test]
fn resolves_a_fresh_workspace_end_to_end() {
    let (tmp, app) = setup();
    let ws = resolve(&app, &opts(tmp.path())).unwrap();

    assert_eq!(ws.root.config.name, "app");
    assert_eq!(ws.deps.len(), 1);
    assert_eq!(ws.deps[0].name, "dep");
    assert!(ws.deps[0].rev.is_some());
    assert!(app.join(".lake/packages/dep/Dep.lean").is_file()); // materialized

    let names: Vec<Vec<String>> = ws
        .waves
        .iter()
        .map(|w| {
            w.iter()
                .map(|id| ws.graph.modules[id.0 as usize].name.to_string())
                .collect()
        })
        .collect();
    assert_eq!(
        names,
        [
            vec!["App.Sub".to_string(), "Dep".to_string()],
            vec!["App".to_string()]
        ]
    );
    assert!(ws.warnings.is_empty());
}

#[test]
fn second_resolve_is_idempotent() {
    let (tmp, app) = setup();
    let o = opts(tmp.path());
    let w1 = resolve(&app, &o).unwrap();
    let w2 = resolve(&app, &o).unwrap();
    assert_eq!(w1.graph.modules.len(), w2.graph.modules.len());
}

#[test]
fn explicit_target_and_unknown_target() {
    let (tmp, app) = setup();
    let mut o = opts(tmp.path());
    o.targets = vec!["App".into()];
    assert!(resolve(&app, &o).is_ok());
    o.targets = vec!["Nope".into()];
    match resolve(&app, &o) {
        Err(BuildError::UnknownTarget(t)) => assert_eq!(t, "Nope"),
        other => panic!("expected UnknownTarget, got {other:?}"),
    }
}

#[test]
fn missing_manifest_says_run_lake_update() {
    let (tmp, app) = setup();
    std::fs::remove_file(app.join("lake-manifest.json")).unwrap();
    let err = resolve(&app, &opts(tmp.path())).unwrap_err();
    assert!(err.to_string().contains("lake update"));
}

#[test]
fn stale_manifest_names_the_missing_require() {
    let (tmp, app) = setup();
    // Add a require with no manifest entry.
    let lf = app.join("lakefile.toml");
    let mut text = std::fs::read_to_string(&lf).unwrap();
    text.push_str("\n[[require]]\nname = \"ghost\"\n");
    std::fs::write(&lf, text).unwrap();
    let err = resolve(&app, &opts(tmp.path())).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("ghost") && msg.contains("lake update"),
        "got: {msg}"
    );
}

#[test]
fn find_root_walks_up_and_prefers_toml() {
    let (_tmp, app) = setup();
    let nested = app.join("App");
    assert_eq!(find_workspace_root(&nested).unwrap(), app);
    let err = find_workspace_root(Path::new("/")).unwrap_err();
    assert!(matches!(err, BuildError::NoWorkspaceRoot(_)));
}
