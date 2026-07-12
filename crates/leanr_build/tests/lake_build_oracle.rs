//! Differential probe-project oracle (M2b spec §Testing): each fixture
//! project is built by pinned official lake AND by leanr; every artifact
//! in the family is byte-diffed. Local tier: needs the elan toolchain
//! (`mise run build:differential`), hence #[ignore].

use std::path::{Path, PathBuf};
use std::process::Command;

use leanr_build::compile::{build_workspace, BuildOptions, LeanInvoker};
use leanr_build::setup::Layout;
use leanr_build::{resolve, ResolveOptions, Workspace};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}

fn write(root: &Path, rel: &str, text: &str) {
    let p = root.join(rel);
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(p, text).unwrap();
}

/// A probe project skeleton with the repo's pinned lean-toolchain.
fn probe(files: &[(&str, &str)]) -> tempfile::TempDir {
    let tmp = tempfile::TempDir::new().unwrap();
    std::fs::copy(
        repo_root().join("lean-toolchain"),
        tmp.path().join("lean-toolchain"),
    )
    .unwrap();
    for (rel, text) in files {
        write(tmp.path(), rel, text);
    }
    tmp
}

fn run_lake_build(root: &Path) {
    let out = Command::new("lake")
        .arg("build")
        .current_dir(root)
        .output()
        .expect("lake on PATH (elan)");
    assert!(
        out.status.success(),
        "lake build failed:\n{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

fn lean_print_libdir() -> PathBuf {
    let out = Command::new("lean").arg("--print-libdir").output().unwrap();
    assert!(out.status.success());
    PathBuf::from(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

fn run_leanr_build(root: &Path) -> (Workspace, Layout) {
    let toolchain = std::fs::read_to_string(root.join("lean-toolchain"))
        .ok()
        .map(|s| s.trim().to_string());
    let opts = ResolveOptions {
        targets: vec![],
        lake: leanr_build::bridge::LakeInvoker {
            toolchain: toolchain.clone(),
            ..Default::default()
        },
        toolchain_olean_dir: lean_print_libdir(),
        cache_root: root.join("xdg-cache"), // isolated per probe
    };
    let ws = resolve(root, &opts).unwrap();
    build_workspace(
        &ws,
        &BuildOptions {
            jobs: 4,
            lean: LeanInvoker {
                program: "lean".into(),
                toolchain,
            },
            cache: None,
            force: false,
            fp_env: leanr_build::fingerprint::FingerprintEnv {
                leanr_version: "test".into(),
                toolchain_id: "test-tc".into(),
                platform: "test-plat".into(),
            },
        },
        &|_| {},
    )
    .unwrap();
    let layout = Layout::new(&ws.root_dir);
    (ws, layout)
}

/// Build the same sources with lake (one checkout) and leanr (a sibling
/// checkout), then byte-diff every planned module's artifact family.
fn diff_probe(files: &[(&str, &str)]) {
    let lake_side = probe(files);
    run_lake_build(lake_side.path());
    let leanr_side = probe(files);
    let (ws, layout) = run_leanr_build(leanr_side.path());
    // Compare leanr's artifacts against the lake build of the *same*
    // sources in the sibling checkout.
    for m in &ws.graph.modules {
        let lake_lib = if m.package == ws.root.name {
            lake_side.path().join(".lake/build/lib/lean")
        } else {
            lake_side
                .path()
                .join(".lake/packages")
                .join(&m.package)
                .join(".lake/build/lib/lean")
        };
        let ours_lib = layout.lib_dir(&m.package);
        for ours in layout.artifact_paths(&m.package, m) {
            let rel = ours.strip_prefix(&ours_lib).unwrap();
            let theirs = lake_lib.join(rel);
            let a = std::fs::read(&ours)
                .unwrap_or_else(|e| panic!("missing leanr artifact {}: {e}", ours.display()));
            let b = std::fs::read(&theirs)
                .unwrap_or_else(|e| panic!("missing lake artifact {}: {e}", theirs.display()));
            assert!(a == b, "mismatch for {} at {}", m.name, rel.display());
        }
    }
}

const BASIC_LAKEFILE: &str =
    "name = \"probe\"\ndefaultTargets = [\"Probe\"]\n\n[[lean_lib]]\nname = \"Probe\"\n";

#[test]
#[ignore]
fn plain_modules_build_byte_identically() {
    diff_probe(&[
        ("lakefile.toml", BASIC_LAKEFILE),
        (
            "lake-manifest.json",
            r#"{"version": "1.2.0", "packages": []}"#,
        ),
        (
            "Probe.lean",
            "import Probe.Basic\ndef two := Probe.one + 1\n",
        ),
        (
            "Probe/Basic.lean",
            "namespace Probe\ndef one := 1\nend Probe\n",
        ),
    ]);
}

#[test]
#[ignore]
fn prelude_module_builds_byte_identically() {
    // Fixture note: `prelude` suppresses the implicit `import Init`, so
    // there is no `Nat` (or anything else from the stdlib) to lean on —
    // verified empirically (matches crates/leanr_olean/tests/fixtures/
    // Prelude0.lean's header comment). The probe must declare its own
    // self-contained inductive rather than reference `Nat`.
    diff_probe(&[
        ("lakefile.toml", BASIC_LAKEFILE),
        (
            "lake-manifest.json",
            r#"{"version": "1.2.0", "packages": []}"#,
        ),
        (
            "Probe.lean",
            "prelude\n\ninductive N where\n  | zero : N\n  | succ : N → N\n\n\
             def probeAxiomFree (n : N) : N := n\n",
        ),
    ]);
}

#[test]
#[ignore]
fn lean_options_flow_into_the_build() {
    // Fixture note: a *quoted* dotted key (`"pp.unicode.fun" = true`)
    // parses as a single TOML key whose one string component contains
    // dots; lake's config translation turns that into a single-atom Lean
    // `Name` printed with guillemets (`«pp.unicode.fun»`), which the
    // pinned lean then rejects as an unknown option ("invalid -D
    // parameter, unknown configuration option '«pp.unicode.fun»'" — a
    // real `lake build` failure, verified empirically, not a leanr/lake
    // divergence). An *unquoted* dotted key defines nested TOML tables
    // (`pp.unicode.fun = true` -> `pp = { unicode = { fun = true } }`),
    // which both real lake and leanr's own flatten_toml_value (see
    // crates/leanr_build/src/config.rs) fold into the intended
    // hierarchical option name — this is the form real Mathlib's
    // lakefile uses (tests/fixtures/mathlib-lakefile-golden.toml).
    diff_probe(&[
        (
            "lakefile.toml",
            "name = \"probe\"\ndefaultTargets = [\"Probe\"]\n\n[[lean_lib]]\nname = \"Probe\"\n\
             leanOptions = {autoImplicit = false, pp.unicode.fun = true}\n",
        ),
        (
            "lake-manifest.json",
            r#"{"version": "1.2.0", "packages": []}"#,
        ),
        ("Probe.lean", "theorem t (n : Nat) : n = n := rfl\n"),
    ]);
}

#[test]
#[ignore]
fn module_system_artifact_family_matches() {
    diff_probe(&[
        ("lakefile.toml", BASIC_LAKEFILE),
        (
            "lake-manifest.json",
            r#"{"version": "1.2.0", "packages": []}"#,
        ),
        ("Probe.lean", "module\n\ndef x := 1\n"),
    ]);
}

#[test]
#[ignore]
fn git_dependency_builds_byte_identically() {
    // Local origin repo for the dep: no network.
    let dep_origin = tempfile::TempDir::new().unwrap();
    write(
        dep_origin.path(),
        "lakefile.toml",
        "name = \"dep\"\ndefaultTargets = [\"Dep\"]\n\n[[lean_lib]]\nname = \"Dep\"\n",
    );
    write(dep_origin.path(), "Dep.lean", "def Dep.answer := 42\n");
    write(
        dep_origin.path(),
        "lake-manifest.json",
        r#"{"version": "1.2.0", "packages": []}"#,
    );
    std::fs::copy(
        repo_root().join("lean-toolchain"),
        dep_origin.path().join("lean-toolchain"),
    )
    .unwrap();
    let sh = |cmd: &str| {
        let out = Command::new("sh")
            .arg("-c")
            .arg(cmd)
            .current_dir(dep_origin.path())
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8(out.stdout).unwrap().trim().to_string()
    };
    sh("git init -q -b main && git add -A && git -c user.email=t@t -c user.name=t commit -q -m dep");
    let rev = sh("git rev-parse HEAD");
    let url = dep_origin.path().to_str().unwrap();
    let manifest = format!(
        r#"{{"version": "1.2.0", "packages": [{{"type": "git", "url": "{url}", "rev": "{rev}",
            "name": "dep", "manifestFile": "lake-manifest.json", "inherited": false,
            "configFile": "lakefile.toml", "inputRev": "main", "subDir": null, "scope": ""}}]}}"#
    );
    let root_lakefile =
        "name = \"probe\"\ndefaultTargets = [\"Probe\"]\n\n[[require]]\nname = \"dep\"\n\
         git = \"URL\"\nrev = \"main\"\n\n[[lean_lib]]\nname = \"Probe\"\n"
            .replace("URL", url);
    diff_probe(&[
        ("lakefile.toml", root_lakefile.as_str()),
        ("lake-manifest.json", manifest.as_str()),
        (
            "Probe.lean",
            "import Dep\ndef fortyThree := Dep.answer + 1\n",
        ),
    ]);
}
