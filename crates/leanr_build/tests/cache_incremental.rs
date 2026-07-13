//! M2c staleness-correctness gate (spec §Staleness-correctness harness):
//! perturb one input axis at a time and assert the EXACT rebuild set.
//! Under-invalidation (a changed input that fails to rebuild a dependent)
//! is release-blocking; over-invalidation (an unrelated module rebuilds)
//! is a fingerprint-scope regression. Uses a counting fake `lean` — no
//! toolchain needed.
//!
//! Fixture: a three-module workspace, `Root`, `Root.A`, `Root.B`, all in
//! one lib ("Root"), where `Root` imports both `Root.A` and `Root.B`.
//! `Root.A`/`Root.B` are pulled into the same lib by
//! `ModuleResolver::resolve`'s longest-root-prefix match (graph.rs), not
//! by the lib's glob, so a `leanOptions` toggle on the lib applies to all
//! three (setup.rs's `module_options` overlays the *owning lib's*
//! `lean_options` onto every module it owns).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use leanr_build::bridge::LakeInvoker;
use leanr_build::cache::Cache;
use leanr_build::compile::{BuildOptions, BuildReport, LeanInvoker};
use leanr_build::fingerprint::FingerprintEnv;
use leanr_build::modules::ModuleName;
use leanr_build::{resolve, ResolveOptions, Workspace};

fn counting_lean() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/counting-lean.sh")
}

fn write(dir: &Path, rel: &str, text: &str) {
    let p = dir.join(rel);
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(p, text).unwrap();
}

fn resolve_opts(dir: &Path) -> ResolveOptions {
    ResolveOptions {
        targets: Vec::new(), // defaultTargets = ["Root"]
        lake: LakeInvoker::default(),
        toolchain_olean_dir: dir.join("fake-toolchain"),
        cache_root: dir.join("resolve-cache"),
    }
}

/// Build the fixture workspace at `dir`: `Root` imports `Root.A` and
/// `Root.B`, all three owned by lib "Root" (root's default glob covers
/// only `Root` itself; `Root.A`/`Root.B` enter the graph — and the lib —
/// via import resolution, exactly like `App`/`App.Sub` in testws.rs).
fn fixture(dir: &Path) -> Workspace {
    write(
        dir,
        "lakefile.toml",
        "name = \"app\"\ndefaultTargets = [\"Root\"]\n\n[[lean_lib]]\nname = \"Root\"\n",
    );
    write(dir, "Root.lean", "import Root.A\nimport Root.B\n");
    write(dir, "Root/A.lean", "-- leaf A\ndef a := 1\n");
    write(dir, "Root/B.lean", "-- leaf B\ndef b := 2\n");
    write(
        dir,
        "lake-manifest.json",
        r#"{"version": "1.2.0", "packages": []}"#,
    );
    // Fake toolchain: a real toolchain always ships Init.olean, implicitly
    // imported by every non-prelude module (leanr_build::graph::add_implicit_init).
    let fake_toolchain = dir.join("fake-toolchain");
    std::fs::create_dir_all(&fake_toolchain).unwrap();
    std::fs::write(fake_toolchain.join("Init.olean"), "").unwrap();

    resolve(dir, &resolve_opts(dir)).unwrap()
}

fn fp_env() -> FingerprintEnv {
    FingerprintEnv {
        leanr_version: "test".into(),
        toolchain_id: "test-tc".into(),
        platform: "test-plat".into(),
    }
}

// `COUNTING_LEAN_LOG` is a process-wide env var (std::env::set_var has no
// per-thread scope), but cargo runs this file's #[test]s concurrently in
// the same process. Guard the set/build/unset sequence so no two builds
// in flight at once can observe each other's log path (same fix as
// compile.rs's ENV_GUARD for FAKE_LEAN_FAIL_ON).
static ENV_GUARD: Mutex<()> = Mutex::new(());

fn build_counting_with_env(
    ws: &Workspace,
    xdg: &Path,
    log: &Path,
    env: &FingerprintEnv,
) -> BuildReport {
    let _guard = ENV_GUARD.lock().unwrap_or_else(|e| e.into_inner());
    std::env::set_var("COUNTING_LEAN_LOG", log);
    let opts = BuildOptions {
        jobs: 2,
        lean: LeanInvoker {
            program: counting_lean(),
            toolchain: None,
        },
        cache: Some(Cache::new(xdg)),
        force: false,
        fp_env: FingerprintEnv {
            leanr_version: env.leanr_version.clone(),
            toolchain_id: env.toolchain_id.clone(),
            platform: env.platform.clone(),
        },
        remote: None,
    };
    let report = leanr_build::compile::build_workspace(ws, &opts, &|_| {}).unwrap();
    std::env::remove_var("COUNTING_LEAN_LOG");
    report
}

fn build_counting(ws: &Workspace, xdg: &Path, log: &Path) -> BuildReport {
    build_counting_with_env(ws, xdg, log, &fp_env())
}

fn invocations(log: &Path) -> Vec<String> {
    std::fs::read_to_string(log)
        .unwrap_or_default()
        .lines()
        .map(|s| s.to_string())
        .collect()
}

fn invocation_set(log: &Path) -> BTreeSet<String> {
    invocations(log).into_iter().collect()
}

fn module_file(ws: &Workspace, name: &str) -> String {
    let id = ws
        .graph
        .id_of(&ModuleName::parse(name).unwrap())
        .unwrap_or_else(|| panic!("module {name} not in graph"));
    ws.graph.modules[id.0 as usize].file.display().to_string()
}

fn all_module_files(ws: &Workspace) -> BTreeSet<String> {
    ws.graph
        .modules
        .iter()
        .map(|m| m.file.display().to_string())
        .collect()
}

#[test]
fn warm_build_runs_zero_lean() {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = tmp.path().join("ws");
    std::fs::create_dir_all(&dir).unwrap();
    let ws = fixture(&dir);
    let xdg = tmp.path().join("xdg-cache");

    let log1 = tmp.path().join("cold.log");
    let cold = build_counting(&ws, &xdg, &log1);
    assert_eq!(cold.built, 3, "cold build compiles all three modules");
    assert_eq!(cold.cached, 0);
    assert_eq!(
        invocation_set(&log1),
        all_module_files(&ws),
        "cold build must invoke lean on exactly the three modules"
    );

    // Second build over the SAME xdg cache: zero lean invocations.
    let log2 = tmp.path().join("warm.log");
    let warm = build_counting(&ws, &xdg, &log2);
    assert!(
        invocations(&log2).is_empty(),
        "warm build ran lean, expected zero invocations: {:?}",
        invocations(&log2)
    );
    assert_eq!(warm.built, 0);
    assert_eq!(warm.cached, 3);
}

#[test]
fn editing_a_leaf_rebuilds_only_its_cone() {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = tmp.path().join("ws");
    std::fs::create_dir_all(&dir).unwrap();
    let ws = fixture(&dir);
    let xdg = tmp.path().join("xdg-cache");

    let log1 = tmp.path().join("cold.log");
    build_counting(&ws, &xdg, &log1);

    // Edit the leaf Root/A.lean's *contents* — counting-lean.sh's bytes
    // are derived from source contents, so this genuinely changes A's
    // fingerprint, which (via Merkle recursion over import fingerprints,
    // fingerprint.rs's `fingerprint_all`) must change Root's fingerprint
    // too, since Root imports Root.A.
    let a_path = ws.graph.modules[ws
        .graph
        .id_of(&ModuleName::parse("Root.A").unwrap())
        .unwrap()
        .0 as usize]
        .file
        .clone();
    std::fs::write(&a_path, "-- leaf A, edited\ndef a := 2\n").unwrap();

    // Fresh log for the second phase.
    let log2 = tmp.path().join("edit.log");
    build_counting(&ws, &xdg, &log2);

    let got = invocation_set(&log2);
    let expected: BTreeSet<String> = [module_file(&ws, "Root.A"), module_file(&ws, "Root")]
        .into_iter()
        .collect();
    // EXACT-SET equality: both Root/A.lean (the edited leaf) and
    // Root.lean (its dependent) must be present, and Root/B.lean (an
    // unrelated sibling import of Root) must be ABSENT. A subset check
    // ("contains A") would miss under-invalidation of Root; a count
    // check ("len == 2") would miss over-invalidation of Root/B.
    assert_eq!(
        got, expected,
        "editing Root/A.lean must rebuild exactly {{Root/A.lean, Root.lean}}, got {got:?}"
    );
}

#[test]
fn toggling_a_lean_option_rebuilds_that_libs_modules() {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = tmp.path().join("ws");
    std::fs::create_dir_all(&dir).unwrap();
    let ws = fixture(&dir);
    let xdg = tmp.path().join("xdg-cache");

    let log1 = tmp.path().join("cold.log");
    build_counting(&ws, &xdg, &log1);

    // Add a leanOption to the lib. setup.rs's `module_options` overlays
    // the *owning lib's* leanOptions onto every module the lib owns
    // (Root, Root.A, Root.B all have `m.lib == "Root"`), so this must
    // change all three modules' fingerprints (fingerprint.rs's
    // `setup_inputs_bytes` hashes `options` into the module key).
    let lakefile = dir.join("lakefile.toml");
    let mut text = std::fs::read_to_string(&lakefile).unwrap();
    text.push_str("leanOptions = {autoImplicit = false}\n");
    std::fs::write(&lakefile, text).unwrap();
    let ws2 = resolve(&dir, &resolve_opts(&dir)).unwrap();

    let log2 = tmp.path().join("toggle.log");
    build_counting(&ws2, &xdg, &log2);

    assert_eq!(
        invocation_set(&log2),
        all_module_files(&ws2),
        "toggling a leanOption on the lib must rebuild every module the lib owns"
    );
}

#[test]
fn deep_verify_is_clean_after_build_and_flags_a_tampered_blob() {
    let _guard = ENV_GUARD.lock().unwrap_or_else(|e| e.into_inner());
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = tmp.path().join("ws");
    std::fs::create_dir_all(&dir).unwrap();
    let ws = fixture(&dir);
    let xdg = tmp.path().join("xdg-cache");
    let cache = Cache::new(&xdg);
    let env = fp_env();
    let invoker = LeanInvoker {
        program: counting_lean(),
        toolchain: None,
    };

    // 1. Build the fixture into a project + cache (counting-lean writes
    //    source-derived bytes, so the rebuild below reproduces exactly
    //    the bytes that were cached).
    let log1 = tmp.path().join("cold.log");
    std::env::set_var("COUNTING_LEAN_LOG", &log1);
    let opts = BuildOptions {
        jobs: 2,
        lean: LeanInvoker {
            program: counting_lean(),
            toolchain: None,
        },
        cache: Some(Cache::new(&xdg)),
        force: false,
        fp_env: FingerprintEnv {
            leanr_version: env.leanr_version.clone(),
            toolchain_id: env.toolchain_id.clone(),
            platform: env.platform.clone(),
        },
        remote: None,
    };
    leanr_build::compile::build_workspace(&ws, &opts, &|_| {}).unwrap();
    std::env::remove_var("COUNTING_LEAN_LOG");

    // 2. deep_verify against the SAME counting-lean invoker → clean.
    let log2 = tmp.path().join("verify-clean.log");
    std::env::set_var("COUNTING_LEAN_LOG", &log2);
    let report = cache.deep_verify(&ws, &env, &invoker, 2).unwrap();
    std::env::remove_var("COUNTING_LEAN_LOG");
    assert_eq!(report.checked, ws.graph.modules.len());
    assert!(
        report.mismatches.is_empty(),
        "expected a clean deep_verify, got mismatches: {:?}",
        report.mismatches
    );

    // 3. Tamper one cached blob (Root.A's olean) — make it writable, then
    //    rewrite its bytes.
    let fps = leanr_build::fingerprint::fingerprint_all(&ws, &env).unwrap();
    let a_id = ws
        .graph
        .id_of(&ModuleName::parse("Root.A").unwrap())
        .unwrap();
    let manifest = cache.lookup(&fps[a_id.0 as usize]).unwrap().unwrap();
    let blob_path = cache.blob_path(&manifest.artifacts[0].blob);
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&blob_path, std::fs::Permissions::from_mode(0o644)).unwrap();
    std::fs::write(&blob_path, b"TAMPERED").unwrap();

    let log3 = tmp.path().join("verify-tampered.log");
    std::env::set_var("COUNTING_LEAN_LOG", &log3);
    let report2 = cache.deep_verify(&ws, &env, &invoker, 2).unwrap();
    std::env::remove_var("COUNTING_LEAN_LOG");
    assert!(
        report2.mismatches.iter().any(|m| m.starts_with("Root.A:")),
        "expected Root.A to be flagged, got: {:?}",
        report2.mismatches
    );
}

#[test]
fn changing_the_env_rebuilds_everything() {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = tmp.path().join("ws");
    std::fs::create_dir_all(&dir).unwrap();
    let ws = fixture(&dir);
    let xdg = tmp.path().join("xdg-cache");

    let log1 = tmp.path().join("cold.log");
    build_counting(&ws, &xdg, &log1);

    // Same xdg cache, but a different FingerprintEnv.toolchain_id: this
    // is a whole-cache invalidation axis (env is folded into every
    // module's fingerprint, fingerprint.rs's `hash_module`), not scoped
    // to any one module.
    let mut env2 = fp_env();
    env2.toolchain_id = "other-toolchain".into();
    let log2 = tmp.path().join("env-changed.log");
    build_counting_with_env(&ws, &xdg, &log2, &env2);

    assert_eq!(
        invocation_set(&log2),
        all_module_files(&ws),
        "changing FingerprintEnv.toolchain_id must invalidate the whole cache"
    );
}
