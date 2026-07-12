//! Build execution (M2b spec §Architecture, component `job` + the
//! orchestration glue): one official `lean` process per module over the
//! pool, unconditional, fail-fast; artifacts into `setup::Layout`;
//! diagnostics from `--json` stdout rendered for humans. On job failure
//! the module's declared outputs are deleted so a failed build never
//! leaves partial artifacts a later run could trust.

use std::path::PathBuf;
use std::process::Command;
use std::sync::Mutex;
use std::time::Instant;

use crate::error::BuildError;
use crate::pool;
use crate::setup::{lean_path_env, module_setup, Layout};
use crate::subprocess::{self, RunError};
use crate::Workspace;

pub struct LeanInvoker {
    /// The lean executable (PATH-resolved name or explicit path).
    pub program: PathBuf,
    /// elan toolchain override (`+<toolchain>`), pinning workers to the
    /// root workspace's toolchain — same rule as bridge::LakeInvoker.
    pub toolchain: Option<String>,
}

impl Default for LeanInvoker {
    fn default() -> LeanInvoker {
        LeanInvoker {
            program: PathBuf::from("lean"),
            toolchain: None,
        }
    }
}

pub struct BuildOptions {
    pub jobs: usize,
    pub lean: LeanInvoker,
    /// `None` = `--no-cache` (M2b's pure unconditional path). `Some` =
    /// cache-aware; with `force`, always run `lean` then refresh the cache.
    pub cache: Option<crate::cache::Cache>,
    pub force: bool,
    pub fp_env: crate::fingerprint::FingerprintEnv,
}

pub struct BuiltEvent<'a> {
    pub module: &'a str,
    pub done: usize,
    pub total: usize,
    pub secs: f64,
    /// Rendered diagnostics (warnings) from a successful build; empty
    /// when lean was silent.
    pub diagnostics: &'a str,
    /// True when this module's artifacts came from the cache (no lean run).
    pub cached: bool,
}

#[derive(Debug)]
pub struct BuildReport {
    pub built: usize,
    pub cached: usize,
}

#[derive(serde::Deserialize)]
struct Diag {
    severity: Option<String>,
    pos: Option<DiagPos>,
    #[serde(rename = "fileName")]
    file_name: Option<String>,
    data: Option<serde_json::Value>,
}

#[derive(serde::Deserialize)]
struct DiagPos {
    line: u64,
    column: u64,
}

/// Render lean's `--json` stdout (one JSON object per line) for humans;
/// unparseable lines pass through verbatim (never panic on subprocess
/// output).
fn render_diagnostics(stdout: &str) -> String {
    let mut out = String::new();
    for line in stdout.lines().filter(|l| !l.trim().is_empty()) {
        match serde_json::from_str::<Diag>(line) {
            Ok(d) => {
                let sev = d.severity.unwrap_or_else(|| "info".into());
                let file = d.file_name.unwrap_or_default();
                let (l, c) = d.pos.map(|p| (p.line, p.column)).unwrap_or((0, 0));
                let msg = match d.data {
                    Some(serde_json::Value::String(s)) => s,
                    Some(v) => v.to_string(),
                    None => String::new(),
                };
                out.push_str(&format!("{file}:{l}:{c}: {sev}: {msg}\n"));
            }
            Err(_) => {
                out.push_str(line);
                out.push('\n');
            }
        }
    }
    out
}

pub fn build_workspace(
    ws: &Workspace,
    opts: &BuildOptions,
    on_built: &(dyn Fn(BuiltEvent<'_>) + Sync),
) -> Result<BuildReport, BuildError> {
    // Unsupported-feature guard (spec §Scope): error naming the package.
    for pkg in std::iter::once(&ws.root).chain(ws.deps.iter()) {
        if pkg.config.precompile_modules == Some(true) {
            return Err(BuildError::Unsupported {
                package: pkg.name.clone(),
                feature: "precompileModules".into(),
            });
        }
    }
    let layout = Layout::new(&ws.root_dir);
    // Write every setup file up front (pure planning, cheap, and any IO
    // error surfaces before a single worker spawns).
    for (i, m) in ws.graph.modules.iter().enumerate() {
        let sp = layout.setup_path(&m.package, &m.name);
        let dir = sp.parent().expect("setup path has a parent");
        std::fs::create_dir_all(dir).map_err(|e| BuildError::Io {
            path: dir.to_path_buf(),
            err: e.to_string(),
        })?;
        for art in layout.artifact_paths(&m.package, m) {
            let d = art.parent().expect("artifact path has a parent");
            std::fs::create_dir_all(d).map_err(|e| BuildError::Io {
                path: d.to_path_buf(),
                err: e.to_string(),
            })?;
        }
        let setup = module_setup(ws, &layout, crate::graph::ModuleId(i as u32));
        let text = serde_json::to_string(&setup).expect("setup serializes");
        std::fs::write(&sp, text).map_err(|e| BuildError::Io {
            path: sp.clone(),
            err: e.to_string(),
        })?;
    }
    let lean_path = lean_path_env(ws, &layout);
    let deps: Vec<Vec<usize>> = ws
        .graph
        .modules
        .iter()
        .map(|m| m.deps.iter().map(|d| d.0 as usize).collect())
        .collect();
    // Per-module (secs, rendered-diagnostics), filled by the job and
    // read by on_done (which the pool calls with counts).
    let results: Mutex<Vec<Option<(f64, String)>>> = Mutex::new(vec![None; ws.graph.modules.len()]);
    // Fingerprints computed once up front, only when caching is on
    // (--no-cache skips the fingerprint walk entirely).
    let fps = match &opts.cache {
        Some(_) => Some(crate::fingerprint::fingerprint_all(ws, &opts.fp_env)?),
        None => None,
    };
    #[derive(Clone, Copy, PartialEq)]
    enum Outcome {
        Built,
        Cached,
    }
    let outcomes: Mutex<Vec<Outcome>> = Mutex::new(vec![Outcome::Built; ws.graph.modules.len()]);
    let job = |i: usize| -> Result<(), String> {
        let m = &ws.graph.modules[i];
        let dests = layout.artifact_paths(&m.package, m);
        if let (Some(cache), Some(fps)) = (opts.cache.as_ref(), fps.as_ref()) {
            if !opts.force {
                match cache.lookup(&fps[i]) {
                    Ok(Some(manifest)) => {
                        if let Err(e) = cache.materialize(&manifest, &dests) {
                            return Err(format!("cache materialize failed: {e}"));
                        }
                        outcomes.lock().unwrap()[i] = Outcome::Cached;
                        results.lock().unwrap()[i] = Some((0.0, String::new()));
                        return Ok(());
                    }
                    Ok(None) => {} // miss — fall through to lean
                    Err(e) => return Err(format!("cache lookup failed: {e}")),
                }
            }
        }
        let start = Instant::now();
        let mut cmd = Command::new(&opts.lean.program);
        if let Some(tc) = &opts.lean.toolchain {
            cmd.arg(format!("+{tc}"));
        }
        cmd.arg(&m.file)
            .arg("-o")
            .arg(layout.olean_path(&m.package, &m.name))
            .arg("-i")
            .arg(layout.ilean_path(&m.package, &m.name))
            .arg("--setup")
            .arg(layout.setup_path(&m.package, &m.name))
            .arg("--json")
            .env("LEAN_PATH", &lean_path)
            .current_dir(&ws.root_dir);
        let cleanup = || {
            for p in layout.artifact_paths(&m.package, m) {
                let _ = std::fs::remove_file(p);
            }
        };
        match subprocess::run_drained(&mut cmd) {
            Ok(f) if f.status.success() => {
                let diags = render_diagnostics(&String::from_utf8_lossy(&f.stdout));
                results.lock().unwrap()[i] = Some((start.elapsed().as_secs_f64(), diags));
                if let (Some(cache), Some(fps)) = (opts.cache.as_ref(), fps.as_ref()) {
                    if let Err(e) = cache.insert(&fps[i], &dests) {
                        return Err(format!("cache insert failed: {e}"));
                    }
                }
                Ok(())
            }
            Ok(f) => {
                cleanup();
                let mut details = render_diagnostics(&String::from_utf8_lossy(&f.stdout));
                let stderr = String::from_utf8_lossy(&f.stderr);
                if !stderr.trim().is_empty() {
                    details.push_str(stderr.trim_end());
                    details.push('\n');
                }
                details.push_str(&format!("lean exited with {}", f.status));
                Err(details)
            }
            Err(RunError::Spawn(e)) => {
                cleanup();
                Err(format!(
                    "failed to start `{}` ({e}); install the pinned toolchain \
                     (`mise run elan:bootstrap`) or pass --lean",
                    opts.lean.program.display()
                ))
            }
            Err(RunError::TimedOut(_)) => unreachable!("run_drained has no timeout"),
            Err(RunError::Wait(e, _)) => {
                cleanup();
                Err(format!("wait failed: {e}"))
            }
        }
    };
    let on_done = |i: usize, done: usize, total: usize| {
        let m = &ws.graph.modules[i];
        let (secs, diags) = results.lock().unwrap()[i]
            .take()
            .unwrap_or((0.0, String::new()));
        let cached = outcomes.lock().unwrap()[i] == Outcome::Cached;
        let name = m.name.to_string();
        on_built(BuiltEvent {
            module: &name,
            done,
            total,
            secs,
            diagnostics: &diags,
            cached,
        });
    };
    pool::run(&deps, opts.jobs, &job, &on_done).map_err(|f| {
        let m = &ws.graph.modules[f.item];
        BuildError::ModuleBuild {
            module: m.name.to_string(),
            file: m.file.clone(),
            details: f.message,
        }
    })?;
    // A fail-fast abort returns Err above, so every module counted here
    // actually completed (built or cached) — no partial tally can surface.
    let outs = outcomes.into_inner().unwrap();
    Ok(BuildReport {
        built: outs.iter().filter(|o| **o == Outcome::Built).count(),
        cached: outs.iter().filter(|o| **o == Outcome::Cached).count(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::setup::Layout;
    use crate::testws;
    use std::path::Path;
    use std::sync::Mutex;

    // `FAKE_LEAN_FAIL_ON` is process-wide (std::env::set_var has no
    // per-thread scope), but cargo runs this module's tests concurrently
    // in the same process. `builds_every_module_in_dependency_order`
    // never touches the var itself yet is still vulnerable to inheriting
    // it from a sibling test's fake-lean children racing on another
    // thread. Serialize just the two tests that spawn fake-lean while the
    // var is live so neither can observe the other's setting; this is a
    // test-only fix, not a change to build_workspace's semantics.
    static ENV_GUARD: Mutex<()> = Mutex::new(());

    use crate::cache::Cache;
    use crate::fingerprint::FingerprintEnv;

    fn fake_lean() -> LeanInvoker {
        LeanInvoker {
            program: Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/fake-lean.sh"),
            toolchain: None,
        }
    }

    fn fp_env() -> FingerprintEnv {
        FingerprintEnv {
            leanr_version: "test".into(),
            toolchain_id: "test-tc".into(),
            platform: "test-plat".into(),
        }
    }

    fn opts(jobs: usize, cache: Option<Cache>, force: bool) -> BuildOptions {
        BuildOptions {
            jobs,
            lean: fake_lean(),
            cache,
            force,
            fp_env: fp_env(),
        }
    }

    #[test]
    fn cold_build_populates_then_warm_build_is_all_cached() {
        let _guard = ENV_GUARD.lock().unwrap_or_else(|e| e.into_inner());
        let t = testws::synthetic();
        let xdg = tempfile::TempDir::new().unwrap();
        let cold = build_workspace(
            &t.ws,
            &opts(1, Some(Cache::new(xdg.path())), false),
            &|_| {},
        )
        .unwrap();
        assert_eq!((cold.built, cold.cached), (2, 0));
        // Second build over the same cache: zero lean runs.
        let warm = build_workspace(
            &t.ws,
            &opts(1, Some(Cache::new(xdg.path())), false),
            &|_| {},
        )
        .unwrap();
        assert_eq!((warm.built, warm.cached), (0, 2));
    }

    #[test]
    fn force_reruns_lean_even_on_a_full_cache() {
        let _guard = ENV_GUARD.lock().unwrap_or_else(|e| e.into_inner());
        let t = testws::synthetic();
        let xdg = tempfile::TempDir::new().unwrap();
        build_workspace(
            &t.ws,
            &opts(1, Some(Cache::new(xdg.path())), false),
            &|_| {},
        )
        .unwrap();
        let forced =
            build_workspace(&t.ws, &opts(1, Some(Cache::new(xdg.path())), true), &|_| {}).unwrap();
        assert_eq!((forced.built, forced.cached), (2, 0));
    }

    #[test]
    fn no_cache_neither_reads_nor_writes() {
        let _guard = ENV_GUARD.lock().unwrap_or_else(|e| e.into_inner());
        let t = testws::synthetic();
        let xdg = tempfile::TempDir::new().unwrap();
        let r = build_workspace(&t.ws, &opts(1, None, false), &|_| {}).unwrap();
        assert_eq!((r.built, r.cached), (2, 0));
        // Cache dir stays empty.
        assert!(!Cache::new(xdg.path())
            .blob_path("00")
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .exists());
    }

    #[test]
    fn builds_every_module_in_dependency_order() {
        let _guard = ENV_GUARD.lock().unwrap_or_else(|e| e.into_inner());
        let t = testws::synthetic();
        let events: Mutex<Vec<String>> = Mutex::new(Vec::new());
        // Event ordering is only structural with jobs=1: the pool's on_done fires before
        // the worker loop observes the next ready module.
        let report = build_workspace(&t.ws, &opts(1, None, false), &|e: BuiltEvent<'_>| {
            events.lock().unwrap().push(e.module.to_string())
        })
        .unwrap();
        assert_eq!(report.built, 2);
        let layout = Layout::new(&t.ws.root_dir);
        for m in &t.ws.graph.modules {
            for p in layout.artifact_paths(&m.package, m) {
                assert!(p.is_file(), "missing artifact {}", p.display());
            }
        }
        let order = events.into_inner().unwrap();
        let pos = |x: &str| order.iter().position(|m| m == x).unwrap();
        assert!(pos("App.Sub") < pos("App"));
    }

    #[test]
    fn parallel_build_produces_every_artifact() {
        let _guard = ENV_GUARD.lock().unwrap_or_else(|e| e.into_inner());
        let t = testws::synthetic();
        let report = build_workspace(&t.ws, &opts(2, None, false), &|_| {}).unwrap();
        assert_eq!(report.built, 2);
        let layout = Layout::new(&t.ws.root_dir);
        for m in &t.ws.graph.modules {
            for p in layout.artifact_paths(&m.package, m) {
                assert!(p.is_file(), "missing artifact {}", p.display());
            }
        }
    }

    #[test]
    fn failing_module_reports_diagnostics_and_deletes_partial_outputs() {
        let _guard = ENV_GUARD.lock().unwrap_or_else(|e| e.into_inner());
        let t = testws::synthetic();
        std::env::set_var("FAKE_LEAN_FAIL_ON", "Sub.lean");
        let err = build_workspace(&t.ws, &opts(1, None, false), &|_| {}).unwrap_err();
        std::env::remove_var("FAKE_LEAN_FAIL_ON");
        let msg = err.to_string();
        assert!(msg.contains("App.Sub"), "names the module: {msg}");
        assert!(
            msg.contains("unknown identifier"),
            "carries the diagnostic: {msg}"
        );
        assert!(msg.contains(":3:7:"), "renders position: {msg}");
        let layout = Layout::new(&t.ws.root_dir);
        let sub = &t.ws.graph.modules[t
            .ws
            .graph
            .id_of(&crate::modules::ModuleName::parse("App.Sub").unwrap())
            .unwrap()
            .0 as usize];
        for p in layout.artifact_paths(&sub.package, sub) {
            assert!(!p.exists(), "partial output survived: {}", p.display());
        }
    }

    #[test]
    fn precompile_modules_is_a_clear_unsupported_error() {
        let mut t = testws::synthetic();
        t.ws.root.config.precompile_modules = Some(true);
        let err = build_workspace(&t.ws, &opts(1, None, false), &|_| {}).unwrap_err();
        assert!(err.to_string().contains("precompileModules"));
    }

    #[test]
    fn diagnostics_render_falls_back_to_raw_lines() {
        let out = render_diagnostics("not json at all\n");
        assert_eq!(out, "not json at all\n");
        let out = render_diagnostics(
            r#"{"severity":"warning","pos":{"line":1,"column":0},"fileName":"A.lean","data":"declaration uses sorry"}"#,
        );
        assert_eq!(out, "A.lean:1:0: warning: declaration uses sorry\n");
    }
}
