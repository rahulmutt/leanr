# M2b Build Orchestrator Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bare `leanr build` compiles every planned module of a fresh clone by driving pinned official `lean` processes in parallel over M2a's module DAG, unconditionally, into leanr's own layout.

**Architecture:** Three new units inside `leanr_build`: `setup` (pure per-module invocation planning: artifact paths under `.leanr/build/`, the `--setup` JSON, `LEAN_PATH`), `pool` (index-based dependency-counter scheduler, fail-fast), `compile` (spawns one `lean` per module, parses `--json` diagnostics). Dependency sources move from `.lake/packages/` to an immutable, flock-guarded per-user XDG cache; the bridge cache moves to XDG too. Spec: `docs/superpowers/specs/2026-07-12-m2b-build-orchestrator-design.md`.

**Tech Stack:** Rust (std threads, `Mutex`+`Condvar`), `serde_json` (setup files, diagnostics), `libc` (flock), `git`/`lean` as subprocesses. **Zero new cargo dependencies.**

## Global Constraints

- No new cargo dependencies anywhere (spec §Architecture).
- `leanr_build` depends on no workspace crate (dev-dependencies excepted); `leanr_kernel` untouched.
- All CLI logic stays thin: `leanr_cli` parses arguments and prints; behavior lives in `leanr_build`.
- Env reads (`XDG_CACHE_HOME`, `HOME`) happen in `leanr_cli` only, matching the `discover_roots` convention (`crates/leanr_cli/src/main.rs:155-157`); `leanr_build` receives paths as inputs.
- Every error names the file/package it came from and the action that fixes it.
- No panics on untrusted input; subprocesses get explicit argv vectors, no shell.
- Unix-only `flock` with a documented `cfg(not(unix))` fallback, matching the existing process-group cfg split in `subprocess.rs`.
- Before each commit: `mise run lint && cargo test --workspace`. Conventional-commit prefixes (`feat(build):`, `fix(cli):`, `docs:`, `test(build):`).
- The pinned toolchain is `leanprover/lean4:v4.32.0-rc1` (`lean-toolchain`); the Mathlib pin is line 3 of `mathlib-pin`. Never bump either.

## File Structure

- `crates/leanr_build/src/cache_dir.rs` (new) — pure XDG cache-root resolution.
- `crates/leanr_build/src/fetch.rs` — rewritten materialization: `<cache>/src/<name>/<rev>/`, immutable, flock-guarded.
- `crates/leanr_build/src/lib.rs` — `ResolveOptions.cache_root`; dep dirs from the src cache; bridge cache under the cache root.
- `crates/leanr_build/src/graph.rs` — `LibUnit.lib` + `ModuleInfo.lib` (lib attribution for `leanOptions`).
- `crates/leanr_build/src/setup.rs` (new) — `Layout`, `SetupFile`, artifact paths, `LEAN_PATH`.
- `crates/leanr_build/src/pool.rs` (new) — generic dependency-counter scheduler over indices.
- `crates/leanr_build/src/compile.rs` (new) — `LeanInvoker`, `build_workspace`, diagnostics rendering.
- `crates/leanr_build/src/subprocess.rs` — add `run_drained` (no timeout, no process-group detach).
- `crates/leanr_build/src/error.rs` — `Unsupported`, `ModuleBuild` variants.
- `crates/leanr_build/src/testws.rs` (new, `#[cfg(test)]`) — shared synthetic-workspace test helper.
- `crates/leanr_build/tests/fixtures/fake-lean.sh` (new) — fake `lean` for unit tests.
- `crates/leanr_build/tests/lake_build_oracle.rs` (new) — differential probe-project oracle (`#[ignore]`).
- `crates/leanr_cli/src/main.rs` — bare `build`, `--jobs`/`--lean`, revised JSON plan, progress output.
- `crates/leanr_cli/tests/build_cli.rs` — updated + bare-build integration test.
- `mise.toml`, `scripts/build-fresh-acceptance.sh`, `ARCHITECTURE.md`, `docs/THREAT_MODEL.md`, the M2b spec (acceptance results).

---

### Task 1: XDG cache root, threaded through `ResolveOptions`; bridge cache moves there

**Files:**
- Create: `crates/leanr_build/src/cache_dir.rs`
- Modify: `crates/leanr_build/src/lib.rs` (module decl, `ResolveOptions`, `resolve()` bridge-cache path)
- Modify: `crates/leanr_cli/src/main.rs` (compute cache root from env, pass it)
- Modify: `crates/leanr_cli/tests/build_cli.rs` (isolate tests from the user's real cache)
- Modify: every other `ResolveOptions { .. }` construction (find with `grep -rn "ResolveOptions {" crates/`)

**Interfaces:**
- Consumes: nothing new.
- Produces: `pub fn cache_dir::cache_root(xdg_cache_home: Option<&OsStr>, home: Option<&OsStr>) -> Option<PathBuf>`; `ResolveOptions` gains `pub cache_root: PathBuf` (the per-user leanr cache root, e.g. `~/.cache/leanr`). Task 2 uses `opts.cache_root.join("src")`; `resolve()` now uses `opts.cache_root.join("config-cache")` for the bridge.

- [ ] **Step 1: Write the failing unit tests**

Create `crates/leanr_build/src/cache_dir.rs`:

```rust
//! leanr's per-user cache root (M2b spec §Layout): `$XDG_CACHE_HOME/leanr`,
//! falling back to `~/.cache/leanr`. Pure resolution — env values are
//! passed in by the caller; the CLI owns env reads (the `discover_roots`
//! convention in leanr_cli).

use std::ffi::OsStr;
use std::path::PathBuf;

/// Resolve the leanr cache root from caller-supplied env values. Empty
/// values are treated as unset (XDG basedir spec). `None` only when
/// neither `XDG_CACHE_HOME` nor `HOME` is usable.
pub fn cache_root(xdg_cache_home: Option<&OsStr>, home: Option<&OsStr>) -> Option<PathBuf> {
    if let Some(x) = xdg_cache_home {
        if !x.is_empty() {
            return Some(PathBuf::from(x).join("leanr"));
        }
    }
    home.filter(|h| !h.is_empty())
        .map(|h| PathBuf::from(h).join(".cache").join("leanr"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::OsStr;
    use std::path::Path;

    #[test]
    fn xdg_cache_home_wins_when_set() {
        let got = cache_root(Some(OsStr::new("/xdg")), Some(OsStr::new("/home/u"))).unwrap();
        assert_eq!(got, Path::new("/xdg/leanr"));
    }

    #[test]
    fn empty_xdg_falls_back_to_home() {
        let got = cache_root(Some(OsStr::new("")), Some(OsStr::new("/home/u"))).unwrap();
        assert_eq!(got, Path::new("/home/u/.cache/leanr"));
    }

    #[test]
    fn unset_xdg_falls_back_to_home() {
        let got = cache_root(None, Some(OsStr::new("/home/u"))).unwrap();
        assert_eq!(got, Path::new("/home/u/.cache/leanr"));
    }

    #[test]
    fn neither_set_is_none() {
        assert!(cache_root(None, None).is_none());
        assert!(cache_root(Some(OsStr::new("")), Some(OsStr::new(""))).is_none());
    }
}
```

- [ ] **Step 2: Run to verify the module isn't wired yet**

Run: `cargo test -p leanr_build cache_dir`
Expected: compile error (module not declared) — add `pub mod cache_dir;` to `crates/leanr_build/src/lib.rs` (alphabetical, after `pub mod bridge;`), re-run, expect 4 PASS.

- [ ] **Step 3: Thread `cache_root` through `ResolveOptions` and `resolve()`**

In `crates/leanr_build/src/lib.rs`:

```rust
pub struct ResolveOptions {
    /// lean_lib targets in the root package; empty = defaultTargets.
    pub targets: Vec<String>,
    pub lake: bridge::LakeInvoker,
    /// Toolchain olean root (`lean --print-libdir`) for classifying
    /// imports that resolve to no workspace module.
    pub toolchain_olean_dir: PathBuf,
    /// Per-user leanr cache root (spec 2026-07-12 §Layout): shared git
    /// source checkouts under `src/`, the bridge cache under
    /// `config-cache/`. The CLI resolves it from XDG_CACHE_HOME/HOME.
    pub cache_root: PathBuf,
}
```

and in `resolve()` replace the bridge cache-dir line:

```rust
    let cache_dir = opts.cache_root.join("config-cache");
```

- [ ] **Step 4: CLI computes the cache root from env**

In `crates/leanr_cli/src/main.rs`, inside `build()`'s `run` closure, after `toolchain_olean_dir`:

```rust
        let cache_root = leanr_build::cache_dir::cache_root(
            std::env::var_os("XDG_CACHE_HOME").as_deref(),
            std::env::var_os("HOME").as_deref(),
        )
        .ok_or_else(|| {
            "cannot determine the leanr cache directory: set XDG_CACHE_HOME or HOME".to_string()
        })?;
```

and add `cache_root,` to the `ResolveOptions` construction.

- [ ] **Step 5: Update every other `ResolveOptions` construction**

Run `grep -rn "ResolveOptions {" crates/` and add a `cache_root` to each (tests use a tempdir subdir, e.g. `cache_root: tmp.path().join("xdg-cache")`). In `crates/leanr_cli/tests/build_cli.rs`, isolate the CLI from the real user cache: in the `leanr(&tmp)` helper (and every raw `Command::cargo_bin("leanr")` call) add:

```rust
        .env("XDG_CACHE_HOME", tmp.path().join("xdg-cache"))
```

(For `setup_with_path_dependency` tests, use `tmp.path().join("xdg-cache")` of the outer tempdir.)

- [ ] **Step 6: Verify and commit**

Run: `mise run lint && cargo test --workspace`
Expected: all green (the differential `#[ignore]` tests don't run in this tier).

```bash
git add -A
git commit -m "feat(build): per-user XDG cache root; bridge cache moves to it"
```

---

### Task 2: Sources move to the shared XDG cache (immutable, flock-guarded); dry-run plan JSON revised

**Files:**
- Modify: `crates/leanr_build/src/fetch.rs` (materialize into `<src_cache>/<name>/<rev>/`; flock; immutability; tests)
- Modify: `crates/leanr_build/src/lib.rs` (dep dirs from the src cache)
- Modify: `crates/leanr_cli/src/main.rs` (`print_json_plan`: package-relative module files, per-package source dir)
- Modify: `crates/leanr_cli/tests/build_cli.rs` (assertion updates)

**Interfaces:**
- Consumes: `ResolveOptions.cache_root` (Task 1).
- Produces: `fetch::materialize(packages: &[ManifestPackage], ws_root: &Path, src_cache: &Path) -> Result<(), BuildError>` — git checkouts at `<src_cache>/<name>/<rev>/`. `ResolvedPackage.dir` for git deps now points into the cache (absolute). JSON plan schema: `packages[].dir` = workspace-relative for path deps, absolute cache path for git deps; `modules[].file` = **package-relative**.

- [ ] **Step 1: Rewrite `ensure_git` + `materialize` with immutable rev-keyed checkouts**

In `crates/leanr_build/src/fetch.rs`, update the module doc comment first line to:

```rust
//! Dependency materialization (M2b spec §Layout): ensure the shared
//! per-user source cache holds `<src_cache>/<name>/<rev>/`, an immutable
//! git checkout at exactly that rev. Shells out to the `git` CLI (as lake
//! itself does) with explicit argument vectors and validated URLs; a
//! cache entry that fails rev verification is an error, never repaired.
```

Replace `ensure_git` with (keep `git()`, the three validators, and `GIT_TIMEOUT` as they are):

```rust
/// Advisory exclusive lock guarding creation of one `<name>/<rev>`
/// checkout; released when the returned file drops. Unix `flock`; the
/// `cfg(not(unix))` fallback creates the lock file without holding a
/// lock (same cfg split as subprocess.rs's process-group kill —
/// documented, and the double-check after acquisition still catches
/// most races there).
fn lock_exclusive(path: &Path) -> Result<std::fs::File, std::io::Error> {
    let f = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(path)?;
    #[cfg(unix)]
    {
        use std::os::unix::io::AsRawFd;
        // SAFETY: flock on a fd we own; blocks until the lock is granted.
        if unsafe { libc::flock(f.as_raw_fd(), libc::LOCK_EX) } != 0 {
            return Err(std::io::Error::last_os_error());
        }
    }
    Ok(f)
}

/// A shared cache entry's directory name promises its rev; verify HEAD
/// actually matches (spec §Error handling & trust: a tampered checkout
/// fails verification and errors rather than being trusted).
fn verify_checkout(name: &str, rev: &str, dest: &Path) -> Result<(), BuildError> {
    let ferr = |msg: String| BuildError::Fetch {
        name: name.to_string(),
        msg,
    };
    let head = git(&["rev-parse", "HEAD"], dest).map_err(|e| {
        ferr(format!(
            "could not read the current commit in {}: {e}; remove the directory and re-run",
            dest.display()
        ))
    })?;
    if head != rev {
        return Err(ferr(format!(
            "shared source cache entry {} is at {head}, not the {rev} its path promises; \
             cache entries are immutable — remove the directory and re-run",
            dest.display()
        )));
    }
    Ok(())
}

fn ensure_git(name: &str, url: &str, rev: &str, pkg_cache: &Path) -> Result<(), BuildError> {
    let ferr = |msg: String| BuildError::Fetch {
        name: name.to_string(),
        msg,
    };
    let manifest_action = |msg: String| {
        ferr(format!(
            "{msg} (from lake-manifest.json); fix the entry or regenerate with `lake update`"
        ))
    };
    validate_package_name(name).map_err(manifest_action)?;
    validate_git_url(url).map_err(&ferr)?;
    validate_rev(rev).map_err(manifest_action)?;
    let dest = pkg_cache.join(rev);
    if dest.is_dir() {
        return verify_checkout(name, rev, &dest);
    }
    std::fs::create_dir_all(pkg_cache)
        .map_err(|e| ferr(format!("cannot create {}: {e}", pkg_cache.display())))?;
    let _lock = lock_exclusive(&pkg_cache.join(format!("{rev}.lock")))
        .map_err(|e| ferr(format!("cannot lock {}: {e}", pkg_cache.display())))?;
    if dest.is_dir() {
        // Another process created it while we waited on the lock.
        return verify_checkout(name, rev, &dest);
    }
    // Clone into a temp sibling, pin the rev, verify, then rename: a
    // crashed run never leaves a half-clone posing as a valid entry.
    let tmp = pkg_cache.join(format!("{rev}.tmp-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    git(
        &[
            "clone",
            "--",
            url,
            tmp.to_str().ok_or_else(|| ferr("non-UTF-8 cache path".into()))?,
        ],
        pkg_cache,
    )
    .map_err(|e| ferr(format!("clone failed: {e}")))?;
    git(
        &[
            "-c",
            "advice.detachedHead=false",
            "checkout",
            "--detach",
            rev,
            "--",
        ],
        &tmp,
    )
    .map_err(|e| ferr(format!("checkout of {rev} failed: {e}")))?;
    verify_checkout(name, rev, &tmp)?;
    std::fs::rename(&tmp, &dest)
        .map_err(|e| ferr(format!("cannot move {} into place: {e}", tmp.display())))?;
    Ok(())
}
```

Update `materialize`'s signature and Git arm (Path arm unchanged):

```rust
/// Materialize every manifest package into the shared per-user source
/// cache (spec: fresh clones work with no lake invocation). Concurrent
/// across packages; deterministic first error in package order.
pub fn materialize(
    packages: &[ManifestPackage],
    ws_root: &Path,
    src_cache: &Path,
) -> Result<(), BuildError> {
```

with the Git arm now `ensure_git(&p.name, url, rev, &src_cache.join(&p.name))`.

- [ ] **Step 2: Update `lib.rs` to place deps in the cache**

In `resolve()`, replace the `packages_dir` line and Git-arm dir computation:

```rust
    // 4. Materialize into the shared per-user source cache.
    let src_cache = opts.cache_root.join("src");
    fetch::materialize(&manifest.packages, root_dir, &src_cache)?;
```

```rust
            manifest::PackageSource::Git { rev, sub_dir, .. } => {
                let base = src_cache.join(&entry.name).join(rev);
                let dir = match sub_dir {
                    Some(sd) => base.join(sd),
                    None => base,
                };
                (dir, Some(rev.clone()))
            }
```

(`manifest.packages_dir` stays parsed but is no longer read here; leave the manifest type alone.)

- [ ] **Step 3: Update fetch tests to the new layout + add contention/tamper tests**

In `fetch.rs`'s test module: everywhere a test used `ws.path().join(".lake/packages")` as the dest, use `ws.path().join("src-cache")` and assert against `cache.join("dep").join(&rev)`. Concretely:

- `clones_at_the_pinned_rev_not_head`: assert `sh(&cache.join("dep").join(&r1), "git rev-parse HEAD") == r1`.
- Delete `existing_clean_checkout_at_wrong_rev_is_moved_to_the_pin` (rev-keyed dirs make "move to pin" meaningless) and replace with:

```rust
    #[test]
    fn tampered_cache_entry_is_an_error_never_repaired() {
        let (orig, r1, r2) = origin();
        let ws = tempfile::TempDir::new().unwrap();
        let cache = ws.path().join("src-cache");
        let url: String = orig.path().to_str().unwrap().into();
        materialize(&[git_pkg("dep", url.clone(), r1.clone())], ws.path(), &cache).unwrap();
        // Tamper: move the r1-keyed entry to r2 behind leanr's back.
        sh(
            &cache.join("dep").join(&r1),
            &format!("git -c advice.detachedHead=false checkout -q --detach {r2}"),
        );
        let err = materialize(&[git_pkg("dep", url, r1.clone())], ws.path(), &cache).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("immutable") && msg.contains(&r1), "got: {msg}");
    }

    #[test]
    fn concurrent_materialize_of_the_same_rev_races_safely() {
        let (orig, r1, _r2) = origin();
        let ws = tempfile::TempDir::new().unwrap();
        let cache = ws.path().join("src-cache");
        let url: String = orig.path().to_str().unwrap().into();
        let results: Vec<Result<(), BuildError>> = std::thread::scope(|s| {
            let handles: Vec<_> = (0..4)
                .map(|_| {
                    let pkg = git_pkg("dep", url.clone(), r1.clone());
                    let cache = cache.clone();
                    let root = ws.path().to_path_buf();
                    s.spawn(move || materialize(&[pkg], &root, &cache))
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        for r in results {
            r.unwrap();
        }
        assert_eq!(sh(&cache.join("dep").join(&r1), "git rev-parse HEAD"), r1);
        let leftovers: Vec<_> = std::fs::read_dir(cache.join("dep"))
            .unwrap()
            .filter_map(|e| e.ok())
            .filter(|e| e.file_name().to_string_lossy().contains(".tmp-"))
            .collect();
        assert!(leftovers.is_empty(), "leftover tmp dirs: {leftovers:?}");
    }
```

- `dirty_checkout_is_an_error_never_overwritten` → rename to `dirty_entry_at_the_right_rev_is_left_alone` with the *matching-rev* semantics only (write a scratch file into `cache/dep/<r1>`, re-materialize the same rev, expect Ok and the file surviving) — HEAD is the verification, `status` is no longer consulted. Delete the old `matching_rev_is_a_no_op_even_when_dirty` (now redundant with this one).
- `malicious_package_name_is_rejected_before_touching_the_filesystem`, `malicious_rev_is_rejected_before_invoking_git`, `stray_non_git_directory_reports_the_package_name`, `unknown_rev_reports_the_package`, `missing_path_dependency_is_a_clear_error`: mechanical dest-path updates only (`pkgs_dir` → `cache`; the stray-dir test creates `cache/dep/<rev>/not-a-repo.txt` with the 40-hex rev it passes).

- [ ] **Step 4: Revise the CLI JSON plan**

In `crates/leanr_cli/src/main.rs`:

Add a helper next to `print_json_plan`:

```rust
/// The source directory a module's `file` is relative to in the JSON
/// plan. Root modules → the workspace root; dep modules → the dep's
/// resolved source dir (spec 2026-07-12 §Layout: module files live
/// outside the project root now, so the plan carries package-relative
/// paths plus a per-package source-dir field).
fn package_dir<'a>(ws: &'a leanr_build::Workspace, package: &str) -> &'a std::path::Path {
    ws.deps
        .iter()
        .find(|d| d.name == package)
        .map(|d| d.dir.as_path())
        .unwrap_or(&ws.root_dir)
}
```

In `print_json_plan`, packages: path deps keep `rel_display` (unchanged); git deps use the absolute cache path:

```rust
    for d in &ws.deps {
        let dir = match d.rev {
            // Git deps live in the per-user source cache; absolute by design.
            Some(_) => d.dir.display().to_string(),
            None => rel_display(&d.dir, &ws.root_dir).map_err(|abs| {
                format!(
                    "dependency `{}` resolves to an absolute path {} outside the workspace; \
                     use a workspace-relative `dir` in lake-manifest.json",
                    d.name,
                    abs.display()
                )
            })?,
        };
        packages.push(JsonPackage { name: &d.name, rev: d.rev.as_deref(), dir });
    }
```

(change `JsonPackage`'s `dir` field type from `&str`/borrowed form to `String` if needed). Modules become package-relative:

```rust
            let m = &ws.graph.modules[id.0 as usize];
            let file = rel_display(&m.file, package_dir(ws, &m.package)).map_err(|abs| {
                format!(
                    "module `{}` (package `{}`) resolves to {} outside its package directory; \
                     this is a leanr bug — please report it",
                    m.name,
                    m.package,
                    abs.display()
                )
            })?;
```

- [ ] **Step 5: Update CLI test assertions**

In `crates/leanr_cli/tests/build_cli.rs`, `json_output_carries_path_dependency_package_and_module`: `packages[0]["dir"]` stays `"../dep"`; the module file assertion becomes package-relative:

```rust
    assert_eq!(dep_module["file"], "Dep.lean");
```

(root-package module assertions like `"App/Sub.lean"` are unchanged — package dir == workspace root there).

- [ ] **Step 6: Verify and commit**

Run: `mise run lint && cargo test --workspace`
Expected: all green.

```bash
git add -A
git commit -m "feat(build): shared XDG source cache — immutable rev-keyed checkouts, flock-guarded; package-relative plan JSON"
```

Note for the reviewer: the `#[ignore]` differential tier (`mise run build:differential`) now clones the 8 Mathlib deps into the user cache on first run (network, ~1 min) instead of reusing `.mathlib/.lake/packages`; subsequent runs are warm. This is the designed behavior, verified again in Task 9.

---

### Task 3: Lib attribution — modules know which `lean_lib` owns them

**Files:**
- Modify: `crates/leanr_build/src/graph.rs` (`LibUnit`, `ModuleResolver::resolve`, `build_graph`, `ModuleInfo`)
- Modify: `crates/leanr_build/src/lib.rs` (populate `LibUnit.lib`)
- Modify: any graph tests constructing `LibUnit` (find with `grep -rn "LibUnit" crates/`)

**Interfaces:**
- Consumes: existing `LibUnit`/`ModuleResolver`/`build_graph`.
- Produces: `LibUnit { package: String, lib: String, src_dir: PathBuf, root: ModuleName }`; `ModuleResolver::resolve(&self, m) -> Option<(String, String, PathBuf)>` (package, lib, file); `ModuleInfo` gains `pub lib: String`. Task 4 reads `ModuleInfo.lib` to look up the owning lib's `leanOptions`.

- [ ] **Step 1: Write the failing test**

In `graph.rs`'s test module (adapt to the existing test helpers there — they already build synthetic package trees):

```rust
    #[test]
    fn modules_carry_their_owning_lib() {
        // Reuse the existing synthetic-tree helper pattern in this module:
        // one package "app", lib "App", module App imports App.Sub.
        let tmp = tempfile::TempDir::new().unwrap();
        std::fs::write(tmp.path().join("App.lean"), "import App.Sub\n").unwrap();
        std::fs::create_dir_all(tmp.path().join("App")).unwrap();
        std::fs::write(tmp.path().join("App/Sub.lean"), "prelude\n").unwrap();
        let resolver = ModuleResolver::new(vec![LibUnit {
            package: "app".into(),
            lib: "App".into(),
            src_dir: tmp.path().to_path_buf(),
            root: ModuleName::parse("App").unwrap(),
        }]);
        struct NoToolchain;
        impl ToolchainIndex for NoToolchain {
            fn contains(&self, _m: &ModuleName) -> bool {
                true // classify Init etc. as toolchain
            }
        }
        let g = build_graph(&[ModuleName::parse("App").unwrap()], &resolver, &NoToolchain).unwrap();
        for m in &g.modules {
            assert_eq!(m.lib, "App", "module {} lost its lib attribution", m.name);
        }
    }
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p leanr_build modules_carry_their_owning_lib`
Expected: compile error — `LibUnit` has no field `lib`.

- [ ] **Step 3: Implement**

- `LibUnit` gains `pub lib: String` (between `package` and `src_dir`).
- `ModuleResolver::resolve` returns `Option<(String, String, PathBuf)>`: `return Some((u.package.clone(), u.lib.clone(), file));`.
- In `build_graph`: the `scanned` map value becomes `(String, String, PathBuf, Header)`; the resolve arm destructures `Some((pkg, lib, file))`; the scan tuple carries `lib` through; `ModuleInfo` construction adds `lib`.
- `ModuleInfo` gains `pub lib: String` (after `package`).
- In `lib.rs`, the `units.push(LibUnit { ... })` adds `lib: lib.name.clone(),`.
- Fix every other `LibUnit`/`resolve` use the grep finds (tests in `graph.rs`/`modules.rs` and the differential test file if it constructs units).

- [ ] **Step 4: Run tests, lint, commit**

Run: `mise run lint && cargo test --workspace`
Expected: all green.

```bash
git add -A
git commit -m "feat(build): modules carry their owning lean_lib (leanOptions attribution for M2b setup files)"
```

---

### Task 4: `setup` — layout, setup JSON, LEAN_PATH (pure planning)

**Files:**
- Create: `crates/leanr_build/src/setup.rs`
- Create: `crates/leanr_build/src/testws.rs` (`#[cfg(test)]` helper)
- Modify: `crates/leanr_build/src/lib.rs` (`pub mod setup;` and `#[cfg(test)] pub(crate) mod testws;`)

**Interfaces:**
- Consumes: `Workspace`, `ModuleInfo` (+ `.lib` from Task 3), `config::{LeanOptionValue, PackageConfig}`, `modules::ModuleName`.
- Produces (Task 6 consumes all of these):
  - `pub struct Layout { pub build_root: PathBuf }` with `Layout::new(root_dir: &Path)`, `lib_dir(&self, package: &str) -> PathBuf`, `olean_path/ilean_path/setup_path(&self, package: &str, m: &ModuleName) -> PathBuf`, `artifact_paths(&self, package: &str, m: &ModuleInfo) -> Vec<PathBuf>`.
  - `pub struct SetupFile { ... }` (serde-serializable) + `pub fn module_setup(ws: &Workspace, layout: &Layout, id: ModuleId) -> SetupFile`.
  - `pub fn lean_path_env(ws: &Workspace, layout: &Layout) -> std::ffi::OsString`.

- [ ] **Step 1: Create the shared synthetic-workspace test helper**

Create `crates/leanr_build/src/testws.rs`:

```rust
//! #[cfg(test)] support: a real `Workspace` resolved from a synthetic
//! on-disk project (no git, no lake, fake toolchain dir). Shared by the
//! setup and compile unit tests.

use std::path::PathBuf;

pub(crate) struct TestWs {
    pub tmp: tempfile::TempDir,
    pub ws: crate::Workspace,
}

pub(crate) fn synthetic() -> TestWs {
    let tmp = tempfile::TempDir::new().unwrap();
    let write = |rel: &str, text: &str| {
        let p = tmp.path().join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    };
    write(
        "lakefile.toml",
        "name = \"app\"\ndefaultTargets = [\"App\"]\nleanOptions = {autoImplicit = false}\n\n\
         [[lean_lib]]\nname = \"App\"\nleanOptions = {\"pp.unicode.fun\" = true}\n",
    );
    write("App.lean", "import App.Sub\n");
    write("App/Sub.lean", "");
    write(
        "lake-manifest.json",
        r#"{"version": "1.2.0", "packages": []}"#,
    );
    let fake_toolchain = tmp.path().join("fake-toolchain");
    std::fs::create_dir_all(&fake_toolchain).unwrap();
    std::fs::write(fake_toolchain.join("Init.olean"), "").unwrap();
    let opts = crate::ResolveOptions {
        targets: vec![],
        lake: crate::bridge::LakeInvoker::default(),
        toolchain_olean_dir: fake_toolchain,
        cache_root: tmp.path().join("xdg-cache"),
    };
    let ws = crate::resolve(tmp.path(), &opts).unwrap();
    TestWs { tmp, ws }
}
```

Add to `lib.rs`: `#[cfg(test)] pub(crate) mod testws;`.

- [ ] **Step 2: Write the failing setup tests**

Create `crates/leanr_build/src/setup.rs` with tests first (implementation stubs after Step 3):

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::testws;

    #[test]
    fn layout_paths_are_under_leanr_build() {
        let t = testws::synthetic();
        let layout = Layout::new(&t.ws.root_dir);
        let sub = crate::modules::ModuleName::parse("App.Sub").unwrap();
        assert_eq!(
            layout.olean_path("app", &sub),
            t.ws.root_dir.join(".leanr/build/app/lib/App/Sub.olean")
        );
        assert_eq!(
            layout.ilean_path("app", &sub),
            t.ws.root_dir.join(".leanr/build/app/lib/App/Sub.ilean")
        );
        assert_eq!(
            layout.setup_path("app", &sub),
            t.ws.root_dir.join(".leanr/build/app/setup/App/Sub.setup.json")
        );
    }

    #[test]
    fn setup_file_carries_import_arts_options_and_is_module() {
        let t = testws::synthetic();
        let layout = Layout::new(&t.ws.root_dir);
        let app_id = t
            .ws
            .graph
            .id_of(&crate::modules::ModuleName::parse("App").unwrap())
            .unwrap();
        let s = module_setup(&t.ws, &layout, app_id);
        let got = serde_json::to_value(&s).unwrap();
        let sub_olean = layout
            .olean_path("app", &crate::modules::ModuleName::parse("App.Sub").unwrap())
            .display()
            .to_string();
        assert_eq!(
            got,
            serde_json::json!({
                "package": "app",
                "name": "App",
                "isModule": false,
                "options": {"autoImplicit": false, "pp.unicode.fun": true},
                "importArts": {"App.Sub": [sub_olean]},
                "plugins": [],
                "dynlibs": []
            })
        );
    }

    #[test]
    fn module_system_modules_get_the_full_artifact_family() {
        let t = testws::synthetic();
        let layout = Layout::new(&t.ws.root_dir);
        let sub_id = t
            .ws
            .graph
            .id_of(&crate::modules::ModuleName::parse("App.Sub").unwrap())
            .unwrap();
        let m = &t.ws.graph.modules[sub_id.0 as usize];
        // Non-module module: olean + ilean only.
        assert_eq!(layout.artifact_paths("app", m).len(), 2);
        // A module-system ModuleInfo adds .ir/.olean.server/.olean.private.
        let mm = crate::graph::ModuleInfo {
            name: m.name.clone(),
            package: m.package.clone(),
            lib: m.lib.clone(),
            file: m.file.clone(),
            imports: vec![],
            deps: vec![],
            prelude: m.prelude,
            is_module: true,
        };
        let arts = layout.artifact_paths("app", &mm);
        let exts: Vec<String> = arts
            .iter()
            .map(|p| p.to_string_lossy().rsplit('/').next().unwrap().to_string())
            .collect();
        assert_eq!(
            exts,
            vec![
                "Sub.olean",
                "Sub.ilean",
                "Sub.ir",
                "Sub.olean.server",
                "Sub.olean.private"
            ]
        );
    }

    #[test]
    fn lean_path_lists_every_package_lib_dir() {
        let t = testws::synthetic();
        let layout = Layout::new(&t.ws.root_dir);
        let lp = lean_path_env(&t.ws, &layout);
        let parts: Vec<PathBuf> = std::env::split_paths(&lp).collect();
        assert!(parts.contains(&layout.lib_dir("app")));
    }
}
```

- [ ] **Step 3: Run to verify failure, then implement**

Run: `cargo test -p leanr_build setup` — expected: compile errors (nothing defined). Implement above the tests:

```rust
//! Per-module `lean` invocation planning (M2b spec §Architecture,
//! component `setup`): artifact paths in leanr's own layout
//! (`.leanr/build/<pkg>/…`), the `--setup` JSON lake hands to lean
//! (verified against `lake build --verbose` on the pinned toolchain,
//! spec §Key empirical facts), and LEAN_PATH for transitive olean
//! loads. Pure functions — nothing here runs a process.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::{Path, PathBuf};

use crate::config::LeanOptionValue;
use crate::graph::{ModuleId, ModuleInfo};
use crate::modules::ModuleName;
use crate::Workspace;

pub struct Layout {
    /// `<workspace root>/.leanr/build`
    pub build_root: PathBuf,
}

impl Layout {
    pub fn new(root_dir: &Path) -> Layout {
        Layout {
            build_root: root_dir.join(".leanr").join("build"),
        }
    }

    pub fn lib_dir(&self, package: &str) -> PathBuf {
        self.build_root.join(package).join("lib")
    }

    fn module_path(&self, base: PathBuf, m: &ModuleName, ext: &str) -> PathBuf {
        let mut p = base.join(m.components().iter().collect::<PathBuf>());
        p.set_extension(ext);
        p
    }

    pub fn olean_path(&self, package: &str, m: &ModuleName) -> PathBuf {
        self.module_path(self.lib_dir(package), m, "olean")
    }

    pub fn ilean_path(&self, package: &str, m: &ModuleName) -> PathBuf {
        self.module_path(self.lib_dir(package), m, "ilean")
    }

    pub fn setup_path(&self, package: &str, m: &ModuleName) -> PathBuf {
        self.module_path(
            self.build_root.join(package).join("setup"),
            m,
            "setup.json",
        )
    }

    /// The artifact family `lean` emits: `.olean` + `.ilean` always;
    /// module-system modules add `.ir`, `.olean.server`, `.olean.private`
    /// (siblings lean derives from `-o` — spec §Key empirical facts).
    pub fn artifact_paths(&self, package: &str, m: &ModuleInfo) -> Vec<PathBuf> {
        let mut arts = vec![
            self.olean_path(package, &m.name),
            self.ilean_path(package, &m.name),
        ];
        if m.is_module {
            for ext in ["ir", "olean.server", "olean.private"] {
                arts.push(self.module_path(self.lib_dir(package), &m.name, ext));
            }
        }
        arts
    }
}

/// The `--setup` JSON, shaped exactly like lake's (observed on the
/// pinned toolchain): importArts lists the exact artifact paths of each
/// direct *workspace* import (toolchain imports are omitted, resolved
/// via lean's own sysroot); options carry the owning package's
/// leanOptions overlaid by the owning lib's.
#[derive(Debug, serde::Serialize)]
pub struct SetupFile {
    pub package: String,
    pub name: String,
    #[serde(rename = "isModule")]
    pub is_module: bool,
    pub options: BTreeMap<String, serde_json::Value>,
    #[serde(rename = "importArts")]
    pub import_arts: BTreeMap<String, Vec<String>>,
    pub plugins: Vec<String>,
    pub dynlibs: Vec<String>,
}

fn option_value(v: &LeanOptionValue) -> serde_json::Value {
    match v {
        LeanOptionValue::Bool(b) => (*b).into(),
        LeanOptionValue::Int(i) => (*i).into(),
        LeanOptionValue::String(s) => s.clone().into(),
    }
}

fn module_options(ws: &Workspace, m: &ModuleInfo) -> BTreeMap<String, serde_json::Value> {
    let mut out = BTreeMap::new();
    let pkg = std::iter::once(&ws.root)
        .chain(ws.deps.iter())
        .find(|p| p.name == m.package);
    if let Some(p) = pkg {
        for (k, v) in &p.config.lean_options {
            out.insert(k.clone(), option_value(v));
        }
        if let Some(lib) = p.config.lean_libs.iter().find(|l| l.name == m.lib) {
            for (k, v) in &lib.lean_options {
                out.insert(k.clone(), option_value(v));
            }
        }
    }
    out
}

pub fn module_setup(ws: &Workspace, layout: &Layout, id: ModuleId) -> SetupFile {
    let m = &ws.graph.modules[id.0 as usize];
    let mut import_arts = BTreeMap::new();
    for &d in &m.deps {
        let dm = &ws.graph.modules[d.0 as usize];
        let mut arts = vec![layout.olean_path(&dm.package, &dm.name).display().to_string()];
        if dm.is_module {
            for ext in ["ir", "olean.server", "olean.private"] {
                arts.push(
                    layout
                        .module_path(layout.lib_dir(&dm.package), &dm.name, ext)
                        .display()
                        .to_string(),
                );
            }
        }
        import_arts.insert(dm.name.to_string(), arts);
    }
    SetupFile {
        package: m.package.clone(),
        name: m.name.to_string(),
        is_module: m.is_module,
        options: module_options(ws, m),
        import_arts,
        plugins: vec![],
        dynlibs: vec![],
    }
}

/// LEAN_PATH for every worker: each package's lib dir (transitive olean
/// loads resolve through it — lake sets it too, spec §Key empirical facts).
pub fn lean_path_env(ws: &Workspace, layout: &Layout) -> OsString {
    let dirs = std::iter::once(&ws.root)
        .chain(ws.deps.iter())
        .map(|p| layout.lib_dir(&p.name));
    std::env::join_paths(dirs).expect("lib dirs contain no path separators")
}
```

(Make `module_path` visible to `module_setup` — it is, same module. If the compiler objects to the private `module_path` call pattern above, inline the three-extension loop via `artifact_paths` minus the first two entries instead.)

- [ ] **Step 4: Run tests, lint, commit**

Run: `mise run lint && cargo test -p leanr_build`
Expected: all green (4 new tests pass).

```bash
git add -A
git commit -m "feat(build): setup planning — leanr artifact layout, --setup JSON, LEAN_PATH"
```

---

### Task 5: `pool` — generic dependency-counter scheduler

**Files:**
- Create: `crates/leanr_build/src/pool.rs`
- Modify: `crates/leanr_build/src/lib.rs` (`pub mod pool;`)

**Interfaces:**
- Consumes: nothing from this crate (index-based on purpose — knows nothing about modules or processes).
- Produces (Task 6 consumes): `pub struct PoolFailure { pub item: usize, pub message: String }`; `pub fn run(deps: &[Vec<usize>], jobs: usize, job: &(dyn Fn(usize) -> Result<(), String> + Sync), on_done: &(dyn Fn(usize, usize, usize) + Sync)) -> Result<(), PoolFailure>` — `deps[i]` = indices `i` waits on; `on_done(item, done_count, total)` fires after each success.

- [ ] **Step 1: Write the failing tests**

Create `crates/leanr_build/src/pool.rs` with the test module first:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;

    fn record_order(deps: &[Vec<usize>], jobs: usize) -> Vec<usize> {
        let order = Mutex::new(Vec::new());
        run(
            deps,
            jobs,
            &|i| {
                order.lock().unwrap().push(i);
                Ok(())
            },
            &|_, _, _| {},
        )
        .unwrap();
        order.into_inner().unwrap()
    }

    #[test]
    fn empty_graph_completes() {
        assert!(run(&[], 4, &|_| Ok(()), &|_, _, _| {}).is_ok());
    }

    #[test]
    fn diamond_respects_dependency_order() {
        // 0 -> {1, 2} -> 3   (deps[i] lists what i waits on)
        let deps = vec![vec![], vec![0], vec![0], vec![1, 2]];
        for jobs in [1, 4] {
            let order = record_order(&deps, jobs);
            assert_eq!(order.len(), 4);
            let pos = |x: usize| order.iter().position(|&i| i == x).unwrap();
            assert!(pos(0) < pos(1) && pos(0) < pos(2) && pos(1) < pos(3) && pos(2) < pos(3));
        }
    }

    #[test]
    fn long_chain_completes_with_many_workers() {
        let deps: Vec<Vec<usize>> = (0..100).map(|i| if i == 0 { vec![] } else { vec![i - 1] }).collect();
        let order = record_order(&deps, 8);
        assert_eq!(order, (0..100).collect::<Vec<_>>());
    }

    #[test]
    fn failure_cancels_downstream_and_reports_first_failure() {
        // 0 -> 1(fails) -> 2 ; 3 independent
        let deps = vec![vec![], vec![0], vec![1], vec![]];
        let ran = Mutex::new(Vec::new());
        let err = run(
            &deps,
            1,
            &|i| {
                ran.lock().unwrap().push(i);
                if i == 1 {
                    Err("boom".into())
                } else {
                    Ok(())
                }
            },
            &|_, _, _| {},
        )
        .unwrap_err();
        assert_eq!(err.item, 1);
        assert_eq!(err.message, "boom");
        assert!(!ran.lock().unwrap().contains(&2), "dependent of a failure must never run");
    }

    #[test]
    fn parallelism_is_bounded_by_jobs() {
        let deps: Vec<Vec<usize>> = (0..16).map(|_| vec![]).collect();
        let current = AtomicUsize::new(0);
        let high = AtomicUsize::new(0);
        run(
            &deps,
            2,
            &|_| {
                let c = current.fetch_add(1, Ordering::SeqCst) + 1;
                high.fetch_max(c, Ordering::SeqCst);
                std::thread::sleep(std::time::Duration::from_millis(10));
                current.fetch_sub(1, Ordering::SeqCst);
                Ok(())
            },
            &|_, _, _| {},
        )
        .unwrap();
        assert!(high.load(Ordering::SeqCst) <= 2);
    }

    #[test]
    fn on_done_counts_monotonically_to_total() {
        let deps: Vec<Vec<usize>> = (0..5).map(|_| vec![]).collect();
        let seen = Mutex::new(Vec::new());
        run(&deps, 3, &|_| Ok(()), &|_, done, total| {
            assert_eq!(total, 5);
            seen.lock().unwrap().push(done);
        })
        .unwrap();
        let mut s = seen.into_inner().unwrap();
        s.sort_unstable();
        assert_eq!(s, vec![1, 2, 3, 4, 5]);
    }
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_build pool`
Expected: compile error — `run` not defined.

- [ ] **Step 3: Implement**

Above the tests:

```rust
//! Generic dependency-counter scheduler (M2b spec §Architecture,
//! component `pool`): the leanr_check shape — ready queue under a
//! Mutex+Condvar, fail-fast, first-failure slot — reimplemented for
//! index-based jobs. One Mutex around all state (not leanr_check's
//! lock-free atomics): pool items here are 100ms+ subprocesses, so
//! lock contention is noise. Knows nothing about modules or processes;
//! this genericity is the seam where M2c inserts cache lookups and M4
//! swaps in leanr's own elaborator.
//!
//! Cycles are the caller's problem: `resolve()` already rejects them
//! (`topo_waves`), and the in-flight guard below turns an impossible
//! stall into a clean return rather than a hang.

use std::collections::VecDeque;
use std::sync::{Condvar, Mutex};

pub struct PoolFailure {
    pub item: usize,
    pub message: String,
}

struct State {
    ready: VecDeque<usize>,
    remaining: Vec<usize>,
    in_flight: usize,
    done: usize,
    cancelled: bool,
    failure: Option<PoolFailure>,
}

/// Run `job` for every item, respecting `deps` (deps[i] = indices i
/// waits on), at most `jobs` at a time. Fail-fast: the first failure
/// abandons everything not yet started; in-flight jobs finish.
/// `on_done(item, done_count, total)` fires after each success.
pub fn run(
    deps: &[Vec<usize>],
    jobs: usize,
    job: &(dyn Fn(usize) -> Result<(), String> + Sync),
    on_done: &(dyn Fn(usize, usize, usize) + Sync),
) -> Result<(), PoolFailure> {
    let total = deps.len();
    let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); total];
    let mut remaining = vec![0usize; total];
    for (i, ds) in deps.iter().enumerate() {
        remaining[i] = ds.len();
        for &d in ds {
            dependents[d].push(i);
        }
    }
    let state = Mutex::new(State {
        ready: (0..total).filter(|&i| remaining[i] == 0).collect(),
        remaining,
        in_flight: 0,
        done: 0,
        cancelled: false,
        failure: None,
    });
    let cv = Condvar::new();
    let workers = jobs.max(1).min(total.max(1));
    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| loop {
                let item = {
                    let mut st = state.lock().unwrap();
                    loop {
                        if st.cancelled || st.done == total {
                            return;
                        }
                        if let Some(i) = st.ready.pop_front() {
                            st.in_flight += 1;
                            break i;
                        }
                        if st.in_flight == 0 {
                            // Nothing ready, nothing running: exhausted
                            // (or a cycle, excluded upstream) — don't hang.
                            return;
                        }
                        st = cv.wait(st).unwrap();
                    }
                };
                let result = job(item);
                let mut st = state.lock().unwrap();
                st.in_flight -= 1;
                match result {
                    Ok(()) => {
                        st.done += 1;
                        let done = st.done;
                        for &d in &dependents[item] {
                            st.remaining[d] -= 1;
                            if st.remaining[d] == 0 {
                                st.ready.push_back(d);
                            }
                        }
                        drop(st);
                        cv.notify_all();
                        on_done(item, done, total);
                    }
                    Err(message) => {
                        if st.failure.is_none() {
                            st.failure = Some(PoolFailure { item, message });
                        }
                        st.cancelled = true;
                        drop(st);
                        cv.notify_all();
                        return;
                    }
                }
            });
        }
    });
    let mut st = state.lock().unwrap();
    match st.failure.take() {
        Some(f) => Err(f),
        None => Ok(()),
    }
}
```

Add `pub mod pool;` to `lib.rs`.

- [ ] **Step 4: Run tests, lint, commit**

Run: `mise run lint && cargo test -p leanr_build pool`
Expected: 6 PASS.

```bash
git add -A
git commit -m "feat(build): dependency-counter pool — fail-fast index scheduler"
```

---

### Task 6: `compile` — drive `lean` per module; diagnostics; failure hygiene

**Files:**
- Create: `crates/leanr_build/src/compile.rs`
- Create: `crates/leanr_build/tests/fixtures/fake-lean.sh` (chmod +x)
- Modify: `crates/leanr_build/src/subprocess.rs` (add `run_drained`)
- Modify: `crates/leanr_build/src/error.rs` (two variants)
- Modify: `crates/leanr_build/src/lib.rs` (`pub mod compile;`)

**Interfaces:**
- Consumes: `setup::{Layout, module_setup, lean_path_env}` (Task 4), `pool::run` (Task 5), `Workspace`.
- Produces (Task 7 consumes):
  - `pub struct LeanInvoker { pub program: PathBuf, pub toolchain: Option<String> }` (+`Default` = `"lean"`, no toolchain)
  - `pub struct BuildOptions { pub jobs: usize, pub lean: LeanInvoker }`
  - `pub struct BuiltEvent<'a> { pub module: &'a str, pub done: usize, pub total: usize, pub secs: f64, pub diagnostics: &'a str }`
  - `pub struct BuildReport { pub built: usize }`
  - `pub fn build_workspace(ws: &Workspace, opts: &BuildOptions, on_built: &(dyn Fn(BuiltEvent<'_>) + Sync)) -> Result<BuildReport, BuildError>`
  - `BuildError::{Unsupported, ModuleBuild}`

- [ ] **Step 1: Add error variants and `run_drained`**

`error.rs` — append to the enum:

```rust
    #[error("package `{package}` requires {feature}, which `leanr build` does not support yet (M2b builds lean_lib artifacts only)")]
    Unsupported { package: String, feature: String },
    #[error("building `{module}` ({file}) failed:\n{details}")]
    ModuleBuild {
        module: String,
        file: PathBuf,
        details: String,
    },
```

`subprocess.rs` — append:

```rust
/// Spawn with drained pipes, NO timeout and NO process-group detach:
/// a compile job legitimately runs for minutes (a Mathlib module's
/// elaboration), and build workers must stay in leanr's own process
/// group so a terminal Ctrl-C kills them together — the opposite of
/// the bridge's translate-config (timed out + group-killed).
pub(crate) fn run_drained(cmd: &mut Command) -> Result<Finished, RunError> {
    cmd.stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = cmd.spawn().map_err(RunError::Spawn)?;
    let stdout_thread = drain(child.stdout.take());
    let stderr_thread = drain(child.stderr.take());
    match child.wait() {
        Ok(status) => Ok(Finished {
            status,
            stdout: join(stdout_thread),
            stderr: join(stderr_thread),
        }),
        Err(e) => Err(RunError::Wait(e, join(stderr_thread))),
    }
}
```

- [ ] **Step 2: Create the fake-lean fixture**

`crates/leanr_build/tests/fixtures/fake-lean.sh`:

```sh
#!/bin/sh
# Fake `lean` for compile-layer unit tests. Understands the argv shape
# compile.rs produces: <src> -o <olean> -i <ilean> --setup <setup> --json.
# FAKE_LEAN_FAIL_ON=<substr>: for a matching <src>, write a partial
# olean, emit one JSON diagnostic on stdout, exit 1.
src=""; o=""; i=""; setup=""
while [ $# -gt 0 ]; do
  case "$1" in
    -o) o="$2"; shift 2 ;;
    -i) i="$2"; shift 2 ;;
    --setup) setup="$2"; shift 2 ;;
    --json) shift ;;
    +*) shift ;;
    -*) shift ;;
    *) src="$1"; shift ;;
  esac
done
[ -f "$setup" ] || { echo "fake-lean: missing setup file $setup" >&2; exit 3; }
mkdir -p "$(dirname "$o")" "$(dirname "$i")"
case "$src" in
  *"${FAKE_LEAN_FAIL_ON:-@@never@@}"*)
    printf 'partial' > "$o"
    printf '{"severity":"error","pos":{"line":3,"column":7},"fileName":"%s","data":"unknown identifier `nope`"}\n' "$src"
    exit 1 ;;
esac
printf 'olean:%s' "$src" > "$o"
printf 'ilean:%s' "$src" > "$i"
exit 0
```

Run: `chmod +x crates/leanr_build/tests/fixtures/fake-lean.sh`

- [ ] **Step 3: Write the failing compile tests**

Create `crates/leanr_build/src/compile.rs` with the test module first:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::setup::Layout;
    use crate::testws;
    use std::path::{Path, PathBuf};
    use std::sync::Mutex;

    fn fake_lean() -> LeanInvoker {
        LeanInvoker {
            program: Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/fake-lean.sh"),
            toolchain: None,
        }
    }

    #[test]
    fn builds_every_module_in_dependency_order() {
        let t = testws::synthetic();
        let events: Mutex<Vec<String>> = Mutex::new(Vec::new());
        let report = build_workspace(
            &t.ws,
            &BuildOptions { jobs: 2, lean: fake_lean() },
            &|e: BuiltEvent<'_>| events.lock().unwrap().push(e.module.to_string()),
        )
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
    fn failing_module_reports_diagnostics_and_deletes_partial_outputs() {
        let t = testws::synthetic();
        std::env::set_var("FAKE_LEAN_FAIL_ON", "Sub.lean");
        let err = build_workspace(
            &t.ws,
            &BuildOptions { jobs: 1, lean: fake_lean() },
            &|_| {},
        )
        .unwrap_err();
        std::env::remove_var("FAKE_LEAN_FAIL_ON");
        let msg = err.to_string();
        assert!(msg.contains("App.Sub"), "names the module: {msg}");
        assert!(msg.contains("unknown identifier"), "carries the diagnostic: {msg}");
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
        let err = build_workspace(
            &t.ws,
            &BuildOptions { jobs: 1, lean: fake_lean() },
            &|_| {},
        )
        .unwrap_err();
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
```

Note: `failing_module_...` and `builds_every_module_...` both spawn processes reading `FAKE_LEAN_FAIL_ON`; the `set_var`/`remove_var` pair plus distinct workspaces keeps them independent, but run them serially if flaky: `cargo test -p leanr_build compile -- --test-threads=1` is acceptable to encode in the test names' module docs — prefer making the env var a `BuildOptions`-independent concern by setting it only around the one test as shown.

- [ ] **Step 4: Run to verify failure, then implement**

Run: `cargo test -p leanr_build compile` — expected: compile errors. Implement above the tests:

```rust
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
}

pub struct BuiltEvent<'a> {
    pub module: &'a str,
    pub done: usize,
    pub total: usize,
    pub secs: f64,
    /// Rendered diagnostics (warnings) from a successful build; empty
    /// when lean was silent.
    pub diagnostics: &'a str,
}

pub struct BuildReport {
    pub built: usize,
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
    let results: Mutex<Vec<Option<(f64, String)>>> =
        Mutex::new(vec![None; ws.graph.modules.len()]);
    let job = |i: usize| -> Result<(), String> {
        let m = &ws.graph.modules[i];
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
                Ok(())
            }
            Ok(f) => {
                cleanup();
                let mut details =
                    render_diagnostics(&String::from_utf8_lossy(&f.stdout));
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
        let (secs, diags) = results.lock().unwrap()[i].take().unwrap_or((0.0, String::new()));
        on_built(BuiltEvent {
            module: &m.name.to_string(),
            done,
            total,
            secs,
            diagnostics: &diags,
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
    Ok(BuildReport {
        built: ws.graph.modules.len(),
    })
}
```

(The `BuiltEvent { module: &m.name.to_string(), ... }` borrow won't compile as written — bind `let name = m.name.to_string();` first and pass `&name`. Same for `&diags`. Fix mechanically.)

Add `pub mod compile;` to `lib.rs`.

- [ ] **Step 5: Run tests, lint, commit**

Run: `mise run lint && cargo test -p leanr_build`
Expected: all green.

```bash
git add -A
git commit -m "feat(build): compile layer — parallel official-lean workers, diagnostics, failure hygiene"
```

---

### Task 7: CLI — bare `leanr build` with progress; `--jobs`, `--lean`

**Files:**
- Modify: `crates/leanr_cli/src/main.rs` (Build args; `build()` executes when `!dry_run`)
- Modify: `crates/leanr_cli/tests/build_cli.rs` (replace the "coming in M2b" test with a real bare-build test)

**Interfaces:**
- Consumes: `compile::{build_workspace, BuildOptions, LeanInvoker, BuiltEvent}` (Task 6).
- Produces: user-facing `leanr build [targets] [--jobs N] [--lean PATH]`; progress lines `[done/total] Module.Name (X.Xs)` on stdout; warnings on stderr; summary line.

- [ ] **Step 1: Write the failing CLI test**

In `build_cli.rs`, replace `build_without_dry_run_is_a_clear_not_yet_error` with:

```rust
fn fake_lean_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../leanr_build/tests/fixtures/fake-lean.sh")
        .canonicalize()
        .unwrap()
}

#[test]
fn bare_build_compiles_the_plan_with_progress_and_summary() {
    let tmp = setup();
    Command::cargo_bin("leanr")
        .unwrap()
        .current_dir(tmp.path())
        .env("XDG_CACHE_HOME", tmp.path().join("xdg-cache"))
        .args(["build"])
        .args([
            "--toolchain-dir",
            tmp.path().join("fake-toolchain").to_str().unwrap(),
        ])
        .args(["--lean", fake_lean_path().to_str().unwrap()])
        .args(["--jobs", "2"])
        .assert()
        .success()
        .stdout(predicate::str::contains("[1/2] App.Sub"))
        .stdout(predicate::str::contains("[2/2] App"))
        .stdout(predicate::str::contains("built 2 modules"));
    assert!(tmp
        .path()
        .join(".leanr/build/app/lib/App/Sub.olean")
        .is_file());
}

#[test]
fn failed_module_build_is_reported_with_its_diagnostics() {
    let tmp = setup();
    Command::cargo_bin("leanr")
        .unwrap()
        .current_dir(tmp.path())
        .env("XDG_CACHE_HOME", tmp.path().join("xdg-cache"))
        .env("FAKE_LEAN_FAIL_ON", "Sub.lean")
        .args(["build"])
        .args([
            "--toolchain-dir",
            tmp.path().join("fake-toolchain").to_str().unwrap(),
        ])
        .args(["--lean", fake_lean_path().to_str().unwrap()])
        .assert()
        .failure()
        .stderr(predicate::str::contains("App.Sub"))
        .stderr(predicate::str::contains("unknown identifier"));
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_cli --test build_cli bare_build`
Expected: FAIL — unknown `--lean`/`--jobs` args, and bare `build` still errors.

- [ ] **Step 3: Implement**

`Command::Build` gains:

```rust
        /// Worker processes (default: available parallelism).
        #[arg(long)]
        jobs: Option<usize>,
        /// lean executable to drive (default: `lean` on PATH; primarily
        /// for tests and debugging).
        #[arg(long)]
        lean: Option<PathBuf>,
```

(thread both through the `match` arm into `build()`). In `build()`, delete the `if !dry_run { ... M2b ... }` block; after the warnings loop, branch:

```rust
        if dry_run {
            if json {
                print_json_plan(&ws)?;
            } else {
                print_text_plan(&ws);
            }
            return Ok(());
        }
        let jobs = jobs.unwrap_or_else(|| {
            std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1)
        });
        let build_opts = leanr_build::compile::BuildOptions {
            jobs,
            lean: leanr_build::compile::LeanInvoker {
                program: lean.clone().unwrap_or_else(|| PathBuf::from("lean")),
                toolchain: toolchain.clone(),
            },
        };
        let start = std::time::Instant::now();
        let report = leanr_build::compile::build_workspace(&ws, &build_opts, &|e| {
            if !e.diagnostics.is_empty() {
                eprint!("{}", e.diagnostics);
            }
            println!("[{}/{}] {} ({:.1}s)", e.done, e.total, e.module, e.secs);
        })
        .map_err(|e| e.to_string())?;
        println!(
            "built {} modules in {:.1}s ({} jobs)",
            report.built,
            start.elapsed().as_secs_f64(),
            jobs
        );
        Ok(())
```

(`toolchain` is currently moved into the `LakeInvoker`; clone it before that construction: `let toolchain_for_lean = toolchain.clone();` or restructure so both invokers get a clone.)

- [ ] **Step 4: Run tests, lint, commit**

Run: `mise run lint && cargo test --workspace`
Expected: all green (including the updated CLI suite).

```bash
git add -A
git commit -m "feat(cli): bare `leanr build` — parallel compile with progress, --jobs/--lean"
```

---

### Task 8: Documentation — ARCHITECTURE.md and THREAT_MODEL.md

**Files:**
- Modify: `ARCHITECTURE.md` (the `leanr_build` bullet)
- Modify: `docs/THREAT_MODEL.md` (new M2b section)

**Interfaces:** none (docs only). This is its own task so the reviewer can gate on doc accuracy separately.

- [ ] **Step 1: Update the `leanr_build` bullet in ARCHITECTURE.md**

Replace the current bullet body (lines 73–76) with:

```markdown
- `crates/leanr_build` — Lake-compatible package model + module graph
  (M2a: lakefile.toml schema, translate-config bridge, manifest-driven
  git materialization, import DAG) and the build orchestrator (M2b:
  `setup` plans per-module official-`lean` invocations into leanr's own
  layout under `.leanr/build/`; `pool` is a fail-fast dependency-counter
  scheduler; `compile` drives one `lean` process per module,
  unconditionally — no up-to-date skipping until M2c). Dependency
  sources live in the per-user XDG cache
  (`$XDG_CACHE_HOME/leanr/src/<name>/<rev>/`, immutable, flock-guarded),
  as does the bridge cache; Lake-layout interop is retired as of the
  M2b spec (`docs/superpowers/specs/2026-07-12-m2b-build-orchestrator-design.md`).
  `leanr build` / `leanr build --dry-run`. No kernel dependency.
```

- [ ] **Step 2: Add the M2b section to docs/THREAT_MODEL.md**

Read the file first and match its existing section format (the M2a section is the template). Content to convey, in that format:

```markdown
## M2b — build orchestrator

**Surface.** `leanr build` runs the official `lean` on package sources:
elaboration executes metaprograms, so building a package is arbitrary
code execution by design — the same posture as the M2a bridge and as
lake itself. Stated, not mitigated.

**Shared source cache.** Dependency checkouts move to a per-user cache
(`$XDG_CACHE_HOME/leanr/src/<name>/<rev>/`) shared across projects — a
new cross-project surface. Entries are keyed by `<name>/<rev>` and HEAD
is re-verified (`git rev-parse`) on every use: a tampered checkout
fails verification and errors rather than being trusted; a checkout is
never repaired or overwritten in place. Creation is guarded by an
advisory `flock` (unix; the non-unix fallback is best-effort, matching
the subprocess process-group cfg split). The bridge cache is
content-keyed (blake3 of the lakefile), so cross-project sharing cannot
serve stale or foreign config. Residual, accepted: running the bridge
(`lake translate-config`) inside a shared checkout lets lake drop its
own `.lake` cache dir there — a benign side effect; the content-keyed
bridge cache makes repeats no-ops.

**Subprocess hygiene.** As established (M2a): explicit argv vectors, no
shell, drained pipes. Build workers get no timeout (a Mathlib module
legitimately elaborates for minutes) and are NOT detached into their
own process group — a terminal Ctrl-C kills leanr and its workers
together. lean's outputs are never parsed by leanr in M2b (decoding
stays in `leanr_olean`, used only by test oracles); setup files are
leanr-written, never read back.
```

- [ ] **Step 3: Commit**

Run: `mise run lint` (doc-only, but keeps the habit).

```bash
git add ARCHITECTURE.md docs/THREAT_MODEL.md
git commit -m "docs: ARCHITECTURE + THREAT_MODEL updates for the M2b orchestrator"
```

---

### Task 9: Differential tier — probe-project oracle vs pinned lake

**Files:**
- Create: `crates/leanr_build/tests/lake_build_oracle.rs`
- Modify: `mise.toml` (`build:differential` runs the new test file too)

**Interfaces:**
- Consumes: the public `leanr_build` API (`resolve`, `compile::build_workspace`, `setup::Layout`) plus real `lake`/`lean` on PATH (elan shims; the repo's `lean-toolchain` is copied into each fixture project so the pin applies).
- Produces: `#[ignore]` tests run by `mise run build:differential`.

- [ ] **Step 1: Write the oracle harness and the five probe cases**

Create `crates/leanr_build/tests/lake_build_oracle.rs`:

```rust
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap()
}

fn write(root: &Path, rel: &str, text: &str) {
    let p = root.join(rel);
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(p, text).unwrap();
}

/// A probe project skeleton with the repo's pinned lean-toolchain.
fn probe(files: &[(&str, &str)]) -> tempfile::TempDir {
    let tmp = tempfile::TempDir::new().unwrap();
    std::fs::copy(repo_root().join("lean-toolchain"), tmp.path().join("lean-toolchain")).unwrap();
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
        lake: leanr_build::bridge::LakeInvoker { toolchain: toolchain.clone(), ..Default::default() },
        toolchain_olean_dir: lean_print_libdir(),
        cache_root: root.join("xdg-cache"), // isolated per probe
    };
    let ws = resolve(root, &opts).unwrap();
    build_workspace(
        &ws,
        &BuildOptions { jobs: 4, lean: LeanInvoker { program: "lean".into(), toolchain } },
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
            lake_side.path().join(".lake/packages").join(&m.package).join(".lake/build/lib/lean")
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
        ("lake-manifest.json", r#"{"version": "1.2.0", "packages": []}"#),
        ("Probe.lean", "import Probe.Basic\ndef two := Probe.one + 1\n"),
        ("Probe/Basic.lean", "namespace Probe\ndef one := 1\nend Probe\n"),
    ]);
}

#[test]
#[ignore]
fn prelude_module_builds_byte_identically() {
    diff_probe(&[
        ("lakefile.toml", BASIC_LAKEFILE),
        ("lake-manifest.json", r#"{"version": "1.2.0", "packages": []}"#),
        ("Probe.lean", "prelude\ndef probeAxiomFree : Nat → Nat := fun n => n\n"),
    ]);
}

#[test]
#[ignore]
fn lean_options_flow_into_the_build() {
    diff_probe(&[
        (
            "lakefile.toml",
            "name = \"probe\"\ndefaultTargets = [\"Probe\"]\n\n[[lean_lib]]\nname = \"Probe\"\n\
             leanOptions = {autoImplicit = false, \"pp.unicode.fun\" = true}\n",
        ),
        ("lake-manifest.json", r#"{"version": "1.2.0", "packages": []}"#),
        ("Probe.lean", "theorem t (n : Nat) : n = n := rfl\n"),
    ]);
}

#[test]
#[ignore]
fn module_system_artifact_family_matches() {
    diff_probe(&[
        ("lakefile.toml", BASIC_LAKEFILE),
        ("lake-manifest.json", r#"{"version": "1.2.0", "packages": []}"#),
        ("Probe.lean", "module\n\ndef x := 1\n"),
    ]);
}

#[test]
#[ignore]
fn git_dependency_builds_byte_identically() {
    // Local origin repo for the dep: no network.
    let dep_origin = tempfile::TempDir::new().unwrap();
    write(dep_origin.path(), "lakefile.toml",
        "name = \"dep\"\ndefaultTargets = [\"Dep\"]\n\n[[lean_lib]]\nname = \"Dep\"\n");
    write(dep_origin.path(), "Dep.lean", "def Dep.answer := 42\n");
    write(dep_origin.path(), "lake-manifest.json", r#"{"version": "1.2.0", "packages": []}"#);
    std::fs::copy(repo_root().join("lean-toolchain"), dep_origin.path().join("lean-toolchain")).unwrap();
    let sh = |cmd: &str| {
        let out = Command::new("sh").arg("-c").arg(cmd).current_dir(dep_origin.path()).output().unwrap();
        assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
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
        ("lakefile.toml", &root_lakefile),
        ("lake-manifest.json", &manifest),
        ("Probe.lean", "import Dep\ndef fortyThree := Dep.answer + 1\n"),
    ]);
}
```

(Adjust the `diff_probe(&[...])` slice literal to accept `&str` values built at runtime for the git case — change the parameter type to `&[(&str, &str)]` callers with owned `String`s using `.as_str()`.)

- [ ] **Step 2: Run against the real toolchain**

Run: `cargo test --release -p leanr_build --test lake_build_oracle -- --ignored --nocapture`
Expected: 5 PASS. Two known adjustment points, verify empirically and fix the *fixture* (never skip the assertion): (a) if the pinned toolchain rejects the minimal `module` file, reshape it to a form pinned Mathlib actually uses (copy the header of any Mathlib module-system file); (b) the manifest JSON must satisfy real lake's schema — if lake rejects it, copy a real entry from `crates/leanr_build/tests/fixtures/mathlib-manifest.json` and adjust fields.

- [ ] **Step 3: Extend the mise task**

In `mise.toml`, `build:differential`'s `run` becomes a list:

```toml
[tasks."build:differential"]
description = "M2 differential oracles vs pinned lake: M2a bridge/import/module-set + M2b probe-project artifact byte-diff (needs mathlib:fetch + elan)"
depends = ["elan:bootstrap"]
run = [
  "sh -c 'LEANR_MATHLIB_DIR=\"$PWD/.mathlib\" LEANR_OLEAN_PATH=\"$(cd .mathlib && lake env printenv LEAN_PATH)\" cargo test --release -p leanr_build --test mathlib_oracle -- --ignored --nocapture'",
  "cargo test --release -p leanr_build --test lake_build_oracle -- --ignored --nocapture",
]
```

- [ ] **Step 4: Run the full differential tier, lint, commit**

Run: `mise run build:differential`
Expected: both test binaries green (first run re-clones the 8 Mathlib deps into the user cache — designed behavior from Task 2).

```bash
git add -A
git commit -m "test(build): M2b differential tier — probe projects byte-diffed against pinned lake"
```

---

### Task 10: Acceptance — full Mathlib closure, fresh clone, byte-diffed

**Files:**
- Modify: `scripts/build-fresh-acceptance.sh` (full rewrite below)
- Modify: `mise.toml` (`build:acceptance` description)
- Modify: `docs/superpowers/specs/2026-07-12-m2b-build-orchestrator-design.md` (append recorded results)

**Interfaces:**
- Consumes: the finished `leanr build` (Task 7), the lake-built artifacts in `.mathlib`.
- Produces: the recorded M2b acceptance run.

- [ ] **Step 1: Rewrite the acceptance script**

Replace `scripts/build-fresh-acceptance.sh` with:

```sh
#!/bin/sh
# M2b acceptance (spec §Testing): fresh clone of pinned Mathlib, isolated
# XDG cache, bare `leanr build` of the full closure; every artifact
# byte-diffed against the lake-built artifacts in .mathlib. Hours of
# compute; network (dependency clones from GitHub); local only, never CI.
# Needs: mathlib:fetch done (lake-built artifacts present), elan toolchain.
set -eu

repo_root=$(cd "$(dirname "$0")/.." && pwd)
sha=$(sed -n '3p' "$repo_root/mathlib-pin")
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT INT TERM

echo "acceptance: building leanr ..." >&2
cargo build --release -p leanr_cli
leanr="$repo_root/target/release/leanr"

echo "acceptance: fresh clone at $sha (tracked files only — no .lake) ..." >&2
git clone -q "$repo_root/.mathlib" "$tmp/mathlib"
git -C "$tmp/mathlib" -c advice.detachedHead=false checkout -q --detach "$sha"
test ! -e "$tmp/mathlib/.lake" || { echo "clone unexpectedly has .lake" >&2; exit 1; }

export XDG_CACHE_HOME="$tmp/xdg"
echo "acceptance: leanr build (full closure — this takes hours) ..." >&2
start=$(date +%s)
(cd "$tmp/mathlib" && "$leanr" build)
end=$(date +%s)
echo "acceptance: build wall time ${start}..${end}: $((end - start))s" >&2

echo "acceptance: byte-diffing artifacts against .mathlib ..." >&2
mismatches="$tmp/mismatches.txt"; : > "$mismatches"
total_file="$tmp/count.txt"; echo 0 > "$total_file"
for pkg_dir in "$tmp/mathlib/.leanr/build"/*/; do
    pkg=$(basename "$pkg_dir")
    if [ "$pkg" = mathlib ]; then
        oracle="$repo_root/.mathlib/.lake/build/lib/lean"
    else
        oracle="$repo_root/.mathlib/.lake/packages/$pkg/.lake/build/lib/lean"
    fi
    [ -d "$pkg_dir/lib" ] || continue
    (cd "$pkg_dir/lib" && find . -type f | sort) | while IFS= read -r f; do
        echo $(($(cat "$total_file") + 1)) > "$total_file"
        cmp -s "$pkg_dir/lib/$f" "$oracle/$f" || echo "$pkg/$f" >> "$mismatches"
    done
done
count=$(cat "$total_file")
if [ -s "$mismatches" ]; then
    echo "acceptance: FAIL — $(wc -l < "$mismatches") of $count artifacts differ:" >&2
    head -50 "$mismatches" >&2
    exit 1
fi
echo "acceptance: PASS — $count artifacts byte-identical to lake's" >&2
echo "acceptance: record wall time, --jobs (default nproc), and module count in the M2b spec" >&2
```

Update the mise task description:

```toml
[tasks."build:acceptance"]
description = "M2b acceptance: fresh clone of pinned Mathlib, full `leanr build`, every artifact byte-diffed vs lake's (hours; network; local only)"
depends = ["elan:bootstrap"]
run = "scripts/build-fresh-acceptance.sh"
```

- [ ] **Step 2: Sanity-run the diff loop cheaply first**

Before the hours-long run, dry-test the script's diff plumbing: temporarily point it at a tiny probe project (or run the Task 9 oracle again) to confirm `cmp` mapping and the counting logic hold. Then run for real:

Run: `mise run build:acceptance` (expect hours; run under `nohup`/background and monitor)
Expected: `acceptance: PASS — <N> artifacts byte-identical to lake's`, exit 0.

If artifacts mismatch: treat as a real divergence — investigate (options, setup content, toolchain), fix, re-run. The spec's documented-divergence fallback (semantic equality via `leanr_olean` decode) may be invoked ONLY for divergences with a verified benign cause, documented in the spec.

- [ ] **Step 3: Record results in the spec**

Append to `docs/superpowers/specs/2026-07-12-m2b-build-orchestrator-design.md`, before `## Constraints (inherited)`:

```markdown
## Acceptance (recorded on completion)

Run: <date>, pod: <describe>. `mise run build:acceptance`:
- fresh clone at <sha>, XDG cache isolated;
- `leanr build` of <N> modules, --jobs <J>, wall time <T>;
- <count> artifacts byte-diffed against lake's — <mismatches> mismatches;
- `cargo test --workspace`, `mise run lint`, and `mise run build:differential`
  all green at this commit.
```

(fill every `<placeholder>` with the actual run's numbers — a placeholder left in the spec is a task failure).

- [ ] **Step 4: Full gate and final commit**

Run: `mise run ci`
Expected: green.

```bash
git add -A
git commit -m "feat: M2b acceptance — full Mathlib closure built and byte-verified against lake"
```

---

## Plan Self-Review (performed at write time)

- **Spec coverage:** libraries-only artifacts (Tasks 4/6 — no `-c`), unconditional rebuilds (no skip logic anywhere), XDG sources + flock + immutability (Task 2), bridge cache to XDG (Task 1), project-local artifacts (Task 4), pool fail-fast + seam (Tasks 5/6), diagnostics + failure deletion (Task 6), `--jobs`/progress/summary (Task 7), unsupported-feature guard (Task 6), docs (Task 8), unit/differential/acceptance tiers + mise tasks (Tasks 2–10). JSON plan revision (Task 2).
- **Known deliberate deviation to verify at Task 4/9:** the spec allows toolchain entries in `importArts`; lake empirically omits them — the plan matches lake (omission), and the Task 9 oracle arbitrates.
- **Type consistency:** `ResolveOptions.cache_root` (Tasks 1→2→4 testws→9), `LibUnit.lib`/`ModuleInfo.lib` (Task 3→4), `Layout`/`module_setup`/`lean_path_env` (Task 4→6→9), `pool::run` signature (Task 5→6), `BuildOptions`/`LeanInvoker`/`BuiltEvent` (Task 6→7→9).
