# M2c — Content-Addressed Cache & Incremental Builds Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `leanr build` cache-aware — a module whose complete input surface is unchanged is served from a shared content-addressed store instead of re-running `lean` — plus `leanr cache verify`/`gc`.

**Architecture:** Two new pure/IO modules in `leanr_build` (`fingerprint`, `cache`), wired into M2b's existing `pool` job seam ("module ready → run job → outcome"). The scheduler, `setup::Layout`, and `subprocess` layers are reused unchanged. A recursive content-Merkle fingerprint keys a per-user CAS under XDG; the project's `.leanr/build/<pkg>/lib` is materialized (hardlink, copy fallback) from it.

**Tech Stack:** Rust; `blake3` (already a dep) for content hashing; `serde`/`serde_json` for manifests; `libc` `flock` (unix, already a dep) for write serialization; `std::thread::scope` pool (existing).

## Global Constraints

- `leanr_build` stays **off the kernel dependency graph** and gains **no new workspace-crate deps** (AGENTS.md; ARCHITECTURE.md). No new external crate without justification — everything here uses crates already in `crates/leanr_build/Cargo.toml` (`blake3`, `serde`, `serde_json`, `libc`; dev-deps `tempfile`, `proptest`).
- **Staleness-correctness is release-blocking.** An under-inclusive fingerprint (a changed input that fails to invalidate a dependent) is a correctness bug, not a perf bug (ARCHITECTURE.md §Risks). The staleness harness (Task 9) gates this.
- **Untrusted-bytes discipline:** parsers never panic on arbitrary bytes (`docs/THREAT_MODEL.md`). Cache manifests are our own output in M2c but become the seam M2d ingests untrusted remote blobs through — so blob reads use content-hash verification and manifest parsing tolerates garbage (returns a miss/error, never panics).
- **flock is unix-only** with a documented `cfg(not(unix))` no-lock fallback, matching `fetch.rs`/`subprocess.rs`.
- **All CLI logic is arg-parsing + printing only** — build/cache logic lives in `leanr_build`, never `leanr_cli` (ARCHITECTURE.md: "logic in `leanr_cli` is a bug").
- **Workflows are mise tasks;** CI runs `mise run ci`. New gated tests get a named task.
- Spec: `docs/superpowers/specs/2026-07-12-m2c-cache-incremental-design.md`.

---

## File Structure

- **Create `crates/leanr_build/src/fslock.rs`** — the advisory-lock helper extracted from `fetch.rs` (shared by `fetch` and `cache`).
- **Create `crates/leanr_build/src/fingerprint.rs`** — `FingerprintEnv`, the domain-separated hash primitive, and `fingerprint_all(ws, env)`.
- **Create `crates/leanr_build/src/cache.rs`** — the CAS: blob store, module manifests, `lookup`/`insert`/`materialize`, `verify`, `deep_verify`, `gc`.
- **Modify `crates/leanr_build/src/fetch.rs`** — use `fslock::lock_exclusive`.
- **Modify `crates/leanr_build/src/compile.rs`** — cache-aware job; `BuildReport { built, cached }`; `BuiltEvent.cached`.
- **Modify `crates/leanr_build/src/lib.rs`** — declare `fslock`, `fingerprint`, `cache` modules.
- **Modify `crates/leanr_cli/src/main.rs`** — `build --no-cache/--force`; `cache verify [--deep]` / `cache gc --max-size`.
- **Create `crates/leanr_build/tests/cache_incremental.rs`** — the staleness-correctness harness.
- **Modify `mise.toml`** — `cache:incremental` task; extend acceptance.
- **Modify `scripts/build-fresh-acceptance.sh`, `ARCHITECTURE.md`, `docs/THREAT_MODEL.md`.**

---

### Task 1: Extract the advisory-lock helper into `fslock`

DRY: `cache` needs the same `flock` helper `fetch` already has (currently private in `fetch.rs`). Extract it verbatim so both share one tested copy.

**Files:**
- Create: `crates/leanr_build/src/fslock.rs`
- Modify: `crates/leanr_build/src/lib.rs` (add `mod fslock;`)
- Modify: `crates/leanr_build/src/fetch.rs:157-172` (delete local `lock_exclusive`, call `fslock::lock_exclusive`)

**Interfaces:**
- Produces: `pub(crate) fn fslock::lock_exclusive(path: &Path) -> std::io::Result<std::fs::File>` — advisory exclusive lock held until the returned file drops.

- [ ] **Step 1: Create `fslock.rs` with the helper moved out of `fetch.rs`**

```rust
//! Advisory exclusive file lock shared by the git-source cache (`fetch`)
//! and the artifact CAS (`cache`). Unix `flock`; the `cfg(not(unix))`
//! fallback creates the lock file without holding a lock (same cfg split
//! as `subprocess.rs`'s process-group kill — callers still double-check
//! the guarded invariant after acquisition).

use std::path::Path;

/// Take an advisory exclusive lock on `path` (created if absent),
/// released when the returned file is dropped.
pub(crate) fn lock_exclusive(path: &Path) -> std::io::Result<std::fs::File> {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lock_is_created_and_reacquirable_after_drop() {
        let tmp = tempfile::TempDir::new().unwrap();
        let p = tmp.path().join("x.lock");
        {
            let _g = lock_exclusive(&p).unwrap();
            assert!(p.exists());
        }
        // Dropped — a second acquisition must not deadlock.
        let _g2 = lock_exclusive(&p).unwrap();
    }
}
```

- [ ] **Step 2: Add the module to `lib.rs`**

In `crates/leanr_build/src/lib.rs`, in the module block (near `pub mod fetch;`), add:

```rust
mod fslock;
```

- [ ] **Step 3: Point `fetch.rs` at the shared helper**

In `crates/leanr_build/src/fetch.rs`, delete the local `fn lock_exclusive(...) { ... }` (lines ~151-172, keep its doc-comment intent in `fslock`) and change its single call site (`ensure_git`, ~line 219) from `lock_exclusive(&lock_path)` to `crate::fslock::lock_exclusive(&lock_path)`.

- [ ] **Step 4: Build and run the affected tests**

Run: `cargo test -p leanr_build fslock:: fetch::`
Expected: PASS (fetch's `concurrent_materialize_of_the_same_rev_races_safely` still green; new `lock_is_created_and_reacquirable_after_drop` passes).

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_build/src/fslock.rs crates/leanr_build/src/lib.rs crates/leanr_build/src/fetch.rs
git commit -m "refactor(build): extract shared advisory-lock helper into fslock"
```

---

### Task 2: Fingerprint env + the domain-separated hash primitive

The pure core: given a module's already-serialized input components, produce its fingerprint. No graph/IO here — trivially testable.

**Files:**
- Create: `crates/leanr_build/src/fingerprint.rs`
- Modify: `crates/leanr_build/src/lib.rs` (add `pub mod fingerprint;`)

**Interfaces:**
- Produces:
  - `pub struct FingerprintEnv { pub leanr_version: String, pub toolchain_id: String, pub platform: String }`
  - `pub type Fingerprint = String;` (lowercase 64-char blake3 hex)
  - `pub(crate) fn hash_module(env: &FingerprintEnv, provenance: &[u8], source: &[u8], setup_inputs: &[u8], import_fps: &[String]) -> Fingerprint` — `import_fps` MUST be caller-sorted `"{name}\u{0}{fp}"` strings.

- [ ] **Step 1: Write the failing tests**

Create `crates/leanr_build/src/fingerprint.rs`:

```rust
//! Recursive content-Merkle fingerprint (M2c spec §Fingerprint). A
//! module's key folds in its source, semantic setup inputs, toolchain,
//! leanr's own version, its owning package's provenance (git rev, or
//! declared custom inputs for root/path deps), and the *fingerprints* of
//! its direct imports — so one fixed-size hash captures the whole
//! transitive input closure. Pure content (no mtimes): reproducible
//! across machines and worktrees, which is what a shared CAS needs.

use crate::graph::ModuleId;
use crate::setup::Layout;
use crate::Workspace;

/// Ambient inputs shared by every module in a build.
pub struct FingerprintEnv {
    /// Stable leanr release/commit id (never a per-build nonce) — an
    /// upgrade invalidates the whole cache (spec §Scope decisions).
    pub leanr_version: String,
    /// The pinned `lean-toolchain` string.
    pub toolchain_id: String,
    /// Target platform tag (arch-os).
    pub platform: String,
}

/// Lowercase 64-char blake3 hex.
pub type Fingerprint = String;

/// Domain-separated, length-prefixed field write: `blake3` over a field
/// stream where each field is `len(u64-LE) || bytes`, so no two distinct
/// component tuples can collide by concatenation ambiguity.
fn put(h: &mut blake3::Hasher, field: &[u8]) {
    h.update(&(field.len() as u64).to_le_bytes());
    h.update(field);
}

pub(crate) fn hash_module(
    env: &FingerprintEnv,
    provenance: &[u8],
    source: &[u8],
    setup_inputs: &[u8],
    import_fps: &[String],
) -> Fingerprint {
    let mut h = blake3::Hasher::new();
    put(&mut h, b"leanr-m2c-fingerprint-v1"); // DOMAIN_TAG + FP_SCHEMA_VERSION
    put(&mut h, env.leanr_version.as_bytes());
    put(&mut h, env.toolchain_id.as_bytes());
    put(&mut h, env.platform.as_bytes());
    put(&mut h, provenance);
    put(&mut h, source);
    put(&mut h, setup_inputs);
    put(&mut h, &(import_fps.len() as u64).to_le_bytes());
    for imp in import_fps {
        put(&mut h, imp.as_bytes());
    }
    h.finalize().to_hex().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn env() -> FingerprintEnv {
        FingerprintEnv {
            leanr_version: "0.1.0".into(),
            toolchain_id: "leanprover/lean4:v4.32.0-rc1".into(),
            platform: "x86_64-linux".into(),
        }
    }

    #[test]
    fn deterministic_and_64_hex() {
        let a = hash_module(&env(), b"p", b"src", b"{}", &["A\u{0}ff".into()]);
        let b = hash_module(&env(), b"p", b"src", b"{}", &["A\u{0}ff".into()]);
        assert_eq!(a, b);
        assert_eq!(a.len(), 64);
        assert!(a.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn every_component_changes_the_hash() {
        let base = hash_module(&env(), b"p", b"src", b"{}", &["A\u{0}ff".into()]);
        let mut e2 = env();
        e2.leanr_version = "0.2.0".into();
        assert_ne!(base, hash_module(&e2, b"p", b"src", b"{}", &["A\u{0}ff".into()]));
        let mut e3 = env();
        e3.toolchain_id = "other".into();
        assert_ne!(base, hash_module(&e3, b"p", b"src", b"{}", &["A\u{0}ff".into()]));
        assert_ne!(base, hash_module(&env(), b"q", b"src", b"{}", &["A\u{0}ff".into()]));
        assert_ne!(base, hash_module(&env(), b"p", b"src2", b"{}", &["A\u{0}ff".into()]));
        assert_ne!(base, hash_module(&env(), b"p", b"src", b"{\"x\":1}", &["A\u{0}ff".into()]));
        assert_ne!(base, hash_module(&env(), b"p", b"src", b"{}", &["A\u{0}00".into()]));
    }

    #[test]
    fn length_prefixing_blocks_boundary_collisions() {
        // ("ab","c") must not equal ("a","bc").
        let x = hash_module(&env(), b"ab", b"c", b"{}", &[]);
        let y = hash_module(&env(), b"a", b"bc", b"{}", &[]);
        assert_ne!(x, y);
    }
}
```

- [ ] **Step 2: Add module and dev-dep visibility, run tests to confirm they fail then pass**

In `crates/leanr_build/src/lib.rs` add `pub mod fingerprint;` (near `pub mod fetch;`).

Run: `cargo test -p leanr_build fingerprint::`
Expected: PASS (this task's primitive has no missing deps; `graph`/`setup`/`Workspace` imports are used by Task 3, add them there — for Step 1 remove the three unused `use` lines if the compiler warns, or leave and let Task 3 use them). If `use crate::graph::ModuleId;` etc. warn as unused, delete those three `use` lines now; Task 3 re-adds them.

- [ ] **Step 3: Commit**

```bash
git add crates/leanr_build/src/fingerprint.rs crates/leanr_build/src/lib.rs
git commit -m "feat(build): M2c fingerprint hash primitive (domain-separated, length-prefixed)"
```

---

### Task 3: `fingerprint_all` over the module graph (provenance + Merkle recursion)

Wire the graph into per-module fingerprints in topological order using `ws.waves` (imports are always fingerprinted before their dependents).

**Files:**
- Modify: `crates/leanr_build/src/fingerprint.rs`

**Interfaces:**
- Consumes: `Workspace { root, deps, graph, waves }` (lib.rs); `graph::ModuleInfo { name, package, deps, is_module, file }`; `setup::module_setup`; `ResolvedPackage { rev, config }`.
- Produces: `pub fn fingerprint_all(ws: &Workspace, env: &FingerprintEnv) -> Result<Vec<Fingerprint>, crate::BuildError>` — indexed by `ModuleId.0 as usize`.

- [ ] **Step 1: Write the failing tests (append to `fingerprint.rs`'s test module)**

```rust
    use crate::testws;

    #[test]
    fn leaf_and_dependent_get_distinct_fingerprints() {
        let t = testws::synthetic();
        let fps = fingerprint_all(&t.ws, &env()).unwrap();
        assert_eq!(fps.len(), t.ws.graph.modules.len());
        assert!(fps.iter().all(|f| f.len() == 64));
        // App imports App.Sub — distinct sources ⇒ distinct fingerprints.
        assert_ne!(fps[0], fps[1]);
    }

    #[test]
    fn changing_an_import_changes_the_dependent() {
        // App -> App.Sub. Editing App.Sub's source must change App's fp
        // (Merkle recursion), not just App.Sub's.
        let t1 = testws::synthetic();
        let before = fingerprint_all(&t1.ws, &env()).unwrap();
        let app = t1.ws.graph.id_of(&crate::modules::ModuleName::parse("App").unwrap()).unwrap();
        let sub = t1.ws.graph.id_of(&crate::modules::ModuleName::parse("App.Sub").unwrap()).unwrap();
        // Rewrite App.Sub.lean in the synthetic workspace, re-resolve.
        std::fs::write(&t1.ws.graph.modules[sub.0 as usize].file, "-- edited\n").unwrap();
        let after = fingerprint_all(&t1.ws, &env()).unwrap();
        assert_ne!(before[sub.0 as usize], after[sub.0 as usize], "leaf fp changes");
        assert_ne!(before[app.0 as usize], after[app.0 as usize], "dependent fp changes (Merkle)");
    }

    #[test]
    fn declared_input_file_enters_root_provenance() {
        let t = testws::synthetic();
        let base = fingerprint_all(&t.ws, &env()).unwrap();
        let mut t2 = testws::synthetic();
        t2.ws.root.config.input_file =
            Some(vec![toml::Value::String("widget.js".into())]);
        let changed = fingerprint_all(&t2.ws, &env()).unwrap();
        // Root package's modules must re-fingerprint when its declared
        // custom inputs change.
        assert_ne!(base[0], changed[0]);
    }
```

Note: the git-dep **rev** provenance axis is exercised by the staleness harness (Task 9), which builds a workspace whose module carries a `rev`; `synthetic()` has no git deps.

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_build fingerprint::changing_an_import_changes_the_dependent`
Expected: FAIL ("cannot find function `fingerprint_all`").

- [ ] **Step 3: Implement `fingerprint_all` and provenance**

Add to `fingerprint.rs` (restore the `use crate::graph::ModuleId; use crate::setup::Layout; use crate::Workspace;` lines at the top if Task 2 removed them):

```rust
use crate::graph::ModuleInfo;
use crate::ResolvedPackage;

/// Owning-package provenance for a module's fingerprint.
/// - git dep (rev = Some): the pinned rev captures the entire immutable
///   rev-keyed checkout (incl. committed non-`.lean` compile inputs like
///   ProofWidgets' JS) by reference — sound because `fetch::verify_checkout`
///   guarantees rev == checkout bytes.
/// - root / path dep (rev = None): the serialized declared custom inputs
///   (`input_file`/`input_dir`); a lean_lib module's compile otherwise
///   reads only its `.lean` source + imports, both already in the key.
fn owner_provenance(pkg: &ResolvedPackage) -> Vec<u8> {
    match &pkg.rev {
        Some(rev) => {
            let mut v = b"rev\0".to_vec();
            v.extend_from_slice(rev.as_bytes());
            v
        }
        None => {
            let decls = serde_json::to_vec(&(&pkg.config.input_file, &pkg.config.input_dir))
                .unwrap_or_default();
            let mut v = b"inputs\0".to_vec();
            v.extend_from_slice(&decls);
            v
        }
    }
}

/// Canonical semantic setup inputs (spec §Fingerprint): options,
/// isModule, plugins, dynlibs — NOT the machine-specific importArts paths
/// (import identity enters via the recursive import fps instead).
fn setup_inputs_bytes(ws: &Workspace, layout: &Layout, id: ModuleId) -> Vec<u8> {
    let s = crate::setup::module_setup(ws, layout, id);
    serde_json::to_vec(&serde_json::json!({
        "options": s.options,
        "isModule": s.is_module,
        "plugins": s.plugins,
        "dynlibs": s.dynlibs,
    }))
    .expect("setup inputs serialize")
}

pub fn fingerprint_all(
    ws: &Workspace,
    env: &FingerprintEnv,
) -> Result<Vec<Fingerprint>, crate::BuildError> {
    let layout = Layout::new(&ws.root_dir);
    let n = ws.graph.modules.len();
    let mut fps: Vec<Option<Fingerprint>> = vec![None; n];
    // Provenance per package, computed once.
    let provenance_of = |m: &ModuleInfo| -> Vec<u8> {
        let pkg = std::iter::once(&ws.root)
            .chain(ws.deps.iter())
            .find(|p| p.name == m.package);
        pkg.map(owner_provenance).unwrap_or_default()
    };
    // `waves` is a topological layering: every dep of a wave-k module is
    // in a wave < k, so its fp is already computed.
    for wave in &ws.waves {
        for &id in wave {
            let i = id.0 as usize;
            let m = &ws.graph.modules[i];
            let source = std::fs::read(&m.file).map_err(|e| crate::BuildError::Io {
                path: m.file.clone(),
                err: e.to_string(),
            })?;
            let mut import_fps: Vec<String> = m
                .deps
                .iter()
                .map(|d| {
                    let dm = &ws.graph.modules[d.0 as usize];
                    let fp = fps[d.0 as usize]
                        .as_ref()
                        .expect("import fingerprinted before dependent (topo waves)");
                    format!("{}\u{0}{}", dm.name, fp)
                })
                .collect();
            import_fps.sort();
            let fp = hash_module(
                env,
                &provenance_of(m),
                &source,
                &setup_inputs_bytes(ws, &layout, id),
                &import_fps,
            );
            fps[i] = Some(fp);
        }
    }
    Ok(fps.into_iter().map(|f| f.expect("every module in some wave")).collect())
}
```

- [ ] **Step 4: Run the tests**

Run: `cargo test -p leanr_build fingerprint::`
Expected: PASS (all five fingerprint tests).

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_build/src/fingerprint.rs
git commit -m "feat(build): fingerprint_all — Merkle recursion over the module graph + provenance"
```

---

### Task 4: CAS blob store (content-addressed put/get)

**Files:**
- Create: `crates/leanr_build/src/cache.rs`
- Modify: `crates/leanr_build/src/lib.rs` (add `pub mod cache;`)

**Interfaces:**
- Produces:
  - `pub struct Cache { root: PathBuf }`
  - `pub fn Cache::new(cache_root: &Path) -> Cache` — `root = cache_root.join("cache")`.
  - `pub fn store_blob(&self, bytes: &[u8]) -> std::io::Result<String>` — returns lowercase hex; idempotent; blob is read-only.
  - `pub fn blob_path(&self, hex: &str) -> PathBuf` — `root/blobs/<aa>/<hex>`.

- [ ] **Step 1: Write the failing tests**

Create `crates/leanr_build/src/cache.rs`:

```rust
//! Content-addressed artifact store (M2c spec §Layout, §Architecture
//! `cache`). Two levels: a module manifest keyed by fingerprint names the
//! artifact family; each member points at a content blob keyed by the
//! blake3 of its own bytes. Immutable, sharded, flock-guarded, atomic
//! writes. Lives at `$XDG_CACHE_HOME/leanr/cache/` alongside M2b's
//! `src/` and `config-cache/`.

use std::path::{Path, PathBuf};

pub struct Cache {
    root: PathBuf,
}

fn shard(hex: &str) -> &str {
    &hex[..2]
}

/// Write `bytes` to `path` atomically (temp sibling + rename), flock-
/// guarded on `path.lock`, leaving the file read-only. A concurrent
/// writer of identical content races safely (rename is atomic).
fn write_atomic_readonly(path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    let parent = path.parent().expect("cache path has a parent");
    std::fs::create_dir_all(parent)?;
    let lock = path.with_extension("lock");
    let _g = crate::fslock::lock_exclusive(&lock)?;
    if path.exists() {
        return Ok(()); // content-addressed: already present, identical bytes.
    }
    let tmp = path.with_extension("tmp");
    std::fs::write(&tmp, bytes)?;
    let mut perms = std::fs::metadata(&tmp)?.permissions();
    perms.set_readonly(true);
    std::fs::set_permissions(&tmp, perms)?;
    std::fs::rename(&tmp, path)?;
    Ok(())
}

impl Cache {
    pub fn new(cache_root: &Path) -> Cache {
        Cache { root: cache_root.join("cache") }
    }

    pub fn blob_path(&self, hex: &str) -> PathBuf {
        self.root.join("blobs").join(shard(hex)).join(hex)
    }

    pub fn store_blob(&self, bytes: &[u8]) -> std::io::Result<String> {
        let hex = blake3::hash(bytes).to_hex().to_string();
        let path = self.blob_path(&hex);
        write_atomic_readonly(&path, bytes)?;
        Ok(hex)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cache() -> (tempfile::TempDir, Cache) {
        let tmp = tempfile::TempDir::new().unwrap();
        let c = Cache::new(tmp.path());
        (tmp, c)
    }

    #[test]
    fn store_blob_is_content_addressed_and_idempotent() {
        let (_t, c) = cache();
        let h1 = c.store_blob(b"hello olean").unwrap();
        let h2 = c.store_blob(b"hello olean").unwrap();
        assert_eq!(h1, h2);
        assert_eq!(h1, blake3::hash(b"hello olean").to_hex().to_string());
        assert_eq!(std::fs::read(c.blob_path(&h1)).unwrap(), b"hello olean");
    }

    #[test]
    fn blob_is_sharded_and_read_only() {
        let (_t, c) = cache();
        let h = c.store_blob(b"x").unwrap();
        let p = c.blob_path(&h);
        assert!(p.parent().unwrap().ends_with(&h[..2]));
        assert!(std::fs::metadata(&p).unwrap().permissions().readonly());
    }
}
```

- [ ] **Step 2: Register module, run to verify pass**

Add `pub mod cache;` to `lib.rs`.
Run: `cargo test -p leanr_build cache::`
Expected: PASS.

- [ ] **Step 3: Commit**

```bash
git add crates/leanr_build/src/cache.rs crates/leanr_build/src/lib.rs
git commit -m "feat(build): CAS blob store — content-addressed, sharded, atomic, read-only"
```

---

### Task 5: Module manifests — `insert` / `lookup`

**Files:**
- Modify: `crates/leanr_build/src/cache.rs`

**Interfaces:**
- Produces:
  - `#[derive(Serialize, Deserialize, PartialEq, Debug)] pub struct ArtifactEntry { pub name: String, pub blob: String }`
  - `pub struct Manifest { pub artifacts: Vec<ArtifactEntry> }`
  - `pub fn insert(&self, fp: &str, artifacts: &[PathBuf]) -> std::io::Result<Manifest>` — reads each artifact file, stores its blob, records `(basename, blob)` in the given order; writes `modules/<aa>/<fp>.json`.
  - `pub fn lookup(&self, fp: &str) -> std::io::Result<Option<Manifest>>` — `None` if the manifest is absent, unparseable, or references a missing blob (self-healing miss).
  - `pub fn manifest_path(&self, fp: &str) -> PathBuf`

- [ ] **Step 1: Write the failing tests (append to `cache.rs` tests)**

```rust
    fn write(p: &Path, b: &[u8]) {
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, b).unwrap();
    }

    #[test]
    fn insert_then_lookup_roundtrips() {
        let (t, c) = cache();
        let a = t.path().join("A.olean");
        let b = t.path().join("A.ilean");
        write(&a, b"olean-bytes");
        write(&b, b"ilean-bytes");
        let m = c.insert("deadbeef", &[a.clone(), b.clone()]).unwrap();
        assert_eq!(m.artifacts.len(), 2);
        assert_eq!(m.artifacts[0].name, "A.olean");
        let got = c.lookup("deadbeef").unwrap().unwrap();
        assert_eq!(got.artifacts, m.artifacts);
    }

    #[test]
    fn lookup_miss_is_none() {
        let (_t, c) = cache();
        assert!(c.lookup("nope").unwrap().is_none());
    }

    #[test]
    fn lookup_with_a_missing_blob_is_a_self_healing_miss() {
        let (t, c) = cache();
        let a = t.path().join("A.olean");
        write(&a, b"olean-bytes");
        let m = c.insert("cafe", &[a]).unwrap();
        std::fs::remove_file(c.blob_path(&m.artifacts[0].blob)).unwrap();
        assert!(c.lookup("cafe").unwrap().is_none());
    }

    #[test]
    fn corrupt_manifest_json_is_a_miss_not_a_panic() {
        let (_t, c) = cache();
        let p = c.manifest_path("beef");
        write(&p, b"{ this is not json");
        assert!(c.lookup("beef").unwrap().is_none());
    }
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_build cache::insert_then_lookup_roundtrips`
Expected: FAIL ("no method named `insert`").

- [ ] **Step 3: Implement manifests**

Add to `cache.rs` (add `use serde::{Deserialize, Serialize};` at the top):

```rust
#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct ArtifactEntry {
    pub name: String,
    pub blob: String,
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct Manifest {
    pub artifacts: Vec<ArtifactEntry>,
}

impl Cache {
    pub fn manifest_path(&self, fp: &str) -> PathBuf {
        self.root.join("modules").join(shard(fp)).join(format!("{fp}.json"))
    }

    pub fn insert(&self, fp: &str, artifacts: &[PathBuf]) -> std::io::Result<Manifest> {
        let mut entries = Vec::with_capacity(artifacts.len());
        for art in artifacts {
            let bytes = std::fs::read(art)?;
            let blob = self.store_blob(&bytes)?;
            let name = art
                .file_name()
                .map(|s| s.to_string_lossy().into_owned())
                .unwrap_or_default();
            entries.push(ArtifactEntry { name, blob });
        }
        let manifest = Manifest { artifacts: entries };
        let json = serde_json::to_vec(&manifest).expect("manifest serializes");
        write_atomic_readonly(&self.manifest_path(fp), &json)?;
        Ok(manifest)
    }

    pub fn lookup(&self, fp: &str) -> std::io::Result<Option<Manifest>> {
        let path = self.manifest_path(fp);
        let bytes = match std::fs::read(&path) {
            Ok(b) => b,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e),
        };
        // Untrusted-bytes discipline: a malformed manifest is a miss.
        let manifest: Manifest = match serde_json::from_slice(&bytes) {
            Ok(m) => m,
            Err(_) => return Ok(None),
        };
        if manifest.artifacts.iter().any(|a| !self.blob_path(&a.blob).exists()) {
            return Ok(None);
        }
        Ok(Some(manifest))
    }
}
```

- [ ] **Step 4: Run the tests**

Run: `cargo test -p leanr_build cache::`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_build/src/cache.rs
git commit -m "feat(build): CAS module manifests — insert/lookup with self-healing misses"
```

---

### Task 6: Materialize artifacts from the store into the project layout

**Files:**
- Modify: `crates/leanr_build/src/cache.rs`

**Interfaces:**
- Produces: `pub fn materialize(&self, manifest: &Manifest, dests: &[PathBuf]) -> std::io::Result<()>` — hardlink each blob to the corresponding dest (copy fallback across mounts); overwrites an existing dest; `dests` must match `manifest.artifacts` in order/length (caller passes `layout.artifact_paths(pkg, m)`).

- [ ] **Step 1: Write the failing tests (append to `cache.rs` tests)**

```rust
    #[test]
    fn materialize_recreates_every_artifact() {
        let (t, c) = cache();
        let a = t.path().join("A.olean");
        let b = t.path().join("A.ilean");
        write(&a, b"olean-bytes");
        write(&b, b"ilean-bytes");
        let m = c.insert("d00d", &[a.clone(), b.clone()]).unwrap();
        let out = t.path().join("proj");
        let da = out.join("A.olean");
        let db = out.join("A.ilean");
        c.materialize(&m, &[da.clone(), db.clone()]).unwrap();
        assert_eq!(std::fs::read(&da).unwrap(), b"olean-bytes");
        assert_eq!(std::fs::read(&db).unwrap(), b"ilean-bytes");
    }

    #[test]
    fn materialize_overwrites_a_pre_existing_dest() {
        let (t, c) = cache();
        let a = t.path().join("A.olean");
        write(&a, b"fresh");
        let m = c.insert("f00d", &[a]).unwrap();
        let dest = t.path().join("out/A.olean");
        write(&dest, b"stale-and-readonly");
        let mut perms = std::fs::metadata(&dest).unwrap().permissions();
        perms.set_readonly(true);
        std::fs::set_permissions(&dest, perms).unwrap();
        c.materialize(&m, &[dest.clone()]).unwrap();
        assert_eq!(std::fs::read(&dest).unwrap(), b"fresh");
    }
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_build cache::materialize_recreates_every_artifact`
Expected: FAIL ("no method named `materialize`").

- [ ] **Step 3: Implement**

Add to `cache.rs`'s `impl Cache`:

```rust
    pub fn materialize(&self, manifest: &Manifest, dests: &[PathBuf]) -> std::io::Result<()> {
        assert_eq!(
            manifest.artifacts.len(),
            dests.len(),
            "manifest/dest arity mismatch — caller must pass layout.artifact_paths order"
        );
        for (entry, dest) in manifest.artifacts.iter().zip(dests) {
            let blob = self.blob_path(&entry.blob);
            if let Some(parent) = dest.parent() {
                std::fs::create_dir_all(parent)?;
            }
            // Overwrite: a prior materialization left a read-only hardlink.
            if dest.exists() {
                std::fs::remove_file(dest)?;
            }
            match std::fs::hard_link(&blob, dest) {
                Ok(()) => {}
                // Cross-device (EXDEV) or other link failure: copy instead.
                Err(_) => {
                    std::fs::copy(&blob, dest)?;
                }
            }
        }
        Ok(())
    }
```

- [ ] **Step 4: Run the tests**

Run: `cargo test -p leanr_build cache::`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_build/src/cache.rs
git commit -m "feat(build): materialize CAS artifacts into the project layout (hardlink, copy fallback)"
```

---

### Task 7: Cache-aware build job (`compile.rs` integration)

Insert cache lookup/insert at the M2b `pool` seam; split the report into `built` vs `cached`.

**Files:**
- Modify: `crates/leanr_build/src/compile.rs`

**Interfaces:**
- Consumes: `cache::Cache`, `fingerprint::{FingerprintEnv, fingerprint_all}`, `setup::Layout::artifact_paths`.
- Produces (changed):
  - `pub struct BuildReport { pub built: usize, pub cached: usize }`
  - `pub struct BuildOptions { pub jobs: usize, pub lean: LeanInvoker, pub cache: Option<cache::Cache>, pub force: bool, pub fp_env: fingerprint::FingerprintEnv }`
  - `pub struct BuiltEvent<'a> { ..., pub cached: bool }`

- [ ] **Step 1: Write the failing tests (append to `compile.rs` tests)**

```rust
    use crate::cache::Cache;
    use crate::fingerprint::FingerprintEnv;

    fn fp_env() -> FingerprintEnv {
        FingerprintEnv {
            leanr_version: "test".into(),
            toolchain_id: "test-tc".into(),
            platform: "test-plat".into(),
        }
    }

    fn opts(jobs: usize, cache: Option<Cache>, force: bool) -> BuildOptions {
        BuildOptions { jobs, lean: fake_lean(), cache, force, fp_env: fp_env() }
    }

    #[test]
    fn cold_build_populates_then_warm_build_is_all_cached() {
        let _guard = ENV_GUARD.lock().unwrap_or_else(|e| e.into_inner());
        let t = testws::synthetic();
        let xdg = tempfile::TempDir::new().unwrap();
        let cold = build_workspace(&t.ws, &opts(1, Some(Cache::new(xdg.path())), false), &|_| {}).unwrap();
        assert_eq!((cold.built, cold.cached), (2, 0));
        // Second build over the same cache: zero lean runs.
        let warm = build_workspace(&t.ws, &opts(1, Some(Cache::new(xdg.path())), false), &|_| {}).unwrap();
        assert_eq!((warm.built, warm.cached), (0, 2));
    }

    #[test]
    fn force_reruns_lean_even_on_a_full_cache() {
        let _guard = ENV_GUARD.lock().unwrap_or_else(|e| e.into_inner());
        let t = testws::synthetic();
        let xdg = tempfile::TempDir::new().unwrap();
        build_workspace(&t.ws, &opts(1, Some(Cache::new(xdg.path())), false), &|_| {}).unwrap();
        let forced = build_workspace(&t.ws, &opts(1, Some(Cache::new(xdg.path())), true), &|_| {}).unwrap();
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
        assert!(!Cache::new(xdg.path()).blob_path("00").parent().unwrap().parent().unwrap().exists());
    }
```

Also update the three existing tests' `BuildOptions { jobs, lean }` literals and `report.built` assertions: change each `BuildOptions { jobs: N, lean: fake_lean() }` to `opts(N, None, false)`, and `assert_eq!(report.built, 2)` stays valid (no-cache path).

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_build compile::cold_build_populates`
Expected: FAIL (BuildOptions has no `cache` field).

- [ ] **Step 3: Update the structs**

In `compile.rs`, replace the `BuildOptions`, `BuildReport`, and `BuiltEvent` definitions:

```rust
pub struct BuildOptions {
    pub jobs: usize,
    pub lean: LeanInvoker,
    /// `None` = `--no-cache` (M2b's pure unconditional path). `Some` =
    /// cache-aware; with `force`, always run `lean` then refresh the cache.
    pub cache: Option<crate::cache::Cache>,
    pub force: bool,
    pub fp_env: crate::fingerprint::FingerprintEnv,
}

#[derive(Debug)]
pub struct BuildReport {
    pub built: usize,
    pub cached: usize,
}
```

And add `pub cached: bool,` to `BuiltEvent`.

- [ ] **Step 4: Rework `build_workspace`'s job + tally**

In `build_workspace`, after the setup-file-writing loop and `lean_path`/`deps` setup, compute fingerprints when caching is on and add an outcomes vector:

```rust
    let fps = match &opts.cache {
        Some(_) => Some(crate::fingerprint::fingerprint_all(ws, &opts.fp_env)?),
        None => None,
    };
    #[derive(Clone, Copy, PartialEq)]
    enum Outcome { Built, Cached }
    let outcomes: Mutex<Vec<Outcome>> = Mutex::new(vec![Outcome::Built; ws.graph.modules.len()]);
```

Then, inside the `job` closure, before spawning `lean`, add the cache fast-path and record the outcome. Insert at the top of the closure body (after `let m = &ws.graph.modules[i];`):

```rust
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
```

And in the `Ok(f) if f.status.success()` arm, after recording `results[i]`, insert the built artifacts into the cache (they are already at `dests`, freshly written by `lean`):

```rust
                if let (Some(cache), Some(fps)) = (opts.cache.as_ref(), fps.as_ref()) {
                    if let Err(e) = cache.insert(&fps[i], &dests) {
                        return Err(format!("cache insert failed: {e}"));
                    }
                }
```

Update `on_done`'s `BuiltEvent` construction to set `cached: outcomes.lock().unwrap()[i] == Outcome::Cached,`.

Finally, replace the trailing `Ok(BuildReport { built })` with a tally from outcomes:

```rust
    pool::run(&deps, opts.jobs, &job, &on_done).map_err(|f| {
        let m = &ws.graph.modules[f.item];
        BuildError::ModuleBuild {
            module: m.name.to_string(),
            file: m.file.clone(),
            details: f.message,
        }
    })?;
    let outs = outcomes.into_inner().unwrap();
    Ok(BuildReport {
        built: outs.iter().filter(|o| **o == Outcome::Built).count(),
        cached: outs.iter().filter(|o| **o == Outcome::Cached).count(),
    })
```

(Note: this counts every module by its outcome; a fail-fast abort still returns `Err` above, so partial tallies never surface.)

- [ ] **Step 5: Run the tests**

Run: `cargo test -p leanr_build compile::`
Expected: PASS (all existing + three new; `builds_every_module_in_dependency_order` still asserts `report.built == 2` on the no-cache path).

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_build/src/compile.rs
git commit -m "feat(build): cache-aware build job — lookup/materialize hits, insert misses; built vs cached"
```

---

### Task 8: `cache verify` (integrity) + `cache gc`

**Files:**
- Modify: `crates/leanr_build/src/cache.rs`

**Interfaces:**
- Produces:
  - `pub struct VerifyReport { pub blobs: usize, pub bad_blobs: Vec<String>, pub dangling: Vec<String> }`
  - `pub fn verify(&self) -> std::io::Result<VerifyReport>` — re-hash every blob (name must equal content hash → else `bad_blobs`); every manifest's referenced blobs must exist (→ else `dangling`). A clean store: both empty.
  - `pub struct GcReport { pub removed: usize, pub freed: u64, pub kept: u64 }`
  - `pub fn gc(&self, max_size: u64) -> std::io::Result<GcReport>` — LRU by blob mtime; delete oldest until total blob bytes ≤ `max_size`.

- [ ] **Step 1: Write the failing tests (append to `cache.rs` tests)**

```rust
    #[test]
    fn verify_is_clean_for_a_well_formed_store() {
        let (t, c) = cache();
        let a = t.path().join("A.olean");
        write(&a, b"bytes");
        c.insert("aa11", &[a]).unwrap();
        let r = c.verify().unwrap();
        assert_eq!(r.bad_blobs.len(), 0);
        assert_eq!(r.dangling.len(), 0);
        assert_eq!(r.blobs, 1);
    }

    #[test]
    fn verify_flags_a_tampered_blob() {
        let (t, c) = cache();
        let a = t.path().join("A.olean");
        write(&a, b"bytes");
        let m = c.insert("bb22", &[a]).unwrap();
        // Tamper: rewrite the blob's bytes (make it writable first).
        let bp = c.blob_path(&m.artifacts[0].blob);
        let mut perms = std::fs::metadata(&bp).unwrap().permissions();
        perms.set_readonly(false);
        std::fs::set_permissions(&bp, perms).unwrap();
        std::fs::write(&bp, b"TAMPERED").unwrap();
        let r = c.verify().unwrap();
        assert_eq!(r.bad_blobs, vec![m.artifacts[0].blob.clone()]);
    }

    #[test]
    fn gc_evicts_oldest_until_under_cap() {
        let (_t, c) = cache();
        // Three ~1 KiB blobs; cap at 2 KiB must drop exactly one.
        let a = c.store_blob(&vec![1u8; 1024]).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(10));
        let b = c.store_blob(&vec![2u8; 1024]).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(10));
        let cc = c.store_blob(&vec![3u8; 1024]).unwrap();
        let r = c.gc(2048).unwrap();
        assert_eq!(r.removed, 1);
        assert!(!c.blob_path(&a).exists(), "oldest evicted");
        assert!(c.blob_path(&b).exists() && c.blob_path(&cc).exists(), "newest kept");
    }
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_build cache::verify_is_clean`
Expected: FAIL ("no method named `verify`").

- [ ] **Step 3: Implement `verify` + `gc`**

Add a small blob-walk helper and both methods to `cache.rs`:

```rust
#[derive(Debug)]
pub struct VerifyReport {
    pub blobs: usize,
    pub bad_blobs: Vec<String>,
    pub dangling: Vec<String>,
}

#[derive(Debug)]
pub struct GcReport {
    pub removed: usize,
    pub freed: u64,
    pub kept: u64,
}

impl Cache {
    /// All blob files as (hex, path, len, mtime). Empty if the store is absent.
    fn walk_blobs(&self) -> std::io::Result<Vec<(String, PathBuf, u64, std::time::SystemTime)>> {
        let blobs_root = self.root.join("blobs");
        let mut out = Vec::new();
        let shards = match std::fs::read_dir(&blobs_root) {
            Ok(rd) => rd,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(out),
            Err(e) => return Err(e),
        };
        for shard in shards {
            let shard = shard?;
            if !shard.file_type()?.is_dir() {
                continue;
            }
            for blob in std::fs::read_dir(shard.path())? {
                let blob = blob?;
                let meta = blob.metadata()?;
                if !meta.is_file() {
                    continue;
                }
                let hex = blob.file_name().to_string_lossy().into_owned();
                let mtime = meta.modified().unwrap_or(std::time::UNIX_EPOCH);
                out.push((hex, blob.path(), meta.len(), mtime));
            }
        }
        Ok(out)
    }

    pub fn verify(&self) -> std::io::Result<VerifyReport> {
        let mut bad_blobs = Vec::new();
        let blobs = self.walk_blobs()?;
        for (hex, path, _, _) in &blobs {
            let bytes = std::fs::read(path)?;
            if blake3::hash(&bytes).to_hex().to_string() != *hex {
                bad_blobs.push(hex.clone());
            }
        }
        // Dangling manifests: referenced blob missing.
        let mut dangling = Vec::new();
        let modules_root = self.root.join("modules");
        if let Ok(shards) = std::fs::read_dir(&modules_root) {
            for shard in shards {
                let shard = shard?;
                if !shard.file_type()?.is_dir() {
                    continue;
                }
                for man in std::fs::read_dir(shard.path())? {
                    let man = man?;
                    let bytes = std::fs::read(man.path())?;
                    if let Ok(m) = serde_json::from_slice::<Manifest>(&bytes) {
                        if m.artifacts.iter().any(|a| !self.blob_path(&a.blob).exists()) {
                            dangling.push(man.file_name().to_string_lossy().into_owned());
                        }
                    }
                }
            }
        }
        Ok(VerifyReport { blobs: blobs.len(), bad_blobs, dangling })
    }

    pub fn gc(&self, max_size: u64) -> std::io::Result<GcReport> {
        let mut blobs = self.walk_blobs()?;
        let total: u64 = blobs.iter().map(|b| b.2).sum();
        if total <= max_size {
            return Ok(GcReport { removed: 0, freed: 0, kept: total });
        }
        // Oldest first.
        blobs.sort_by_key(|b| b.3);
        let mut kept = total;
        let mut removed = 0;
        let mut freed = 0;
        for (_, path, len, _) in blobs {
            if kept <= max_size {
                break;
            }
            std::fs::remove_file(&path)?;
            kept -= len;
            freed += len;
            removed += 1;
        }
        Ok(GcReport { removed, freed, kept })
    }
}
```

- [ ] **Step 4: Run the tests**

Run: `cargo test -p leanr_build cache::`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_build/src/cache.rs
git commit -m "feat(build): cache verify (integrity) + gc (LRU eviction to a size cap)"
```

---

### Task 9: Staleness-correctness harness (release-blocking gate)

The correctness gate: perturb each input axis on a synthetic workspace and assert **exactly** the right rebuild set, via an invocation-counting fake `lean`.

**Files:**
- Create: `crates/leanr_build/tests/cache_incremental.rs`
- Create: `crates/leanr_build/tests/fixtures/counting-lean.sh`

**Interfaces:**
- Consumes: `leanr_build::resolve`, `compile::{build_workspace, BuildOptions}`, `cache::Cache`, `fingerprint::FingerprintEnv`. Uses the public API only (integration test).

- [ ] **Step 1: Write the counting fake-lean**

Create `crates/leanr_build/tests/fixtures/counting-lean.sh` (mirrors `fake-lean.sh` but appends the source path to `$COUNTING_LEAN_LOG` so the test can count invocations). Base it on the existing `crates/leanr_build/tests/fixtures/fake-lean.sh`; add near the top, after argument parsing locates the source `.lean` path in `$1`:

```sh
#!/bin/sh
# Test double: records each invocation's source path, then emits the same
# artifact family real lean would (empty-but-present files), so the CAS and
# byte-diffs behave deterministically. See fake-lean.sh for the arg shape.
set -eu
src="$1"; shift
: "${COUNTING_LEAN_LOG:=/dev/null}"
printf '%s\n' "$src" >> "$COUNTING_LEAN_LOG"
# ... reuse fake-lean.sh's -o/-i parsing + artifact-family emission verbatim,
# writing deterministic bytes derived from "$src" so edits change outputs ...
```

The implementer copies `fake-lean.sh`'s `-o`/`-i` handling and artifact emission; the only additions are the log line and making each artifact's bytes a function of the source **contents** (e.g. `cat "$src" > "$out.olean"` plus a marker), so a source edit yields different olean bytes (needed for the byte-diff/deep-verify axes). `chmod +x` it.

- [ ] **Step 2: Write the harness tests**

Create `crates/leanr_build/tests/cache_incremental.rs`. Use a helper that builds a small three-module workspace on disk (`Root`, `Root.A`, `Root.B` where `Root` imports both), runs `resolve` + `build_workspace` with a `Cache`, and returns the invocation log. Structure:

```rust
//! M2c staleness-correctness gate (spec §Staleness-correctness harness):
//! perturb one input axis at a time and assert the EXACT rebuild set.
//! Under-invalidation (a changed input that fails to rebuild a dependent)
//! is release-blocking; over-invalidation (an unrelated module rebuilds)
//! is a fingerprint-scope regression. Uses a counting fake `lean` — no
//! toolchain needed.

use std::path::{Path, PathBuf};

fn counting_lean() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/counting-lean.sh")
}

// Build the fixture workspace at `dir`; return (Workspace, XDG cache dir).
// Writes lakefile.toml + lake-manifest.json + Root.lean/Root/A.lean/Root/B.lean.
// Root imports Root.A and Root.B.
fn fixture(dir: &Path) -> leanr_build::Workspace { /* ...write files, resolve... */ unimplemented!() }

fn build_counting(ws: &leanr_build::Workspace, xdg: &Path, log: &Path)
    -> leanr_build::compile::BuildReport { /* set COUNTING_LEAN_LOG=log; build_workspace with Cache::new(xdg) */ unimplemented!() }

fn invocations(log: &Path) -> Vec<String> {
    std::fs::read_to_string(log).unwrap_or_default().lines().map(|s| s.to_string()).collect()
}
```

Then these tests (each in its own `tempfile::TempDir` so they are hermetic and parallel-safe):

1. `warm_build_runs_zero_lean` — cold build logs 3 invocations; a second build over the same XDG logs 0 more; `report.cached == 3`.
2. `editing_a_leaf_rebuilds_only_its_cone` — cold build; edit `Root/A.lean`; rebuild. Assert the new invocations are exactly `{Root/A.lean, Root.lean}` (A and its dependent Root) and **not** `Root/B.lean`. This is the no-under-invalidation + no-over-invalidation assertion.
3. `toggling_a_lean_option_rebuilds_that_libs_modules` — cold build; add a `leanOption` to the lib; rebuild. Assert every module of that lib re-ran.
4. `changing_the_env_rebuilds_everything` — cold build; rebuild with a different `FingerprintEnv.toolchain_id`. Assert all 3 re-ran (whole-cache invalidation).

Each test's assertion compares `invocations(log)` deltas (truncate the log between phases by pointing to a fresh log file for the second build).

The implementer fills `fixture` and `build_counting` following `crates/leanr_build/tests/synthetic_workspace.rs` (which already constructs an on-disk workspace and calls `resolve`) and `crates/leanr_cli/tests/build_cli.rs` (which drives builds) as the concrete patterns for writing the lakefile/manifest and invoking `resolve`.

- [ ] **Step 3: Run the harness**

Run: `cargo test -p leanr_build --test cache_incremental`
Expected: PASS (all four axes). If `editing_a_leaf_rebuilds_only_its_cone` shows `Root/B.lean` re-running, the fingerprint is over-inclusive; if it shows `Root.lean` NOT re-running after editing `Root/A.lean`, the Merkle recursion is broken (under-invalidation — release-blocking). Fix `fingerprint_all` before proceeding.

- [ ] **Step 4: Commit**

```bash
git add crates/leanr_build/tests/cache_incremental.rs crates/leanr_build/tests/fixtures/counting-lean.sh
git commit -m "test(build): M2c staleness-correctness harness — exact-cone rebuild per input axis"
```

---

### Task 10: `deep_verify` — oracle rebuild-and-diff

`cache verify --deep`: re-run `lean` for a module set and byte-diff against the cached artifacts, directly testing fingerprint completeness. Runs against the current project's already-built layout (imports resolve through it).

**Files:**
- Modify: `crates/leanr_build/src/cache.rs`

**Interfaces:**
- Consumes: `Workspace`, `setup::{Layout, module_setup, lean_path_env}`, `subprocess::run_drained`, `fingerprint::{FingerprintEnv, fingerprint_all}`, `compile::LeanInvoker`, `pool::run`.
- Produces: `pub struct DeepReport { pub checked: usize, pub mismatches: Vec<String> }` and `pub fn deep_verify(&self, ws: &Workspace, env: &FingerprintEnv, lean: &crate::compile::LeanInvoker, jobs: usize) -> Result<DeepReport, crate::BuildError>`.

- [ ] **Step 1: Write the failing test (append to `cache.rs` tests, gated so it uses the counting fake-lean via an env-driven helper)**

Because `deep_verify` needs a `Workspace`, test it at the integration layer instead. Add to `crates/leanr_build/tests/cache_incremental.rs`:

```rust
#[test]
fn deep_verify_is_clean_after_build_and_flags_a_tampered_blob() {
    // 1. Build the fixture into a project + cache (counting-lean writes
    //    source-derived bytes, so rebuild output is deterministic).
    // 2. cache.deep_verify(...) → mismatches empty.
    // 3. Tamper one cached blob; deep_verify → that module in mismatches.
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_build --test cache_incremental deep_verify`
Expected: FAIL ("no method named `deep_verify`").

- [ ] **Step 3: Implement `deep_verify`**

Add to `cache.rs`. For each module, run `lean` with `-o`/`-i` pointed at a per-run temp dir (imports resolve via `LEAN_PATH` = the project's built lib dirs), then hash each produced artifact and compare to the cache blob named by that module's fingerprint manifest:

```rust
#[derive(Debug)]
pub struct DeepReport {
    pub checked: usize,
    pub mismatches: Vec<String>,
}

impl Cache {
    pub fn deep_verify(
        &self,
        ws: &crate::Workspace,
        env: &crate::fingerprint::FingerprintEnv,
        lean: &crate::compile::LeanInvoker,
        jobs: usize,
    ) -> Result<DeepReport, crate::BuildError> {
        let layout = crate::setup::Layout::new(&ws.root_dir);
        let lean_path = crate::setup::lean_path_env(ws, &layout);
        let fps = crate::fingerprint::fingerprint_all(ws, env)?;
        let scratch = ws.root_dir.join(".leanr").join("verify");
        std::fs::create_dir_all(&scratch).ok();
        let deps: Vec<Vec<usize>> = (0..ws.graph.modules.len()).map(|_| Vec::new()).collect();
        let mismatches: std::sync::Mutex<Vec<String>> = std::sync::Mutex::new(Vec::new());
        let job = |i: usize| -> Result<(), String> {
            let m = &ws.graph.modules[i];
            let expected = match self.lookup(&fps[i]) {
                Ok(Some(man)) => man,
                Ok(None) => return Ok(()), // nothing cached for this fp — skip
                Err(e) => return Err(format!("lookup: {e}")),
            };
            let mod_scratch = scratch.join(i.to_string());
            std::fs::create_dir_all(&mod_scratch).map_err(|e| e.to_string())?;
            let out = mod_scratch.join(format!("{}.olean", m.name.components().last().cloned().unwrap_or_default()));
            let ile = out.with_extension("ilean");
            let mut cmd = std::process::Command::new(&lean.program);
            if let Some(tc) = &lean.toolchain {
                cmd.arg(format!("+{tc}"));
            }
            cmd.arg(&m.file).arg("-o").arg(&out).arg("-i").arg(&ile)
                .arg("--setup").arg(layout.setup_path(&m.package, &m.name))
                .arg("--json").env("LEAN_PATH", &lean_path).current_dir(&ws.root_dir);
            match crate::subprocess::run_drained(&mut cmd) {
                Ok(f) if f.status.success() => {}
                Ok(f) => return Err(format!("rebuild failed: {}", f.status)),
                Err(e) => return Err(format!("spawn: {e:?}")),
            }
            // Diff each produced artifact against its cached blob by basename.
            for entry in &expected.artifacts {
                let produced = mod_scratch.join(&entry.name);
                let ok = std::fs::read(&produced)
                    .map(|b| blake3::hash(&b).to_hex().to_string() == entry.blob)
                    .unwrap_or(false);
                if !ok {
                    mismatches.lock().unwrap().push(format!("{}:{}", m.name, entry.name));
                }
            }
            Ok(())
        };
        crate::pool::run(&deps, jobs.max(1), &job, &|_, _, _| {})
            .map_err(|f| crate::BuildError::ModuleBuild {
                module: ws.graph.modules[f.item].name.to_string(),
                file: ws.graph.modules[f.item].file.clone(),
                details: f.message,
            })?;
        let _ = std::fs::remove_dir_all(&scratch);
        let mismatches = mismatches.into_inner().unwrap();
        Ok(DeepReport { checked: ws.graph.modules.len(), mismatches })
    }
}
```

Note: `deep_verify` requires the project to be built/materialized first (imports must exist in `.leanr/build/<pkg>/lib`); if an import artifact is missing, `lean` errors and the module is reported — acceptable and clearly surfaced for M2c. `setup_path` files are written by a prior `build`; if absent, the CLI (Task 12) regenerates them before calling `deep_verify` (reuse the up-front setup-writing loop, or call `build --force` first).

- [ ] **Step 4: Run the test**

Run: `cargo test -p leanr_build --test cache_incremental deep_verify`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_build/src/cache.rs crates/leanr_build/tests/cache_incremental.rs
git commit -m "feat(build): cache deep_verify — rebuild-and-diff oracle for fingerprint completeness"
```

---

### Task 11: CLI — `build --no-cache/--force`

**Files:**
- Modify: `crates/leanr_cli/src/main.rs:51-74` (Build variant), `:101-109` (dispatch), `:449-536` (`build`)

**Interfaces:**
- Consumes: `compile::{BuildOptions, BuildReport}`, `cache::Cache`, `fingerprint::FingerprintEnv`, `cache_dir::cache_root`.

- [ ] **Step 1: Write the failing CLI test (append to `crates/leanr_cli/tests/build_cli.rs`)**

```rust
#[test]
fn second_build_reports_cached_modules() {
    // Build a fixture twice with an isolated XDG_CACHE_HOME; the second
    // run's stdout says "cached N".  (Follow this file's existing harness
    // for driving `leanr build` with a fake lean + temp workspace.)
}

#[test]
fn no_cache_flag_forces_a_full_build() {
    // With --no-cache, a second build still runs lean for every module.
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_cli --test build_cli second_build_reports_cached`
Expected: FAIL (flag/behavior absent).

- [ ] **Step 3: Add the flags and wire them**

In the `Build` variant add:

```rust
        /// Ignore the artifact cache: always run `lean`, never read or write it.
        #[arg(long)]
        no_cache: bool,
        /// Rebuild every module with `lean`, then refresh the cache.
        #[arg(long, conflicts_with = "no_cache")]
        force: bool,
```

Thread `no_cache, force` through the `Command::Build { .. }` destructure and the `build(...)` signature. In `build`, after resolving `cache_root`, construct the fingerprint env and cache, and pass them into `BuildOptions`:

```rust
        let fp_env = leanr_build::fingerprint::FingerprintEnv {
            leanr_version: env!("CARGO_PKG_VERSION").to_string(),
            toolchain_id: toolchain_for_lean.clone().unwrap_or_default(),
            platform: format!("{}-{}", std::env::consts::ARCH, std::env::consts::OS),
        };
        let cache = if no_cache {
            None
        } else {
            Some(leanr_build::cache::Cache::new(&cache_root))
        };
        let build_opts = leanr_build::compile::BuildOptions {
            jobs,
            lean: leanr_build::compile::LeanInvoker {
                program: lean.unwrap_or_else(|| PathBuf::from("lean")),
                toolchain: toolchain_for_lean,
            },
            cache,
            force,
            fp_env,
        };
```

(`toolchain_for_lean` is already cloned earlier at main.rs:479; reuse it — clone once more for `fp_env` as shown.)

Update the final print to include cached, and the per-module line to mark cache hits:

```rust
        let report = leanr_build::compile::build_workspace(&ws, &build_opts, &|e| {
            if !e.diagnostics.is_empty() {
                eprint!("{}", e.diagnostics);
            }
            let tag = if e.cached { " (cached)" } else { "" };
            println!("[{}/{}] {}{} ({:.1}s)", e.done, e.total, e.module, tag, e.secs);
        })
        .map_err(|e| e.to_string())?;
        println!(
            "built {} modules ({} cached) in {:.1}s ({} jobs)",
            report.built, report.cached,
            build_start.elapsed().as_secs_f64(), jobs
        );
```

- [ ] **Step 4: Run the tests**

Run: `cargo test -p leanr_cli --test build_cli`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_cli/src/main.rs crates/leanr_cli/tests/build_cli.rs
git commit -m "feat(cli): build --no-cache/--force; report cached module counts"
```

---

### Task 12: CLI — `cache verify [--deep]` and `cache gc --max-size`

**Files:**
- Modify: `crates/leanr_cli/src/main.rs` (new `Cache` subcommand + dispatch + handler)
- Modify: `crates/leanr_cli/tests/cli.rs` (or `build_cli.rs`) — verify/gc tests

**Interfaces:**
- Consumes: `cache::{Cache, VerifyReport, DeepReport, GcReport}`, `cache_dir::cache_root`, `resolve` (for `--deep`).

- [ ] **Step 1: Write the failing tests**

Append to `crates/leanr_cli/tests/build_cli.rs`:

```rust
#[test]
fn cache_verify_reports_clean_after_a_build() {
    // build a fixture, then `leanr cache verify` exits 0 and prints "OK".
}

#[test]
fn cache_gc_reports_eviction_under_a_small_cap() {
    // populate the cache, run `leanr cache gc --max-size 0`, expect removal.
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_cli --test build_cli cache_verify_reports_clean`
Expected: FAIL (no `cache` subcommand).

- [ ] **Step 3: Add the subcommand**

Add to the `Command` enum:

```rust
    /// Inspect and maintain the shared artifact cache.
    Cache {
        #[command(subcommand)]
        command: CacheCommand,
    },
```

And a new subcommand enum:

```rust
#[derive(Subcommand)]
enum CacheCommand {
    /// Check store integrity (blob bytes == content key; no dangling
    /// manifests). `--deep` also rebuilds and byte-diffs against `lean`.
    Verify {
        /// Rebuild each module with `lean` and byte-diff against the cache.
        #[arg(long)]
        deep: bool,
        /// Workspace dir for `--deep` (default: walk up from cwd).
        #[arg(long)]
        dir: Option<PathBuf>,
        #[arg(long)]
        jobs: Option<usize>,
        #[arg(long)]
        lean: Option<PathBuf>,
    },
    /// Evict least-recently-used blobs until the store is at most SIZE bytes.
    Gc {
        #[arg(long = "max-size")]
        max_size: u64,
    },
}
```

Dispatch in `main()`:

```rust
        Command::Cache { command } => cache_cmd(command),
```

Handler (integrity path always available; `--deep` resolves a workspace and reuses the build toolchain wiring from `build`):

```rust
fn cache_cmd(command: CacheCommand) -> ExitCode {
    let run = || -> Result<(), String> {
        let cache_root = leanr_build::cache_dir::cache_root(
            std::env::var_os("XDG_CACHE_HOME").as_deref(),
            std::env::var_os("HOME").as_deref(),
        )
        .ok_or_else(|| "cannot determine the leanr cache directory: set XDG_CACHE_HOME or HOME".to_string())?;
        let cache = leanr_build::cache::Cache::new(&cache_root);
        match command {
            CacheCommand::Gc { max_size } => {
                let r = cache.gc(max_size).map_err(|e| e.to_string())?;
                println!("gc: removed {} blobs, freed {} bytes, {} bytes kept", r.removed, r.freed, r.kept);
                Ok(())
            }
            CacheCommand::Verify { deep, dir, jobs, lean } => {
                let r = cache.verify().map_err(|e| e.to_string())?;
                if r.bad_blobs.is_empty() && r.dangling.is_empty() {
                    println!("cache verify: OK ({} blobs)", r.blobs);
                } else {
                    return Err(format!(
                        "cache integrity FAILED: {} corrupt blob(s), {} dangling manifest(s)",
                        r.bad_blobs.len(), r.dangling.len()
                    ));
                }
                if deep {
                    // Resolve the workspace the same way `build` does, then
                    // deep_verify. (Factor the resolve block from `build` into
                    // a shared helper `resolve_workspace(dir) -> (Workspace, toolchain)`
                    // and call it from both.)
                    let (ws, toolchain) = resolve_workspace(dir)?;
                    let env = leanr_build::fingerprint::FingerprintEnv {
                        leanr_version: env!("CARGO_PKG_VERSION").to_string(),
                        toolchain_id: toolchain.clone().unwrap_or_default(),
                        platform: format!("{}-{}", std::env::consts::ARCH, std::env::consts::OS),
                    };
                    let invoker = leanr_build::compile::LeanInvoker {
                        program: lean.unwrap_or_else(|| PathBuf::from("lean")),
                        toolchain,
                    };
                    let jobs = jobs.unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1));
                    let d = cache.deep_verify(&ws, &env, &invoker, jobs).map_err(|e| e.to_string())?;
                    if d.mismatches.is_empty() {
                        println!("cache verify --deep: OK ({} modules byte-identical)", d.checked);
                    } else {
                        return Err(format!("cache verify --deep FAILED: {} mismatch(es): {}", d.mismatches.len(), d.mismatches.join(", ")));
                    }
                }
                Ok(())
            }
        }
    };
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(msg) => { eprintln!("error: {msg}"); ExitCode::FAILURE }
    }
}
```

Extract the resolve block (main.rs:459-489) into `fn resolve_workspace(dir: Option<PathBuf>) -> Result<(leanr_build::Workspace, Option<String>), String>` and call it from both `build` and `cache_cmd` (DRY; keeps CLI free of build logic). `--deep` regenerates setup files by resolving then running `build --force` semantics is out of scope here — instead document that `cache verify --deep` must follow a `leanr build` (setup files + materialized imports present); if a setup file is missing, `deep_verify`'s `lean` run errors and the module is reported.

- [ ] **Step 4: Run the tests + a manual smoke**

Run: `cargo test -p leanr_cli --test build_cli`
Expected: PASS.
Run: `cargo run -p leanr_cli -- cache gc --max-size 0`
Expected: prints a gc line, exit 0 (empty store → "removed 0 blobs").

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_cli/src/main.rs crates/leanr_cli/tests/build_cli.rs
git commit -m "feat(cli): cache verify [--deep] and cache gc --max-size"
```

---

### Task 13: mise task, acceptance extension, docs

**Files:**
- Modify: `mise.toml` (add `cache:incremental`)
- Modify: `scripts/build-fresh-acceptance.sh` (warm + incremental assertions)
- Modify: `ARCHITECTURE.md` (`leanr_build` blurb, cache/fingerprint modules), `docs/THREAT_MODEL.md` (cache-store integrity invariant)

**Interfaces:** none (config/docs).

- [ ] **Step 1: Add the mise task**

In `mise.toml`, add near the other test tasks:

```toml
[tasks."cache:incremental"]
description = "M2c staleness-correctness gate: exact-cone rebuild per perturbed input axis (fast; no toolchain)"
run = "cargo test --package leanr_build --test cache_incremental"
```

Add `cache:incremental` to the `ci` task's step list (find `[tasks.ci]` and append it to the `depends`/`run` sequence used there, matching how existing test tasks are chained).

- [ ] **Step 2: Verify the task runs**

Run: `mise run cache:incremental`
Expected: PASS (the Task 9/10 tests).

- [ ] **Step 3: Extend the acceptance script**

In `scripts/build-fresh-acceptance.sh`, after the existing cold build + byte-diff, add:
1. **Warm assertion:** run `leanr build` a second time on the same clone + XDG; capture stdout; assert it reports `0 cached`... — actually assert `built 0 modules (<N> cached)` (zero `lean` runs). Fail the script if any module reports non-cached.
2. **Incremental assertion:** `touch`/edit one leaf `.lean` in the clone, rebuild, assert only its downstream cone reports non-cached (grep the per-module `(cached)` tags; the edited module + dependents lack the tag, all others have it).
3. **Integrity:** run `leanr cache verify` and assert exit 0.

Keep these guarded behind the same "hours; local only; needs toolchain" banner. Write the assertions in `sh` with `grep -c` on the captured build output.

- [ ] **Step 4: Update docs**

In `ARCHITECTURE.md`, extend the `crates/leanr_build` bullet: note the M2c `fingerprint` (recursive content-Merkle) and `cache` (XDG content-addressed store; hardlink materialization; `verify`/`gc`) modules, and that `leanr build` is now cache-aware by default with `--no-cache`/`--force`; update the line that currently reads "no up-to-date skipping until M2c" to reflect that M2c landed. In `docs/THREAT_MODEL.md`, add the cache-store integrity invariant (blob bytes == content key; the seam that will make M2d's untrusted remote blobs safe to ingest).

- [ ] **Step 5: Commit**

```bash
git add mise.toml scripts/build-fresh-acceptance.sh ARCHITECTURE.md docs/THREAT_MODEL.md
git commit -m "chore(build): M2c cache:incremental gate, acceptance warm/incremental asserts, docs"
```

---

### Task 14: Full verification

- [ ] **Step 1: Format, lint, test the whole workspace**

Run: `mise run fmt && mise run lint && mise run test`
Expected: all PASS. Fix any `clippy` findings (the repo lints deny warnings).

- [ ] **Step 2: Run the full CI task**

Run: `mise run ci`
Expected: PASS (includes `cache:incremental`).

- [ ] **Step 3: Commit any fixups**

```bash
git add -A && git commit -m "chore: M2c fixups from full CI run"
```

---

## Self-Review

**Spec coverage:**
- Shared XDG CAS → Tasks 4-6 (`Cache::new(cache_root)` → `cache/blobs`, `cache/modules`). ✓
- Recursive content-Merkle fingerprint incl. leanr version → Tasks 2-3. ✓
- `owner_provenance` (dep rev / declared inputs) → Task 3. ✓
- Materialize hardlink + copy fallback → Task 6. ✓
- Cache-aware `build` default; `--no-cache`/`--force`; built vs cached → Tasks 7, 11. ✓
- `cache verify` (integrity) + `--deep` (oracle) → Tasks 8, 10, 12. ✓
- `cache gc --max-size` (LRU, manual) → Tasks 8, 12. ✓
- Staleness-correctness harness (release-blocking) → Task 9. ✓
- Acceptance (warm ~zero lean, incremental cone, verify clean) → Task 13. ✓
- Threat-model touch (integrity == M2d seam) → Tasks 5, 13. ✓
- Off-kernel-graph, no new crate deps → Global Constraints; all tasks use existing deps. ✓

**Placeholder scan:** Task 9's `fixture`/`build_counting` and Task 10/12 test bodies are described with the concrete existing patterns to copy (`synthetic_workspace.rs`, `build_cli.rs`, `fake-lean.sh`) rather than fully spelled out, because they are mechanical transcriptions of those files — the implementer has exact references. All production code (`fingerprint`, `cache`, `compile`, CLI) is complete.

**Type consistency:** `Fingerprint = String` (hex) throughout; `Cache::{store_blob,insert,lookup,materialize,verify,gc,deep_verify}` signatures match across producer (Tasks 4-10) and consumers (Tasks 7, 12); `BuildOptions`/`BuildReport`/`BuiltEvent` shape is defined once (Task 7) and consumed by the CLI (Task 11); `FingerprintEnv` fields (`leanr_version`, `toolchain_id`, `platform`) are identical in producer (Task 2) and both CLI call sites (Tasks 11, 12).

## Execution Handoff
