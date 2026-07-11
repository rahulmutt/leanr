# M2a — Package Model + Module Graph Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `leanr build --dry-run` resolves a fresh clone of any manifest-committed Lean project — native config parsing, git dependency materialization, module DAG — and prints the build plan, differential-tested against pinned official lake over the Mathlib closure.

**Architecture:** New crate `leanr_build` with five components (config, bridge, manifest, fetch, modules/scanner/graph) composed by a pure `resolve()` pipeline; `leanr_cli` gains a `build` subcommand. Config has one native schema (the `lakefile.toml` format); `lakefile.lean` packages are bridged through pinned official `lake translate-config toml`, cached by content hash. Spec: `docs/superpowers/specs/2026-07-11-m2a-package-model-design.md`.

**Tech Stack:** Rust (workspace conventions), `serde`/`toml`/`serde_json` (config + manifest), `blake3` (bridge cache key), `thiserror` (errors), subprocesses `git` and `lake` (never linked).

## Global Constraints

- `leanr_build` must NOT depend on `leanr_kernel` or any workspace crate at build time; `leanr_olean`/`leanr_kernel` are **dev-dependencies only** (oracle tests).
- No panics on untrusted bytes: the header scanner is a **total function** over arbitrary input (same discipline as the `.olean` parser, `docs/THREAT_MODEL.md`).
- Subprocesses (`git`, `lake`) get explicit argument vectors (never a shell), captured stderr, and a timeout; manifest git URLs are validated (no leading `-`; scheme whitelist).
- Every error names the file/package it came from and the action that fixes it.
- Commit style: conventional commits (`feat(build): …`, `test(build): …`, `docs: …`). Run `mise run lint` before every commit; it must pass.
- Tools are mise-pinned; differential/acceptance tasks are local-only (CI has no Lean toolchain), matching the existing `check:mathlib` split.
- The Mathlib pin (`mathlib-pin`) and `lean-toolchain` are project constants — never change them in this work.
- Deterministic output: waves sorted, modules sorted lexicographically within a wave, JSON paths workspace-relative (so fresh-clone output is byte-identical to any other checkout's).

## File Structure

```
crates/leanr_build/
  Cargo.toml
  src/lib.rs        resolve() pipeline, Workspace/ResolvedPackage, find_workspace_root
  src/error.rs      BuildError (thiserror)
  src/config.rs     PackageConfig/LeanLibConfig/LeanExeConfig/Require, parse_lakefile_toml
  src/manifest.rs   Manifest/ManifestPackage/PackageSource, parse_manifest
  src/modules.rs    ModuleName, Glob, expand_glob
  src/scanner.rs    scan_header (total header lexer)
  src/graph.rs      ModuleResolver, ToolchainIndex, build_graph, topo_waves
  src/bridge.rs     translate_lakefile, load_config (translate-config bridge + cache)
  src/fetch.rs      validate_git_url, materialize (git subprocess)
  tests/fixtures/lakefiles/*.toml     vendored real dep lakefiles + mathlib golden
  tests/fixtures/fake-lake*.sh        fake lake scripts for bridge unit tests
  tests/config_fixtures.rs            parse every vendored lakefile
  tests/synthetic_workspace.rs        end-to-end resolve() on a tempdir workspace
  tests/mathlib_oracle.rs             #[ignore] differential tier (needs .mathlib)
crates/leanr_cli/src/main.rs          Build subcommand + renderers (modify)
scripts/build-fresh-acceptance.sh     fresh-clone acceptance
mise.toml                             build:differential, build:acceptance tasks (modify)
docs/THREAT_MODEL.md                  new M2a surface section (modify)
ARCHITECTURE.md                       leanr_build crate entry (modify)
```

Later tasks use earlier tasks' types verbatim; each task's **Interfaces** block restates the exact signatures it consumes.

---

### Task 1: Crate scaffold + error type + TOML config schema

**Files:**
- Create: `crates/leanr_build/Cargo.toml`, `crates/leanr_build/src/lib.rs`, `crates/leanr_build/src/error.rs`, `crates/leanr_build/src/config.rs`, `crates/leanr_build/src/modules.rs` (ModuleName + Glob only; expansion is Task 3)
- Create: `crates/leanr_build/tests/config_fixtures.rs`, `crates/leanr_build/tests/fixtures/lakefiles/` (7 vendored files)
- Modify: `Cargo.toml` (workspace members)
- Test: in-file `#[cfg(test)]` + `tests/config_fixtures.rs`

**Interfaces:**
- Consumes: nothing (first task).
- Produces:
  - `BuildError` (all variants below — later tasks add none; the enum is complete here).
  - `modules::ModuleName` — `parse(&str) -> Result<ModuleName, String>`, `components(&self) -> &[String]`, `starts_with(&self, &ModuleName) -> bool`, `child(&self, &str) -> ModuleName`, `rel_lean_path(&self) -> PathBuf`, `Display` (dot-joined), `Ord/Hash/Clone/Eq`.
  - `modules::Glob` — `One(ModuleName) | Submodules(ModuleName) | AndSubmodules(ModuleName)`, `parse(&str) -> Result<Glob, String>`, `Deserialize` from TOML string.
  - `config::{LeanOptionValue, Require, LeanLibConfig, LeanExeConfig, PackageConfig, ParsedConfig}` and `config::parse_lakefile_toml(text: &str, path: &Path) -> Result<ParsedConfig, BuildError>`.
  - `LeanLibConfig::effective_roots(&self) -> Vec<ModuleName>` and `effective_globs(&self) -> Vec<Glob>`.

- [ ] **Step 1: Scaffold the crate and register it**

`crates/leanr_build/Cargo.toml`:

```toml
[package]
name = "leanr_build"
version.workspace = true
edition.workspace = true
license.workspace = true

[dependencies]
serde = { version = "1", features = ["derive"] }
serde_json = "1"
toml = "0.8"
blake3 = "1"
thiserror = "2"

[dev-dependencies]
proptest = "1"
tempfile = "3"
leanr_olean = { path = "../leanr_olean" }
leanr_kernel = { path = "../leanr_kernel" }
```

Dependency justification (AGENTS.md rule, record in the commit message): `toml`+`serde` — the native config format is TOML; `serde_json` — `lake-manifest.json`; `blake3` — bridge cache key and the hash M2c standardizes on; `thiserror` — existing convention (`leanr_olean`); dev-only `tempfile` (synthetic workspaces), `proptest` (scanner no-panic property), `leanr_olean`/`leanr_kernel` (oracle tests only — the spec forbids them as build deps).

In root `Cargo.toml` change the members line to:

```toml
members = ["crates/leanr_kernel", "crates/leanr_check", "crates/leanr_cli", "crates/leanr_query", "crates/leanr_olean", "crates/leanr_build"]
```

`crates/leanr_build/src/lib.rs` (starter — grows in later tasks):

```rust
//! Lake-compatible package model + module graph (M2a).
//! Spec: docs/superpowers/specs/2026-07-11-m2a-package-model-design.md

pub mod config;
mod error;
pub mod modules;

pub use error::BuildError;
```

`crates/leanr_build/src/error.rs` (complete — later tasks add no variants):

```rust
use std::path::PathBuf;

/// Every user-facing failure of the build pipeline. Postcondition of the
/// whole crate: errors name the file/package they came from and the action
/// that fixes them (spec §Error handling & trust).
#[derive(Debug, thiserror::Error)]
pub enum BuildError {
    #[error("no lakefile.toml or lakefile.lean found in {0} or any parent directory")]
    NoWorkspaceRoot(PathBuf),
    #[error("{path}: {msg}")]
    Config { path: PathBuf, msg: String },
    #[error("no lake-manifest.json in {0}; run `lake update` once and commit it")]
    NoManifest(PathBuf),
    #[error("{path}: {msg}")]
    Manifest { path: PathBuf, msg: String },
    #[error("manifest is stale: `require {name}` in {config} has no lake-manifest.json entry; run `lake update` and commit the result")]
    StaleManifest { name: String, config: PathBuf },
    #[error("package `{name}`: {msg}")]
    Fetch { name: String, msg: String },
    #[error("`{cmd}` {reason}\n{stderr}")]
    Subprocess { cmd: String, reason: String, stderr: String },
    #[error("import cycle: {}", cycle.join(" -> "))]
    ImportCycle { cycle: Vec<String> },
    #[error("module `{module}` (imported by `{importer}`) not found in the workspace or the toolchain")]
    UnresolvedImport { module: String, importer: String },
    #[error("target `{0}` is not a lean_lib of the root package (only lean_lib targets are supported in M2a)")]
    UnknownTarget(String),
    #[error("{path}: {err}")]
    Io { path: PathBuf, err: String },
}
```

- [ ] **Step 2: Write failing tests for ModuleName and Glob**

In `crates/leanr_build/src/modules.rs`, start with the test module:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_dotted_name() {
        let m = ModuleName::parse("Mathlib.Algebra.Group.Basic").unwrap();
        assert_eq!(m.components(), ["Mathlib", "Algebra", "Group", "Basic"]);
        assert_eq!(m.to_string(), "Mathlib.Algebra.Group.Basic");
        assert_eq!(
            m.rel_lean_path(),
            std::path::PathBuf::from("Mathlib/Algebra/Group/Basic.lean")
        );
    }

    #[test]
    fn guillemet_component_is_one_component_and_may_contain_dots() {
        let m = ModuleName::parse("Cache.«cache-test».Main").unwrap();
        assert_eq!(m.components(), ["Cache", "cache-test", "Main"]);
        let d = ModuleName::parse("«a.b»").unwrap();
        assert_eq!(d.components(), ["a.b"]);
    }

    #[test]
    fn rejects_malformed_names() {
        for bad in ["", ".", "A..B", "A.", ".A", "«unclosed", "A B"] {
            assert!(ModuleName::parse(bad).is_err(), "should reject {bad:?}");
        }
    }

    #[test]
    fn starts_with_and_child() {
        let root = ModuleName::parse("Mathlib").unwrap();
        let m = ModuleName::parse("Mathlib.Init").unwrap();
        assert!(m.starts_with(&root));
        assert!(root.starts_with(&root));
        assert!(!root.starts_with(&m));
        assert_eq!(root.child("Init"), m);
    }

    #[test]
    fn glob_forms() {
        assert_eq!(
            Glob::parse("Cache.+").unwrap(),
            Glob::Submodules(ModuleName::parse("Cache").unwrap())
        );
        assert_eq!(
            Glob::parse("Cache.*").unwrap(),
            Glob::AndSubmodules(ModuleName::parse("Cache").unwrap())
        );
        assert_eq!(
            Glob::parse("Cache").unwrap(),
            Glob::One(ModuleName::parse("Cache").unwrap())
        );
        assert!(Glob::parse("").is_err());
    }
}
```

- [ ] **Step 3: Run tests to verify they fail**

Run: `cargo test -p leanr_build`
Expected: compile FAILURE (types not defined).

- [ ] **Step 4: Implement ModuleName and Glob**

Top of `crates/leanr_build/src/modules.rs`:

```rust
//! Module names, globs, and glob expansion (spec §Architecture, component 5).

use std::fmt;
use std::path::PathBuf;

use serde::Deserialize;

/// A dot-separated Lean module name. Guillemet components (`«a.b»`) are
/// stored unquoted; a component never contains `«»` and is never empty.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModuleName(Vec<String>);

impl ModuleName {
    /// Parse `A.B.«c.d»`. Errors (message only; callers add file context)
    /// on empty input, empty components, unclosed guillemets, or
    /// whitespace outside guillemets.
    pub fn parse(s: &str) -> Result<ModuleName, String> {
        let mut comps = Vec::new();
        let mut chars = s.chars().peekable();
        loop {
            let mut comp = String::new();
            if chars.peek() == Some(&'«') {
                chars.next();
                loop {
                    match chars.next() {
                        Some('»') => break,
                        Some(c) => comp.push(c),
                        None => return Err(format!("unclosed «» in `{s}`")),
                    }
                }
            } else {
                while let Some(&c) = chars.peek() {
                    if c == '.' {
                        break;
                    }
                    if c.is_whitespace() || c == '«' || c == '»' {
                        return Err(format!("invalid character {c:?} in `{s}`"));
                    }
                    comp.push(c);
                    chars.next();
                }
            }
            if comp.is_empty() {
                return Err(format!("empty component in `{s}`"));
            }
            comps.push(comp);
            match chars.next() {
                None => break,
                Some('.') => continue,
                Some(c) => return Err(format!("unexpected {c:?} in `{s}`")),
            }
        }
        Ok(ModuleName(comps))
    }

    pub fn components(&self) -> &[String] {
        &self.0
    }

    pub fn starts_with(&self, prefix: &ModuleName) -> bool {
        self.0.len() >= prefix.0.len() && self.0[..prefix.0.len()] == prefix.0[..]
    }

    pub fn child(&self, part: &str) -> ModuleName {
        let mut c = self.0.clone();
        c.push(part.to_string());
        ModuleName(c)
    }

    /// `A.B.C` -> `A/B/C.lean` (component strings used verbatim).
    pub fn rel_lean_path(&self) -> PathBuf {
        let mut p: PathBuf = self.0.iter().collect();
        p.set_extension("lean");
        p
    }
}

impl fmt::Display for ModuleName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.join("."))
    }
}

/// Lake's TOML glob syntax: `X` (the module), `X.+` (strict submodules),
/// `X.*` (module and submodules). Only `X` and `X.+` are observed in the
/// Mathlib closure; `X.*` is implemented for completeness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Glob {
    One(ModuleName),
    Submodules(ModuleName),
    AndSubmodules(ModuleName),
}

impl Glob {
    pub fn parse(s: &str) -> Result<Glob, String> {
        if let Some(base) = s.strip_suffix(".+") {
            Ok(Glob::Submodules(ModuleName::parse(base)?))
        } else if let Some(base) = s.strip_suffix(".*") {
            Ok(Glob::AndSubmodules(ModuleName::parse(base)?))
        } else {
            Ok(Glob::One(ModuleName::parse(s)?))
        }
    }
}

impl<'de> Deserialize<'de> for Glob {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Glob, D::Error> {
        let s = String::deserialize(d)?;
        Glob::parse(&s).map_err(serde::de::Error::custom)
    }
}
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p leanr_build`
Expected: PASS (all Step 2 tests green).

- [ ] **Step 6: Vendor the 7 real dependency lakefiles as fixtures**

```bash
mkdir -p crates/leanr_build/tests/fixtures/lakefiles
for p in aesop batteries Cli importGraph LeanSearchClient plausible Qq; do
  cp .mathlib/.lake/packages/$p/lakefile.toml crates/leanr_build/tests/fixtures/lakefiles/$p.toml
done
```

(Requires the `.mathlib` checkout from `mise run mathlib:fetch`. If absent on this machine, fetch first — the fixtures are committed, so this is one-time.)

- [ ] **Step 7: Write failing config tests**

`crates/leanr_build/tests/config_fixtures.rs`:

```rust
use std::path::Path;

use leanr_build::config::{parse_lakefile_toml, LeanOptionValue};
use leanr_build::modules::{Glob, ModuleName};

/// Every vendored real-world lakefile parses with zero unknown-key warnings.
#[test]
fn all_vendored_lakefiles_parse_cleanly() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/lakefiles");
    let mut seen = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("toml") {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        let parsed = parse_lakefile_toml(&text, &path).unwrap();
        assert!(
            parsed.warnings.is_empty(),
            "{}: unexpected warnings {:?}",
            path.display(),
            parsed.warnings
        );
        assert!(!parsed.config.name.is_empty());
        seen += 1;
    }
    assert!(seen >= 7, "expected the 7 vendored fixtures, found {seen}");
}

#[test]
fn batteries_fields_land_where_expected() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/lakefiles");
    let path = dir.join("batteries.toml");
    let parsed =
        parse_lakefile_toml(&std::fs::read_to_string(&path).unwrap(), &path).unwrap();
    let c = parsed.config;
    assert_eq!(c.name, "batteries");
    assert_eq!(c.default_targets, ["Batteries", "runLinter"]);
    assert_eq!(
        c.lean_options.get("linter.missingDocs"),
        Some(&LeanOptionValue::Bool(true))
    );
    let recycling = c
        .lean_libs
        .iter()
        .find(|l| l.name == "BatteriesRecycling")
        .unwrap();
    assert_eq!(
        recycling.effective_globs(),
        [Glob::Submodules(ModuleName::parse("BatteriesRecycling").unwrap())]
    );
    // Default globs: roots default to [name], globs default to roots.map(One).
    let main = c.lean_libs.iter().find(|l| l.name == "Batteries").unwrap();
    assert_eq!(
        main.effective_roots(),
        [ModuleName::parse("Batteries").unwrap()]
    );
    assert_eq!(
        main.effective_globs(),
        [Glob::One(ModuleName::parse("Batteries").unwrap())]
    );
    assert_eq!(c.lean_exes.len(), 3);
    let shake = c.lean_exes.iter().find(|e| e.name == "shake").unwrap();
    assert_eq!(shake.root.as_deref(), Some("Shake.Main"));
}

#[test]
fn unknown_keys_warn_but_do_not_fail() {
    let text = r#"
name = "x"
someFutureLakeKey = 3

[[lean_lib]]
name = "X"
anotherNewKey = "y"
"#;
    let parsed = parse_lakefile_toml(text, Path::new("lakefile.toml")).unwrap();
    assert_eq!(parsed.config.name, "x");
    assert_eq!(parsed.warnings.len(), 2);
    assert!(parsed.warnings[0].contains("someFutureLakeKey"));
    assert!(parsed.warnings[1].contains("anotherNewKey"));
}

#[test]
fn option_value_types_and_guillemet_exe_names() {
    let text = r#"
name = "x"

[[lean_lib]]
name = "X"
leanOptions = {a = true, b = 3, c = "s"}

[[lean_exe]]
name = "«cache-test»"
root = "Cache.Test"
"#;
    let parsed = parse_lakefile_toml(text, Path::new("lakefile.toml")).unwrap();
    let lib = &parsed.config.lean_libs[0];
    assert_eq!(lib.lean_options.get("a"), Some(&LeanOptionValue::Bool(true)));
    assert_eq!(lib.lean_options.get("b"), Some(&LeanOptionValue::Int(3)));
    assert_eq!(
        lib.lean_options.get("c"),
        Some(&LeanOptionValue::String("s".into()))
    );
    assert_eq!(parsed.config.lean_exes[0].name, "«cache-test»");
}

#[test]
fn toml_syntax_error_names_the_file() {
    let err = parse_lakefile_toml("name = ", Path::new("pkg/lakefile.toml")).unwrap_err();
    assert!(err.to_string().contains("pkg/lakefile.toml"));
}
```

- [ ] **Step 8: Run tests to verify they fail**

Run: `cargo test -p leanr_build --test config_fixtures`
Expected: compile FAILURE (`config` module empty).

- [ ] **Step 9: Implement the config schema**

`crates/leanr_build/src/config.rs`:

```rust
//! Native `lakefile.toml` schema (spec §Architecture, component 1).
//! Field coverage = what the Mathlib closure exercises plus obvious
//! basics; unknown keys warn (forward compatibility), never fail.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use serde::Deserialize;

use crate::error::BuildError;
use crate::modules::{Glob, ModuleName};

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(untagged)]
pub enum LeanOptionValue {
    Bool(bool),
    Int(i64),
    String(String),
}

pub type LeanOptions = BTreeMap<String, LeanOptionValue>;

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Require {
    pub name: String,
    #[serde(default)]
    pub scope: Option<String>,
    #[serde(default)]
    pub rev: Option<String>,
    #[serde(default)]
    pub version: Option<String>,
    #[serde(default)]
    pub git: Option<String>,
    #[serde(default)]
    pub path: Option<PathBuf>,
    #[serde(default)]
    pub options: BTreeMap<String, toml::Value>,
    #[serde(flatten)]
    pub unknown: BTreeMap<String, toml::Value>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LeanLibConfig {
    pub name: String,
    #[serde(default)]
    pub src_dir: Option<PathBuf>,
    #[serde(default)]
    pub roots: Option<Vec<String>>,
    #[serde(default)]
    pub globs: Option<Vec<Glob>>,
    #[serde(default)]
    pub lean_options: LeanOptions,
    #[serde(default)]
    pub default_facets: Option<toml::Value>,
    #[serde(flatten)]
    pub unknown: BTreeMap<String, toml::Value>,
}

impl LeanLibConfig {
    /// Lake defaults: `roots` defaults to `[name]`.
    /// A root that fails to parse as a module name is dropped here and
    /// surfaces later as an unresolved import; real-world roots are plain
    /// identifiers.
    pub fn effective_roots(&self) -> Vec<ModuleName> {
        match &self.roots {
            Some(rs) => rs.iter().filter_map(|r| ModuleName::parse(r).ok()).collect(),
            None => ModuleName::parse(&self.name).ok().into_iter().collect(),
        }
    }

    /// Lake defaults: `globs` defaults to `roots.map(Glob::One)`.
    pub fn effective_globs(&self) -> Vec<Glob> {
        match &self.globs {
            Some(gs) => gs.clone(),
            None => self.effective_roots().into_iter().map(Glob::One).collect(),
        }
    }
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LeanExeConfig {
    pub name: String,
    #[serde(default)]
    pub src_dir: Option<PathBuf>,
    #[serde(default)]
    pub root: Option<String>,
    #[serde(default)]
    pub support_interpreter: Option<bool>,
    #[serde(default)]
    pub weak_link_args: Option<Vec<String>>,
    #[serde(flatten)]
    pub unknown: BTreeMap<String, toml::Value>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PackageConfig {
    pub name: String,
    #[serde(default)]
    pub default_targets: Vec<String>,
    #[serde(default)]
    pub src_dir: Option<PathBuf>,
    #[serde(default)]
    pub lean_options: LeanOptions,
    // Parsed-but-unused (observed in the Mathlib closure; kept out of the
    // unknown-key warning path):
    #[serde(default)]
    pub test_driver: Option<String>,
    #[serde(default)]
    pub test_driver_args: Option<Vec<String>>,
    #[serde(default)]
    pub lint_driver: Option<String>,
    #[serde(default)]
    pub lint_driver_args: Option<Vec<String>>,
    #[serde(default)]
    pub precompile_modules: Option<bool>,
    #[serde(default)]
    pub platform_independent: Option<bool>,
    #[serde(default)]
    pub version: Option<toml::Value>,
    #[serde(default)]
    pub description: Option<String>,
    #[serde(default)]
    pub keywords: Option<Vec<String>>,
    #[serde(default)]
    pub license: Option<String>,
    #[serde(default, rename = "require")]
    pub requires: Vec<Require>,
    #[serde(default, rename = "lean_lib")]
    pub lean_libs: Vec<LeanLibConfig>,
    #[serde(default, rename = "lean_exe")]
    pub lean_exes: Vec<LeanExeConfig>,
    #[serde(flatten)]
    pub unknown: BTreeMap<String, toml::Value>,
}

#[derive(Debug)]
pub struct ParsedConfig {
    pub config: PackageConfig,
    /// Unknown-key warnings, in document order: "path: unknown key `k` (ignored)".
    pub warnings: Vec<String>,
}

pub fn parse_lakefile_toml(text: &str, path: &Path) -> Result<ParsedConfig, BuildError> {
    let config: PackageConfig = toml::from_str(text).map_err(|e| BuildError::Config {
        path: path.to_path_buf(),
        msg: e.to_string(),
    })?;
    let mut warnings = Vec::new();
    let warn = |warnings: &mut Vec<String>, ctx: &str, keys: &BTreeMap<String, toml::Value>| {
        for k in keys.keys() {
            warnings.push(format!("{}: unknown key `{k}` in {ctx} (ignored)", path.display()));
        }
    };
    warn(&mut warnings, "package", &config.unknown);
    for l in &config.lean_libs {
        warn(&mut warnings, &format!("lean_lib `{}`", l.name), &l.unknown);
    }
    for e in &config.lean_exes {
        warn(&mut warnings, &format!("lean_exe `{}`", e.name), &e.unknown);
    }
    for r in &config.requires {
        warn(&mut warnings, &format!("require `{}`", r.name), &r.unknown);
    }
    Ok(ParsedConfig { config, warnings })
}
```

Note: `#[serde(rename_all = "camelCase")]` maps `src_dir`→`srcDir`, `lean_options`→`leanOptions`, `default_targets`→`defaultTargets`, etc.; `require`/`lean_lib`/`lean_exe` array-of-table names are snake_case in Lake's format, hence the explicit renames. If the vendored-fixture test reports a warning for a key Lake actually defines (e.g. `defaultFacets` elsewhere in the wild), add it as a parsed-but-unused field rather than suppressing the warning.

- [ ] **Step 10: Run all tests, lint, commit**

Run: `cargo test -p leanr_build && mise run lint`
Expected: PASS.

```bash
git add Cargo.toml Cargo.lock crates/leanr_build
git commit -m "feat(build): leanr_build crate — lakefile.toml schema, ModuleName, Glob

New deps: toml+serde (native config format), serde_json (manifest, next
task), blake3 (bridge cache key, M2c hash), thiserror (crate convention).
Dev-only: tempfile, proptest, leanr_olean+leanr_kernel (oracle tests)."
```

Also run `mise run lint:deps`; if cargo-deny rejects a license from the new dependency tree, add the specific license to `deny.toml`'s allow list with a comment naming the crate that pulls it in (pattern already used for `Apache-2.0 WITH LLVM-exception`), and amend the commit.

---

### Task 2: Manifest reader

**Files:**
- Create: `crates/leanr_build/src/manifest.rs`
- Create: `crates/leanr_build/tests/fixtures/mathlib-manifest.json` (vendored)
- Modify: `crates/leanr_build/src/lib.rs` (add `pub mod manifest;`)
- Test: in-file `#[cfg(test)]`

**Interfaces:**
- Consumes: `BuildError` (Task 1).
- Produces:
  - `manifest::PackageSource` — `Git { url: String, rev: String, sub_dir: Option<PathBuf> } | Path { dir: PathBuf }`.
  - `manifest::ManifestPackage` — `{ name: String, source: PackageSource, config_file: PathBuf, inherited: bool }`.
  - `manifest::Manifest` — `{ packages_dir: PathBuf, packages: Vec<ManifestPackage> }`.
  - `manifest::parse_manifest(text: &str, path: &Path) -> Result<Manifest, BuildError>`.

- [ ] **Step 1: Vendor the fixture**

```bash
cp .mathlib/lake-manifest.json crates/leanr_build/tests/fixtures/mathlib-manifest.json
```

- [ ] **Step 2: Write failing tests**

In `crates/leanr_build/src/manifest.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    fn fixture() -> String {
        std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mathlib-manifest.json"),
        )
        .unwrap()
    }

    #[test]
    fn parses_mathlib_manifest() {
        let m = parse_manifest(&fixture(), Path::new("lake-manifest.json")).unwrap();
        assert_eq!(m.packages_dir, Path::new(".lake/packages"));
        assert_eq!(m.packages.len(), 8);
        let names: Vec<&str> = m.packages.iter().map(|p| p.name.as_str()).collect();
        assert!(names.contains(&"batteries") && names.contains(&"proofwidgets"));
        let b = m.packages.iter().find(|p| p.name == "batteries").unwrap();
        match &b.source {
            PackageSource::Git { url, rev, sub_dir } => {
                assert!(url.starts_with("https://github.com/"));
                assert_eq!(rev.len(), 40);
                assert!(sub_dir.is_none());
            }
            other => panic!("expected git source, got {other:?}"),
        }
        assert_eq!(b.config_file, Path::new("lakefile.toml"));
        let pw = m.packages.iter().find(|p| p.name == "proofwidgets").unwrap();
        assert_eq!(pw.config_file, Path::new("lakefile.lean"));
    }

    #[test]
    fn path_dependency_variant() {
        let text = r#"{"version": "1.2.0", "packagesDir": ".lake/packages",
            "packages": [{"type": "path", "name": "local", "dir": "../local",
                          "manifestFile": "lake-manifest.json", "inherited": false,
                          "configFile": "lakefile.toml"}]}"#;
        let m = parse_manifest(text, Path::new("m.json")).unwrap();
        match &m.packages[0].source {
            PackageSource::Path { dir } => assert_eq!(dir, Path::new("../local")),
            other => panic!("expected path source, got {other:?}"),
        }
    }

    #[test]
    fn unknown_major_version_is_a_clear_error() {
        let text = r#"{"version": "2.0.0", "packages": []}"#;
        let err = parse_manifest(text, Path::new("m.json")).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("2.0.0") && msg.contains("m.json"), "got: {msg}");
    }

    #[test]
    fn malformed_json_names_the_file() {
        let err = parse_manifest("{", Path::new("m.json")).unwrap_err();
        assert!(err.to_string().contains("m.json"));
    }

    #[test]
    fn git_package_missing_rev_is_an_error() {
        let text = r#"{"version": "1.2.0",
            "packages": [{"type": "git", "name": "x", "url": "https://e.com/x",
                          "configFile": "lakefile.toml", "inherited": false}]}"#;
        let err = parse_manifest(text, Path::new("m.json")).unwrap_err();
        assert!(err.to_string().contains("rev"));
    }
}
```

- [ ] **Step 3: Run tests to verify they fail**

Run: `cargo test -p leanr_build manifest`
Expected: compile FAILURE.

- [ ] **Step 4: Implement**

Top of `crates/leanr_build/src/manifest.rs`:

```rust
//! `lake-manifest.json` reader (spec §Architecture, component 3).
//! Schema 1.x observed at the pinned toolchain; unknown major versions
//! error clearly rather than mis-resolving.

use std::path::{Path, PathBuf};

use serde::Deserialize;

use crate::error::BuildError;

#[derive(Debug, Clone)]
pub enum PackageSource {
    Git { url: String, rev: String, sub_dir: Option<PathBuf> },
    Path { dir: PathBuf },
}

#[derive(Debug, Clone)]
pub struct ManifestPackage {
    pub name: String,
    pub source: PackageSource,
    pub config_file: PathBuf,
    pub inherited: bool,
}

#[derive(Debug, Clone)]
pub struct Manifest {
    pub packages_dir: PathBuf,
    pub packages: Vec<ManifestPackage>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct RawManifest {
    version: String,
    #[serde(default)]
    packages_dir: Option<PathBuf>,
    #[serde(default)]
    packages: Vec<RawPackage>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct RawPackage {
    name: String,
    #[serde(rename = "type")]
    kind: String,
    #[serde(default)]
    url: Option<String>,
    #[serde(default)]
    rev: Option<String>,
    #[serde(default)]
    sub_dir: Option<PathBuf>,
    #[serde(default)]
    dir: Option<PathBuf>,
    #[serde(default)]
    config_file: Option<PathBuf>,
    #[serde(default)]
    inherited: bool,
}

pub fn parse_manifest(text: &str, path: &Path) -> Result<Manifest, BuildError> {
    let err = |msg: String| BuildError::Manifest { path: path.to_path_buf(), msg };
    let raw: RawManifest =
        serde_json::from_str(text).map_err(|e| err(e.to_string()))?;
    let major = raw.version.split('.').next().unwrap_or("");
    if major != "1" {
        return Err(err(format!(
            "unsupported manifest version `{}` (leanr understands major version 1); \
             a newer lake wrote this file",
            raw.version
        )));
    }
    let mut packages = Vec::new();
    for p in raw.packages {
        let source = match p.kind.as_str() {
            "git" => PackageSource::Git {
                url: p.url.ok_or_else(|| err(format!("package `{}`: missing url", p.name)))?,
                rev: p.rev.ok_or_else(|| err(format!("package `{}`: missing rev", p.name)))?,
                sub_dir: p.sub_dir,
            },
            "path" => PackageSource::Path {
                dir: p.dir.ok_or_else(|| err(format!("package `{}`: missing dir", p.name)))?,
            },
            other => {
                return Err(err(format!("package `{}`: unknown type `{other}`", p.name)))
            }
        };
        packages.push(ManifestPackage {
            source,
            config_file: p.config_file.unwrap_or_else(|| PathBuf::from("lakefile.lean")),
            inherited: p.inherited,
            name: p.name,
        });
    }
    Ok(Manifest {
        packages_dir: raw.packages_dir.unwrap_or_else(|| PathBuf::from(".lake/packages")),
        packages,
    })
}
```

Add `pub mod manifest;` to `lib.rs`.

- [ ] **Step 5: Run tests, lint, commit**

Run: `cargo test -p leanr_build && mise run lint`
Expected: PASS.

```bash
git add crates/leanr_build
git commit -m "feat(build): lake-manifest.json reader with version check"
```

---

### Task 3: Glob expansion

**Files:**
- Modify: `crates/leanr_build/src/modules.rs`
- Test: in-file `#[cfg(test)]`

**Interfaces:**
- Consumes: `ModuleName`, `Glob`, `BuildError` (Task 1).
- Produces: `modules::expand_glob(glob: &Glob, src_dir: &Path) -> Result<Vec<ModuleName>, BuildError>` — sorted, deduplicated.

- [ ] **Step 1: Write failing tests**

Append to the `tests` module in `modules.rs`:

```rust
    fn touch(dir: &std::path::Path, rel: &str) {
        let p = dir.join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, "").unwrap();
    }

    #[test]
    fn expand_one_yields_the_module_without_touching_disk() {
        let m = ModuleName::parse("Mathlib").unwrap();
        let got = expand_glob(&Glob::One(m.clone()), std::path::Path::new("/nonexistent")).unwrap();
        assert_eq!(got, [m]);
    }

    #[test]
    fn expand_submodules_walks_the_directory() {
        let tmp = tempfile::TempDir::new().unwrap();
        touch(tmp.path(), "Cache/IO.lean");
        touch(tmp.path(), "Cache/Requests/Sub.lean");
        touch(tmp.path(), "Cache/README.md"); // ignored: not .lean
        touch(tmp.path(), "Cache.lean"); // ignored: Submodules is strict
        let g = Glob::Submodules(ModuleName::parse("Cache").unwrap());
        let got = expand_glob(&g, tmp.path()).unwrap();
        let names: Vec<String> = got.iter().map(|m| m.to_string()).collect();
        assert_eq!(names, ["Cache.IO", "Cache.Requests.Sub"]); // sorted
    }

    #[test]
    fn expand_and_submodules_includes_the_root_module() {
        let tmp = tempfile::TempDir::new().unwrap();
        touch(tmp.path(), "Cache.lean");
        touch(tmp.path(), "Cache/IO.lean");
        let g = Glob::AndSubmodules(ModuleName::parse("Cache").unwrap());
        let got = expand_glob(&g, tmp.path()).unwrap();
        let names: Vec<String> = got.iter().map(|m| m.to_string()).collect();
        assert_eq!(names, ["Cache", "Cache.IO"]);
    }

    #[test]
    fn expand_submodules_of_missing_dir_is_empty_not_an_error() {
        let g = Glob::Submodules(ModuleName::parse("Nope").unwrap());
        let tmp = tempfile::TempDir::new().unwrap();
        assert_eq!(expand_glob(&g, tmp.path()).unwrap(), []);
    }
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_build modules`
Expected: compile FAILURE (`expand_glob` undefined).

- [ ] **Step 3: Implement**

Add to `modules.rs`:

```rust
/// Expand a glob against a library source directory (spec component 5).
/// `One` is purely nominal (existence is checked later, at resolve time);
/// the directory walks are iterative (explicit stack — untrusted-deep
/// trees must not overflow) and results are sorted for determinism.
pub fn expand_glob(glob: &Glob, src_dir: &Path) -> Result<Vec<ModuleName>, BuildError> {
    match glob {
        Glob::One(m) => Ok(vec![m.clone()]),
        Glob::Submodules(m) => walk_submodules(m, src_dir),
        Glob::AndSubmodules(m) => {
            let mut out = vec![m.clone()];
            out.extend(walk_submodules(m, src_dir)?);
            out.sort();
            out.dedup();
            Ok(out)
        }
    }
}

fn walk_submodules(root: &ModuleName, src_dir: &Path) -> Result<Vec<ModuleName>, BuildError> {
    let base: PathBuf = src_dir.join(root.components().iter().collect::<PathBuf>());
    let mut out = Vec::new();
    if !base.is_dir() {
        return Ok(out); // no submodule directory — an empty glob, like lake
    }
    let mut stack = vec![(base.clone(), root.clone())];
    while let Some((dir, prefix)) = stack.pop() {
        let entries = std::fs::read_dir(&dir).map_err(|e| BuildError::Io {
            path: dir.clone(),
            err: e.to_string(),
        })?;
        for entry in entries {
            let entry = entry.map_err(|e| BuildError::Io {
                path: dir.clone(),
                err: e.to_string(),
            })?;
            let path = entry.path();
            let Some(stem) = path.file_stem().and_then(|s| s.to_str()) else {
                continue; // non-UTF-8 file name: not a Lean module
            };
            if path.is_dir() {
                stack.push((path, prefix.child(stem)));
            } else if path.extension().and_then(|e| e.to_str()) == Some("lean") {
                out.push(prefix.child(stem));
            }
        }
    }
    out.sort();
    out.dedup();
    Ok(out)
}
```

- [ ] **Step 4: Run tests, lint, commit**

Run: `cargo test -p leanr_build && mise run lint`
Expected: PASS.

```bash
git add crates/leanr_build/src/modules.rs
git commit -m "feat(build): glob expansion over library source trees"
```

---

### Task 4: Header scanner

**Files:**
- Create: `crates/leanr_build/src/scanner.rs`
- Modify: `crates/leanr_build/src/lib.rs` (add `pub mod scanner;`)
- Test: in-file `#[cfg(test)]` (tables + proptest)

**Interfaces:**
- Consumes: `ModuleName` (Task 1).
- Produces:
  - `scanner::Header` — `{ is_module: bool, prelude: bool, imports: Vec<ModuleName> }`.
  - `scanner::scan_header(bytes: &[u8]) -> Header` — **total**: never panics, never errors; malformed input just ends the header early. Grammar (surveyed over the whole Mathlib closure): optional `module`, optional `prelude`, then imports of the form `[public|private] [meta] import [all] <Name>`.

- [ ] **Step 1: Write failing tests**

`crates/leanr_build/src/scanner.rs`, tests first:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn imports(src: &str) -> Vec<String> {
        scan_header(src.as_bytes()).imports.iter().map(|m| m.to_string()).collect()
    }

    #[test]
    fn plain_imports() {
        let h = scan_header(b"import Foo\nimport Foo.Bar\ndef x := 1\nimport Nope");
        assert_eq!(
            h.imports.iter().map(|m| m.to_string()).collect::<Vec<_>>(),
            ["Foo", "Foo.Bar"]
        );
        assert!(!h.is_module && !h.prelude);
    }

    #[test]
    fn module_system_header_with_visibility_and_meta() {
        let src = "/- copyright -/\nmodule\n\npublic import Aesop\npublic meta import B.C\nmeta import D\nprivate import E\nimport all F\n\n/-! # doc -/\ntheorem t : True := trivial";
        let h = scan_header(src.as_bytes());
        assert!(h.is_module);
        assert_eq!(
            h.imports.iter().map(|m| m.to_string()).collect::<Vec<_>>(),
            ["Aesop", "B.C", "D", "E", "F"]
        );
    }

    #[test]
    fn prelude_and_trailing_line_comment_on_module() {
        let h = scan_header(b"module  -- shake: keep-all\nprelude\nimport Init.Core\n");
        assert!(h.is_module && h.prelude);
        assert_eq!(h.imports[0].to_string(), "Init.Core");
    }

    #[test]
    fn comments_anywhere_in_the_header() {
        let src = "-- line\n/- block /- nested -/ still -/ import A\nimport --mid\n B\n";
        assert_eq!(imports(src), ["A", "B"]);
    }

    #[test]
    fn import_all_takes_the_following_name() {
        assert_eq!(imports("import all Mathlib.X\n"), ["Mathlib.X"]);
        // `all` with no name after it is the imported module itself.
        assert_eq!(imports("import all\ndef x := 1"), ["all"]);
    }

    #[test]
    fn modifier_words_starting_a_declaration_end_the_header() {
        // `public def` / `meta def` are declarations, not imports.
        assert_eq!(imports("import A\npublic def f := 1\n"), ["A"]);
        assert_eq!(imports("import A\nmeta def f := 1\n"), ["A"]);
    }

    #[test]
    fn guillemet_import_and_word_module_only_at_start() {
        assert_eq!(imports("import «weird.name».Sub\n"), ["weird.name.Sub"]);
        // 'module' later in a file is prose/code, not a header keyword.
        let h = scan_header(b"import A\nmodule\n");
        assert!(!h.is_module);
        assert_eq!(h.imports.len(), 1);
    }

    #[test]
    fn degenerate_inputs_are_calm() {
        for src in [
            &b""[..], b"--", b"/- unterminated", b"import", b"import .", b"import \xFF\xFE",
            b"public", b"prelude", b"module", b"\xFF\xFF\xFF",
        ] {
            let _ = scan_header(src); // must not panic; imports may be empty
        }
        assert!(scan_header(b"import").imports.is_empty());
    }

    proptest! {
        /// Never-panic guarantee over arbitrary bytes (THREAT_MODEL.md
        /// discipline, same as the olean decoder).
        #[test]
        fn scan_header_never_panics(bytes in proptest::collection::vec(any::<u8>(), 0..4096)) {
            let _ = scan_header(&bytes);
        }
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_build scanner`
Expected: compile FAILURE.

- [ ] **Step 3: Implement the lexer**

Top of `crates/leanr_build/src/scanner.rs`:

```rust
//! Total header scanner (spec §Architecture, component 5): extracts
//! `module` / `prelude` / import statements from the top of a `.lean`
//! file. Grammar surveyed empirically over the pinned Mathlib closure:
//! `[module] [prelude] ([public|private] [meta] import [all] Name)*`.
//! Anything unrecognized simply ends the header — declarations like
//! `public def` must not be misread as imports.

use crate::modules::ModuleName;

#[derive(Debug, Default, PartialEq)]
pub struct Header {
    pub is_module: bool,
    pub prelude: bool,
    pub imports: Vec<ModuleName>,
}

/// Total over arbitrary bytes: invalid UTF-8 is decoded lossily and the
/// replacement characters end the header at the first token they corrupt.
pub fn scan_header(bytes: &[u8]) -> Header {
    let text = String::from_utf8_lossy(bytes);
    let mut lx = Lexer { s: &text, pos: 0 };
    let mut h = Header::default();

    lx.skip_trivia();
    if lx.eat_word("module") {
        h.is_module = true;
        lx.skip_trivia();
    }
    if lx.eat_word("prelude") {
        h.prelude = true;
        lx.skip_trivia();
    }
    loop {
        let mark = lx.pos;
        // Modifiers: at most one visibility, at most one `meta`.
        let _vis = lx.eat_word("public") || lx.eat_word("private");
        lx.skip_trivia();
        let _meta = lx.eat_word("meta");
        lx.skip_trivia();
        if !lx.eat_word("import") {
            lx.pos = mark; // `public def …`, EOF, or any declaration
            break;
        }
        lx.skip_trivia();
        // `import all Foo`: `all` is a keyword iff a name follows it;
        // otherwise `all` itself is the imported module.
        let mut name = lx.module_name();
        if name.as_ref().map(|m| m.to_string()).as_deref() == Some("all") {
            lx.skip_trivia();
            if let Some(real) = lx.module_name() {
                name = Some(real);
            }
        }
        match name {
            Some(m) => h.imports.push(m),
            None => {
                lx.pos = mark;
                break;
            }
        }
        lx.skip_trivia();
    }
    h
}

struct Lexer<'a> {
    s: &'a str,
    pos: usize,
}

impl<'a> Lexer<'a> {
    fn rest(&self) -> &'a str {
        &self.s[self.pos..]
    }

    /// Skip whitespace, `--` line comments, and (nested) `/- -/` block
    /// comments. An unterminated block comment consumes to EOF.
    fn skip_trivia(&mut self) {
        loop {
            let r = self.rest();
            if let Some(c) = r.chars().next() {
                if c.is_whitespace() {
                    self.pos += c.len_utf8();
                    continue;
                }
            }
            if r.starts_with("--") {
                match r.find('\n') {
                    Some(i) => self.pos += i + 1,
                    None => self.pos = self.s.len(),
                }
                continue;
            }
            if r.starts_with("/-") {
                let mut depth = 1usize;
                let mut i = 2;
                let b = r.as_bytes();
                while i < b.len() && depth > 0 {
                    if r[i..].starts_with("/-") {
                        depth += 1;
                        i += 2;
                    } else if r[i..].starts_with("-/") {
                        depth -= 1;
                        i += 2;
                    } else {
                        // advance one whole char, not one byte
                        let ch = r[i..].chars().next().unwrap();
                        i += ch.len_utf8();
                    }
                }
                self.pos += i;
                continue;
            }
            break;
        }
    }

    /// Consume `word` iff the next token is exactly that identifier.
    fn eat_word(&mut self, word: &str) -> bool {
        let r = self.rest();
        if r.starts_with(word) {
            let after = r[word.len()..].chars().next();
            if after.is_none() || !after.unwrap().is_alphanumeric() && after != Some('_') {
                if after != Some('.') && after != Some('«') {
                    self.pos += word.len();
                    return true;
                }
            }
        }
        false
    }

    /// Consume a dotted module name: `comp ('.' comp)*` where comp is an
    /// identifier (`[A-Za-z_][A-Za-z0-9_'!?]*`, plus any non-ASCII
    /// letter Lean allows — we accept any non-ASCII alphanumeric) or a
    /// `«...»` atom. Returns None (consuming nothing) if no name starts here.
    fn module_name(&mut self) -> Option<ModuleName> {
        let start = self.pos;
        let mut raw = String::new();
        loop {
            let r = self.rest();
            let mut chars = r.chars();
            match chars.next() {
                Some('«') => {
                    raw.push('«');
                    self.pos += '«'.len_utf8();
                    loop {
                        let c = self.rest().chars().next();
                        match c {
                            Some(c) => {
                                raw.push(c);
                                self.pos += c.len_utf8();
                                if c == '»' {
                                    break;
                                }
                            }
                            None => {
                                self.pos = start;
                                return None; // unclosed
                            }
                        }
                    }
                }
                Some(c) if c.is_alphabetic() || c == '_' => {
                    while let Some(c) = self.rest().chars().next() {
                        if c.is_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?') {
                            raw.push(c);
                            self.pos += c.len_utf8();
                        } else {
                            break;
                        }
                    }
                }
                _ => {
                    self.pos = start;
                    return None;
                }
            }
            if self.rest().starts_with('.') {
                // A dot continues the name only if a component follows.
                let peek = self.s[self.pos + 1..].chars().next();
                let continues = matches!(peek, Some(c) if c.is_alphabetic() || c == '_' || c == '«');
                if continues {
                    raw.push('.');
                    self.pos += 1;
                    continue;
                }
            }
            break;
        }
        match ModuleName::parse(&raw) {
            Ok(m) => Some(m),
            Err(_) => {
                self.pos = start;
                None
            }
        }
    }
}
```

Note for the implementer: the `eat_word` guard rejects `moduleX` / `import.Y` / `prelude«x»` as keyword hits; the table tests pin this. If a table test fails, fix the lexer — do not weaken the test.

- [ ] **Step 4: Run tests to verify they pass (incl. proptest)**

Run: `cargo test -p leanr_build scanner`
Expected: PASS (proptest runs 256 cases by default).

- [ ] **Step 5: Lint, commit**

```bash
mise run lint && git add crates/leanr_build/src/scanner.rs crates/leanr_build/src/lib.rs
git commit -m "feat(build): total .lean header scanner (module/prelude/import grammar)"
```

---

### Task 5: Module resolver, graph builder, topological waves

**Files:**
- Create: `crates/leanr_build/src/graph.rs`
- Modify: `crates/leanr_build/src/lib.rs` (add `pub mod graph;`)
- Test: in-file `#[cfg(test)]` (synthetic tempdir trees)

**Interfaces:**
- Consumes: `ModuleName` (Task 1), `scanner::scan_header` (Task 4), `BuildError` (Task 1).
- Produces:
  - `graph::LibUnit` — `{ package: String, src_dir: PathBuf, root: ModuleName }`.
  - `graph::ModuleResolver` — `new(units: Vec<LibUnit>)`, `resolve(&self, m: &ModuleName) -> Option<(String, PathBuf)>` (longest-root-prefix match; `Some` only if the file exists).
  - `graph::ToolchainIndex` trait — `fn contains(&self, m: &ModuleName) -> bool`; impl `graph::OleanDirIndex { root: PathBuf }` (stats `<root>/<A/B/C>.olean`).
  - `graph::ModuleId(u32)`, `graph::ModuleInfo` — `{ name, package, file, imports: Vec<ModuleName>, deps: Vec<ModuleId>, prelude: bool, is_module: bool }`.
  - `graph::ModuleGraph` — `{ modules: Vec<ModuleInfo> }` with `id_of(&ModuleName) -> Option<ModuleId>`.
  - `graph::build_graph(seeds: &[ModuleName], resolver: &ModuleResolver, toolchain: &dyn ToolchainIndex) -> Result<ModuleGraph, BuildError>`.
  - `graph::topo_waves(g: &ModuleGraph) -> Result<Vec<Vec<ModuleId>>, BuildError>` — waves sorted internally by module name; cycle → `BuildError::ImportCycle`.

- [ ] **Step 1: Write failing tests**

Test module of `crates/leanr_build/src/graph.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::modules::ModuleName;
    use std::collections::HashSet;
    use std::path::PathBuf;

    fn mn(s: &str) -> ModuleName {
        ModuleName::parse(s).unwrap()
    }

    fn write(dir: &std::path::Path, rel: &str, text: &str) {
        let p = dir.join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    }

    /// Toolchain fake: a fixed set of module names.
    struct FakeToolchain(HashSet<String>);
    impl ToolchainIndex for FakeToolchain {
        fn contains(&self, m: &ModuleName) -> bool {
            self.0.contains(&m.to_string())
        }
    }

    fn fake_toolchain() -> FakeToolchain {
        FakeToolchain(["Init", "Init.Core", "Lean"].iter().map(|s| s.to_string()).collect())
    }

    /// Two packages: `app` (lib App) depends on `dep` (lib Dep).
    fn two_package_workspace() -> (tempfile::TempDir, ModuleResolver) {
        let tmp = tempfile::TempDir::new().unwrap();
        write(tmp.path(), "app/App.lean", "import App.A\nimport Dep\n");
        write(tmp.path(), "app/App/A.lean", "import Init.Core\n");
        write(tmp.path(), "dep/Dep.lean", "prelude\n");
        let resolver = ModuleResolver::new(vec![
            LibUnit { package: "app".into(), src_dir: tmp.path().join("app"), root: mn("App") },
            LibUnit { package: "dep".into(), src_dir: tmp.path().join("dep"), root: mn("Dep") },
        ]);
        (tmp, resolver)
    }

    #[test]
    fn resolver_longest_prefix_and_existence() {
        let (tmp, r) = two_package_workspace();
        let (pkg, file) = r.resolve(&mn("App.A")).unwrap();
        assert_eq!(pkg, "app");
        assert_eq!(file, tmp.path().join("app/App/A.lean"));
        assert!(r.resolve(&mn("App.Missing")).is_none()); // root matches, file absent
        assert!(r.resolve(&mn("Other")).is_none());
    }

    #[test]
    fn build_graph_follows_transitive_imports_and_classifies_toolchain() {
        let (_tmp, r) = two_package_workspace();
        let g = build_graph(&[mn("App")], &r, &fake_toolchain()).unwrap();
        let names: HashSet<String> = g.modules.iter().map(|m| m.name.to_string()).collect();
        assert_eq!(
            names,
            ["App", "App.A", "Dep"].iter().map(|s| s.to_string()).collect()
        );
        // Init.Core is toolchain-external: recorded in imports, no dep edge.
        let a = &g.modules[g.id_of(&mn("App.A")).unwrap().0 as usize];
        assert!(a.imports.contains(&mn("Init.Core")));
        assert!(a.deps.is_empty());
    }

    #[test]
    fn unresolved_import_names_module_and_importer() {
        let tmp = tempfile::TempDir::new().unwrap();
        write(tmp.path(), "app/App.lean", "import Ghost\n");
        let r = ModuleResolver::new(vec![LibUnit {
            package: "app".into(),
            src_dir: tmp.path().join("app"),
            root: mn("App"),
        }]);
        let err = build_graph(&[mn("App")], &r, &fake_toolchain()).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("Ghost") && msg.contains("App"), "got: {msg}");
    }

    #[test]
    fn waves_respect_deps_and_sort_lexicographically() {
        let (_tmp, r) = two_package_workspace();
        let g = build_graph(&[mn("App")], &r, &fake_toolchain()).unwrap();
        let waves = topo_waves(&g).unwrap();
        let render: Vec<Vec<String>> = waves
            .iter()
            .map(|w| w.iter().map(|id| g.modules[id.0 as usize].name.to_string()).collect())
            .collect();
        assert_eq!(render, [vec!["App.A".to_string(), "Dep".to_string()], vec!["App".to_string()]]);
    }

    #[test]
    fn cycle_is_reported_with_its_members() {
        let tmp = tempfile::TempDir::new().unwrap();
        write(tmp.path(), "app/App.lean", "import App.B\n");
        write(tmp.path(), "app/App/B.lean", "import App\n");
        let r = ModuleResolver::new(vec![LibUnit {
            package: "app".into(),
            src_dir: tmp.path().join("app"),
            root: mn("App"),
        }]);
        let g = build_graph(&[mn("App")], &r, &fake_toolchain()).unwrap();
        let err = topo_waves(&g).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("cycle") && msg.contains("App.B"), "got: {msg}");
    }

    #[test]
    fn duplicate_imports_yield_one_dep_edge() {
        let tmp = tempfile::TempDir::new().unwrap();
        write(tmp.path(), "app/App.lean", "import App.B\nimport App.B\n");
        write(tmp.path(), "app/App/B.lean", "");
        let r = ModuleResolver::new(vec![LibUnit {
            package: "app".into(),
            src_dir: tmp.path().join("app"),
            root: mn("App"),
        }]);
        let g = build_graph(&[mn("App")], &r, &fake_toolchain()).unwrap();
        let app = &g.modules[g.id_of(&mn("App")).unwrap().0 as usize];
        assert_eq!(app.deps.len(), 1);
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_build graph`
Expected: compile FAILURE.

- [ ] **Step 3: Implement**

Top of `crates/leanr_build/src/graph.rs`:

```rust
//! Module resolution + import DAG (spec §Architecture, component 5).
//! BFS from the target seeds; header scans of each frontier run in
//! parallel (scoped threads, no external deps). All ordering is
//! deterministic: frontiers and waves are sorted by module name.

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use crate::error::BuildError;
use crate::modules::ModuleName;
use crate::scanner::{scan_header, Header};

pub struct LibUnit {
    pub package: String,
    pub src_dir: PathBuf,
    pub root: ModuleName,
}

pub struct ModuleResolver {
    units: Vec<LibUnit>,
}

impl ModuleResolver {
    pub fn new(units: Vec<LibUnit>) -> ModuleResolver {
        ModuleResolver { units }
    }

    /// Longest-root-prefix match over all libs; `Some` only if the mapped
    /// file exists on disk (a matching prefix with a missing file falls
    /// through to the next-longest candidate, then to the toolchain).
    pub fn resolve(&self, m: &ModuleName) -> Option<(String, PathBuf)> {
        let mut candidates: Vec<&LibUnit> = self
            .units
            .iter()
            .filter(|u| m.starts_with(&u.root))
            .collect();
        candidates.sort_by_key(|u| std::cmp::Reverse(u.root.components().len()));
        for u in candidates {
            let file = u.src_dir.join(m.rel_lean_path());
            if file.is_file() {
                return Some((u.package.clone(), file));
            }
        }
        None
    }
}

pub trait ToolchainIndex: Sync {
    fn contains(&self, m: &ModuleName) -> bool;
}

/// The real index: `<root>/<A/B/C>.olean` exists in the toolchain libdir
/// (`lean --print-libdir`).
pub struct OleanDirIndex {
    pub root: PathBuf,
}

impl ToolchainIndex for OleanDirIndex {
    fn contains(&self, m: &ModuleName) -> bool {
        let mut p: PathBuf = self.root.join(m.components().iter().collect::<PathBuf>());
        p.set_extension("olean");
        p.is_file()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModuleId(pub u32);

#[derive(Debug)]
pub struct ModuleInfo {
    pub name: ModuleName,
    pub package: String,
    pub file: PathBuf,
    /// Raw scanned imports, including toolchain-external ones.
    pub imports: Vec<ModuleName>,
    /// Workspace-internal dependency edges (deduplicated).
    pub deps: Vec<ModuleId>,
    pub prelude: bool,
    pub is_module: bool,
}

pub struct ModuleGraph {
    pub modules: Vec<ModuleInfo>,
    index: HashMap<ModuleName, ModuleId>,
}

impl ModuleGraph {
    pub fn id_of(&self, m: &ModuleName) -> Option<ModuleId> {
        self.index.get(m).copied()
    }
}

pub fn build_graph(
    seeds: &[ModuleName],
    resolver: &ModuleResolver,
    toolchain: &dyn ToolchainIndex,
) -> Result<ModuleGraph, BuildError> {
    // name -> (package, file, header); imports kept as names until all
    // nodes exist, then edges are wired up.
    let mut scanned: HashMap<ModuleName, (String, PathBuf, Header)> = HashMap::new();
    let mut external: HashSet<ModuleName> = HashSet::new();
    // Frontier entries carry their importer for error messages.
    let mut frontier: Vec<(ModuleName, String)> = seeds
        .iter()
        .map(|m| (m.clone(), "<target>".to_string()))
        .collect();

    while !frontier.is_empty() {
        frontier.sort();
        frontier.dedup();
        // Resolve + classify this frontier.
        let mut to_scan: Vec<(ModuleName, String, PathBuf)> = Vec::new();
        for (m, importer) in frontier.drain(..) {
            if scanned.contains_key(&m) || external.contains(&m) {
                continue;
            }
            match resolver.resolve(&m) {
                Some((pkg, file)) => to_scan.push((m, pkg, file)),
                None if toolchain.contains(&m) => {
                    external.insert(m);
                }
                None => {
                    return Err(BuildError::UnresolvedImport {
                        module: m.to_string(),
                        importer,
                    })
                }
            }
        }
        // Scan the frontier's files in parallel (scoped threads).
        let results: Vec<Result<(ModuleName, String, PathBuf, Header), BuildError>> =
            std::thread::scope(|s| {
                let handles: Vec<_> = to_scan
                    .into_iter()
                    .map(|(m, pkg, file)| {
                        s.spawn(move || {
                            let bytes = std::fs::read(&file).map_err(|e| BuildError::Io {
                                path: file.clone(),
                                err: e.to_string(),
                            })?;
                            Ok((m, pkg, file, scan_header(&bytes)))
                        })
                    })
                    .collect();
                handles.into_iter().map(|h| h.join().expect("scan thread")).collect()
            });
        for r in results {
            let (m, pkg, file, header) = r?;
            for imp in &header.imports {
                frontier.push((imp.clone(), m.to_string()));
            }
            scanned.insert(m, (pkg, file, header));
        }
    }

    // Deterministic node order: sorted by name.
    let mut names: Vec<ModuleName> = scanned.keys().cloned().collect();
    names.sort();
    let index: HashMap<ModuleName, ModuleId> = names
        .iter()
        .enumerate()
        .map(|(i, n)| (n.clone(), ModuleId(i as u32)))
        .collect();
    let mut modules = Vec::with_capacity(names.len());
    for name in names {
        let (package, file, header) = scanned.remove(&name).expect("scanned");
        let mut deps: Vec<ModuleId> = header
            .imports
            .iter()
            .filter_map(|i| index.get(i).copied())
            .collect();
        deps.sort_by_key(|id| id.0);
        deps.dedup();
        modules.push(ModuleInfo {
            name,
            package,
            file,
            imports: header.imports,
            deps,
            prelude: header.prelude,
            is_module: header.is_module,
        });
    }
    Ok(ModuleGraph { modules, index })
}

/// Kahn's algorithm into waves; each wave sorted by module name (module
/// order == index order, which is name-sorted). Cycles are reported with
/// one witness cycle path.
pub fn topo_waves(g: &ModuleGraph) -> Result<Vec<Vec<ModuleId>>, BuildError> {
    let n = g.modules.len();
    let mut remaining_deps: Vec<usize> = g.modules.iter().map(|m| m.deps.len()).collect();
    let mut dependents: Vec<Vec<u32>> = vec![Vec::new(); n];
    for (i, m) in g.modules.iter().enumerate() {
        for d in &m.deps {
            dependents[d.0 as usize].push(i as u32);
        }
    }
    let mut waves = Vec::new();
    let mut done = 0usize;
    let mut ready: Vec<u32> =
        (0..n as u32).filter(|&i| remaining_deps[i as usize] == 0).collect();
    while !ready.is_empty() {
        ready.sort();
        let wave: Vec<ModuleId> = ready.iter().map(|&i| ModuleId(i)).collect();
        let mut next = Vec::new();
        for &i in &ready {
            for &dep in &dependents[i as usize] {
                remaining_deps[dep as usize] -= 1;
                if remaining_deps[dep as usize] == 0 {
                    next.push(dep);
                }
            }
        }
        done += wave.len();
        waves.push(wave);
        ready = next;
    }
    if done < n {
        // Extract one witness cycle by walking deps among leftover nodes.
        let start = (0..n).find(|&i| remaining_deps[i] > 0).expect("leftover");
        let mut path = vec![start];
        let mut seen = HashMap::from([(start, 0usize)]);
        loop {
            let cur = *path.last().expect("nonempty");
            let next = g.modules[cur]
                .deps
                .iter()
                .map(|d| d.0 as usize)
                .find(|&d| remaining_deps[d] > 0)
                .expect("cyclic node has a cyclic dep");
            if let Some(&at) = seen.get(&next) {
                let cycle: Vec<String> = path[at..]
                    .iter()
                    .chain(std::iter::once(&next))
                    .map(|&i| g.modules[i].name.to_string())
                    .collect();
                return Err(BuildError::ImportCycle { cycle });
            }
            seen.insert(next, path.len());
            path.push(next);
        }
    }
    Ok(waves)
}
```

Implementer note: one thread per frontier file is acceptable for M2a's synthetic tests but Mathlib frontiers reach thousands of files — chunk the frontier into `std::thread::available_parallelism()` slices inside the same `thread::scope` (each thread scans a slice sequentially) before running the differential tier. Keep the observable ordering identical (results are re-sorted by name afterward regardless).

- [ ] **Step 4: Run tests, lint, commit**

Run: `cargo test -p leanr_build && mise run lint`
Expected: PASS.

```bash
git add crates/leanr_build/src/graph.rs crates/leanr_build/src/lib.rs
git commit -m "feat(build): module resolver, import DAG builder, topological waves"
```

---

### Task 6: translate-config bridge

**Files:**
- Create: `crates/leanr_build/src/bridge.rs`
- Create: `crates/leanr_build/tests/fixtures/fake-lake-ok.sh`, `fake-lake-fail.sh`, `fake-lake-hang.sh`
- Modify: `crates/leanr_build/src/lib.rs` (add `pub mod bridge;`)
- Test: in-file `#[cfg(test)]`

**Interfaces:**
- Consumes: `config::{ParsedConfig, parse_lakefile_toml}` (Task 1), `BuildError` (Task 1).
- Produces:
  - `bridge::LakeInvoker` — `{ program: PathBuf, toolchain: Option<String>, timeout: Duration }`, `Default` = `{ "lake", None, 300s }`.
  - `bridge::translate_lakefile(pkg_dir: &Path, lake: &LakeInvoker, out: &Path) -> Result<(), BuildError>` — runs `lake [+<toolchain>] translate-config toml <out>` with cwd `pkg_dir`.
  - `bridge::load_config(pkg_dir: &Path, config_file: &Path, cache_dir: &Path, lake: &LakeInvoker) -> Result<ParsedConfig, BuildError>` — native for `.toml`, bridged+cached for `.lean`.

- [ ] **Step 1: Create the fake-lake fixtures**

`crates/leanr_build/tests/fixtures/fake-lake-ok.sh`:

```sh
#!/bin/sh
# Fake `lake translate-config toml <out>` for bridge unit tests:
# $1=translate-config $2=toml $3=<out>. Emits a minimal valid config and
# records its cwd so the test can assert it ran in the package dir.
printf 'name = "fake"\n\n[[lean_lib]]\nname = "Fake"\n' > "$3"
pwd > "${FAKE_LAKE_CWD_FILE:-/dev/null}"
```

`fake-lake-fail.sh`:

```sh
#!/bin/sh
echo "error: ill-formed configuration file" >&2
exit 1
```

`fake-lake-hang.sh`:

```sh
#!/bin/sh
sleep 60
```

```bash
chmod +x crates/leanr_build/tests/fixtures/fake-lake-*.sh
```

- [ ] **Step 2: Write failing tests**

Test module of `crates/leanr_build/src/bridge.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use std::path::{Path, PathBuf};
    use std::time::Duration;

    fn fake(name: &str) -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name)
    }

    fn pkg_with_lakefile_lean() -> tempfile::TempDir {
        let tmp = tempfile::TempDir::new().unwrap();
        std::fs::write(tmp.path().join("lakefile.lean"), "import Lake\n-- v1").unwrap();
        tmp
    }

    #[test]
    fn toml_config_is_parsed_natively_without_invoking_lake() {
        let tmp = tempfile::TempDir::new().unwrap();
        std::fs::write(tmp.path().join("lakefile.toml"), "name = \"native\"").unwrap();
        let lake = LakeInvoker {
            program: PathBuf::from("/definitely/not/a/binary"),
            ..LakeInvoker::default()
        };
        let parsed = load_config(
            tmp.path(),
            Path::new("lakefile.toml"),
            &tmp.path().join("cache"),
            &lake,
        )
        .unwrap();
        assert_eq!(parsed.config.name, "native");
    }

    #[test]
    fn lean_config_is_bridged_and_cached_by_content_hash() {
        let pkg = pkg_with_lakefile_lean();
        let cache = tempfile::TempDir::new().unwrap();
        let cwd_file = cache.path().join("cwd");
        std::env::set_var("FAKE_LAKE_CWD_FILE", &cwd_file);
        let lake = LakeInvoker { program: fake("fake-lake-ok.sh"), ..LakeInvoker::default() };

        let p1 = load_config(pkg.path(), Path::new("lakefile.lean"), cache.path(), &lake).unwrap();
        assert_eq!(p1.config.name, "fake");
        // Ran in the package directory.
        let ran_in = std::fs::read_to_string(&cwd_file).unwrap();
        assert_eq!(
            Path::new(ran_in.trim()).canonicalize().unwrap(),
            pkg.path().canonicalize().unwrap()
        );
        // Exactly one cache entry, keyed by lakefile hash.
        let entries: Vec<_> = std::fs::read_dir(cache.path())
            .unwrap()
            .filter_map(|e| e.ok())
            .filter(|e| e.path().extension().map(|x| x == "toml").unwrap_or(false))
            .collect();
        assert_eq!(entries.len(), 1);

        // Cache hit: a now-broken lake is never invoked.
        let broken = LakeInvoker {
            program: PathBuf::from("/definitely/not/a/binary"),
            ..LakeInvoker::default()
        };
        let p2 =
            load_config(pkg.path(), Path::new("lakefile.lean"), cache.path(), &broken).unwrap();
        assert_eq!(p2.config.name, "fake");

        // Changing the lakefile misses the cache (and here fails: broken lake).
        std::fs::write(pkg.path().join("lakefile.lean"), "import Lake\n-- v2").unwrap();
        assert!(
            load_config(pkg.path(), Path::new("lakefile.lean"), cache.path(), &broken).is_err()
        );
    }

    #[test]
    fn bridge_failure_carries_lakes_stderr() {
        let pkg = pkg_with_lakefile_lean();
        let cache = tempfile::TempDir::new().unwrap();
        let lake = LakeInvoker { program: fake("fake-lake-fail.sh"), ..LakeInvoker::default() };
        let err =
            load_config(pkg.path(), Path::new("lakefile.lean"), cache.path(), &lake).unwrap_err();
        assert!(err.to_string().contains("ill-formed configuration file"));
    }

    #[test]
    fn bridge_times_out_instead_of_hanging() {
        let pkg = pkg_with_lakefile_lean();
        let cache = tempfile::TempDir::new().unwrap();
        let lake = LakeInvoker {
            program: fake("fake-lake-hang.sh"),
            timeout: Duration::from_millis(300),
            ..LakeInvoker::default()
        };
        let start = std::time::Instant::now();
        let err =
            load_config(pkg.path(), Path::new("lakefile.lean"), cache.path(), &lake).unwrap_err();
        assert!(start.elapsed() < Duration::from_secs(10));
        assert!(err.to_string().contains("timed out"));
    }
}
```

(`std::env::set_var` in a test: fine here because only this one test reads `FAKE_LAKE_CWD_FILE`; do not add a second test using it.)

- [ ] **Step 3: Run tests to verify they fail**

Run: `cargo test -p leanr_build bridge`
Expected: compile FAILURE.

- [ ] **Step 4: Implement**

Top of `crates/leanr_build/src/bridge.rs`:

```rust
//! translate-config bridge (spec §Architecture, component 2): obtain a
//! declarative TOML config for `lakefile.lean` packages by running pinned
//! official lake once, cached by lakefile content hash. Executing a
//! lakefile is arbitrary code execution by design — identical trust to
//! running lake itself (spec §Error handling & trust).
//!
//! Verified empirically (spec §Architecture): translation works in a bare
//! checkout with no materialized dependencies, so bridging the root
//! config before fetching is sound; lake errors if the out-file exists,
//! so we hand it a fresh temp path and rename into the cache.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

use crate::config::{parse_lakefile_toml, ParsedConfig};
use crate::error::BuildError;

pub struct LakeInvoker {
    /// The lake executable (PATH-resolved name or explicit path).
    pub program: PathBuf,
    /// elan toolchain override, passed as `+<toolchain>` — pins dependency
    /// bridging to the *root* workspace's toolchain so a dep's own
    /// lean-toolchain file can't trigger a surprise toolchain download.
    pub toolchain: Option<String>,
    pub timeout: Duration,
}

impl Default for LakeInvoker {
    fn default() -> LakeInvoker {
        LakeInvoker {
            program: PathBuf::from("lake"),
            toolchain: None,
            timeout: Duration::from_secs(300),
        }
    }
}

/// Run `lake [+tc] translate-config toml <out>` with cwd `pkg_dir`.
pub fn translate_lakefile(
    pkg_dir: &Path,
    lake: &LakeInvoker,
    out: &Path,
) -> Result<(), BuildError> {
    let mut cmd = Command::new(&lake.program);
    if let Some(tc) = &lake.toolchain {
        cmd.arg(format!("+{tc}"));
    }
    cmd.arg("translate-config").arg("toml").arg(out);
    cmd.current_dir(pkg_dir);
    cmd.stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::piped());
    let display = format!("{} translate-config toml", lake.program.display());
    let sub = |reason: String, stderr: String| BuildError::Subprocess {
        cmd: display.clone(),
        reason,
        stderr,
    };
    let mut child = cmd
        .spawn()
        .map_err(|e| sub(format!("failed to start: {e}"), String::new()))?;
    let deadline = std::time::Instant::now() + lake.timeout;
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let mut stderr = String::new();
                if let Some(mut s) = child.stderr.take() {
                    use std::io::Read;
                    let _ = s.read_to_string(&mut stderr);
                }
                if status.success() {
                    return Ok(());
                }
                return Err(sub(format!("failed ({status})"), stderr));
            }
            Ok(None) => {
                if std::time::Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(sub(
                        format!("timed out after {}s", lake.timeout.as_secs()),
                        String::new(),
                    ));
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(e) => return Err(sub(format!("wait failed: {e}"), String::new())),
        }
    }
}

/// Load a package's config: native parse for `.toml`, bridge for `.lean`
/// (cache: `<cache_dir>/<blake3(lakefile)>.toml`).
pub fn load_config(
    pkg_dir: &Path,
    config_file: &Path,
    cache_dir: &Path,
    lake: &LakeInvoker,
) -> Result<ParsedConfig, BuildError> {
    let config_path = pkg_dir.join(config_file);
    let read = |p: &Path| {
        std::fs::read(p).map_err(|e| BuildError::Io { path: p.to_path_buf(), err: e.to_string() })
    };
    if config_file.extension().and_then(|e| e.to_str()) == Some("toml") {
        let text = String::from_utf8_lossy(&read(&config_path)?).into_owned();
        return parse_lakefile_toml(&text, &config_path);
    }
    let hash = blake3::hash(&read(&config_path)?).to_hex();
    let cached = cache_dir.join(format!("{hash}.toml"));
    if !cached.is_file() {
        std::fs::create_dir_all(cache_dir).map_err(|e| BuildError::Io {
            path: cache_dir.to_path_buf(),
            err: e.to_string(),
        })?;
        let tmp = cache_dir.join(format!("{hash}.toml.tmp{}", std::process::id()));
        let _ = std::fs::remove_file(&tmp); // stale tmp from a killed run
        // Absolute out path: lake runs with cwd = pkg_dir, not cache_dir.
        let tmp_abs = if tmp.is_absolute() {
            tmp.clone()
        } else {
            std::env::current_dir()
                .map_err(|e| BuildError::Io { path: tmp.clone(), err: e.to_string() })?
                .join(&tmp)
        };
        translate_lakefile(pkg_dir, lake, &tmp_abs)?;
        std::fs::rename(&tmp, &cached).map_err(|e| BuildError::Io {
            path: cached.clone(),
            err: e.to_string(),
        })?;
    }
    let text = String::from_utf8_lossy(&read(&cached)?).into_owned();
    // Errors point at the real lakefile, not the cache artifact.
    parse_lakefile_toml(&text, &config_path)
}
```

- [ ] **Step 5: Run tests, lint, commit**

Run: `cargo test -p leanr_build && mise run lint`
Expected: PASS (hang test finishes in <10 s).

```bash
git add crates/leanr_build
git commit -m "feat(build): lake translate-config bridge with content-hash cache and timeout"
```

---

### Task 7: Git materializer + THREAT_MODEL section

**Files:**
- Create: `crates/leanr_build/src/fetch.rs`
- Modify: `crates/leanr_build/src/lib.rs` (add `pub mod fetch;`), `docs/THREAT_MODEL.md`
- Test: in-file `#[cfg(test)]` (local git repos in tempdirs — `git` is required for the whole repo's development, so tests may shell out to it)

**Interfaces:**
- Consumes: `manifest::{ManifestPackage, PackageSource}` (Task 2), `BuildError` (Task 1).
- Produces:
  - `fetch::validate_git_url(url: &str) -> Result<(), String>`.
  - `fetch::materialize(packages: &[ManifestPackage], ws_root: &Path, packages_dir: &Path) -> Result<(), BuildError>` — after `Ok`, every git package is checked out at exactly its manifest rev under `packages_dir/<name>`; path packages verified to exist. Concurrent across packages; first error (in package order) wins.

- [ ] **Step 1: Write failing tests**

Test module of `crates/leanr_build/src/fetch.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::manifest::{ManifestPackage, PackageSource};
    use std::path::{Path, PathBuf};

    fn sh(dir: &Path, cmd: &str) -> String {
        let out = std::process::Command::new("sh")
            .arg("-c")
            .arg(cmd)
            .current_dir(dir)
            .output()
            .unwrap();
        assert!(out.status.success(), "{cmd}: {}", String::from_utf8_lossy(&out.stderr));
        String::from_utf8(out.stdout).unwrap().trim().to_string()
    }

    /// A local origin repo with two commits; returns (tempdir, rev1, rev2).
    fn origin() -> (tempfile::TempDir, String, String) {
        let tmp = tempfile::TempDir::new().unwrap();
        sh(tmp.path(), "git init -q -b main && git -c user.email=t@t -c user.name=t commit -q --allow-empty -m one");
        let r1 = sh(tmp.path(), "git rev-parse HEAD");
        sh(tmp.path(), "git -c user.email=t@t -c user.name=t commit -q --allow-empty -m two");
        let r2 = sh(tmp.path(), "git rev-parse HEAD");
        (tmp, r1, r2)
    }

    fn git_pkg(name: &str, url: String, rev: String) -> ManifestPackage {
        ManifestPackage {
            name: name.into(),
            source: PackageSource::Git { url, rev, sub_dir: None },
            config_file: PathBuf::from("lakefile.toml"),
            inherited: false,
        }
    }

    #[test]
    fn url_validation() {
        assert!(validate_git_url("https://github.com/x/y").is_ok());
        assert!(validate_git_url("ssh://git@github.com/x/y").is_ok());
        assert!(validate_git_url("git@github.com:x/y.git").is_ok());
        assert!(validate_git_url("/abs/path/repo").is_ok());
        assert!(validate_git_url("-oProxyCommand=evil").is_err());
        assert!(validate_git_url("ext::sh -c evil").is_err());
        assert!(validate_git_url("javascript://x").is_err());
        assert!(validate_git_url("").is_err());
    }

    #[test]
    fn clones_at_the_pinned_rev_not_head() {
        let (orig, r1, _r2) = origin();
        let ws = tempfile::TempDir::new().unwrap();
        let pkgs_dir = ws.path().join(".lake/packages");
        let pkg = git_pkg("dep", orig.path().to_str().unwrap().into(), r1.clone());
        materialize(&[pkg], ws.path(), &pkgs_dir).unwrap();
        assert_eq!(sh(&pkgs_dir.join("dep"), "git rev-parse HEAD"), r1);
    }

    #[test]
    fn existing_clean_checkout_at_wrong_rev_is_moved_to_the_pin() {
        let (orig, r1, r2) = origin();
        let ws = tempfile::TempDir::new().unwrap();
        let pkgs_dir = ws.path().join(".lake/packages");
        let url: String = orig.path().to_str().unwrap().into();
        materialize(&[git_pkg("dep", url.clone(), r2)], ws.path(), &pkgs_dir).unwrap();
        materialize(&[git_pkg("dep", url, r1.clone())], ws.path(), &pkgs_dir).unwrap();
        assert_eq!(sh(&pkgs_dir.join("dep"), "git rev-parse HEAD"), r1);
    }

    #[test]
    fn dirty_checkout_is_an_error_never_overwritten() {
        let (orig, r1, r2) = origin();
        let ws = tempfile::TempDir::new().unwrap();
        let pkgs_dir = ws.path().join(".lake/packages");
        let url: String = orig.path().to_str().unwrap().into();
        materialize(&[git_pkg("dep", url.clone(), r1)], ws.path(), &pkgs_dir).unwrap();
        std::fs::write(pkgs_dir.join("dep/local-work.txt"), "precious").unwrap();
        let err = materialize(&[git_pkg("dep", url, r2)], ws.path(), &pkgs_dir).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("dep") && msg.contains("local"), "got: {msg}");
        // The precious file survived.
        assert!(pkgs_dir.join("dep/local-work.txt").exists());
    }

    #[test]
    fn matching_rev_is_a_no_op_even_when_dirty() {
        let (orig, r1, _r2) = origin();
        let ws = tempfile::TempDir::new().unwrap();
        let pkgs_dir = ws.path().join(".lake/packages");
        let url: String = orig.path().to_str().unwrap().into();
        materialize(&[git_pkg("dep", url.clone(), r1.clone())], ws.path(), &pkgs_dir).unwrap();
        std::fs::write(pkgs_dir.join("dep/scratch.txt"), "wip").unwrap();
        // Already at the right rev: leave the user's files alone.
        materialize(&[git_pkg("dep", url, r1)], ws.path(), &pkgs_dir).unwrap();
        assert!(pkgs_dir.join("dep/scratch.txt").exists());
    }

    #[test]
    fn missing_path_dependency_is_a_clear_error() {
        let ws = tempfile::TempDir::new().unwrap();
        let pkg = ManifestPackage {
            name: "local".into(),
            source: PackageSource::Path { dir: PathBuf::from("../nope") },
            config_file: PathBuf::from("lakefile.toml"),
            inherited: false,
        };
        let err = materialize(&[pkg], ws.path(), &ws.path().join("pkgs")).unwrap_err();
        assert!(err.to_string().contains("local"));
    }

    #[test]
    fn unknown_rev_reports_the_package() {
        let (orig, _r1, _r2) = origin();
        let ws = tempfile::TempDir::new().unwrap();
        let bad = "0123456789abcdef0123456789abcdef01234567".to_string();
        let pkg = git_pkg("dep", orig.path().to_str().unwrap().into(), bad);
        let err = materialize(&[pkg], ws.path(), &ws.path().join("pkgs")).unwrap_err();
        assert!(err.to_string().contains("dep"));
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_build fetch`
Expected: compile FAILURE.

- [ ] **Step 3: Implement**

Top of `crates/leanr_build/src/fetch.rs`:

```rust
//! Dependency materialization (spec §Architecture, component 4): ensure
//! `.lake/packages/<name>` is a git checkout at exactly the manifest rev.
//! Shells out to the `git` CLI (as lake itself does) with explicit
//! argument vectors and validated URLs; never overwrites local changes.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::error::BuildError;
use crate::manifest::{ManifestPackage, PackageSource};

/// Reject URLs that could be misparsed as git options or drive exotic
/// transports. Allowed: https/http/ssh/git/file schemes, scp-like
/// `user@host:path`, and local paths — none starting with `-`.
pub fn validate_git_url(url: &str) -> Result<(), String> {
    if url.is_empty() {
        return Err("empty git url".into());
    }
    if url.starts_with('-') {
        return Err(format!("git url starts with `-`: `{url}`"));
    }
    if let Some((scheme, _)) = url.split_once("://") {
        return match scheme {
            "https" | "http" | "ssh" | "git" | "file" => Ok(()),
            other => Err(format!("unsupported git url scheme `{other}` in `{url}`")),
        };
    }
    if url.contains("::") {
        return Err(format!("unsupported git transport in `{url}`"));
    }
    Ok(()) // scp-like or local path
}

fn git(args: &[&str], cwd: &Path) -> Result<String, BuildError> {
    let out = Command::new("git")
        .args(args)
        .current_dir(cwd)
        .output()
        .map_err(|e| BuildError::Subprocess {
            cmd: format!("git {}", args.join(" ")),
            reason: format!("failed to start: {e}"),
            stderr: String::new(),
        })?;
    if !out.status.success() {
        return Err(BuildError::Subprocess {
            cmd: format!("git {}", args.join(" ")),
            reason: format!("failed ({})", out.status),
            stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        });
    }
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

fn ensure_git(name: &str, url: &str, rev: &str, dest: &Path) -> Result<(), BuildError> {
    let ferr = |msg: String| BuildError::Fetch { name: name.to_string(), msg };
    validate_git_url(url).map_err(ferr)?;
    if !dest.is_dir() {
        let parent = dest.parent().unwrap_or(Path::new("."));
        std::fs::create_dir_all(parent)
            .map_err(|e| ferr(format!("cannot create {}: {e}", parent.display())))?;
        git(
            &["clone", "--", url, dest.to_str().ok_or_else(|| ferr("non-UTF-8 dest".into()))?],
            parent,
        )
        .map_err(|e| ferr(format!("clone failed: {e}")))?;
    }
    let head = git(&["rev-parse", "HEAD"], dest)?;
    if head == rev {
        return Ok(()); // already pinned; user files (even dirty) untouched
    }
    let dirty = !git(&["status", "--porcelain"], dest)?.is_empty();
    if dirty {
        return Err(ferr(format!(
            "{} has local modifications but is at {head}, not the manifest rev {rev}; \
             commit/stash or remove the directory",
            dest.display()
        )));
    }
    // Fetch only if the rev isn't already present locally.
    if git(&["rev-parse", "--verify", "--quiet", &format!("{rev}^{{commit}}")], dest).is_err() {
        git(&["fetch", "origin"], dest).map_err(|e| ferr(format!("fetch failed: {e}")))?;
    }
    git(&["-c", "advice.detachedHead=false", "checkout", "--detach", rev], dest)
        .map_err(|e| ferr(format!("checkout of {rev} failed: {e}")))?;
    Ok(())
}

/// Materialize every manifest package (spec: fresh clones work with no
/// lake invocation). Concurrent across packages; deterministic first
/// error in package order.
pub fn materialize(
    packages: &[ManifestPackage],
    ws_root: &Path,
    packages_dir: &Path,
) -> Result<(), BuildError> {
    let results: Vec<Result<(), BuildError>> = std::thread::scope(|s| {
        let handles: Vec<_> = packages
            .iter()
            .map(|p| {
                s.spawn(move || match &p.source {
                    PackageSource::Git { url, rev, sub_dir: _ } => {
                        ensure_git(&p.name, url, rev, &packages_dir.join(&p.name))
                    }
                    PackageSource::Path { dir } => {
                        let full: PathBuf = ws_root.join(dir);
                        if full.is_dir() {
                            Ok(())
                        } else {
                            Err(BuildError::Fetch {
                                name: p.name.clone(),
                                msg: format!("path dependency {} does not exist", full.display()),
                            })
                        }
                    }
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().expect("fetch thread")).collect()
    });
    results.into_iter().collect()
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p leanr_build fetch`
Expected: PASS.

- [ ] **Step 5: Document the new threat surface**

Append to `docs/THREAT_MODEL.md` (adapt heading level to the file's existing structure):

```markdown
## M2a: package resolution surface

New in M2a (`leanr build --dry-run`), all matching lake's own trust
posture:

- **Executing lakefiles.** The translate-config bridge runs pinned
  official `lake` on a package's `lakefile.lean` — arbitrary code
  execution by design, exactly as `lake build` would. leanr adds no
  sandbox in M2a (the M4 VM is the natural place for one). Subprocesses
  get explicit argument vectors, captured stderr, and a timeout.
- **Manifest-supplied git URLs.** `lake-manifest.json` is trusted like
  the lakefile (it lives in the project), but URLs are validated before
  reaching git: no leading `-` (option injection), scheme whitelist
  (https/http/ssh/git/file, scp-like, local paths), `--` separator on
  `git clone`. Materialization never overwrites local modifications.
- **Header scanning.** `scan_header` is a total function over arbitrary
  bytes (property-tested): never panics, never recurses, allocation
  bounded by input size — same discipline as the `.olean` decoder.
```

- [ ] **Step 6: Lint, commit**

```bash
mise run lint && git add crates/leanr_build docs/THREAT_MODEL.md
git commit -m "feat(build): git dependency materializer with URL validation

Documents the M2a resolution surface in THREAT_MODEL.md."
```

---

### Task 8: The resolve() pipeline

**Files:**
- Modify: `crates/leanr_build/src/lib.rs`
- Test: `crates/leanr_build/tests/synthetic_workspace.rs`

**Interfaces:**
- Consumes: everything from Tasks 1–7 (exact signatures restated in their Interfaces blocks).
- Produces (what the CLI and M2b consume):
  - `ResolveOptions` — `{ targets: Vec<String>, lake: bridge::LakeInvoker, toolchain_olean_dir: PathBuf }`.
  - `ResolvedPackage` — `{ name: String, dir: PathBuf, rev: Option<String>, config: config::PackageConfig }`.
  - `Workspace` — `{ root_dir: PathBuf, root: ResolvedPackage, deps: Vec<ResolvedPackage>, graph: graph::ModuleGraph, waves: Vec<Vec<graph::ModuleId>>, warnings: Vec<String> }`.
  - `find_workspace_root(start: &Path) -> Result<PathBuf, BuildError>`.
  - `resolve(root_dir: &Path, opts: &ResolveOptions) -> Result<Workspace, BuildError>`.

- [ ] **Step 1: Write the failing integration test**

`crates/leanr_build/tests/synthetic_workspace.rs`:

```rust
//! End-to-end resolve() over a synthetic two-package workspace with a
//! real local git dependency — no lake, no network, no toolchain.

use std::path::{Path, PathBuf};

use leanr_build::bridge::LakeInvoker;
use leanr_build::{find_workspace_root, resolve, BuildError, ResolveOptions};

fn sh(dir: &Path, cmd: &str) {
    let out = std::process::Command::new("sh").arg("-c").arg(cmd).current_dir(dir).output().unwrap();
    assert!(out.status.success(), "{cmd}: {}", String::from_utf8_lossy(&out.stderr));
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
    write(&dep, "lakefile.toml", "name = \"dep\"\ndefaultTargets = [\"Dep\"]\n\n[[lean_lib]]\nname = \"Dep\"\n");
    write(&dep, "Dep.lean", "module\npublic import Init.Core\n");
    sh(&dep, "git init -q -b main && git add -A && git -c user.email=t@t -c user.name=t commit -qm dep");
    let rev = {
        let out = std::process::Command::new("git").args(["rev-parse", "HEAD"]).current_dir(&dep).output().unwrap();
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

/// Fake toolchain: a dir containing Init/Core.olean.
fn fake_toolchain(tmp: &Path) -> PathBuf {
    let dir = tmp.join("toolchain-lib");
    std::fs::create_dir_all(dir.join("Init")).unwrap();
    std::fs::write(dir.join("Init/Core.olean"), "").unwrap();
    dir
}

fn opts(tmp: &Path) -> ResolveOptions {
    ResolveOptions {
        targets: Vec::new(), // defaultTargets
        lake: LakeInvoker { program: PathBuf::from("/no/lake/needed"), ..LakeInvoker::default() },
        toolchain_olean_dir: fake_toolchain(tmp),
    }
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
        .map(|w| w.iter().map(|id| ws.graph.modules[id.0 as usize].name.to_string()).collect())
        .collect();
    assert_eq!(
        names,
        [vec!["App.Sub".to_string(), "Dep".to_string()], vec!["App".to_string()]]
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
    assert!(msg.contains("ghost") && msg.contains("lake update"), "got: {msg}");
}

#[test]
fn find_root_walks_up_and_prefers_toml() {
    let (_tmp, app) = setup();
    let nested = app.join("App");
    assert_eq!(find_workspace_root(&nested).unwrap(), app);
    let err = find_workspace_root(Path::new("/")).unwrap_err();
    assert!(matches!(err, BuildError::NoWorkspaceRoot(_)));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p leanr_build --test synthetic_workspace`
Expected: compile FAILURE (`resolve` undefined).

- [ ] **Step 3: Implement the pipeline in `lib.rs`**

Replace `crates/leanr_build/src/lib.rs` with:

```rust
//! Lake-compatible package model + module graph (M2a).
//! Spec: docs/superpowers/specs/2026-07-11-m2a-package-model-design.md
//!
//! `resolve()` is the crate's product: a straight-line pure-function
//! pipeline (no query engine yet — spec §Config acquisition, companion
//! decisions) whose output `Workspace` is the interface M2b's
//! orchestrator consumes.

use std::path::{Path, PathBuf};

pub mod bridge;
pub mod config;
mod error;
pub mod fetch;
pub mod graph;
pub mod manifest;
pub mod modules;
pub mod scanner;

pub use error::BuildError;

use graph::{LibUnit, ModuleGraph, ModuleId, ModuleResolver, OleanDirIndex};
use modules::{expand_glob, ModuleName};

pub struct ResolveOptions {
    /// lean_lib targets in the root package; empty = defaultTargets.
    pub targets: Vec<String>,
    pub lake: bridge::LakeInvoker,
    /// Toolchain olean root (`lean --print-libdir`) for classifying
    /// imports that resolve to no workspace module.
    pub toolchain_olean_dir: PathBuf,
}

pub struct ResolvedPackage {
    pub name: String,
    pub dir: PathBuf,
    /// Manifest rev for git packages; None for the root and path deps.
    pub rev: Option<String>,
    pub config: config::PackageConfig,
}

pub struct Workspace {
    pub root_dir: PathBuf,
    pub root: ResolvedPackage,
    /// Manifest order.
    pub deps: Vec<ResolvedPackage>,
    pub graph: ModuleGraph,
    pub waves: Vec<Vec<ModuleId>>,
    pub warnings: Vec<String>,
}

/// Walk up from `start` to the nearest directory containing a lakefile.
pub fn find_workspace_root(start: &Path) -> Result<PathBuf, BuildError> {
    let mut dir = Some(start);
    while let Some(d) = dir {
        if d.join("lakefile.toml").is_file() || d.join("lakefile.lean").is_file() {
            return Ok(d.to_path_buf());
        }
        dir = d.parent();
    }
    Err(BuildError::NoWorkspaceRoot(start.to_path_buf()))
}

/// lakefile.toml wins over lakefile.lean when both exist (lake's rule).
fn config_file_of(dir: &Path) -> Result<PathBuf, BuildError> {
    if dir.join("lakefile.toml").is_file() {
        Ok(PathBuf::from("lakefile.toml"))
    } else if dir.join("lakefile.lean").is_file() {
        Ok(PathBuf::from("lakefile.lean"))
    } else {
        Err(BuildError::NoWorkspaceRoot(dir.to_path_buf()))
    }
}

/// The 7-step pipeline from the spec (§Data flow).
pub fn resolve(root_dir: &Path, opts: &ResolveOptions) -> Result<Workspace, BuildError> {
    let cache_dir = root_dir.join(".leanr/config-cache");
    let mut warnings = Vec::new();

    // 2. Root config (native or bridge).
    let root_cfg_file = config_file_of(root_dir)?;
    let parsed = bridge::load_config(root_dir, &root_cfg_file, &cache_dir, &opts.lake)?;
    warnings.extend(parsed.warnings);
    let root_config = parsed.config;

    // 3. Manifest (committed; its absence is the deferred-resolution boundary).
    let manifest_path = root_dir.join("lake-manifest.json");
    if !manifest_path.is_file() {
        return Err(BuildError::NoManifest(root_dir.to_path_buf()));
    }
    let text = std::fs::read_to_string(&manifest_path).map_err(|e| BuildError::Io {
        path: manifest_path.clone(),
        err: e.to_string(),
    })?;
    let manifest = manifest::parse_manifest(&text, &manifest_path)?;

    // Cross-check: every require has a manifest entry (spec §Data flow).
    for req in &root_config.requires {
        if !manifest.packages.iter().any(|p| p.name == req.name) {
            return Err(BuildError::StaleManifest {
                name: req.name.clone(),
                config: root_dir.join(&root_cfg_file),
            });
        }
    }

    // 4. Materialize.
    let packages_dir = root_dir.join(&manifest.packages_dir);
    fetch::materialize(&manifest.packages, root_dir, &packages_dir)?;

    // 5. Dependency configs.
    let mut deps = Vec::new();
    for entry in &manifest.packages {
        let (dir, rev) = match &entry.source {
            manifest::PackageSource::Git { rev, sub_dir, .. } => {
                let base = packages_dir.join(&entry.name);
                let dir = match sub_dir {
                    Some(sd) => base.join(sd),
                    None => base,
                };
                (dir, Some(rev.clone()))
            }
            manifest::PackageSource::Path { dir } => (root_dir.join(dir), None),
        };
        let parsed = bridge::load_config(&dir, &entry.config_file, &cache_dir, &opts.lake)?;
        warnings.extend(parsed.warnings);
        deps.push(ResolvedPackage { name: entry.name.clone(), dir, rev, config: parsed.config });
    }

    // 6. Module graph. Lib srcDir rule (spec §Data flow): lib.srcDir
    // defaults to the package's srcDir, relative to the package dir —
    // not composed with it. Verified by the differential tier.
    let root_pkg = ResolvedPackage {
        name: root_config.name.clone(),
        dir: root_dir.to_path_buf(),
        rev: None,
        config: root_config,
    };
    let mut units = Vec::new();
    for pkg in std::iter::once(&root_pkg).chain(deps.iter()) {
        for lib in &pkg.config.lean_libs {
            let src = lib
                .src_dir
                .clone()
                .or_else(|| pkg.config.src_dir.clone())
                .unwrap_or_else(|| PathBuf::from("."));
            for root in lib.effective_roots() {
                units.push(LibUnit {
                    package: pkg.name.clone(),
                    src_dir: pkg.dir.join(&src),
                    root,
                });
            }
        }
    }
    let resolver = ModuleResolver::new(units);

    // Seeds: requested targets (or defaultTargets) -> root-package libs.
    let target_names: Vec<String> = if opts.targets.is_empty() {
        root_pkg.config.default_targets.clone()
    } else {
        opts.targets.clone()
    };
    let mut seeds: Vec<ModuleName> = Vec::new();
    for t in &target_names {
        let lib = root_pkg
            .config
            .lean_libs
            .iter()
            .find(|l| &l.name == t)
            .ok_or_else(|| BuildError::UnknownTarget(t.clone()))?;
        let src = lib
            .src_dir
            .clone()
            .or_else(|| root_pkg.config.src_dir.clone())
            .unwrap_or_else(|| PathBuf::from("."));
        for g in lib.effective_globs() {
            seeds.extend(expand_glob(&g, &root_pkg.dir.join(&src))?);
        }
    }
    seeds.sort();
    seeds.dedup();

    let toolchain = OleanDirIndex { root: opts.toolchain_olean_dir.clone() };
    let module_graph = graph::build_graph(&seeds, &resolver, &toolchain)?;
    // 7. Waves.
    let waves = graph::topo_waves(&module_graph)?;

    Ok(Workspace {
        root_dir: root_dir.to_path_buf(),
        root: root_pkg,
        deps,
        graph: module_graph,
        waves,
        warnings,
    })
}
```

- [ ] **Step 4: Run all crate tests, lint, commit**

Run: `cargo test -p leanr_build && mise run lint`
Expected: PASS.

```bash
git add crates/leanr_build
git commit -m "feat(build): resolve() pipeline — configs, manifest cross-check, fetch, module DAG"
```

---

### Task 9: CLI `leanr build --dry-run` + docs front door

**Files:**
- Modify: `crates/leanr_cli/Cargo.toml` (add `leanr_build` + `serde`/`serde_json` deps), `crates/leanr_cli/src/main.rs`, `ARCHITECTURE.md`
- Test: `crates/leanr_cli/tests/build_cli.rs` (assert_cmd, already a dev-dependency)

**Interfaces:**
- Consumes: `leanr_build::{resolve, find_workspace_root, ResolveOptions, Workspace, BuildError}`, `bridge::LakeInvoker` (Task 8/6).
- Produces: the user-visible command. JSON schema (consumed by Task 10/11 diffing — do not change without updating them):

```json
{
  "root": "app",
  "targets": ["App"],
  "packages": [{"name": "dep", "rev": "<sha-or-null>", "dir": ".lake/packages/dep"}],
  "modules": [{"name": "App.Sub", "package": "app", "file": "App/Sub.lean", "wave": 0}]
}
```

`packages` in manifest order; `modules` sorted by (wave, name); `dir`/`file` **workspace-relative** with forward slashes (fresh-clone byte-identity).

- [ ] **Step 1: Write failing CLI tests**

`crates/leanr_cli/tests/build_cli.rs`:

```rust
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
    write("lake-manifest.json", r#"{"version": "1.2.0", "packages": []}"#);
    // Fake toolchain dir for --toolchain-dir.
    std::fs::create_dir_all(tmp.path().join("fake-toolchain")).unwrap();
    tmp
}

fn leanr(tmp: &tempfile::TempDir) -> Command {
    let mut c = Command::cargo_bin("leanr").unwrap();
    c.current_dir(tmp.path())
        .args(["build", "--dry-run"])
        .args(["--toolchain-dir", tmp.path().join("fake-toolchain").to_str().unwrap()]);
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
    let out = leanr(&tmp).arg("--json").assert().success().get_output().stdout.clone();
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
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_cli --test build_cli`
Expected: compile/run FAILURE (no `build` subcommand).

- [ ] **Step 3: Implement the subcommand**

`crates/leanr_cli/Cargo.toml` — add to `[dependencies]`:

```toml
leanr_build = { version = "0.1.0", path = "../leanr_build" }
serde = { version = "1", features = ["derive"] }
serde_json = "1"
```

Add to `[dev-dependencies]`: `tempfile = "3"`.

In `crates/leanr_cli/src/main.rs`, add the variant to `enum Command`:

```rust
    /// Resolve the workspace and plan a build (M2a: --dry-run only).
    Build {
        /// lean_lib targets (default: the root package's defaultTargets).
        targets: Vec<String>,
        /// Resolve, fetch dependencies, and print the module build plan
        /// without compiling anything.
        #[arg(long)]
        dry_run: bool,
        /// Machine-readable JSON plan on stdout.
        #[arg(long, requires = "dry_run")]
        json: bool,
        /// Workspace directory (default: walk up from the current directory).
        #[arg(long)]
        dir: Option<PathBuf>,
        /// Toolchain olean directory (default: `lean --print-libdir`).
        #[arg(long)]
        toolchain_dir: Option<PathBuf>,
    },
```

wire it in `main()`:

```rust
        Command::Build { targets, dry_run, json, dir, toolchain_dir } => {
            build(targets, dry_run, json, dir, toolchain_dir)
        }
```

and implement (same file, alongside the other command fns):

```rust
#[derive(serde::Serialize)]
struct JsonPackage<'a> {
    name: &'a str,
    rev: Option<&'a str>,
    dir: String,
}

#[derive(serde::Serialize)]
struct JsonModule {
    name: String,
    package: String,
    file: String,
    wave: usize,
}

#[derive(serde::Serialize)]
struct JsonPlan<'a> {
    root: &'a str,
    targets: &'a [String],
    packages: Vec<JsonPackage<'a>>,
    modules: Vec<JsonModule>,
}

/// Workspace-relative path with forward slashes (JSON byte-identity
/// across checkouts; see the plan's Task 9 interface note).
fn rel_display(path: &std::path::Path, root: &std::path::Path) -> String {
    let rel = path.strip_prefix(root).unwrap_or(path);
    rel.components()
        .map(|c| c.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}

fn build(
    targets: Vec<String>,
    dry_run: bool,
    json: bool,
    dir: Option<PathBuf>,
    toolchain_dir: Option<PathBuf>,
) -> ExitCode {
    if !dry_run {
        eprintln!(
            "error: `leanr build` without --dry-run is not implemented yet (coming in M2b); \
             run `leanr build --dry-run`"
        );
        return ExitCode::FAILURE;
    }
    let run = || -> Result<(), String> {
        let start = match &dir {
            Some(d) => d.clone(),
            None => std::env::current_dir().map_err(|e| e.to_string())?,
        };
        let root_dir = leanr_build::find_workspace_root(&start).map_err(|e| e.to_string())?;
        let toolchain_olean_dir = match toolchain_dir {
            Some(d) => d,
            None => lean_print_libdir()?,
        };
        // Pin dependency bridging to the root workspace's toolchain.
        let toolchain = std::fs::read_to_string(root_dir.join("lean-toolchain"))
            .ok()
            .map(|s| s.trim().to_string());
        let opts = leanr_build::ResolveOptions {
            targets: targets.clone(),
            lake: leanr_build::bridge::LakeInvoker {
                toolchain,
                ..leanr_build::bridge::LakeInvoker::default()
            },
            toolchain_olean_dir,
        };
        let ws = leanr_build::resolve(&root_dir, &opts).map_err(|e| e.to_string())?;
        for w in &ws.warnings {
            eprintln!("warning: {w}");
        }
        let effective_targets: Vec<String> = if targets.is_empty() {
            ws.root.config.default_targets.clone()
        } else {
            targets
        };
        if json {
            print_json_plan(&ws, &effective_targets);
        } else {
            print_text_plan(&ws);
        }
        Ok(())
    };
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(msg) => {
            eprintln!("error: {msg}");
            ExitCode::FAILURE
        }
    }
}

fn lean_print_libdir() -> Result<PathBuf, String> {
    let out = std::process::Command::new("lean")
        .arg("--print-libdir")
        .output()
        .map_err(|e| {
            format!(
                "cannot run `lean --print-libdir` ({e}); install the pinned toolchain \
                 (`mise run elan:bootstrap`) or pass --toolchain-dir"
            )
        })?;
    if !out.status.success() {
        return Err(format!(
            "`lean --print-libdir` failed: {}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok(PathBuf::from(String::from_utf8_lossy(&out.stdout).trim().to_string()))
}

fn print_json_plan(ws: &leanr_build::Workspace, targets: &[String]) {
    let packages = ws
        .deps
        .iter()
        .map(|d| JsonPackage {
            name: &d.name,
            rev: d.rev.as_deref(),
            dir: rel_display(&d.dir, &ws.root_dir),
        })
        .collect();
    let mut modules = Vec::new();
    for (wave, ids) in ws.waves.iter().enumerate() {
        for id in ids {
            let m = &ws.graph.modules[id.0 as usize];
            modules.push(JsonModule {
                name: m.name.to_string(),
                package: m.package.clone(),
                file: rel_display(&m.file, &ws.root_dir),
                wave,
            });
        }
    }
    let plan = JsonPlan { root: &ws.root.name, targets, packages, modules };
    println!("{}", serde_json::to_string_pretty(&plan).expect("plan serializes"));
}

fn print_text_plan(ws: &leanr_build::Workspace) {
    println!("workspace: {} ({})", ws.root.name, ws.root_dir.display());
    for d in &ws.deps {
        println!("  dep: {} @ {}", d.name, d.rev.as_deref().unwrap_or("path"));
    }
    let total: usize = ws.waves.iter().map(|w| w.len()).sum();
    println!("plan: {total} modules in {} waves", ws.waves.len());
    for (i, w) in ws.waves.iter().enumerate() {
        println!("  wave {i} ({} modules):", w.len());
        for id in w {
            println!("    {}", ws.graph.modules[id.0 as usize].name);
        }
    }
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p leanr_cli`
Expected: PASS (including the pre-existing CLI tests).

- [ ] **Step 5: Document the crate in ARCHITECTURE.md**

Add `leanr_build` to the crate table/map in `ARCHITECTURE.md`, following the file's existing format, with the one-liner: "Lake-compatible package model + module graph (M2a): lakefile.toml schema, translate-config bridge, manifest-driven git materialization, import DAG. `leanr build --dry-run`. No kernel dependency." Mention the `.leanr/config-cache/` directory where the file documents on-disk layout, if it does.

- [ ] **Step 6: Full gate, commit**

Run: `mise run ci`
Expected: PASS (lint, tests, deps, secrets).

```bash
git add crates/leanr_cli ARCHITECTURE.md Cargo.lock
git commit -m "feat(cli): leanr build --dry-run — resolved plan as text or JSON"
```

---

### Task 10: Differential tier — three oracles vs pinned Mathlib

**Files:**
- Create: `crates/leanr_build/tests/mathlib_oracle.rs`
- Create: `crates/leanr_build/tests/fixtures/mathlib-lakefile-golden.toml`
- Modify: `mise.toml` (task `build:differential`; extend `fixtures:regen`)
- Test: this task IS tests (all `#[ignore]`; local-only, like `sweep:stdlib`)

**Interfaces:**
- Consumes: `resolve`/`ResolveOptions`/`Workspace` (Task 8), `bridge::{translate_lakefile, LakeInvoker}` (Task 6), dev-deps `leanr_olean::{SearchPath, ModuleData}` + `leanr_kernel::{bank::Store, Name}`.
- Produces: the differential gate the spec's Testing section requires. Env contract (set by the mise task): `LEANR_MATHLIB_DIR` = the pinned checkout; `LEANR_OLEAN_PATH` = lake's resolved `LEAN_PATH` (`:`-separated).

- [ ] **Step 1: Generate the golden fixture**

```bash
cd .mathlib && lake translate-config toml /tmp/mathlib-golden.toml && cd ..
cp /tmp/mathlib-golden.toml crates/leanr_build/tests/fixtures/mathlib-lakefile-golden.toml
```

- [ ] **Step 2: Write the oracle tests**

`crates/leanr_build/tests/mathlib_oracle.rs`:

```rust
//! Differential tier (spec §Testing): leanr's package model vs pinned
//! official lake over the Mathlib closure. All #[ignore]; run via
//! `mise run build:differential` (needs `mise run mathlib:fetch` first).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use leanr_build::bridge::{translate_lakefile, LakeInvoker};
use leanr_build::modules::ModuleName;
use leanr_build::{resolve, ResolveOptions};
use leanr_kernel::{bank::Store, Name};
use leanr_olean::{ModuleData, SearchPath};

fn mathlib_dir() -> PathBuf {
    PathBuf::from(std::env::var("LEANR_MATHLIB_DIR").expect("set LEANR_MATHLIB_DIR"))
}

fn olean_search_path() -> SearchPath {
    let raw = std::env::var("LEANR_OLEAN_PATH").expect("set LEANR_OLEAN_PATH");
    SearchPath::new(raw.split(':').map(PathBuf::from).collect())
}

fn kernel_name(m: &ModuleName) -> Arc<Name> {
    let mut n = Arc::new(Name::Anonymous);
    for part in m.components() {
        n = Arc::new(Name::Str { parent: n, part: part.clone() });
    }
    n
}

fn resolve_mathlib() -> leanr_build::Workspace {
    let root = mathlib_dir();
    let toolchain = std::fs::read_to_string(root.join("lean-toolchain"))
        .ok()
        .map(|s| s.trim().to_string());
    // Toolchain olean dir = the LEAN_PATH entry that contains Init.olean.
    let sp = olean_search_path();
    let init = sp
        .find(&kernel_name(&ModuleName::parse("Init").unwrap()))
        .expect("Init.olean on LEANR_OLEAN_PATH");
    let toolchain_olean_dir = init.parent().expect("Init.olean has a parent").to_path_buf();
    let opts = ResolveOptions {
        targets: Vec::new(), // defaultTargets = ["Mathlib"]
        lake: LakeInvoker { toolchain, ..LakeInvoker::default() },
        toolchain_olean_dir,
    };
    resolve(&root, &opts).expect("mathlib resolves")
}

/// Oracle 1 (bridge golden): translate-config output for Mathlib's
/// lakefile.lean is byte-identical to the committed fixture.
#[test]
#[ignore]
fn bridge_golden_matches_committed_fixture() {
    let out = tempfile::TempDir::new().unwrap();
    let out_file = out.path().join("translated.toml");
    let toolchain = std::fs::read_to_string(mathlib_dir().join("lean-toolchain"))
        .ok()
        .map(|s| s.trim().to_string());
    let lake = LakeInvoker { toolchain, ..LakeInvoker::default() };
    translate_lakefile(&mathlib_dir(), &lake, &out_file).unwrap();
    let got = std::fs::read_to_string(&out_file).unwrap();
    let want = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mathlib-lakefile-golden.toml"),
    )
    .unwrap();
    assert_eq!(got, want, "regen via `mise run fixtures:regen` if the pin moved");
}

/// Oracle 2 (import graph — the strong one): for every planned module,
/// header-scanned imports == the .olean's recorded imports. Implicit-Init
/// rule: non-prelude modules whose header lists no imports get `Init`
/// (adjust ONLY with a comment citing the Lean source if the sweep
/// disagrees — the 8k-module diff will say so precisely).
#[test]
#[ignore]
fn scanned_imports_match_olean_imports_across_the_closure() {
    let ws = resolve_mathlib();
    let sp = olean_search_path();
    let mut checked = 0usize;
    let mut mismatches = Vec::new();
    for m in &ws.graph.modules {
        let olean = sp
            .find(&kernel_name(&m.name))
            .unwrap_or_else(|| panic!("{}: no .olean on LEANR_OLEAN_PATH", m.name));
        let bytes = std::fs::read(&olean).unwrap();
        let mut store = Store::persistent();
        let md = ModuleData::parse(&bytes, &mut store).unwrap();
        let olean_imports: BTreeSet<String> =
            md.imports.iter().map(|i| i.module.to_string()).collect();
        let mut scanned: BTreeSet<String> =
            m.imports.iter().map(|i| i.to_string()).collect();
        if !m.prelude && scanned.is_empty() {
            scanned.insert("Init".to_string());
        }
        if scanned != olean_imports {
            mismatches.push(format!(
                "{}: scanned {:?} != olean {:?}",
                m.name, scanned, olean_imports
            ));
        }
        checked += 1;
    }
    assert!(checked > 5000, "expected the full closure, checked only {checked}");
    assert!(
        mismatches.is_empty(),
        "{} mismatches:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// Oracle 3 (module set): (a) every planned module has an .olean lake
/// built; (b) planned root-package modules == the on-disk Mathlib
/// build's module set (mk_all guarantees Mathlib.lean imports them all).
#[test]
#[ignore]
fn planned_module_set_matches_lakes_build() {
    let ws = resolve_mathlib();
    let sp = olean_search_path();
    // (a) subset: everything planned exists as an olean.
    for m in &ws.graph.modules {
        assert!(
            sp.find(&kernel_name(&m.name)).is_some(),
            "{}: planned but lake never built it",
            m.name
        );
    }
    // (b) equality on the root package.
    let planned: BTreeSet<String> = ws
        .graph
        .modules
        .iter()
        .filter(|m| m.package == ws.root.name)
        .map(|m| m.name.to_string())
        .collect();
    let build_dir = mathlib_dir().join(".lake/build/lib/lean");
    let mut on_disk = BTreeSet::new();
    let mut stack = vec![build_dir.clone()];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).unwrap() {
            let p = e.unwrap().path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().map(|x| x == "olean").unwrap_or(false) {
                let rel = p.strip_prefix(&build_dir).unwrap().with_extension("");
                let name = rel
                    .components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect::<Vec<_>>()
                    .join(".");
                on_disk.insert(name);
            }
        }
    }
    // The build dir holds only root-package modules (deps build in their
    // own .lake dirs); restrict to the planned targets' prefixes anyway
    // in case lake built extra targets (Cache, MathlibTest, ...).
    let planned_prefixes: BTreeSet<&str> =
        planned.iter().map(|n| n.split('.').next().unwrap()).collect();
    let on_disk_restricted: BTreeSet<String> = on_disk
        .into_iter()
        .filter(|n| planned_prefixes.contains(n.split('.').next().unwrap()))
        .collect();
    assert_eq!(
        planned, on_disk_restricted,
        "planned vs lake-built module sets differ for the root package"
    );
}

/// Warnings check: resolving the whole closure emits no unknown-key
/// warnings (the schema covers everything the closure exercises).
#[test]
#[ignore]
fn closure_resolves_without_warnings() {
    let ws = resolve_mathlib();
    assert!(ws.warnings.is_empty(), "unexpected warnings: {:?}", ws.warnings);
}
```

- [ ] **Step 3: Add the mise task and extend fixtures:regen**

In `mise.toml`, after the `check:mathlib` block:

```toml
[tasks."build:differential"]
description = "M2a differential oracles vs pinned Mathlib: bridge golden, olean import diff, module set (needs mathlib:fetch)"
depends = ["elan:bootstrap"]
run = "sh -c 'LEANR_MATHLIB_DIR=\"$PWD/.mathlib\" LEANR_OLEAN_PATH=\"$(cd .mathlib && lake env printenv LEAN_PATH)\" cargo test --release -p leanr_build --test mathlib_oracle -- --ignored --nocapture'"
```

Append to the `fixtures:regen` run list (it is a TOML array of commands):

```toml
  "sh -c 'cd .mathlib && rm -f /tmp/leanr-mathlib-golden.toml && lake translate-config toml /tmp/leanr-mathlib-golden.toml && cp /tmp/leanr-mathlib-golden.toml ../crates/leanr_build/tests/fixtures/mathlib-lakefile-golden.toml'",
  "sh -c 'for p in aesop batteries Cli importGraph LeanSearchClient plausible Qq; do cp .mathlib/.lake/packages/$p/lakefile.toml crates/leanr_build/tests/fixtures/lakefiles/$p.toml; done'",
```

- [ ] **Step 4: Run the differential tier**

Run: `mise run build:differential`
Expected: all 4 tests PASS. Failure modes and what they mean:
- Oracle 2 mismatches list concrete modules — fix the scanner grammar or the implicit-Init rule (with a Lean-source citation), never skip modules.
- Oracle 3 asymmetric diff — fix glob/srcDir semantics in `resolve()`.
- Warnings — add the reported key as a parsed-but-unused config field.

This is the task where reality bites; budget iteration time here. Each fix follows TDD: reproduce the failing case as a small unit test in the relevant module first, then fix, then re-run the tier.

- [ ] **Step 5: Lint, commit**

```bash
mise run lint && git add crates/leanr_build mise.toml
git commit -m "test(build): Mathlib differential tier — bridge golden, olean import oracle, module-set oracle"
```

---

### Task 11: Fresh-clone acceptance + spec results

**Files:**
- Create: `scripts/build-fresh-acceptance.sh`
- Modify: `mise.toml` (task `build:acceptance`), `docs/superpowers/specs/2026-07-11-m2a-package-model-design.md` (Acceptance results), `README.md` (only if it lists commands — follow its existing structure)

**Interfaces:**
- Consumes: the `leanr build --dry-run --json` CLI (Task 9), the pinned `.mathlib` checkout, `mathlib-pin`.
- Produces: the recorded M2a acceptance run.

- [ ] **Step 1: Write the acceptance script**

`scripts/build-fresh-acceptance.sh`:

```sh
#!/bin/sh
# M2a acceptance (spec §Testing): a fresh clone of pinned Mathlib —
# no .lake/, lake never run by the user — resolves via
# `leanr build --dry-run --json` byte-identically to the
# pre-materialized .mathlib checkout. Network (dependency clones from
# GitHub); local only, never CI. Needs: mathlib:fetch done, elan
# toolchain installed.
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

echo "acceptance: resolving the fresh clone (fetches deps from GitHub) ..." >&2
(cd "$tmp/mathlib" && "$leanr" build --dry-run --json) > "$tmp/fresh.json"

echo "acceptance: resolving the pre-materialized checkout ..." >&2
(cd "$repo_root/.mathlib" && "$leanr" build --dry-run --json) > "$tmp/base.json"

if ! diff -q "$tmp/fresh.json" "$tmp/base.json" >/dev/null; then
    echo "acceptance: FAIL — fresh-clone plan differs from baseline:" >&2
    diff "$tmp/fresh.json" "$tmp/base.json" | head -50 >&2
    exit 1
fi

modules=$(grep -c '"wave"' "$tmp/fresh.json")
packages=$(grep -c '"rev"' "$tmp/fresh.json")
echo "acceptance: PASS — plans identical; $packages packages, $modules modules" >&2
echo "acceptance: record these numbers in the M2a spec's Acceptance section" >&2
```

```bash
chmod +x scripts/build-fresh-acceptance.sh
```

In `mise.toml`, after `build:differential`:

```toml
[tasks."build:acceptance"]
description = "M2a acceptance: fresh clone of pinned Mathlib resolves byte-identically to the materialized checkout (network; local only)"
depends = ["elan:bootstrap"]
run = "scripts/build-fresh-acceptance.sh"
```

- [ ] **Step 2: Run acceptance**

Run: `mise run build:acceptance`
Expected: `acceptance: PASS — plans identical; 8 packages, N modules` (N is the recorded constant; expect roughly the Mathlib closure size, ~8,000+).

- [ ] **Step 3: Record results in the spec**

Append to `docs/superpowers/specs/2026-07-11-m2a-package-model-design.md`:

```markdown
## Acceptance (recorded on completion)

Run: <date>, pod: <describe briefly>.

- `mise run build:differential`: 4/4 oracles green over the pinned
  Mathlib closure (<N> modules import-diffed against their .oleans,
  0 mismatches).
- `mise run build:acceptance`: fresh clone resolved byte-identically
  to the materialized checkout; 8 packages at manifest revs;
  <N> modules planned in <W> waves.
```

Replace `<date>`, `<N>`, `<W>`, and the pod description with the real values from the runs.

- [ ] **Step 4: Full gate, commit**

Run: `mise run ci`
Expected: PASS.

```bash
git add scripts/build-fresh-acceptance.sh mise.toml docs/superpowers/specs/2026-07-11-m2a-package-model-design.md README.md
git commit -m "feat: M2a acceptance — fresh-clone Mathlib resolve, recorded results"
```

---

## Verification (whole plan)

After Task 11, the M2a bar from the spec is met when all of these are true:

1. `mise run ci` green (unit tier: config fixtures, manifest, scanner incl. proptest, glob, graph, bridge fakes, fetch git-tempdir tests, synthetic workspace, CLI).
2. `mise run build:differential` green (4 oracles).
3. `mise run build:acceptance` green (fresh clone, byte-identical plan).
4. Spec's Acceptance section carries the recorded numbers.

