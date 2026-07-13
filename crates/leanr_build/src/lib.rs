//! Lake-compatible package model + module graph (M2a).
//! Spec: docs/superpowers/specs/2026-07-11-m2a-package-model-design.md
//!
//! `resolve()` is the crate's product: a straight-line pure-function
//! pipeline (no query engine yet — spec §Config acquisition, companion
//! decisions) whose output `Workspace` is the interface M2b's
//! orchestrator consumes.

use std::path::{Path, PathBuf};

pub mod bridge;
pub mod cache;
pub mod cache_dir;
pub mod compile;
pub mod config;
mod error;
pub mod fetch;
pub mod fingerprint;
mod fslock;
pub mod graph;
pub mod manifest;
pub mod modules;
pub mod pool;
pub mod remote;
pub mod scanner;
pub mod setup;
mod subprocess;
#[cfg(test)]
pub(crate) mod testws;

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
    /// Per-user leanr cache root (spec 2026-07-12 §Layout): shared git
    /// source checkouts under `src/`, the bridge cache under
    /// `config-cache/`. The CLI resolves it from XDG_CACHE_HOME/HOME.
    pub cache_root: PathBuf,
}

#[derive(Debug)]
pub struct ResolvedPackage {
    pub name: String,
    pub dir: PathBuf,
    /// Manifest rev for git packages; None for the root and path deps.
    pub rev: Option<String>,
    pub config: config::PackageConfig,
}

#[derive(Debug)]
pub struct Workspace {
    pub root_dir: PathBuf,
    pub root: ResolvedPackage,
    /// Manifest order.
    pub deps: Vec<ResolvedPackage>,
    pub graph: ModuleGraph,
    pub waves: Vec<Vec<ModuleId>>,
    pub warnings: Vec<String>,
    /// The effective target list `resolve()` actually seeded the module
    /// graph from: `ResolveOptions::targets` if non-empty, else the root
    /// package's `defaultTargets`. Single-sourced here so callers (the
    /// CLI's JSON plan) never have to recompute the same fallback.
    pub targets: Vec<String>,
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
    let cache_dir = opts.cache_root.join("config-cache");
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

    // 4. Materialize into the shared per-user source cache.
    let src_cache = opts.cache_root.join("src");
    fetch::materialize(&manifest.packages, root_dir, &src_cache)?;

    // 5. Dependency configs.
    let mut deps = Vec::new();
    for entry in &manifest.packages {
        let (dir, rev) = match &entry.source {
            manifest::PackageSource::Git { rev, sub_dir, .. } => {
                let base = src_cache.join(&entry.name).join(rev);
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
        deps.push(ResolvedPackage {
            name: entry.name.clone(),
            dir,
            rev,
            config: parsed.config,
        });
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
                    lib: lib.name.clone(),
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

    let toolchain = OleanDirIndex {
        root: opts.toolchain_olean_dir.clone(),
    };
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
        targets: target_names,
    })
}
