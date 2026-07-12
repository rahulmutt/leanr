use std::collections::HashMap;
use std::path::{Component, Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc;

use clap::{Parser, Subcommand};
use leanr_kernel::bank::NameId;
use leanr_kernel::{ConstantInfo, Environment, Name};
use leanr_olean::SearchPath;

/// A pure-Rust Lean 4 toolchain.
#[derive(Parser)]
#[command(name = "leanr", version)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Inspect official Lean artifacts.
    Olean {
        #[command(subcommand)]
        command: OleanCommand,
    },
    /// Kernel-check modules (LeanChecker's `--fresh` semantics: replayed
    /// from an empty environment, exactly the acceptance bar).
    Check {
        /// Modules to check, e.g. `Init.Data.Nat`. Mutually exclusive
        /// with `--all`.
        #[arg(required_unless_present = "all")]
        modules: Vec<String>,
        /// Check every `.olean` found under the search roots, instead of
        /// named modules.
        #[arg(long, conflicts_with = "modules")]
        all: bool,
        /// Extra search root (repeatable, highest priority first).
        /// Combined with `LEAN_PATH` (`:`-split) and
        /// `lean --print-libdir` (if resolvable), in that order.
        #[arg(long = "path")]
        path: Vec<PathBuf>,
        /// Worker threads (default: available parallelism).
        #[arg(long)]
        jobs: Option<usize>,
        /// use the sequential reference checker (replay) — differential/debugging only.
        #[arg(long)]
        sequential: bool,
    },
    /// Resolve the workspace and build every planned module (`--dry-run`
    /// prints the plan without building).
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
        /// Worker processes (default: available parallelism).
        #[arg(long)]
        jobs: Option<usize>,
        /// lean executable to drive (default: `lean` on PATH; primarily
        /// for tests and debugging).
        #[arg(long)]
        lean: Option<PathBuf>,
    },
}

#[derive(Subcommand)]
enum OleanCommand {
    /// Print the header of an .olean file.
    Info { path: PathBuf },
    /// List the declarations stored in an .olean file.
    Decls { path: PathBuf },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match cli.command {
        Command::Olean {
            command: OleanCommand::Info { path },
        } => olean_info(&path),
        Command::Olean {
            command: OleanCommand::Decls { path },
        } => olean_decls(&path),
        Command::Check {
            modules,
            all,
            path,
            jobs,
            sequential,
        } => check(modules, all, path, jobs, sequential),
        Command::Build {
            targets,
            dry_run,
            json,
            dir,
            toolchain_dir,
            jobs,
            lean,
        } => build(targets, dry_run, json, dir, toolchain_dir, jobs, lean),
    }
}

fn olean_info(path: &std::path::Path) -> ExitCode {
    let bytes = match std::fs::read(path) {
        Ok(bytes) => bytes,
        Err(err) => {
            eprintln!("error: cannot read {}: {err}", path.display());
            return ExitCode::FAILURE;
        }
    };
    match leanr_olean::OleanHeader::parse(&bytes) {
        Ok(header) => {
            println!("githash:      {}", header.githash);
            println!("base address: {:#x}", header.base_addr);
            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("error: {}: {err}", path.display());
            ExitCode::FAILURE
        }
    }
}

fn olean_decls(path: &std::path::Path) -> ExitCode {
    let bytes = match std::fs::read(path) {
        Ok(bytes) => bytes,
        Err(err) => {
            eprintln!("error: cannot read {}: {err}", path.display());
            return ExitCode::FAILURE;
        }
    };
    let mut store = leanr_kernel::bank::Store::persistent();
    match leanr_olean::ModuleData::parse(&bytes, &mut store) {
        Ok(module) => {
            // Same line format as the oracle-side dump script
            // (tests/fixtures/dump_decls.lean) — golden-compared in CI.
            let mut out = String::new();
            for c in &module.constants {
                out.push_str(&format!(
                    "{} {}\n",
                    c.kind(),
                    store.to_name(None, Some(c.name()))
                ));
            }
            print!("{out}");
            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("error: {}: {err}", path.display());
            ExitCode::FAILURE
        }
    }
}

/// Roots := `--path` args (in priority order) ++ `LEAN_PATH` (`:`-split)
/// ++ `lean --print-libdir` (if resolvable). Env/program reads happen HERE
/// only — `leanr_olean`'s `SearchPath` takes roots verbatim.
fn discover_roots(explicit: Vec<PathBuf>) -> Vec<PathBuf> {
    let mut roots = explicit;
    if let Ok(lean_path) = std::env::var("LEAN_PATH") {
        for p in lean_path.split(':') {
            if !p.is_empty() {
                roots.push(PathBuf::from(p));
            }
        }
    }
    if let Ok(output) = std::process::Command::new("lean")
        .arg("--print-libdir")
        .output()
    {
        if output.status.success() {
            if let Ok(s) = String::from_utf8(output.stdout) {
                let s = s.trim();
                if !s.is_empty() {
                    roots.push(PathBuf::from(s));
                }
            }
        }
    }
    roots
}

/// Build a hierarchical `Name` from a dotted CLI argument, e.g.
/// `Init.Data.Nat` -> `Str(Str(Str(Anonymous, "Init"), "Data"), "Nat")`.
fn parse_module_name(dotted: &str) -> Arc<Name> {
    let mut n = Arc::new(Name::Anonymous);
    for part in dotted.split('.') {
        n = Arc::new(Name::Str {
            parent: n,
            part: part.to_string(),
        });
    }
    n
}

/// The inverse mapping used by `--all`: a root-relative path (extension
/// already stripped) back to a module `Name`. `None` if any component
/// isn't an ordinary path segment (defensive; `collect_oleans` only ever
/// hands this real relative paths it just walked).
fn path_to_module_name(rel: &Path) -> Option<Arc<Name>> {
    let mut n = Arc::new(Name::Anonymous);
    for comp in rel.components() {
        match comp {
            Component::Normal(s) => {
                n = Arc::new(Name::Str {
                    parent: n,
                    part: s.to_str()?.to_string(),
                });
            }
            _ => return None,
        }
    }
    Some(n)
}

/// Recursively collect every base `.olean` under `dir`. Companion parts
/// (`Foo.olean.server`/`Foo.olean.private`) have extension `server`/
/// `private`, not `olean`, so this filter naturally excludes them — they
/// load automatically as part of their base module (Task 13a).
fn collect_oleans(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_oleans(&path, out);
        } else if path.extension().is_some_and(|e| e == "olean") {
            out.push(path);
        }
    }
}

/// `--all`: every `.olean` under every root, mapped back to module names
/// (deduped, sorted for a deterministic progress order).
fn enumerate_all(roots: &[PathBuf]) -> Vec<Arc<Name>> {
    let mut seen = std::collections::HashSet::new();
    let mut names = Vec::new();
    for root in roots {
        let mut files = Vec::new();
        collect_oleans(root, &mut files);
        for f in files {
            let Ok(rel) = f.strip_prefix(root) else {
                continue;
            };
            let rel = rel.with_extension("");
            if let Some(n) = path_to_module_name(&rel) {
                if seen.insert(n.to_string()) {
                    names.push(n);
                }
            }
        }
    }
    names.sort_by_key(|n| n.to_string());
    names
}

fn check(
    modules: Vec<String>,
    all: bool,
    path: Vec<PathBuf>,
    jobs: Option<usize>,
    sequential: bool,
) -> ExitCode {
    let roots = discover_roots(path);
    if roots.is_empty() {
        eprintln!("error: no search roots (pass --path, set LEAN_PATH, or install `lean` on PATH)");
        return ExitCode::FAILURE;
    }

    let targets: Vec<Arc<Name>> = if all {
        enumerate_all(&roots)
    } else {
        modules.iter().map(|m| parse_module_name(m)).collect()
    };
    if targets.is_empty() {
        eprintln!("error: no modules to check");
        return ExitCode::FAILURE;
    }

    let sp = SearchPath::new(roots);
    let mut env = Environment::default();
    let loaded = match leanr_olean::load_closure(&sp, &targets, env.store_mut()) {
        Ok(loaded) => loaded,
        Err(err) => {
            eprintln!("error: {err}");
            return ExitCode::FAILURE;
        }
    };

    // Per-module progress (stderr) while folding the union of constants
    // to replay, and the module that first supplies each constant (so a
    // replay failure can be attributed back to its module). Decoding
    // already interned everything (phase 3, direct-to-id decode) — this
    // loop just builds maps of ids.
    let n = loaded.len();
    let mut constants: HashMap<NameId, ConstantInfo> = HashMap::new();
    let mut owner: HashMap<NameId, Arc<Name>> = HashMap::new();
    for (i, (mod_name, md)) in loaded.into_iter().enumerate() {
        eprintln!("checking {mod_name} ({}/{n})", i + 1);
        for ci in md.constants {
            let name = ci.name();
            owner.entry(name).or_insert_with(|| Arc::clone(&mod_name));
            constants.entry(name).or_insert(ci);
        }
    }

    if sequential {
        // Faithful reference path: unchanged from before `--jobs` existed.
        // `replay` does its own unsafe/partial skipping, so it gets the
        // UNFILTERED `constants` map, and the store stays live (`&mut
        // env`) rather than being frozen.
        return match leanr_kernel::replay(&mut env, constants) {
            Ok(stats) => {
                println!(
                    "checked {n} modules, {} declarations (skipped {} unsafe/partial)",
                    stats.checked, stats.skipped_unsafe
                );
                ExitCode::SUCCESS
            }
            Err(err) => {
                // `ReplayError.decl` is an Arc<Name> render; map it back to
                // an id to look up the owning module.
                let module = env
                    .store_mut()
                    .intern_name(None, &err.decl)
                    .ok()
                    .flatten()
                    .and_then(|id| owner.get(&id))
                    .map(|m| m.to_string())
                    .unwrap_or_else(|| "?".to_string());
                eprintln!(
                    "error: {module}: while replaying '{}': {}",
                    err.decl, err.error
                );
                ExitCode::FAILURE
            }
        };
    }

    // Exclude unsafe/partial exactly as replay does, BEFORE building the
    // table the parallel driver consults — the driver never sees them, so
    // `CheckStats.skipped_unsafe` from `check_parallel` is always 0 here;
    // this loop's `skipped_unsafe` is the one that goes on the stats line.
    let mut skipped_unsafe = 0usize;
    let mut table_map: HashMap<NameId, ConstantInfo> = HashMap::new();
    for (name, ci) in constants {
        if leanr_kernel::is_unsafe_or_partial(&ci) {
            skipped_unsafe += 1;
        } else {
            table_map.insert(name, ci);
        }
    }

    let jobs = jobs.unwrap_or_else(|| {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
    });
    let store = Arc::new(env.into_store());
    let table = Arc::new(leanr_kernel::CheckedConstants::new(table_map));
    let graph = match leanr_check::graph::build_graph(&store, &table) {
        Ok(g) => g,
        Err(err) => {
            eprintln!("error: {err}");
            return ExitCode::FAILURE;
        }
    };

    match leanr_check::check_parallel(store.clone(), table, graph, jobs, |done| {
        if done % 1000 == 0 {
            eprintln!("checked {done} declarations");
        }
    }) {
        Ok(stats) => {
            println!(
                "checked {n} modules, {} declarations (skipped {} unsafe/partial)",
                stats.checked, skipped_unsafe
            );
            ExitCode::SUCCESS
        }
        Err(f) => {
            let module = owner
                .get(&f.decl)
                .map(|m| m.to_string())
                .unwrap_or_else(|| "?".to_string());
            eprintln!(
                "error: {module}: while replaying '{}': {}",
                store.to_name(None, Some(f.decl)),
                f.error
            );
            ExitCode::FAILURE
        }
    }
}

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
///
/// Errs with the offending absolute path when `path` doesn't resolve
/// under `root` — this happens when a lake-manifest.json path-dependency's
/// `dir` is itself absolute, which *replaces* (rather than joins) the
/// workspace root when composed with it. Silently falling back to the raw
/// path would leak a machine-specific absolute path into the plan, which
/// must be byte-identical across checkouts; callers turn this into a loud
/// CLI error naming the package/module and the fix instead.
fn rel_display(path: &std::path::Path, root: &std::path::Path) -> Result<String, PathBuf> {
    let rel = path.strip_prefix(root).map_err(|_| path.to_path_buf())?;
    Ok(rel
        .components()
        .map(|c| c.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/"))
}

fn build(
    targets: Vec<String>,
    dry_run: bool,
    json: bool,
    dir: Option<PathBuf>,
    toolchain_dir: Option<PathBuf>,
    jobs: Option<usize>,
    lean: Option<PathBuf>,
) -> ExitCode {
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
        let cache_root = leanr_build::cache_dir::cache_root(
            std::env::var_os("XDG_CACHE_HOME").as_deref(),
            std::env::var_os("HOME").as_deref(),
        )
        .ok_or_else(|| {
            "cannot determine the leanr cache directory: set XDG_CACHE_HOME or HOME".to_string()
        })?;
        // Pin dependency bridging to the root workspace's toolchain.
        let toolchain = std::fs::read_to_string(root_dir.join("lean-toolchain"))
            .ok()
            .map(|s| s.trim().to_string());
        let toolchain_for_lean = toolchain.clone();
        let opts = leanr_build::ResolveOptions {
            targets: targets.clone(),
            lake: leanr_build::bridge::LakeInvoker {
                toolchain,
                ..leanr_build::bridge::LakeInvoker::default()
            },
            toolchain_olean_dir,
            cache_root,
        };
        let ws = leanr_build::resolve(&root_dir, &opts).map_err(|e| e.to_string())?;
        for w in &ws.warnings {
            eprintln!("warning: {w}");
        }
        if dry_run {
            if json {
                print_json_plan(&ws)?;
            } else {
                print_text_plan(&ws);
            }
            return Ok(());
        }
        let jobs = jobs.unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(1)
        });
        let build_opts = leanr_build::compile::BuildOptions {
            jobs,
            lean: leanr_build::compile::LeanInvoker {
                program: lean.unwrap_or_else(|| PathBuf::from("lean")),
                toolchain: toolchain_for_lean,
            },
        };
        let build_start = std::time::Instant::now();
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
            build_start.elapsed().as_secs_f64(),
            jobs
        );
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
    Ok(PathBuf::from(
        String::from_utf8_lossy(&out.stdout).trim().to_string(),
    ))
}

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

fn print_json_plan(ws: &leanr_build::Workspace) -> Result<(), String> {
    let mut packages = Vec::with_capacity(ws.deps.len());
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
        packages.push(JsonPackage {
            name: &d.name,
            rev: d.rev.as_deref(),
            dir,
        });
    }
    let mut modules = Vec::new();
    for (wave, ids) in ws.waves.iter().enumerate() {
        for id in ids {
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
            modules.push(JsonModule {
                name: m.name.to_string(),
                package: m.package.clone(),
                file,
                wave,
            });
        }
    }
    let plan = JsonPlan {
        root: &ws.root.name,
        targets: &ws.targets,
        packages,
        modules,
    };
    println!(
        "{}",
        serde_json::to_string_pretty(&plan).expect("plan serializes")
    );
    Ok(())
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

#[cfg(test)]
mod rel_display_tests {
    use super::rel_display;
    use std::path::Path;

    #[test]
    fn ordinary_nested_path_is_relative() {
        let root = Path::new("/ws");
        let path = Path::new("/ws/App/Sub.lean");
        assert_eq!(rel_display(path, root).unwrap(), "App/Sub.lean");
    }

    #[test]
    fn dotdot_style_relative_dep_dir_keeps_working() {
        // A lake-manifest path dependency with `"dir": "../local"`, joined
        // onto the workspace root, still strips cleanly to a relative
        // display form (components-wise, without resolving `..`).
        let root = Path::new("/ws/app");
        let path = root.join("../local");
        assert_eq!(rel_display(&path, root).unwrap(), "../local");
    }

    #[test]
    fn absolute_dir_outside_workspace_errs_loudly() {
        // Simulates a lake-manifest path dependency whose `dir` is itself
        // absolute: `root_dir.join(dir)` replaces the root entirely, so
        // strip_prefix must fail rather than silently falling back to the
        // raw (machine-specific) absolute path.
        let root = Path::new("/ws/app");
        let outside = Path::new("/somewhere/else");
        let err = rel_display(outside, root).unwrap_err();
        assert_eq!(err, outside);
    }
}
