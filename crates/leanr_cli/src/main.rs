use std::collections::HashMap;
use std::path::{Component, Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc;

use clap::{Parser, Subcommand};
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
        Command::Check { modules, all, path } => check(modules, all, path),
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
    match leanr_olean::ModuleData::parse(&bytes) {
        Ok(module) => {
            // Same line format as the oracle-side dump script
            // (tests/fixtures/dump_decls.lean) — golden-compared in CI.
            let mut out = String::new();
            for c in &module.constants {
                out.push_str(&format!("{} {}\n", c.kind(), c.name()));
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

fn check(modules: Vec<String>, all: bool, path: Vec<PathBuf>) -> ExitCode {
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
    let loaded = match leanr_olean::load_closure(&sp, &targets) {
        Ok(loaded) => loaded,
        Err(err) => {
            eprintln!("error: {err}");
            return ExitCode::FAILURE;
        }
    };

    // Per-module progress (stderr) while building the union of constants
    // to replay, and the module that first supplies each constant (so a
    // replay failure can be attributed back to the module it came from).
    let n = loaded.len();
    let mut constants: HashMap<Arc<Name>, ConstantInfo> = HashMap::new();
    let mut owner: HashMap<Arc<Name>, Arc<Name>> = HashMap::new();
    for (i, (mod_name, md)) in loaded.iter().enumerate() {
        eprintln!("checking {mod_name} ({}/{n})", i + 1);
        for c in &md.constants {
            let cn = Arc::clone(c.name());
            owner
                .entry(Arc::clone(&cn))
                .or_insert_with(|| Arc::clone(mod_name));
            constants.entry(cn).or_insert_with(|| c.clone());
        }
    }

    let mut env = Environment::default();
    match leanr_kernel::replay(&mut env, constants) {
        Ok(stats) => {
            println!(
                "checked {n} modules, {} declarations (skipped {} unsafe/partial)",
                stats.checked, stats.skipped_unsafe
            );
            ExitCode::SUCCESS
        }
        Err(err) => {
            let module = owner
                .get(&err.decl)
                .map(|m| m.to_string())
                .unwrap_or_else(|| "?".to_string());
            eprintln!(
                "error: {module}: while replaying '{}': {}",
                err.decl, err.error
            );
            ExitCode::FAILURE
        }
    }
}
