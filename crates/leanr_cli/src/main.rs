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
        /// Ignore the artifact cache: always run `lean`, never read or write it.
        #[arg(long)]
        no_cache: bool,
        /// Rebuild every module with `lean`, then refresh the cache.
        #[arg(long, conflicts_with = "no_cache")]
        force: bool,
        /// Remote cache URL to read through (env: LEANR_REMOTE_CACHE).
        #[arg(long, conflicts_with_all = ["no_cache", "no_remote"])]
        remote: Option<String>,
        /// Ignore any configured remote cache (local CAS only).
        #[arg(long)]
        no_remote: bool,
    },
    /// Inspect and maintain the shared artifact cache.
    Cache {
        #[command(subcommand)]
        command: CacheCommand,
    },
    /// Parse a Lean source file, folding in notation from its imports
    /// when a search root is available, and report syntax errors.
    Parse {
        /// The .lean file to parse.
        file: PathBuf,
        /// Print the canonical parse tree as JSON lines (the oracle-
        /// comparable form; see leanr_syntax::canon).
        #[arg(long)]
        dump: bool,
        /// Olean search roots for resolving the file's imports (repeatable,
        /// highest priority first; combined with LEAN_PATH and
        /// `lean --print-libdir`, like `check`). Without any resolvable
        /// root the file parses under the builtin grammar only.
        #[arg(long = "path")]
        path: Vec<PathBuf>,
        /// List imported parser entries that were skipped (raw parsers,
        /// unknown aliases, scoped) to stderr.
        #[arg(long)]
        verbose: bool,
    },
    /// Format Lean source files (leanr fmt).
    Fmt {
        /// Files to format; `-` reads stdin and writes stdout. With no
        /// files, walks the current directory for `*.lean`, respecting
        /// `.gitignore` and skipping hidden directories.
        files: Vec<PathBuf>,
        /// Check mode: write nothing, print a unified diff for each input
        /// that would change, exit non-zero if any would.
        #[arg(long)]
        check: bool,
        /// Root(s) to resolve the import closure for the grammar snapshot.
        #[arg(long)]
        path: Vec<PathBuf>,
    },
}

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
        /// Worker processes for `--deep` (default: available parallelism).
        #[arg(long)]
        jobs: Option<usize>,
        /// lean executable to drive for `--deep` (default: `lean` on PATH).
        #[arg(long)]
        lean: Option<PathBuf>,
    },
    /// Evict least-recently-used blobs until the store is at most SIZE bytes.
    Gc {
        #[arg(long = "max-size")]
        max_size: u64,
    },
    /// Prefetch the workspace's whole module closure from a remote cache
    /// into the local store (no lean, no materialization).
    Get {
        /// Remote cache URL (env: LEANR_REMOTE_CACHE).
        #[arg(long)]
        remote: Option<String>,
        /// Workspace dir (default: walk up from cwd).
        #[arg(long)]
        dir: Option<PathBuf>,
        /// Toolchain olean directory (default: `lean --print-libdir`).
        #[arg(long)]
        toolchain_dir: Option<PathBuf>,
        /// Download worker threads (default: available parallelism).
        #[arg(long)]
        jobs: Option<usize>,
    },
    /// Upload the workspace's locally-cached artifacts to an S3-compatible
    /// bucket (credentials via AWS_* env vars; CI-side, explicit only).
    Push {
        /// Target: s3://bucket[/prefix].
        #[arg(long)]
        to: String,
        /// Workspace dir (default: walk up from cwd).
        #[arg(long)]
        dir: Option<PathBuf>,
        /// Toolchain olean directory (default: `lean --print-libdir`).
        #[arg(long)]
        toolchain_dir: Option<PathBuf>,
        /// Upload worker threads (default: available parallelism).
        #[arg(long)]
        jobs: Option<usize>,
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
            no_cache,
            force,
            remote,
            no_remote,
        } => build(
            targets,
            dry_run,
            json,
            dir,
            toolchain_dir,
            jobs,
            lean,
            no_cache,
            force,
            remote,
            no_remote,
        ),
        Command::Cache { command } => cache_cmd(command),
        Command::Parse {
            file,
            dump,
            path,
            verbose,
        } => parse_cmd(&file, dump, path, verbose),
        Command::Fmt { files, check, path } => fmt_cmd(files, check, path),
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

/// Owns whatever backs a grammar snapshot so callers can borrow it.
enum SnapshotHolder {
    Assembled(leanr_grammar::AssembledGrammar),
    Builtin(leanr_syntax::grammar::GrammarSnapshot),
}

impl SnapshotHolder {
    fn snapshot(&self) -> &leanr_syntax::grammar::GrammarSnapshot {
        match self {
            SnapshotHolder::Assembled(a) => &a.snapshot,
            SnapshotHolder::Builtin(s) => s,
        }
    }
}

/// Build the grammar snapshot for `src` from its import closure (or the
/// builtin snapshot when there are no imports / no roots). Mirrors the
/// logic previously inline in `parse_cmd`.
fn load_snapshot(src: &str, path: Vec<PathBuf>, verbose: bool) -> Result<SnapshotHolder, String> {
    let imports = leanr_syntax::parse_header_imports(src);
    if imports.is_empty() {
        return Ok(SnapshotHolder::Builtin(leanr_syntax::builtin::snapshot()));
    }
    let roots = discover_roots(path);
    if roots.is_empty() {
        return Ok(SnapshotHolder::Builtin(leanr_syntax::builtin::snapshot()));
    }
    let sp = SearchPath::new(roots);
    let targets: Vec<_> = imports.iter().map(|m| parse_module_name(m)).collect();
    let mut st = leanr_kernel::bank::Store::persistent();
    let loaded = leanr_olean::load_closure(&sp, &targets, &mut st)
        .map_err(|e| format!("error[E0306]: cannot load imports: {e}"))?;
    let assembled = leanr_grammar::assemble(&loaded, &st);
    if verbose {
        for s in &assembled.skipped {
            eprintln!("skipped parser entry {} ({:?})", s.decl, s.reason);
        }
    }
    Ok(SnapshotHolder::Assembled(assembled))
}

fn parse_cmd(file: &Path, dump: bool, path: Vec<PathBuf>, verbose: bool) -> ExitCode {
    let bytes = match std::fs::read(file) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("error: cannot read {}: {e}", file.display());
            return ExitCode::FAILURE;
        }
    };
    let src = match String::from_utf8(bytes) {
        Ok(s) => s,
        Err(_) => {
            eprintln!("{}: error[E0305]: file is not valid UTF-8", file.display());
            return ExitCode::FAILURE;
        }
    };
    let holder = match load_snapshot(&src, path, verbose) {
        Ok(h) => h,
        Err(msg) => {
            eprintln!("{msg}");
            return ExitCode::FAILURE;
        }
    };
    let snap = holder.snapshot();
    let result = leanr_syntax::parse_module(&src, snap);
    if dump {
        print!("{}", leanr_syntax::canon::canon_jsonl(&result.tree));
    }
    for e in &result.errors {
        eprintln!(
            "{}:{}",
            file.display(),
            leanr_syntax::parse::render_error(&src, e)
        );
    }
    if result.errors.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// The inputs to format. Explicit arguments win; with none, walk the
/// current directory for `*.lean`, respecting `.gitignore`.
///
/// `ignore::WalkBuilder`'s defaults are almost exactly the wanted
/// behavior: hidden entries are skipped (so `.lake`, `.git`, and
/// `.mathlib` are excluded regardless of any ignore file), symlinks are
/// not followed, and nested `.gitignore` files compose. The one default
/// overridden is `require_git`, which otherwise only honors `.gitignore`
/// inside a directory that itself contains a `.git`; a project without
/// (or not yet inside) VCS metadata should still respect it. Results are
/// sorted so output order does not depend on filesystem iteration order.
fn resolve_inputs(files: Vec<PathBuf>) -> Vec<PathBuf> {
    if !files.is_empty() {
        return files;
    }
    let mut found: Vec<PathBuf> = ignore::WalkBuilder::new(".")
        // Honor `.gitignore` even when the walked directory is not itself
        // inside a `.git` repository (e.g. a project root without VCS
        // metadata, or in tests): the file is still a statement of intent.
        .require_git(false)
        .build()
        .filter_map(Result::ok)
        .filter(|e| e.file_type().is_some_and(|ft| ft.is_file()))
        .map(|e| e.into_path())
        .filter(|p| p.extension().and_then(|x| x.to_str()) == Some("lean"))
        .collect();
    found.sort();
    found
}

/// A unified diff of `before` → `after`, headed by `name` (a file path,
/// or `<stdin>`). Printed by `--check` for every input that would change.
fn unified_diff(name: &str, before: &str, after: &str) -> String {
    similar::TextDiff::from_lines(before, after)
        .unified_diff()
        .context_radius(3)
        .header(name, name)
        .to_string()
}

fn fmt_cmd(files: Vec<PathBuf>, check: bool, path: Vec<PathBuf>) -> ExitCode {
    let inputs = resolve_inputs(files);
    let mut any_would_change = false;
    let mut had_error = false;
    for file in &inputs {
        let is_stdin = file.as_os_str() == "-";
        let src = if is_stdin {
            let mut s = String::new();
            use std::io::Read;
            if std::io::stdin().read_to_string(&mut s).is_err() {
                eprintln!("error: stdin is not valid UTF-8");
                had_error = true;
                continue;
            }
            s
        } else {
            match std::fs::read(file) {
                Ok(b) => match String::from_utf8(b) {
                    Ok(s) => s,
                    Err(_) => {
                        eprintln!("{}: error[E0305]: file is not valid UTF-8", file.display());
                        had_error = true;
                        continue;
                    }
                },
                Err(e) => {
                    eprintln!("error: cannot read {}: {e}", file.display());
                    had_error = true;
                    continue;
                }
            }
        };
        let holder = match load_snapshot(&src, path.clone(), false) {
            Ok(h) => h,
            Err(msg) => {
                eprintln!("{}: {msg}", file.display());
                had_error = true;
                continue;
            }
        };
        let formatted = match leanr_fmt::format_src(&src, holder.snapshot()) {
            Ok(s) => s,
            Err(leanr_fmt::FormatError::Unparseable(msgs)) => {
                eprintln!("{}: error: cannot format unparseable file:", file.display());
                for m in msgs {
                    eprintln!("  {m}");
                }
                had_error = true;
                continue;
            }
        };
        let name = if is_stdin {
            "<stdin>".to_string()
        } else {
            file.display().to_string()
        };
        if check {
            // Check mode: never write a file, never emit the formatted
            // text (that is the non-check stdin behavior and would be
            // indistinguishable from it). Only diffs go to stdout.
            if formatted != src {
                any_would_change = true;
                print!("{}", unified_diff(&name, &src, &formatted));
            }
            continue;
        }
        if is_stdin {
            print!("{formatted}");
            continue;
        }
        if formatted != src {
            if let Err(e) = std::fs::write(file, &formatted) {
                eprintln!("error: cannot write {}: {e}", file.display());
                had_error = true;
            }
        }
    }
    if had_error || (check && any_would_change) {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
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

/// M2d remote-read config: `--remote` flag > `LEANR_REMOTE_CACHE` env;
/// `--no-remote` forces local-only without disturbing the environment.
fn resolve_remote_url(
    flag: Option<String>,
    no_remote: bool,
    env_val: Option<String>,
) -> Option<String> {
    if no_remote {
        return None;
    }
    flag.or(env_val)
}

fn fp_env_for(toolchain: &Option<String>) -> leanr_build::fingerprint::FingerprintEnv {
    leanr_build::fingerprint::FingerprintEnv {
        leanr_version: env!("CARGO_PKG_VERSION").to_string(),
        toolchain_id: toolchain.clone().unwrap_or_default(),
        platform: format!("{}-{}", std::env::consts::ARCH, std::env::consts::OS),
    }
}

fn remote_cache_for(url: &str) -> leanr_build::remote::RemoteCache {
    leanr_build::remote::RemoteCache::new(url, Box::new(|msg| eprintln!("warning: {msg}")))
}

fn default_jobs(jobs: Option<usize>) -> usize {
    jobs.unwrap_or_else(|| {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
    })
}

/// Resolve the workspace rooted at (or found by walking up from) `dir`,
/// deriving its packages, module graph, and build waves. `targets` and
/// `toolchain_dir` mirror `build`'s own flags of the same name (empty
/// `targets` := the root package's `defaultTargets`; no `toolchain_dir` :=
/// `lean --print-libdir`). Also returns the pinned `lean-toolchain` string
/// (if any), used to bridge `lake` and to drive `lean`. Shared by `build`
/// and `cache verify --deep` so both resolve through identical wiring.
fn resolve_workspace(
    dir: Option<PathBuf>,
    targets: Vec<String>,
    toolchain_dir: Option<PathBuf>,
) -> Result<(leanr_build::Workspace, Option<String>), String> {
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
    let opts = leanr_build::ResolveOptions {
        targets,
        lake: leanr_build::bridge::LakeInvoker {
            toolchain: toolchain.clone(),
            ..leanr_build::bridge::LakeInvoker::default()
        },
        toolchain_olean_dir,
        cache_root,
    };
    let ws = leanr_build::resolve(&root_dir, &opts).map_err(|e| e.to_string())?;
    for w in &ws.warnings {
        eprintln!("warning: {w}");
    }
    Ok((ws, toolchain))
}

#[allow(clippy::too_many_arguments)]
fn build(
    targets: Vec<String>,
    dry_run: bool,
    json: bool,
    dir: Option<PathBuf>,
    toolchain_dir: Option<PathBuf>,
    jobs: Option<usize>,
    lean: Option<PathBuf>,
    no_cache: bool,
    force: bool,
    remote: Option<String>,
    no_remote: bool,
) -> ExitCode {
    let run = || -> Result<(), String> {
        let (ws, toolchain_for_lean) = resolve_workspace(dir, targets, toolchain_dir)?;
        if dry_run {
            if json {
                print_json_plan(&ws)?;
            } else {
                print_text_plan(&ws);
            }
            return Ok(());
        }
        let jobs = default_jobs(jobs);
        let fp_env = fp_env_for(&toolchain_for_lean);
        let cache = if no_cache {
            None
        } else {
            let cache_root = leanr_build::cache_dir::cache_root(
                std::env::var_os("XDG_CACHE_HOME").as_deref(),
                std::env::var_os("HOME").as_deref(),
            )
            .ok_or_else(|| {
                "cannot determine the leanr cache directory: set XDG_CACHE_HOME or HOME".to_string()
            })?;
            Some(leanr_build::cache::Cache::new(&cache_root))
        };
        let remote = match &cache {
            Some(_) => {
                resolve_remote_url(remote, no_remote, std::env::var("LEANR_REMOTE_CACHE").ok())
                    .map(|url| remote_cache_for(&url))
            }
            None => None, // --no-cache bypasses everything, remote included
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
            remote,
        };
        let build_start = std::time::Instant::now();
        let report = leanr_build::compile::build_workspace(&ws, &build_opts, &|e| {
            if !e.diagnostics.is_empty() {
                eprint!("{}", e.diagnostics);
            }
            let tag = if e.cached {
                " (cached)"
            } else if e.downloaded {
                " (downloaded)"
            } else {
                ""
            };
            println!(
                "[{}/{}] {}{} ({:.1}s)",
                e.done, e.total, e.module, tag, e.secs
            );
        })
        .map_err(|e| e.to_string())?;
        println!(
            "built {} modules ({} cached, {} downloaded) in {:.1}s ({} jobs)",
            report.built,
            report.cached,
            report.downloaded,
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

/// `cache verify`'s integrity check (blob bytes == content key; no
/// dangling manifests) always runs; `--deep` additionally resolves a
/// workspace (must already be built — see `CacheCommand::Verify`'s help)
/// and rebuilds-and-diffs every cached module against a fresh `lean` run.
fn cache_cmd(command: CacheCommand) -> ExitCode {
    let run = || -> Result<(), String> {
        let cache_root = leanr_build::cache_dir::cache_root(
            std::env::var_os("XDG_CACHE_HOME").as_deref(),
            std::env::var_os("HOME").as_deref(),
        )
        .ok_or_else(|| {
            "cannot determine the leanr cache directory: set XDG_CACHE_HOME or HOME".to_string()
        })?;
        let cache = leanr_build::cache::Cache::new(&cache_root);
        match command {
            CacheCommand::Gc { max_size } => {
                let r = cache.gc(max_size).map_err(|e| e.to_string())?;
                println!(
                    "gc: removed {} blobs, freed {} bytes, {} bytes kept",
                    r.removed, r.freed, r.kept
                );
                Ok(())
            }
            CacheCommand::Verify {
                deep,
                dir,
                jobs,
                lean,
            } => {
                let r = cache.verify().map_err(|e| e.to_string())?;
                if r.bad_blobs.is_empty() && r.dangling.is_empty() {
                    println!("cache verify: OK ({} blobs)", r.blobs);
                } else {
                    return Err(format!(
                        "cache integrity FAILED: {} corrupt blob(s), {} dangling manifest(s)",
                        r.bad_blobs.len(),
                        r.dangling.len()
                    ));
                }
                if deep {
                    let (ws, toolchain) = resolve_workspace(dir, Vec::new(), None)?;
                    let env = fp_env_for(&toolchain);
                    let invoker = leanr_build::compile::LeanInvoker {
                        program: lean.unwrap_or_else(|| PathBuf::from("lean")),
                        toolchain,
                    };
                    let jobs = default_jobs(jobs);
                    let d = cache
                        .deep_verify(&ws, &env, &invoker, jobs)
                        .map_err(|e| e.to_string())?;
                    if d.mismatches.is_empty() {
                        println!(
                            "cache verify --deep: OK ({} modules byte-identical)",
                            d.checked
                        );
                    } else {
                        return Err(format!(
                            "cache verify --deep FAILED: {} mismatch(es): {}",
                            d.mismatches.len(),
                            d.mismatches.join(", ")
                        ));
                    }
                }
                Ok(())
            }
            CacheCommand::Get {
                remote,
                dir,
                toolchain_dir,
                jobs,
            } => {
                let url =
                    resolve_remote_url(remote, false, std::env::var("LEANR_REMOTE_CACHE").ok())
                        .ok_or_else(|| {
                            "no remote configured: pass --remote or set LEANR_REMOTE_CACHE"
                                .to_string()
                        })?;
                let (ws, toolchain) = resolve_workspace(dir, Vec::new(), toolchain_dir)?;
                let mut fps =
                    leanr_build::fingerprint::fingerprint_all(&ws, &fp_env_for(&toolchain))
                        .map_err(|e| e.to_string())?;
                fps.sort();
                fps.dedup();
                let rc = remote_cache_for(&url);
                let r = leanr_build::remote::get_all(&cache, &rc, &fps, default_jobs(jobs));
                println!(
                    "cache get: {} fetched, {} already local, {} not on remote, {} failed",
                    r.fetched, r.already_local, r.missing, r.failed
                );
                if r.failed > 0 {
                    return Err(format!("{} module(s) failed to fetch", r.failed));
                }
                Ok(())
            }
            CacheCommand::Push {
                to,
                dir,
                toolchain_dir,
                jobs,
            } => {
                let (ws, toolchain) = resolve_workspace(dir, Vec::new(), toolchain_dir)?;
                let mut fps =
                    leanr_build::fingerprint::fingerprint_all(&ws, &fp_env_for(&toolchain))
                        .map_err(|e| e.to_string())?;
                fps.sort();
                fps.dedup();
                let pusher = leanr_build::remote::Pusher::from_env(&to)?;
                let r = pusher.push(&cache, &fps, default_jobs(jobs))?;
                println!(
                    "cache push: {} manifests pushed ({} already remote), {} blobs, {} bytes uploaded",
                    r.manifests_pushed, r.manifests_skipped, r.blobs_pushed, r.bytes_uploaded
                );
                Ok(())
            }
        }
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
mod remote_url_tests {
    use super::resolve_remote_url;

    #[test]
    fn flag_wins_over_env() {
        assert_eq!(
            resolve_remote_url(Some("http://flag".into()), false, Some("http://env".into())),
            Some("http://flag".into())
        );
    }

    #[test]
    fn env_applies_when_no_flag() {
        assert_eq!(
            resolve_remote_url(None, false, Some("http://env".into())),
            Some("http://env".into())
        );
    }

    #[test]
    fn no_remote_forces_local_only_even_with_env() {
        assert_eq!(
            resolve_remote_url(None, true, Some("http://env".into())),
            None
        );
    }

    #[test]
    fn nothing_configured_is_none() {
        assert_eq!(resolve_remote_url(None, false, None), None);
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
