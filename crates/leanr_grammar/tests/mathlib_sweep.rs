//! Local-only Mathlib parse sweep + pass-list ratchet (M3b2a
//! acceptance; grows into M3b3's 100% gate). Needs `mise run
//! mathlib:fetch` first. Run via `mise run parse:mathlib`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;

use leanr_grammar::assemble;
use leanr_kernel::bank::Store;
use leanr_olean::SearchPath;
use rayon::prelude::*;

fn passlist_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/syntax/mathlib-passlist.txt")
}

/// Oracle dump with per-file cache under target/leanr-stx-cache/.
/// Key: (oracle githash, blake3 of file bytes). Dumper: the elaborating
/// one — arbitrary real files may grow the grammar mid-file.
fn oracle_dump(mathlib: &Path, lean_path: &str, githash: &str, file: &Path) -> Option<String> {
    let bytes = std::fs::read(file).ok()?;
    let key = format!("{githash}-{}", blake3::hash(&bytes).to_hex());
    let cache = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/leanr-stx-cache")
        .join(&key);
    if let Ok(hit) = std::fs::read_to_string(&cache) {
        return Some(hit);
    }
    let dumper = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/syntax/dump_syntax_elab.lean");
    let out = Command::new("lean")
        .env("LEAN_PATH", lean_path)
        .current_dir(mathlib)
        .arg("--run")
        .arg(&dumper)
        .arg(file)
        .output()
        .ok()?;
    if !out.status.success() {
        return None; // oracle itself failed on this file → not sweepable yet
    }
    let s = String::from_utf8(out.stdout).ok()?;
    std::fs::create_dir_all(cache.parent().unwrap()).ok()?;
    std::fs::write(&cache, &s).ok();
    Some(s)
}

#[test]
#[ignore = "needs .mathlib (mise run mathlib:fetch); run via mise run parse:mathlib"]
fn mathlib_sweep_ratchet() {
    let mathlib = PathBuf::from(std::env::var("LEANR_MATHLIB_DIR").expect("LEANR_MATHLIB_DIR"));
    let lean_path = std::env::var("LEANR_OLEAN_PATH").expect("LEANR_OLEAN_PATH");
    let githash = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/oracle-githash.txt"),
    )
    .expect("oracle-githash.txt (mise run fixtures:regen)")
    .trim()
    .to_string();
    let limit: usize = std::env::var("LEANR_SWEEP_LIMIT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(usize::MAX);

    let roots: Vec<PathBuf> = lean_path
        .split(':')
        .filter(|s| !s.is_empty())
        .map(Into::into)
        .collect();
    let sp = SearchPath::new(roots);

    // Enumerate: Mathlib/**/*.lean + each package's source tree.
    let mut files: Vec<PathBuf> = Vec::new();
    collect_lean_files(&mathlib.join("Mathlib"), &mut files);
    if let Ok(pkgs) = std::fs::read_dir(mathlib.join(".lake/packages")) {
        for p in pkgs.flatten() {
            collect_lean_files(&p.path(), &mut files);
        }
    }
    files.sort();
    let total = files.len();
    files.truncate(limit);
    let truncated = files.len() < total;

    let rel_of = |file: &Path| -> String {
        file.strip_prefix(&mathlib)
            .unwrap_or(file)
            .display()
            .to_string()
    };

    // The set of pass-list entries actually exercised this run — under a
    // bounded LEANR_SWEEP_LIMIT, files outside this set are neither green
    // nor regressed; they simply weren't swept.
    let swept: BTreeSet<String> = files.iter().map(|f| rel_of(f)).collect();

    // Group files by import list (sorted by `Vec<String>` order via
    // `BTreeMap`, giving prefix locality: similar import lists land next to
    // each other below).
    let mut by_imports: BTreeMap<Vec<String>, Vec<PathBuf>> = BTreeMap::new();
    for file in &files {
        let Ok(src) = std::fs::read_to_string(file) else {
            continue;
        };
        by_imports
            .entry(leanr_syntax::parse_header_imports(&src))
            .or_default()
            .push(file.clone());
    }

    // Fused snapshot-build + sweep, one import set at a time, in parallel —
    // no barrier between "build every snapshot" and "sweep every file"
    // (was: phase A built and held all 7,738 `Arc<GrammarSnapshot>`s before
    // phase B could sweep a single file). Each set still gets its OWN fresh
    // `Store::persistent()` (unchanged from before this fix): a chunked,
    // warm-store-per-worker variant of this (reusing one `Store` across many
    // sets sequentially, to collapse decode of shared oleans like
    // Init/Std/Mathlib.Init) was prototyped and passed its own correctness
    // check (LIMIT=30 cold-vs-warm green-list diff was byte-identical, and
    // an isolated single-chunk replay of the exact sequence one worker
    // processed never reproduced any issue) but reliably panicked
    // (`index out of bounds` in `leanr_syntax`'s `KindInterner::name`,
    // reproduced twice) once multiple chunks' independent warm `Store`s ran
    // concurrently at LEANR_SWEEP_LIMIT=200 — a real, reproducible-at-scale
    // failure mode whose exact mechanism wasn't pinned down within budget
    // (see task-1-optimize-report.md). Rather than ship that risk, this
    // keeps the fresh-store-per-set decode cost (no change there) and only
    // banks the two SAFE wins: no phase barrier, and at most one live
    // `Arc<GrammarSnapshot>` in flight per in-progress set (dropped the
    // moment its files are swept) instead of all 7,738 held at once.
    let import_sets: Vec<Vec<String>> = by_imports.keys().cloned().collect();
    let total_sets = import_sets.len();
    let sets_done = std::sync::atomic::AtomicUsize::new(0);
    let green_count = std::sync::atomic::AtomicUsize::new(0);
    let green: BTreeSet<String> = import_sets
        .par_iter()
        .flat_map(|imports| {
            let mut st = Store::persistent();
            let targets: Vec<_> = imports.iter().map(|m| dotted_to_name(m)).collect();
            let snap = leanr_olean::load_closure(&sp, &targets, &mut st)
                .ok()
                .map(|loaded| Arc::new(assemble(&loaded, &st).snapshot));
            let set_green: Vec<String> = match &snap {
                Some(snap) => {
                    let group = &by_imports[imports];
                    group
                        .par_iter()
                        .filter_map(|file| {
                            let rel = rel_of(file);
                            let src = std::fs::read_to_string(file).ok()?;
                            let r = leanr_syntax::parse_module(&src, snap);
                            if r.tree.text() != src || !r.errors.is_empty() {
                                return None;
                            }
                            let want = oracle_dump(&mathlib, &lean_path, &githash, file)?;
                            (leanr_syntax::canon::canon_jsonl(&r.tree) == want).then_some(rel)
                        })
                        .collect()
                }
                None => Vec::new(),
            };
            // `snap` (and its Arc<GrammarSnapshot>) drops here, right after
            // this set's files are swept — never accumulated across sets.
            use std::sync::atomic::Ordering;
            let done = sets_done.fetch_add(1, Ordering::Relaxed) + 1;
            let green_so_far =
                green_count.fetch_add(set_green.len(), Ordering::Relaxed) + set_green.len();
            if done.is_multiple_of(100) || done == total_sets {
                eprintln!("[sweep] {done}/{total_sets} sets, {green_so_far} green so far");
            }
            set_green
        })
        .collect();

    let committed: BTreeSet<String> = std::fs::read_to_string(passlist_path())
        .unwrap_or_default()
        .lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(String::from)
        .collect();

    // Full runs (no LEANR_SWEEP_LIMIT truncation) gate the whole committed
    // list — a deleted/renamed/typo'd pass-list entry fails loudly, forcing
    // a conscious passlist:update. Truncated runs only gate entries actually
    // swept this run; entries outside the swept prefix are neither green nor
    // regressed.
    let committed_swept = committed.iter().filter(|f| swept.contains(*f)).count();
    let regressions: Vec<_> = committed
        .iter()
        .filter(|f| (!truncated || swept.contains(*f)) && !green.contains(*f))
        .collect();
    let newly_green: Vec<_> = green.iter().filter(|f| !committed.contains(*f)).collect();
    eprintln!(
        "sweep: {} files, {} green, {} on pass-list, {}/{} pass-list entries swept, {} regressions, {} newly green",
        files.len(),
        green.len(),
        committed.len(),
        committed_swept,
        committed.len(),
        regressions.len(),
        newly_green.len()
    );

    if std::env::var("LEANR_PASSLIST_UPDATE").as_deref() == Ok("1") {
        let mut out = String::from(
            "# Mathlib-closure files that parse oracle-green (M3b2a ratchet).\n\
             # Regenerate: mise run passlist:update. NEVER hand-edit to hide a regression.\n",
        );
        for f in &green {
            out.push_str(f);
            out.push('\n');
        }
        std::fs::write(passlist_path(), out).unwrap();
        return;
    }
    assert!(
        regressions.is_empty(),
        "pass-list regressions: {regressions:#?}"
    );
}

fn collect_lean_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else {
        return;
    };
    for e in rd.flatten() {
        let p = e.path();
        if p.is_dir() {
            // Skip build dirs — only source trees.
            if p.file_name().is_some_and(|n| n == ".lake" || n == "build") {
                continue;
            }
            collect_lean_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "lean") {
            out.push(p);
        }
    }
}

fn dotted_to_name(dotted: &str) -> Arc<leanr_kernel::Name> {
    use leanr_kernel::Name;
    let mut n = Arc::new(Name::Anonymous);
    for part in dotted.split('.') {
        n = Arc::new(Name::Str {
            parent: n,
            part: part.to_string(),
        });
    }
    n
}
