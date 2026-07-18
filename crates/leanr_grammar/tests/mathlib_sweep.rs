//! Local-only Mathlib parse sweep + pass-list ratchet (M3b2a
//! acceptance; grows into M3b3's 100% gate). Needs `mise run
//! mathlib:fetch` first. Dev loop: `mise run parse:mathlib:fast`
//! (fast regression gate over the committed pass-list only). Full
//! discovery sweep (~35h; nightly only): `mise run parse:mathlib`.

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
#[ignore = "needs .mathlib (mise run mathlib:fetch); dev loop: mise run parse:mathlib:fast; \
            full discovery sweep: mise run parse:mathlib"]
fn mathlib_sweep_ratchet() {
    let mathlib = PathBuf::from(std::env::var("LEANR_MATHLIB_DIR").expect("LEANR_MATHLIB_DIR"));
    let lean_path = std::env::var("LEANR_OLEAN_PATH").expect("LEANR_OLEAN_PATH");
    let githash = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/oracle-githash.txt"),
    )
    .expect("oracle-githash.txt (mise run fixtures:regen)")
    .trim()
    .to_string();

    let passlist_only = std::env::var("LEANR_SWEEP_PASSLIST_ONLY").as_deref() == Ok("1");
    let passlist_update = std::env::var("LEANR_PASSLIST_UPDATE").as_deref() == Ok("1");
    // Rewriting the pass-list from a run that only swept the pass-list would
    // freeze growth forever (no new file is ever discovered) and would
    // silently DROP any entry that regressed (a file not swept this run
    // can't land in `green`, so it would just quietly disappear from the
    // rewritten list instead of failing the gate). Make that footgun
    // impossible rather than documenting it away.
    assert!(
        !(passlist_only && passlist_update),
        "LEANR_SWEEP_PASSLIST_ONLY=1 with LEANR_PASSLIST_UPDATE=1 is rejected: rewriting the \
         pass-list from a pass-list-only run would freeze growth and could silently drop a \
         regressed entry. Use `mise run passlist:update` (full sweep) to rewrite the pass-list."
    );

    // Read the committed pass-list once, up front: passlist-only mode needs
    // it to build the swept file set (instead of walking the corpus), and
    // every mode needs it for the final gating check.
    //
    // In passlist-only mode `committed` IS the entire swept file set (the
    // corpus walk is skipped entirely), so a read failure here must be a
    // hard error, not `unwrap_or_default()`: a silently empty set would
    // sweep zero files and report "0 files, 0 green, 0 regressions" —
    // a GREEN test result with the baseline effectively gone. Full/bounded
    // modes are unaffected: `committed` there is only the gating target,
    // and an empty/missing pass-list still causes the corpus-walked files
    // to be swept (just gated against nothing), so their behavior is left
    // as-is.
    let committed: BTreeSet<String> = if passlist_only {
        let text = std::fs::read_to_string(passlist_path()).expect(
            "failed to read the committed pass-list (tests/fixtures/syntax/mathlib-passlist.txt) \
             in passlist-only mode — this mode's swept file set IS this file, so an unreadable \
             file must fail loudly rather than silently gate zero files as a vacuous pass",
        );
        let set: BTreeSet<String> = text
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .map(String::from)
            .collect();
        assert!(
            !set.is_empty(),
            "committed pass-list is empty in passlist-only mode — refusing to gate vacuously \
             (0 files swept, 0 green, 0 regressions would still report the test as passing)"
        );
        set
    } else {
        std::fs::read_to_string(passlist_path())
            .unwrap_or_default()
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .map(String::from)
            .collect()
    };

    let roots: Vec<PathBuf> = lean_path
        .split(':')
        .filter(|s| !s.is_empty())
        .map(Into::into)
        .collect();
    let sp = SearchPath::new(roots);

    // Three modes, each with distinct gating semantics (see the regression
    // check below, which reads `truncated`):
    //   - bounded (LEANR_SWEEP_LIMIT=N): `files` is a truncated prefix of the
    //     sorted corpus walk; only pass-list entries actually swept this run
    //     are gated (`truncated = true`) — entries outside the prefix are
    //     neither green nor regressed, just not exercised.
    //   - full (no limit, not passlist-only): `files` is the whole corpus
    //     walk; `truncated = false`, so every committed entry is gated,
    //     including one whose file no longer exists on disk (it simply can't
    //     appear in `green`, so it reports as a regression).
    //   - passlist-only (LEANR_SWEEP_PASSLIST_ONLY=1): `files` is built
    //     directly from the committed pass-list, skipping the corpus walk
    //     entirely — no wasted directory I/O and, crucially, no olean
    //     closure decode for any import set no pass-list file uses.
    //     LEANR_SWEEP_LIMIT is ignored here (gating must stay total over the
    //     pass-list); `truncated = false` unconditionally, so this can never
    //     be silently downgraded to bounded-run semantics. A pass-list entry
    //     missing on disk is a loud, distinct failure (not folded into
    //     "regressions") — a deleted/renamed file must force a conscious
    //     `passlist:update`, not a quiet gate pass.
    let (files, truncated): (Vec<PathBuf>, bool) = if passlist_only {
        let mut resolved = Vec::with_capacity(committed.len());
        let mut missing = Vec::new();
        for rel in &committed {
            let p = mathlib.join(rel);
            if p.is_file() {
                resolved.push(p);
            } else {
                missing.push(rel.clone());
            }
        }
        assert!(
            missing.is_empty(),
            "pass-list entries missing on disk (deleted/renamed — this is NOT a parse \
             regression, it needs a conscious `mise run passlist:update`): {missing:#?}"
        );
        (resolved, false)
    } else {
        let limit: usize = std::env::var("LEANR_SWEEP_LIMIT")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(usize::MAX);
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
        (files, truncated)
    };

    let rel_of = |file: &Path| -> String {
        file.strip_prefix(&mathlib)
            .unwrap_or(file)
            .display()
            .to_string()
    };

    // The set of pass-list entries actually exercised this run — under a
    // bounded LEANR_SWEEP_LIMIT, files outside this set are neither green
    // nor regressed; they simply weren't swept. In full and passlist-only
    // modes this is a no-op distinction since `truncated` is false.
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
    // keeps the fresh-store-per-set decode cost (no change there) and banks
    // three SAFE wins: no phase barrier; the decoded `Store` (the biggest
    // per-worker allocation, multi-GB for deep Mathlib closures) is dropped
    // immediately after `assemble` rather than held through the file sweep;
    // and the inner per-file loop is sequential, since the real distribution
    // is 7,738 import sets over 8,844 files (avg ~1.1 files/set) — nested
    // parallelism buys nothing there but lets a thread blocked on a nested
    // join steal another outer set, stacking a second live multi-GB `Store`
    // on top. Live memory is therefore bounded by thread count ×
    // max(one `Store` during load, one `Arc<GrammarSnapshot>` during sweep),
    // instead of all 7,738 snapshots (or worse, stacked stores) held at once.
    let import_sets: Vec<Vec<String>> = by_imports.keys().cloned().collect();
    let total_sets = import_sets.len();
    let sets_done = std::sync::atomic::AtomicUsize::new(0);
    let green_count = std::sync::atomic::AtomicUsize::new(0);
    let green: BTreeSet<String> = import_sets
        .par_iter()
        .flat_map(|imports| {
            let snap = {
                let mut st = Store::persistent();
                let targets: Vec<_> = imports.iter().map(|m| dotted_to_name(m)).collect();
                leanr_olean::load_closure(&sp, &targets, &mut st)
                    .ok()
                    .map(|loaded| Arc::new(assemble(&loaded, &st).snapshot))
                // `st` (the decoded olean Store, the biggest allocation) drops here —
                // only the assembled snapshot is needed to sweep the set's files.
            };
            let set_green: Vec<String> = match &snap {
                Some(snap) => {
                    let group = &by_imports[imports];
                    // Sequential: sets average ~1.1 files, so nested
                    // parallelism has nothing to gain, and it lets an idle
                    // thread steal another outer set while still holding
                    // this set's `Store`/`snap`, stacking a second live
                    // multi-GB allocation.
                    group
                        .iter()
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

    // Full and passlist-only runs (both `!truncated`) gate the whole
    // committed list — a deleted/renamed/typo'd pass-list entry fails
    // loudly (in passlist-only mode, even louder: the `missing` check above
    // already aborted before the sweep ran). Bounded runs only gate entries
    // actually swept this run; entries outside the swept prefix are neither
    // green nor regressed.
    let committed_swept = committed.iter().filter(|f| swept.contains(*f)).count();
    let not_green: Vec<&String> = committed
        .iter()
        .filter(|f| (!truncated || swept.contains(*f)) && !green.contains(*f))
        .collect();
    // A committed entry that isn't green is either corpus churn (upstream
    // deleted/renamed the file — nothing to regress) or a genuine parse
    // regression (the file is still there, it just no longer parses
    // oracle-green). Only the update path (`LEANR_PASSLIST_UPDATE=1`, i.e.
    // `mise run passlist:update`) is allowed to tell them apart and drop the
    // former: its whole job is to reconcile the pass-list against upstream,
    // so silently absorbing a deletion (while still gating and printing it
    // loudly) is exactly the reconciliation it exists to do. The plain gate
    // (`parse:mathlib` / `parse:mathlib:fast`, `passlist_update == false`)
    // keeps failing on a missing file with zero exceptions: that gate's job
    // is only to *notice* churn and report it, never to *absorb* it — the
    // asymmetry is deliberate, not an oversight.
    let regressions: Vec<&String> = if passlist_update {
        let (missing, true_regressions) = split_missing_from_regressions(&mathlib, not_green);
        if !missing.is_empty() {
            eprintln!(
                "[sweep] dropping {} pass-list entries whose files no longer exist:",
                missing.len()
            );
            for f in &missing {
                eprintln!("[sweep]   {f}");
            }
        }
        true_regressions
    } else {
        not_green
    };
    let newly_green: Vec<_> = green.iter().filter(|f| !committed.contains(*f)).collect();
    let mode = if passlist_only {
        "passlist-only"
    } else if truncated {
        "bounded"
    } else {
        "full"
    };
    eprintln!(
        "sweep[{mode}]: {} files, {} green, {} on pass-list, {}/{} pass-list entries swept, {} regressions, {} newly green",
        files.len(),
        green.len(),
        committed.len(),
        committed_swept,
        committed.len(),
        regressions.len(),
        newly_green.len()
    );

    // Gate BEFORE writing, even in passlist-update mode: rewriting the
    // pass-list from `green` unconditionally would re-baseline over any
    // TRUE regression (a file that still exists but no longer parses green
    // would simply be dropped from the rewritten file instead of failing
    // the run) — the same "NEVER hand-edit to hide a regression" philosophy
    // the ratchet already states, now enforced for the automatic rewrite
    // too. `regressions` above has already had upstream-deleted entries
    // reconciled out (loudly, see above) precisely so this assert can stay
    // unconditional here: corpus churn was resolved before this point, so
    // reaching this line with a non-empty `regressions` means a real parse
    // regression, full stop, no further carve-outs needed. This also lets
    // `parse:mathlib:nightly` collapse to a single full sweep that both
    // gates and writes, instead of one sweep to gate followed by a second
    // full sweep to write (~70h for a task documented and budgeted at
    // ~35h).
    assert!(
        regressions.is_empty(),
        "pass-list regressions: {regressions:#?}"
    );

    if passlist_update {
        let mut out = String::from(
            "# Mathlib-closure files that parse oracle-green (M3b2a ratchet).\n\
             # Regenerate: mise run passlist:update. NEVER hand-edit to hide a regression.\n",
        );
        for f in &green {
            out.push_str(f);
            out.push('\n');
        }
        std::fs::write(passlist_path(), out).unwrap();
    }
}

/// Split a not-green pass-list entry set into (upstream-deleted, true
/// regression) by checking each relative path against the filesystem under
/// `mathlib`. Pulled out of `mathlib_sweep_ratchet`'s update-mode branch so
/// it's unit-testable without `.mathlib`/LEANR_MATHLIB_DIR/the oracle —
/// this split is the entire fix for the update-path deadlock, so it earns
/// its own cheap, always-run test.
fn split_missing_from_regressions<'a>(
    mathlib: &Path,
    not_green: Vec<&'a String>,
) -> (Vec<&'a String>, Vec<&'a String>) {
    not_green
        .into_iter()
        .partition(|f| !mathlib.join(f).is_file())
}

#[test]
fn split_missing_from_regressions_separates_deleted_files_from_true_regressions() {
    let dir = std::env::temp_dir().join(format!(
        "leanr-sweep-split-test-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir_all(dir.join("Mathlib")).unwrap();
    std::fs::write(dir.join("Mathlib/StillHere.lean"), "-- present\n").unwrap();
    // "Mathlib/Deleted.lean" is deliberately NOT created — stands in for a
    // pass-list entry whose file upstream renamed/deleted.

    let present = "Mathlib/StillHere.lean".to_string();
    let deleted = "Mathlib/Deleted.lean".to_string();
    let not_green = vec![&present, &deleted];

    let (missing, true_regressions) = split_missing_from_regressions(&dir, not_green);

    assert_eq!(
        missing,
        vec![&deleted],
        "the deleted file must be reconciled out, not gated"
    );
    assert_eq!(
        true_regressions,
        vec![&present],
        "a file that still exists but isn't green must stay a hard regression"
    );

    std::fs::remove_dir_all(&dir).unwrap();
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
