//! Mathlib parse sweep + pass-list ratchet (M3b2a acceptance; grows into
//! M3b3's 100% gate). Needs `mise run mathlib:fetch` first. Dev loop:
//! `mise run parse:mathlib:fast` (fast regression gate over the committed
//! pass-list only). Full discovery sweep (~35h, unsharded, local):
//! `mise run parse:mathlib`. The SCHEDULED nightly is
//! `.github/workflows/nightly-sweep.yml`, which runs that same discovery
//! sweep as 12 `parse:mathlib:shard` jobs plus one `parse:mathlib:merge`
//! job that gates their union.

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
    // `.mathlib` is needed by every mode, including merge — merge does no
    // parsing, but the reconcile step has to test each not-green pass-list
    // entry for existence on disk to tell upstream churn from a true
    // regression.
    let mathlib = PathBuf::from(std::env::var("LEANR_MATHLIB_DIR").expect(
        "LEANR_MATHLIB_DIR is required in every mode, including LEANR_SWEEP_MERGE: the reconcile \
         step tests each not-green pass-list entry for existence under it to separate \
         upstream-deleted files from true parse regressions",
    ));

    // All mode flags are read up front so the mutual-exclusion assertions
    // below fire before any expensive work — and, critically, before
    // anything can write the pass-list.
    let passlist_only = std::env::var("LEANR_SWEEP_PASSLIST_ONLY").as_deref() == Ok("1");
    let passlist_update = std::env::var("LEANR_PASSLIST_UPDATE").as_deref() == Ok("1");
    let shard_raw = non_empty_env("LEANR_SWEEP_SHARD");
    let green_out = non_empty_env("LEANR_SWEEP_GREEN_OUT").map(PathBuf::from);
    let merge_dir = non_empty_env("LEANR_SWEEP_MERGE").map(PathBuf::from);

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

    // Shard mode is a *fragment* of a full sweep: it sees only 1/N of the
    // import sets, so by construction most pass-list entries cannot be green
    // in it. That makes every gating/writing mode incompatible with it, for
    // exactly the reason the passlist-only/update pair above is: a mode that
    // gates or rewrites from a partial `green` either reports mass phantom
    // regressions or silently drops every entry the shard never touched.
    // Assert it rather than document it away.
    assert!(
        !(shard_raw.is_some() && passlist_update),
        "LEANR_SWEEP_SHARD with LEANR_PASSLIST_UPDATE=1 is rejected: a shard sweeps only 1/N of \
         the import sets, so rewriting the pass-list from its partial green list would drop every \
         entry outside this shard's slice. Shards emit a green list (LEANR_SWEEP_GREEN_OUT); only \
         LEANR_SWEEP_MERGE gates and rewrites, over the union of all shards."
    );
    assert!(
        !(shard_raw.is_some() && passlist_only),
        "LEANR_SWEEP_SHARD with LEANR_SWEEP_PASSLIST_ONLY=1 is rejected: passlist-only mode's \
         swept set IS the committed pass-list and its gating is deliberately total, which is \
         precisely what a shard cannot provide. Shard the full corpus sweep instead."
    );
    assert!(
        !(shard_raw.is_some() && merge_dir.is_some()),
        "LEANR_SWEEP_SHARD with LEANR_SWEEP_MERGE is rejected: they are the two halves of the \
         sharded nightly (produce one green list vs. consume all of them), never one run."
    );
    assert!(
        !(merge_dir.is_some() && passlist_only),
        "LEANR_SWEEP_MERGE with LEANR_SWEEP_PASSLIST_ONLY=1 is rejected: merge mode's green set \
         comes from the shard artifacts, not from a sweep, so passlist-only has nothing to mean \
         here."
    );
    assert!(
        !(passlist_only && green_out.is_some()),
        "LEANR_SWEEP_GREEN_OUT with LEANR_SWEEP_PASSLIST_ONLY=1 is rejected: a passlist-only run's \
         green list is at most the committed pass-list it was handed, so emitting it as a \
         shard-style green list would invite merging a slice that discovered nothing."
    );
    assert!(
        !(shard_raw.is_some() && green_out.is_none()),
        "LEANR_SWEEP_SHARD requires LEANR_SWEEP_GREEN_OUT=<path>: a shard does not gate, so its \
         green list is its ONLY output — a shard that wrote nothing would silently contribute an \
         empty slice to the merge."
    );

    // `I/N`, 1-based. Parsed rather than `unwrap`ed so a typo (`12`, `0/12`,
    // `13/12`, `1/0`) says what is wrong with it instead of panicking on an
    // index or, worse, silently sweeping the wrong slice.
    let shard: Option<(usize, usize)> = shard_raw.as_deref().map(|raw| {
        parse_shard_spec(raw)
            .unwrap_or_else(|e| panic!("LEANR_SWEEP_SHARD={raw:?} is malformed: {e}"))
    });

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

    // Merge mode (LEANR_SWEEP_MERGE=<dir>): the second half of the sharded
    // nightly. It parses nothing — its `green` is the union of the shards'
    // green lists — and then runs the SAME gate + reconcile + rewrite path
    // that full update mode runs, `truncated = false`, so the union is gated
    // TOTALLY against the committed pass-list exactly as a single ~35h full
    // sweep would be. That equality is the whole point: sharding must change
    // only where the parsing happens, never what is gated. It is therefore
    // dispatched here, before LEANR_OLEAN_PATH/the oracle githash are
    // required, since neither is needed to union text files.
    if let Some(dir) = &merge_dir {
        let (green, sources) = read_shard_green_lists(dir);
        eprintln!(
            "[merge] union of {} shard green list(s) from {}:",
            sources.len(),
            dir.display()
        );
        for s in &sources {
            eprintln!("[merge]   {}", s.display());
        }
        let before = committed.len();
        let newly_green = gate_and_maybe_rewrite(GateInput {
            mathlib: &mathlib,
            committed: &committed,
            // `truncated` is false, so `swept` is never consulted; the union
            // itself is the only honest value to hand it.
            swept: &green,
            green: &green,
            truncated: false,
            passlist_update: true,
            mode: "merge",
            files_swept: green.len(),
        });
        eprintln!(
            "[merge] pass-list growth: {before} -> {} entries ({newly_green} newly green)",
            green.len()
        );
        return;
    }

    let lean_path = std::env::var("LEANR_OLEAN_PATH").expect("LEANR_OLEAN_PATH");
    let githash = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/oracle-githash.txt"),
    )
    .expect("oracle-githash.txt (mise run fixtures:regen)")
    .trim()
    .to_string();

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
    //
    // Shard mode (LEANR_SWEEP_SHARD=I/N) partitions THIS list — the import
    // sets, i.e. the actual unit of work and of cost — by stride
    // (`index % N == I-1`), not by contiguous chunk. `by_imports` is a
    // `BTreeMap`, so the list is sorted, and sorted import lists share long
    // prefixes: a contiguous chunk would therefore concentrate all the deep,
    // expensive Mathlib closures in a few shards and leave others with the
    // cheap `Init`-only sets, while a stride deals those neighbours out
    // round-robin across every shard.
    let all_sets: Vec<Vec<String>> = by_imports.keys().cloned().collect();
    let import_sets: Vec<Vec<String>> = match shard {
        Some((i, n)) => shard_slice(&all_sets, i, n),
        None => all_sets,
    };
    let files_swept: usize = if shard.is_some() {
        import_sets.iter().map(|k| by_imports[k].len()).sum()
    } else {
        files.len()
    };
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

    // A green list can be emitted from any sweeping mode; in shard mode it
    // is mandatory (asserted above) and is the run's ONLY output.
    if let Some(path) = &green_out {
        write_green_list(path, &green);
    }

    // Shard mode stops HERE, deliberately, before any gating: this run saw
    // only 1/N of the import sets, so every pass-list entry whose file lives
    // in another shard's slice is trivially not-green and would be reported
    // as a regression. Gating a shard is not a stricter check, it is a
    // meaningless one. The merge job re-enters this same gate (see
    // `gate_and_maybe_rewrite`) over the union of every shard's green list,
    // which is exactly the set an unsharded full sweep would have produced.
    if let Some((i, n)) = shard {
        eprintln!(
            "sweep[shard {i}/{n}]: {} of {} import sets, {files_swept} files, {} green (no gate: \
             the merge job gates the union)",
            import_sets.len(),
            by_imports.len(),
            green.len()
        );
        return;
    }

    let mode = if passlist_only {
        "passlist-only"
    } else if truncated {
        "bounded"
    } else {
        "full"
    };
    gate_and_maybe_rewrite(GateInput {
        mathlib: &mathlib,
        committed: &committed,
        swept: &swept,
        green: &green,
        truncated,
        passlist_update,
        mode,
        files_swept,
    });
}

/// Everything a sweep does once it has a green set: gate, reconcile, report,
/// and (in update mode) rewrite the pass-list. Extracted so merge mode runs
/// literally this code rather than a shell reimplementation of it — the
/// sharded nightly is only trustworthy if the union it gates is gated by the
/// same logic, with the same missing-vs-regressed split, as an unsharded
/// full sweep. Returns the newly-green count (the growth delta's numerator).
struct GateInput<'a> {
    mathlib: &'a Path,
    committed: &'a BTreeSet<String>,
    /// Files actually swept this run; only consulted when `truncated`.
    swept: &'a BTreeSet<String>,
    green: &'a BTreeSet<String>,
    /// True only for bounded (LEANR_SWEEP_LIMIT) runs.
    truncated: bool,
    passlist_update: bool,
    mode: &'a str,
    files_swept: usize,
}

fn gate_and_maybe_rewrite(input: GateInput<'_>) -> usize {
    let GateInput {
        mathlib,
        committed,
        swept,
        green,
        truncated,
        passlist_update,
        mode,
        files_swept,
    } = input;

    // Full, passlist-only and merge runs (all `!truncated`) gate the whole
    // committed list — a deleted/renamed/typo'd pass-list entry fails
    // loudly (in passlist-only mode, even louder: the `missing` check in the
    // caller already aborted before the sweep ran). Bounded runs only gate
    // entries actually swept this run; entries outside the swept prefix are
    // neither green nor regressed.
    let committed_swept = committed.iter().filter(|f| swept.contains(*f)).count();
    let not_green: Vec<&String> = committed
        .iter()
        .filter(|f| (!truncated || swept.contains(*f)) && !green.contains(*f))
        .collect();
    // A committed entry that isn't green is either corpus churn (upstream
    // deleted/renamed the file — nothing to regress) or a genuine parse
    // regression (the file is still there, it just no longer parses
    // oracle-green). Only the update path (`LEANR_PASSLIST_UPDATE=1`, i.e.
    // `mise run passlist:update`, and merge mode, which is that same update
    // path fed by the shards) is allowed to tell them apart and drop the
    // former: its whole job is to reconcile the pass-list against upstream,
    // so silently absorbing a deletion (while still gating and printing it
    // loudly) is exactly the reconciliation it exists to do. The plain gate
    // (`parse:mathlib` / `parse:mathlib:fast`, `passlist_update == false`)
    // keeps failing on a missing file with zero exceptions: that gate's job
    // is only to *notice* churn and report it, never to *absorb* it — the
    // asymmetry is deliberate, not an oversight.
    let regressions: Vec<&String> = if passlist_update {
        let (missing, true_regressions) = split_missing_from_regressions(mathlib, not_green);
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
    eprintln!(
        "sweep[{mode}]: {} files, {} green, {} on pass-list, {}/{} pass-list entries swept, {} regressions, {} newly green",
        files_swept,
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
    // ~35h). In the sharded nightly this assert is the alarm: it is the one
    // place a real regression turns into a red workflow run.
    assert!(
        regressions.is_empty(),
        "pass-list regressions: {regressions:#?}"
    );

    if passlist_update {
        let mut out = String::from(
            "# Mathlib-closure files that parse oracle-green (M3b2a ratchet).\n\
             # Regenerate: mise run passlist:update. NEVER hand-edit to hide a regression.\n",
        );
        for f in green {
            out.push_str(f);
            out.push('\n');
        }
        std::fs::write(passlist_path(), out).unwrap();
    }

    newly_green.len()
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

/// Read an env var, treating unset and empty/whitespace-only as equally
/// absent. Every heavyweight mise task in this repo neutralizes a flag
/// leaked in from the calling shell by pinning it to `""`, so an empty value
/// must mean "off" here — never "malformed", and never a shard spec of `""`.
fn non_empty_env(key: &str) -> Option<String> {
    std::env::var(key).ok().filter(|s| !s.trim().is_empty())
}

/// Parse `LEANR_SWEEP_SHARD` as 1-based `I/N`. Returns `Err(reason)` rather
/// than panicking or silently defaulting: a mistyped shard spec that quietly
/// swept the wrong slice would produce a green list that is wrong in a way
/// the merge cannot detect (it would just look like fewer files parse).
fn parse_shard_spec(raw: &str) -> Result<(usize, usize), String> {
    let (i_raw, n_raw) = raw
        .split_once('/')
        .ok_or_else(|| "expected the form I/N (1-based), e.g. 3/12".to_string())?;
    let parse = |s: &str, what: &str| -> Result<usize, String> {
        s.trim()
            .parse::<usize>()
            .map_err(|e| format!("{what} {:?} is not a non-negative integer: {e}", s.trim()))
    };
    let i = parse(i_raw, "shard index")?;
    let n = parse(n_raw, "shard count")?;
    if n == 0 {
        return Err("shard count N must be >= 1".to_string());
    }
    if i == 0 || i > n {
        return Err(format!(
            "shard index I must be in 1..={n} (1-based), got {i}"
        ));
    }
    Ok((i, n))
}

/// The `I`-th of `N` stride shards of `items`: every element whose index is
/// congruent to `I-1` mod `N`. Striding (not chunking) is deliberate — see
/// the call site: the input is sorted by import list, so neighbours have
/// near-identical decode cost and must be dealt out round-robin.
fn shard_slice<T: Clone>(items: &[T], i: usize, n: usize) -> Vec<T> {
    items
        .iter()
        .enumerate()
        .filter(|(idx, _)| idx % n == i - 1)
        .map(|(_, t)| t.clone())
        .collect()
}

/// Write a green list: one relative path per line, sorted (`green` is a
/// `BTreeSet`), no header — this is machine input for merge mode, not the
/// committed pass-list.
fn write_green_list(path: &Path, green: &BTreeSet<String>) {
    if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
        std::fs::create_dir_all(parent).unwrap_or_else(|e| {
            panic!(
                "failed to create the LEANR_SWEEP_GREEN_OUT parent dir ({}): {e}",
                parent.display()
            )
        });
    }
    let mut out = String::new();
    for f in green {
        out.push_str(f);
        out.push('\n');
    }
    std::fs::write(path, out).unwrap_or_else(|e| {
        panic!(
            "failed to write the green list to LEANR_SWEEP_GREEN_OUT ({}): {e}",
            path.display()
        )
    });
}

/// Union every `*.txt` green list in `dir`, returning `(union, sources)`.
///
/// An empty or unreadable directory is a hard error: merge mode rewrites the
/// pass-list from this union, so an empty union would gate every committed
/// entry as a regression (or, if every one of them happened to be gone from
/// disk, reconcile the entire baseline away) — the exact partial-merge
/// failure the CI job's artifact-count assertion also guards against, pinned
/// here too so the guarantee does not live only in YAML.
fn read_shard_green_lists(dir: &Path) -> (BTreeSet<String>, Vec<PathBuf>) {
    let rd = std::fs::read_dir(dir).unwrap_or_else(|e| {
        panic!(
            "LEANR_SWEEP_MERGE directory ({}) is not readable: {e}",
            dir.display()
        )
    });
    let mut sources: Vec<PathBuf> = rd
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_file() && p.extension().is_some_and(|x| x == "txt"))
        .collect();
    sources.sort();
    assert!(
        !sources.is_empty(),
        "no *.txt shard green lists found in the LEANR_SWEEP_MERGE directory ({}) — refusing to \
         merge an empty union, which would gate every committed pass-list entry as a regression",
        dir.display()
    );
    let mut union = BTreeSet::new();
    for src in &sources {
        let text = std::fs::read_to_string(src)
            .unwrap_or_else(|e| panic!("failed to read shard green list {}: {e}", src.display()));
        union.extend(
            text.lines()
                .map(str::trim)
                .filter(|l| !l.is_empty() && !l.starts_with('#'))
                .map(String::from),
        );
    }
    (union, sources)
}

/// The property that makes the sharded nightly's merge sound: the shards
/// PARTITION the import-set list — every set lands in exactly one shard, and
/// their union is the unsharded list. If this ever failed, a dropped set
/// would surface as phantom regressions in the merge (its files missing from
/// the union) and a duplicated one would waste a shard's budget.
#[test]
fn shard_slices_partition_the_import_set_list() {
    let items: Vec<usize> = (0..97).collect();
    for n in 1..=13usize {
        let mut seen: Vec<usize> = Vec::new();
        for i in 1..=n {
            let slice = shard_slice(&items, i, n);
            // Stride shards differ in length by at most one — the load
            // balance the striding exists to provide.
            assert!(
                slice.len().abs_diff(items.len() / n) <= 1,
                "shard {i}/{n} is unbalanced: {} of {}",
                slice.len(),
                items.len()
            );
            seen.extend(slice);
        }
        let mut sorted = seen.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(
            sorted.len(),
            seen.len(),
            "N={n}: a set landed in more than one shard"
        );
        assert_eq!(sorted, items, "N={n}: the union of all shards lost a set");
    }
}

#[test]
fn shard_spec_parsing_rejects_malformed_values_with_a_reason() {
    assert_eq!(parse_shard_spec("1/12"), Ok((1, 12)));
    assert_eq!(parse_shard_spec("12/12"), Ok((12, 12)));
    assert_eq!(parse_shard_spec(" 3 / 12 "), Ok((3, 12)));
    for bad in [
        "12", "", "a/12", "1/b", "0/12", "13/12", "1/0", "-1/12", "1/2/3",
    ] {
        assert!(
            parse_shard_spec(bad).is_err(),
            "{bad:?} must be rejected, not silently accepted"
        );
    }
}

#[test]
fn merged_green_lists_union_shard_outputs() {
    let dir = std::env::temp_dir().join(format!(
        "leanr-sweep-merge-test-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();

    let a: BTreeSet<String> = ["Mathlib/B.lean", "Mathlib/A.lean"]
        .iter()
        .map(|s| (*s).to_string())
        .collect();
    let b: BTreeSet<String> = ["Mathlib/C.lean", "Mathlib/A.lean"]
        .iter()
        .map(|s| (*s).to_string())
        .collect();
    write_green_list(&dir.join("shard-1.txt"), &a);
    write_green_list(&dir.join("shard-2.txt"), &b);
    // A non-.txt file in the artifact dir must be ignored, not merged.
    std::fs::write(dir.join("notes.md"), "Mathlib/NotGreen.lean\n").unwrap();

    let (union, sources) = read_shard_green_lists(&dir);
    assert_eq!(sources.len(), 2, "only the *.txt green lists count");
    assert_eq!(
        union.into_iter().collect::<Vec<_>>(),
        vec!["Mathlib/A.lean", "Mathlib/B.lean", "Mathlib/C.lean"],
        "the union must be deduplicated and sorted"
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
