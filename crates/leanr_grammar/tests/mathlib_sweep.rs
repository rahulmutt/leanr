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
    // All mode flags are read up front so the mutual-exclusion assertions
    // below fire before any expensive work — and, critically, before
    // anything can write the pass-list.
    let passlist_only = std::env::var("LEANR_SWEEP_PASSLIST_ONLY").as_deref() == Ok("1");
    let passlist_update = std::env::var("LEANR_PASSLIST_UPDATE").as_deref() == Ok("1");
    let shard_raw = non_empty_env("LEANR_SWEEP_SHARD");
    let green_out = non_empty_env("LEANR_SWEEP_GREEN_OUT").map(PathBuf::from);
    let manifest_out = non_empty_env("LEANR_SWEEP_MANIFEST_OUT").map(PathBuf::from);
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
    // The manifest is not optional bookkeeping: it is the ONLY evidence merge
    // mode has that a pass-list entry still exists upstream (merge runs
    // without a Mathlib tree, and `.lake/packages/` — where most pass-list
    // entries live — is materialized by lake, not committed to mathlib4's
    // git tree, so a filesystem test there would classify every true
    // regression as an upstream deletion). A shard that emitted a green list
    // but no manifest would contribute its green files while contributing no
    // evidence about its slice's pass-list entries.
    assert!(
        !(shard_raw.is_some() && manifest_out.is_none()),
        "LEANR_SWEEP_SHARD requires LEANR_SWEEP_MANIFEST_OUT=<path>: the merge job takes its \
         existence set from the UNION of the shards' manifests (it has no Mathlib tree of its \
         own), so a shard without a manifest would make its slice's pass-list entries look \
         upstream-deleted and silently absorb any real regression among them."
    );
    assert!(
        !(shard_raw.is_none() && manifest_out.is_some()),
        "LEANR_SWEEP_MANIFEST_OUT without LEANR_SWEEP_SHARD is rejected: a manifest is a shard's \
         receipt (its spec, the pass-list entries it observed on disk, and how much it swept), \
         and only shard mode can honestly produce one."
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
    // dispatched here, before LEANR_MATHLIB_DIR/LEANR_OLEAN_PATH/the oracle
    // githash are required, since none of them is needed to union text files.
    //
    // Merge deliberately has NO Mathlib tree: its "does this pass-list entry
    // still exist upstream?" oracle is the union of the shards' manifests,
    // not the local filesystem. A filesystem test here was actively wrong —
    // the merge job checks out mathlib4's git tree, which does not contain
    // `.lake/packages/` (lake materializes it), so every pass-list entry
    // under a package would test as absent, and every true parse regression
    // among them would be reconciled away as an "upstream deletion" while
    // the run reported zero regressions.
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
        let manifests = read_shard_manifests(dir);
        let present = validate_shard_manifests(&manifests, &committed)
            .unwrap_or_else(|e| panic!("shard manifests in {} are unusable: {e}", dir.display()));
        eprintln!(
            "[merge] {} shard manifest(s), {} import set(s) and {} file(s) swept in total, {} of \
             {} committed pass-list entries observed present on some shard's disk",
            manifests.len(),
            manifests.iter().map(|m| m.import_sets_swept).sum::<usize>(),
            manifests.iter().map(|m| m.files_swept).sum::<usize>(),
            committed.iter().filter(|f| present.contains(*f)).count(),
            committed.len(),
        );
        let exists = |rel: &str| present.contains(rel);
        let before = committed.len();
        let newly_green = gate_and_maybe_rewrite(GateInput {
            exists: &exists,
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

    // Every SWEEPING mode needs the tree on disk (merge, handled above, does
    // not): to walk the corpus, to read the files it parses, and — for the
    // reconcile step and for a shard's manifest — to observe which pass-list
    // entries still exist.
    let mathlib = PathBuf::from(std::env::var("LEANR_MATHLIB_DIR").expect(
        "LEANR_MATHLIB_DIR is required in every sweeping mode: it is the corpus root, and the \
         reconcile step tests each not-green pass-list entry for existence under it to separate \
         upstream-deleted files from true parse regressions",
    ));

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
    // An empty LEANR_OLEAN_PATH is the cheapest way to make a sweep vacuous:
    // `roots` filters to `[]`, every `load_closure` fails, and the run
    // reports "0 green" and exits 0 — which, in shard mode, is a perfectly
    // well-formed (empty) green list that satisfies the workflow's
    // `if-no-files-found: error` and its artifact count check alike. The
    // mise tasks build this value in `sh -c` without `set -e`, so a failing
    // `lake env printenv LEAN_PATH` substitutes in as "". Fail at the source
    // instead of three jobs later.
    assert!(
        !roots.is_empty(),
        "LEANR_OLEAN_PATH resolved to no search roots ({lean_path:?}) — every olean closure would \
         fail to load and the sweep would report 0 green as a PASS. Check that `lake env printenv \
         LEAN_PATH` succeeds in .mathlib (mise run mathlib:fetch)."
    );
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
    // A shard whose slice came out empty even though there was work to deal
    // out never sweeps anything, and an empty green list is indistinguishable
    // from "this whole slice regressed" once it reaches the merge. The merge
    // rejects such a manifest too, but failing here names the shard that is
    // actually broken instead of reporting it three jobs later. `n` above
    // `by_imports.len()` is the one legitimate way to get an empty slice
    // (more shards than import sets — only reachable under a smoke-run
    // LEANR_SWEEP_LIMIT).
    if let Some((i, n)) = shard {
        assert!(
            !import_sets.is_empty() || by_imports.len() < n,
            "shard {i}/{n} swept 0 of {} import sets: its slice is empty even though there are at \
             least {n} sets to deal out. It would emit an empty green list that the merge cannot \
             tell from a mass regression.",
            by_imports.len()
        );
    }
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
        // The shard's receipt for the merge job. The `present` set is the
        // half the merge cannot compute for itself: only a shard has the
        // materialized tree (including `.lake/packages/`, which is not in
        // mathlib4's git tree) to answer "does this pass-list entry still
        // exist upstream?". Every shard observes the SAME tree, so any one
        // of them could answer it — the merge takes the union so that the
        // answer survives as long as at least one shard reported.
        let present: BTreeSet<String> = committed
            .iter()
            .filter(|rel| mathlib.join(rel).is_file())
            .cloned()
            .collect();
        let manifest = ShardManifest {
            shard: i,
            shard_count: n,
            import_sets_swept: import_sets.len(),
            files_swept,
            present,
        };
        if let Some(path) = &manifest_out {
            write_shard_manifest(path, &manifest);
        }
        eprintln!(
            "sweep[shard {i}/{n}]: {} of {} import sets, {files_swept} files, {} green, {} of {} \
             pass-list entries present on disk (no gate: the merge job gates the union)",
            import_sets.len(),
            by_imports.len(),
            green.len(),
            manifest.present.len(),
            committed.len(),
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
    let exists = |rel: &str| mathlib.join(rel).is_file();
    gate_and_maybe_rewrite(GateInput {
        exists: &exists,
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
    /// "Does this pass-list entry still exist upstream?" — a filesystem test
    /// under `.mathlib` in every sweeping mode, and the union of the shards'
    /// manifests in merge mode, which has no tree of its own. Injected rather
    /// than hardcoded to `Path::is_file` precisely because merge must NOT
    /// consult its own filesystem: it checks out mathlib4's git tree, which
    /// omits the lake-materialized `.lake/packages/` where most pass-list
    /// entries live, so every regression there would be absorbed as an
    /// upstream deletion.
    exists: &'a dyn Fn(&str) -> bool,
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
        exists,
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
        let (missing, true_regressions) = split_missing_from_regressions(exists, not_green);
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
/// regression) by asking `exists` about each relative path. Pulled out of
/// `mathlib_sweep_ratchet`'s update-mode branch so it's unit-testable without
/// `.mathlib`/LEANR_MATHLIB_DIR/the oracle — this split is the entire fix for
/// the update-path deadlock, so it earns its own cheap, always-run test.
///
/// `exists` is a parameter, not `mathlib.join(f).is_file()`, because merge
/// mode's answer does not come from a filesystem at all (see `GateInput`).
fn split_missing_from_regressions<'a>(
    exists: &dyn Fn(&str) -> bool,
    not_green: Vec<&'a String>,
) -> (Vec<&'a String>, Vec<&'a String>) {
    not_green.into_iter().partition(|f| !exists(f))
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

    let exists = |rel: &str| dir.join(rel).is_file();
    let (missing, true_regressions) = split_missing_from_regressions(&exists, not_green);

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

/// A shard's receipt, and the merge job's only source of truth about the
/// world outside its own checkout.
///
/// The merge job runs with no Mathlib tree: it cannot walk the corpus, and it
/// must not test the filesystem for pass-list entries (`.lake/packages/`,
/// where most of them live, is materialized by lake and absent from
/// mathlib4's git tree, so every entry there would read as upstream-deleted
/// and every real regression among them would be silently absorbed). Each
/// shard DOES have the full tree, so each one records what it saw; merge
/// takes the union and cross-checks the receipts against each other.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ShardManifest {
    /// 1-based shard index, and the N it was sharded against.
    shard: usize,
    shard_count: usize,
    /// How many import sets this shard's slice contained. Zero means the
    /// shard swept nothing at all — an empty green list that merge would
    /// otherwise read as "this entire slice regressed".
    import_sets_swept: usize,
    files_swept: usize,
    /// The committed pass-list entries this shard observed present on disk.
    present: BTreeSet<String>,
}

/// Line-oriented on purpose: this is a CI artifact a human reads in a failed
/// run's logs, and adding a serde dependency to a test binary to encode five
/// fields would be the wrong trade.
fn render_shard_manifest(m: &ShardManifest) -> String {
    let mut out = String::from(
        "# leanr shard manifest v1 — a shard's receipt for the merge job.\n\
         # Machine input for `mise run parse:mathlib:merge`; see mathlib_sweep.rs.\n",
    );
    out.push_str(&format!("shard {}/{}\n", m.shard, m.shard_count));
    out.push_str(&format!("import_sets_swept {}\n", m.import_sets_swept));
    out.push_str(&format!("files_swept {}\n", m.files_swept));
    for f in &m.present {
        out.push_str("present ");
        out.push_str(f);
        out.push('\n');
    }
    out
}

/// Parse a manifest, returning `Err(reason)` rather than defaulting anything:
/// a manifest that silently parsed as "0 import sets, no entries present"
/// would reintroduce exactly the failure it exists to prevent.
fn parse_shard_manifest(text: &str) -> Result<ShardManifest, String> {
    let mut shard: Option<(usize, usize)> = None;
    let mut import_sets_swept: Option<usize> = None;
    let mut files_swept: Option<usize> = None;
    let mut present = BTreeSet::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (key, value) = line
            .split_once(' ')
            .ok_or_else(|| format!("line {line:?} is not `<key> <value>`"))?;
        let value = value.trim();
        let once = |slot: &mut Option<usize>, what: &str| -> Result<(), String> {
            if slot.is_some() {
                return Err(format!("duplicate `{what}` line"));
            }
            *slot = Some(
                value
                    .parse::<usize>()
                    .map_err(|e| format!("`{what} {value:?}` is not a count: {e}"))?,
            );
            Ok(())
        };
        match key {
            "shard" => {
                if shard.is_some() {
                    return Err("duplicate `shard` line".to_string());
                }
                shard = Some(parse_shard_spec(value).map_err(|e| format!("`shard {value}`: {e}"))?);
            }
            "import_sets_swept" => once(&mut import_sets_swept, "import_sets_swept")?,
            "files_swept" => once(&mut files_swept, "files_swept")?,
            "present" => {
                present.insert(value.to_string());
            }
            other => return Err(format!("unknown key {other:?}")),
        }
    }
    let (shard, shard_count) = shard.ok_or("missing `shard I/N` line")?;
    Ok(ShardManifest {
        shard,
        shard_count,
        import_sets_swept: import_sets_swept.ok_or("missing `import_sets_swept` line")?,
        files_swept: files_swept.ok_or("missing `files_swept` line")?,
        present,
    })
}

fn write_shard_manifest(path: &Path, m: &ShardManifest) {
    if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
        std::fs::create_dir_all(parent).unwrap_or_else(|e| {
            panic!(
                "failed to create the LEANR_SWEEP_MANIFEST_OUT parent dir ({}): {e}",
                parent.display()
            )
        });
    }
    std::fs::write(path, render_shard_manifest(m)).unwrap_or_else(|e| {
        panic!(
            "failed to write the shard manifest to LEANR_SWEEP_MANIFEST_OUT ({}): {e}",
            path.display()
        )
    });
}

/// Read every `*.manifest` in `dir` (the same artifact directory the `*.txt`
/// green lists arrive in — distinct extensions so neither reader can eat the
/// other's files).
fn read_shard_manifests(dir: &Path) -> Vec<ShardManifest> {
    let rd = std::fs::read_dir(dir).unwrap_or_else(|e| {
        panic!(
            "LEANR_SWEEP_MERGE directory ({}) is not readable: {e}",
            dir.display()
        )
    });
    let mut paths: Vec<PathBuf> = rd
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_file() && p.extension().is_some_and(|x| x == "manifest"))
        .collect();
    paths.sort();
    paths
        .iter()
        .map(|p| {
            let text = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("failed to read shard manifest {}: {e}", p.display()));
            parse_shard_manifest(&text)
                .unwrap_or_else(|e| panic!("shard manifest {} is malformed: {e}", p.display()))
        })
        .collect()
}

/// Validate the manifests as a SET and return the union of their `present`
/// entries — the existence oracle merge mode gates with.
///
/// Counting manifests is not enough. The set has to be exactly one manifest
/// per shard index `1..=N` for one agreed `N`, because "12 manifests" is also
/// what you get from shard 7 uploaded twice and shard 4 missing — and shard
/// 4's pass-list entries would then be absent from the union, i.e. classified
/// as upstream deletions and reconciled straight out of the baseline. The
/// two vacuity checks catch the other shape of the same bug: a shard that ran
/// but swept nothing (empty `LEANR_OLEAN_PATH`, empty slice) reports 0 green
/// and exits 0, which every count-based guard happily accepts.
///
/// `committed` (the actual pass-list) is threaded through for the very last
/// check below: without it, a manifest set where EVERY shard is blind is
/// internally consistent (every `present` is `{}`, which trivially equals
/// the `{}` union) and nothing here would catch it. That is not a corner
/// case — all 12 shard jobs run identical steps against one pinned Mathlib
/// SHA, so "one shard blind" is the unlikely, independent-fault shape and
/// "every shard blind" (a bad checkout step, a `mise run mathlib:fetch` that
/// silently no-op'd) is the likely, CORRELATED one. It is also exactly the
/// shape that shipped before this fix: a blind-everywhere manifest set used
/// to satisfy `present.is_empty() => exempt`, sail through gating (every
/// committed entry reads as "upstream deleted", never as a regression), and
/// reach the pass-list rewrite — stopped, in the incident this guards
/// against, only by the rewrite target being read-only.
fn validate_shard_manifests(
    manifests: &[ShardManifest],
    committed: &BTreeSet<String>,
) -> Result<BTreeSet<String>, String> {
    if manifests.is_empty() {
        return Err(
            "no *.manifest shard receipts found — refusing to merge without evidence of which \
             pass-list entries still exist upstream, since with none every entry would look \
             upstream-deleted and any real regression would be reconciled away"
                .to_string(),
        );
    }
    let n = manifests[0].shard_count;
    if let Some(m) = manifests.iter().find(|m| m.shard_count != n) {
        return Err(format!(
            "shards disagree on the shard count: shard {}/{} vs shard {}/{n} — these manifests \
             come from different sweeps and cannot be merged",
            m.shard, m.shard_count, manifests[0].shard
        ));
    }
    let indices: BTreeSet<usize> = manifests.iter().map(|m| m.shard).collect();
    if indices.len() != manifests.len() {
        let mut dupes: Vec<usize> = manifests.iter().map(|m| m.shard).collect();
        dupes.sort_unstable();
        return Err(format!(
            "duplicate shard manifests: got indices {dupes:?} for N={n}. A repeated shard hides a \
             missing one, whose pass-list entries would then be absent from the union and \
             reconciled out of the baseline as upstream deletions."
        ));
    }
    let expected: BTreeSet<usize> = (1..=n).collect();
    if indices != expected {
        let missing: Vec<usize> = expected.difference(&indices).copied().collect();
        let unexpected: Vec<usize> = indices.difference(&expected).copied().collect();
        return Err(format!(
            "shard manifests are not exactly 1..={n}: missing {missing:?}, unexpected \
             {unexpected:?}. Every pass-list entry only a missing shard could vouch for would \
             look upstream-deleted, so its regression would be silently absorbed. Re-run the \
             failed shard(s)."
        ));
    }
    if let Some(m) = manifests.iter().find(|m| m.import_sets_swept == 0) {
        return Err(format!(
            "shard {}/{n} swept 0 import sets — it produced a vacuously empty green list (an \
             empty LEANR_OLEAN_PATH or an empty slice does exactly this while still exiting 0), \
             and merging it would read its whole slice as a mass regression",
            m.shard
        ));
    }
    let present: BTreeSet<String> = manifests
        .iter()
        .flat_map(|m| m.present.iter().cloned())
        .collect();
    // Every shard checks out the SAME Mathlib tree (including
    // `.lake/packages/`) and tests the SAME committed pass-list against it,
    // so under correct operation every shard's `present` IS the full set,
    // which is therefore identical to the union. Requiring merely that the
    // union be non-empty (the old check) only ever catches one shard being
    // blind while its siblings are not — but blindness here is correlated,
    // not independent, so the far likelier failure is several (or all)
    // shards agreeing on a wrong, incomplete view. Requiring every shard's
    // `present` to equal the union catches that whole family in one rule:
    // any shard whose disk view disagrees with the others', whether it saw
    // nothing or merely less, fails the merge.
    if let Some(m) = manifests.iter().find(|m| m.present != present) {
        return Err(format!(
            "shard {}/{n} observed {} committed pass-list entries on disk, but the union across \
             all shards is {} — every shard checks out the SAME Mathlib tree and tests the SAME \
             pass-list, so any shard whose observed-present set differs from the union has an \
             incomplete or stale view of it (a failed/partial fetch), and merging it would \
             silently absorb its blind spot's regressions as upstream deletions. Re-run the \
             disagreeing shard(s).",
            m.shard,
            m.present.len(),
            present.len()
        ));
    }
    // The one shape the equality check above cannot see: ALL shards blind
    // together. Every `present` is `{}`, so every `present` trivially equals
    // the `{}` union and the check above passes. But a non-empty `committed`
    // pass-list observed as wholly absent by every shard is not "the whole
    // pass-list was deleted upstream" (23 files vanishing from one pinned
    // Mathlib SHA in one nightly run) — it is correlated total blindness:
    // the shards ran without the Mathlib tree/oleans actually materialized
    // (e.g. a checkout or `mise run mathlib:fetch` step that silently
    // no-op'd before the sweep). Reconciling the pass-list against that would
    // drop every entry and rewrite the baseline out from under itself.
    if present.is_empty() && !committed.is_empty() {
        return Err(format!(
            "every one of the {} shard manifest(s) observed 0 of the {} committed pass-list \
             entries on disk — since all shards run identical steps against one pinned Mathlib \
             SHA, this is not {} independent coincidences but a single correlated cause, most \
             likely that the shards ran without the Mathlib tree/oleans actually materialized \
             (e.g. a checkout or `mise run mathlib:fetch` step silently no-op'd before the \
             sweep). Refusing to reconcile the entire pass-list away as upstream deletions.",
            manifests.len(),
            committed.len(),
            manifests.len()
        ));
    }
    Ok(present)
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

fn manifest_fixture(shard: usize, shard_count: usize, present: &[&str]) -> ShardManifest {
    ShardManifest {
        shard,
        shard_count,
        import_sets_swept: 685,
        files_swept: 737,
        present: present.iter().map(|s| (*s).to_string()).collect(),
    }
}

/// The manifest is written by one CI job and read by another, so the
/// round-trip through the artifact is load-bearing: a field that silently
/// failed to survive it (`present`, above all) would put the merge back to
/// classifying real regressions as upstream deletions.
#[test]
fn shard_manifest_round_trips_through_its_artifact_form() {
    let dir = std::env::temp_dir().join(format!(
        "leanr-sweep-manifest-test-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    let _ = std::fs::remove_dir_all(&dir);

    let m = manifest_fixture(
        3,
        12,
        &[
            ".lake/packages/batteries/Batteries/B.lean",
            "Mathlib/A.lean",
        ],
    );
    assert_eq!(
        parse_shard_manifest(&render_shard_manifest(&m)),
        Ok(m.clone())
    );

    // Through the filesystem, alongside a green list, exactly as the merge
    // job receives them: neither reader may eat the other's files.
    let path = dir.join("shard-3.manifest");
    write_shard_manifest(&path, &m);
    write_green_list(&dir.join("shard-3.txt"), &m.present);
    let read = read_shard_manifests(&dir);
    assert_eq!(
        read,
        vec![m.clone()],
        "the manifest must survive the artifact round-trip"
    );
    let (union, sources) = read_shard_green_lists(&dir);
    assert_eq!(
        sources.len(),
        1,
        "the *.manifest must not be read as a green list"
    );
    assert_eq!(union, m.present);

    // A manifest with an empty `present` set is legal on its own (that shard
    // simply saw no pass-list entry) — it is only rejected in company, by
    // validate_shard_manifests.
    let empty = manifest_fixture(1, 1, &[]);
    assert_eq!(
        parse_shard_manifest(&render_shard_manifest(&empty)),
        Ok(empty)
    );

    for bad in [
        "",                                                             // no shard line
        "shard 3/12\nfiles_swept 7\n",                                  // no import_sets_swept
        "shard 3/12\nimport_sets_swept 5\n",                            // no files_swept
        "shard 13/12\nimport_sets_swept 5\nfiles_swept 7\n",            // bad spec
        "shard 3/12\nshard 4/12\nimport_sets_swept 5\nfiles_swept 7\n", // duplicate
        "shard 3/12\nimport_sets_swept 5\nimport_sets_swept 6\nfiles_swept 7\n",
        "shard 3/12\nimport_sets_swept x\nfiles_swept 7\n", // not a count
        "shard 3/12\nimport_sets_swept 5\nfiles_swept 7\nbogus k\n", // unknown key
        "shard 3/12\nimport_sets_swept 5\nfiles_swept 7\nlonely\n", // not key/value
    ] {
        assert!(
            parse_shard_manifest(bad).is_err(),
            "{bad:?} must be rejected, not defaulted into a vacuous manifest"
        );
    }

    std::fs::remove_dir_all(&dir).unwrap();
}

/// The Critical this whole manifest mechanism exists for: merge must refuse
/// any receipt set that is not exactly one manifest per shard 1..=N. Counting
/// them is not enough — a duplicate covers for a missing shard, and the
/// missing shard's pass-list entries would then be reconciled out of the
/// baseline as "upstream deletions" while the run reports zero regressions.
///
/// This test's own focus is index validation (missing/duplicate/mismatched
/// shard count) — what each shard claims to have seen on disk is a separate
/// axis, covered by `shard_manifest_validation_rejects_correlated_partial_blindness`
/// and `shard_manifest_validation_rejects_a_vacuous_shard` below.
#[test]
fn shard_manifest_validation_requires_exactly_one_per_shard() {
    let committed: BTreeSet<String> = ["Mathlib/A.lean".to_string()].into_iter().collect();
    let full: Vec<ShardManifest> = (1..=4)
        .map(|i| manifest_fixture(i, 4, &["Mathlib/A.lean"]))
        .collect();
    assert_eq!(
        validate_shard_manifests(&full, &committed),
        Ok(["Mathlib/A.lean".to_string()].into_iter().collect())
    );

    let err = |ms: &[ShardManifest]| validate_shard_manifests(ms, &committed).unwrap_err();

    assert!(
        err(&[]).contains("no *.manifest"),
        "an empty receipt set must be rejected"
    );

    let mut missing = full.clone();
    missing.remove(2); // shard 3 never uploaded
    let e = err(&missing);
    assert!(
        e.contains("not exactly 1..=4") && e.contains("missing [3]"),
        "a missing shard must be named, got: {e}"
    );

    // Right COUNT, wrong SET: shard 2 twice, shard 3 absent. This is the case
    // a `find | wc -l` guard cannot see.
    let mut dup = full.clone();
    dup[2] = manifest_fixture(2, 4, &["Mathlib/A.lean"]);
    let e = err(&dup);
    assert_eq!(
        dup.len(),
        full.len(),
        "the duplicate case has the expected count"
    );
    assert!(e.contains("duplicate shard manifests"), "got: {e}");

    let mut mixed = full.clone();
    mixed[1] = manifest_fixture(2, 12, &["Mathlib/A.lean"]);
    assert!(
        err(&mixed).contains("disagree on the shard count"),
        "manifests from two different sweeps must not merge"
    );
}

/// Correlated PARTIAL blindness: every shard checks out the SAME tree and
/// tests the SAME pass-list, so under correct operation every shard's
/// `present` set is identical (and therefore equal to the union). If two
/// shards disagree — one's fetch step failed or only partially materialized
/// the tree — that disagreement is itself the evidence, whether the shapes
/// are disjoint (each vouches only for what it alone saw) or a strict
/// subset (one shard simply saw fewer entries than its agreeing siblings).
/// The OLD rule (`union non-empty => exempt`) didn't even look at this shape
/// and would have merged both of these as `Ok(union)`.
#[test]
fn shard_manifest_validation_rejects_correlated_partial_blindness() {
    let committed: BTreeSet<String> = [
        "Mathlib/A.lean".to_string(),
        "Mathlib/B.lean".to_string(),
        "Mathlib/C.lean".to_string(),
    ]
    .into_iter()
    .collect();

    // Disjoint views: two shards, each vouching only for what it uniquely
    // saw. The union (`{A, B}`) is non-empty, so the old check passed this
    // straight through as `Ok(union)`.
    let disjoint = vec![
        manifest_fixture(1, 2, &["Mathlib/A.lean"]),
        manifest_fixture(2, 2, &["Mathlib/B.lean"]),
    ];
    let e = validate_shard_manifests(&disjoint, &committed).unwrap_err();
    assert!(
        e.contains("shard 1/2") && e.contains("union across all shards is 2"),
        "disagreeing shards must be rejected, got: {e}"
    );

    // Strict-subset view: shard 2 sees only 2 of the 3 entries its (agreeing)
    // siblings see — not wholly blind, and not a disjoint split, just a
    // genuine partial miss.
    let subset = vec![
        manifest_fixture(
            1,
            3,
            &["Mathlib/A.lean", "Mathlib/B.lean", "Mathlib/C.lean"],
        ),
        manifest_fixture(2, 3, &["Mathlib/A.lean", "Mathlib/B.lean"]),
        manifest_fixture(
            3,
            3,
            &["Mathlib/A.lean", "Mathlib/B.lean", "Mathlib/C.lean"],
        ),
    ];
    let e = validate_shard_manifests(&subset, &committed).unwrap_err();
    assert!(
        e.contains("shard 2/3") && e.contains("2 committed pass-list entries"),
        "a shard that saw fewer entries than its siblings must be named, got: {e}"
    );
}

/// Important 2: a shard that ran, swept nothing, and exited 0 satisfies every
/// count-based guard. Its receipt is where it becomes visible.
#[test]
fn shard_manifest_validation_rejects_a_vacuous_shard() {
    let committed: BTreeSet<String> = ["Mathlib/A.lean".to_string()].into_iter().collect();

    let mut vacuous = vec![
        manifest_fixture(1, 2, &["Mathlib/A.lean"]),
        manifest_fixture(2, 2, &["Mathlib/A.lean"]),
    ];
    vacuous[1].import_sets_swept = 0; // e.g. LEANR_OLEAN_PATH substituted in empty
    let e = validate_shard_manifests(&vacuous, &committed).unwrap_err();
    assert!(
        e.contains("shard 2/2 swept 0 import sets"),
        "a shard that swept nothing must fail the merge loudly, got: {e}"
    );

    // One shard blind while its sibling isn't: a disagreement, caught by the
    // every-shard-equals-the-union check (see
    // shard_manifest_validation_rejects_correlated_partial_blindness).
    let one_blind = vec![
        manifest_fixture(1, 2, &["Mathlib/A.lean"]),
        manifest_fixture(2, 2, &[]),
    ];
    let e = validate_shard_manifests(&one_blind, &committed).unwrap_err();
    assert!(
        e.contains("shard 2/2 observed 0 committed pass-list entries"),
        "a shard blind to the tree must fail the merge loudly, got: {e}"
    );

    // The Critical this re-review is for: EVERY shard blind TOGETHER. The
    // every-shard-equals-the-union check above cannot see this on its own —
    // every `present` is `{}`, which trivially equals the `{}` union — so it
    // takes the separate committed-non-empty-but-union-empty check. This
    // manifest set is exactly what shipped before this fix: the old
    // `present.is_empty() => exempt` rule let it through as
    // `Ok(BTreeSet::new())`, every committed pass-list entry was then
    // classified "upstream deleted" rather than regressed (0 regressions
    // reported), and the run proceeded to rewrite the pass-list.
    let all_blind = vec![manifest_fixture(1, 2, &[]), manifest_fixture(2, 2, &[])];
    let e = validate_shard_manifests(&all_blind, &committed).unwrap_err();
    assert!(
        e.contains("every one of the 2 shard manifest(s)")
            && e.contains("0 of the 1 committed pass-list entries")
            && e.contains("mathlib:fetch"),
        "correlated total blindness must fail the merge loudly and name the likely cause, got: {e}"
    );

    // But a pass-list that is genuinely empty everywhere is not a shard
    // fault, and must not be reported as one: with nothing committed, "every
    // shard saw nothing" is simply true, not evidence of a broken fetch.
    assert_eq!(
        validate_shard_manifests(&all_blind, &BTreeSet::new()),
        Ok(BTreeSet::new())
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
