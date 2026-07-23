//! Nightly Mathlib SYNTHESIS discovery sweep + synth-pass-list ratchet
//! (M4a plan-4 spec, PR-C task C2). The leanr side of the tier-2 nightly:
//! it shards the pinned Mathlib environment's constants (by the SAME sort
//! key + stride as the C1 oracle metaprogram,
//! `tests/fixtures/meta/dump_synth_mathlib.lean`), runs leanr's
//! `synth_instance` on every query C1 mined for each constant, diffs the
//! verdict AND the canonical instance term against C1's oracle JSONL,
//! computes the green constant set, and — in merge/update mode — ratchets
//! `tests/fixtures/meta/synth-passlist.txt` keyed by fully-qualified
//! constant name.
//!
//! STRUCTURE is transcribed VERBATIM from
//! `crates/leanr_grammar/tests/mathlib_sweep.rs` (the proven parse-sweep
//! precedent): the same mode/shard/gate/manifest/merge machinery, the same
//! up-front mutual-exclusion asserts, the same gate-BEFORE-rewrite
//! `assert!(regressions.is_empty())`, the same upstream-deletion reconcile
//! (`split_missing_from_regressions`), and the same shard-manifest set
//! validation (`validate_shard_manifests`). Three deltas, per the C2 brief:
//!   (a) the UNIT OF WORK is the CONSTANT (a `Vec<(rendered-name, NameId)>`
//!       sorted by rendered name), sharded by the same `idx % n == i-1`
//!       stride helper (`shard_slice`);
//!   (b) each shard does ONE `load_closure` over the whole pinned target
//!       set (the `check_sweep.rs` pattern) so every shard's environment —
//!       and thus its constant list — is identical, which is exactly what
//!       `validate_shard_manifests`'s "every `present` equals the union"
//!       invariant relies on;
//!   (c) "green" per constant = EVERY mined query for it agrees with the
//!       oracle record on BOTH the verdict and (when ok) the canonical
//!       term.
//!
//! The full sweep (`synth_sweep_ratchet`) is `#[ignore]`d — it needs the
//! pinned Mathlib `.olean` closure and a C1 oracle dump, and runs at
//! Mathlib scale (C1 confirmed ~931k constants/shard). CI only BUILDS it;
//! the pure helpers below (`shard_slice`, `parse_shard_spec`,
//! `constant_is_green`, `query_agrees`, `parse_oracle_shard`,
//! `split_missing_from_regressions`, `validate_shard_manifests`, the
//! manifest/green-list round-trips) are what CI actually exercises.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{Environment, Name};
use leanr_meta::{Config, MetaCtx};
use leanr_olean::{
    load_closure, DefaultInstanceEntry, InstanceEntry, MatcherEntry, ProjectionFnInfo,
    ReducibilityEntry, SearchPath,
};
use serde_json::{json, Value};

mod support;
use support::{decode_expr, encode_expr, EncSt};

fn passlist_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/meta/synth-passlist.txt")
}

// ===== the pinned Mathlib module set =====
//
// MUST match `dump_synth_mathlib.lean`'s `pinnedModules` EXACTLY — C1 and
// C2 sort+stride the SAME environment, and the environment is exactly the
// import closure of this list. If the two lists ever diverge, C2 shards a
// different constant set than C1 dumped and every shard silently diffs
// against the wrong records. Transcribed verbatim (fix any drift by
// re-reading that file's `pinnedModules`).
fn pinned_modules() -> &'static [&'static str] {
    &[
        "Mathlib.Algebra.Group.Defs",
        "Mathlib.Algebra.Group.Basic",
        "Mathlib.Algebra.Group.Subgroup.Defs",
        "Mathlib.Algebra.Order.Group.Defs",
        "Mathlib.Algebra.Order.Ring.Defs",
        "Mathlib.Algebra.Ring.Defs",
        "Mathlib.Algebra.Field.Defs",
        "Mathlib.Algebra.Field.Basic",
        "Mathlib.Data.Nat.Basic",
        "Mathlib.Data.Int.Basic",
        "Mathlib.Data.Rat.Defs",
        "Mathlib.Data.Real.Basic",
        "Mathlib.Order.Basic",
        "Mathlib.Order.Lattice",
        "Mathlib.Topology.Basic",
        "Mathlib.Topology.MetricSpace.Basic",
        "Mathlib.LinearAlgebra.Finsupp.Span",
        "Mathlib.Analysis.SpecialFunctions.Pow.Real",
        "Mathlib.CategoryTheory.Category.Basic",
        "Mathlib.RingTheory.Ideal.Basic",
    ]
}

// ===== the oracle corpus (C1's per-shard JSONL) =====

/// One decoded C1 oracle record. Field shapes per
/// `dump_synth_mathlib.lean`'s RECORD SCHEMA: an ordinary record has
/// `const`/`id`/`src`/`goal`/`ok`/`val?`/`near_budget`; a per-query `exc`
/// record has `const`/`id`/`src`/`goal`/`exc` (no `ok`/`val`); a
/// constant-level `exc` record has `const`/`id`/`src:"const"`/`exc` (no
/// `goal`). Both `exc` shapes and any `near_budget` record are EXCLUDED
/// from the gate — see `is_comparable`.
#[derive(Debug, Clone, PartialEq)]
struct OracleRecord {
    const_name: String,
    id: String,
    src: String,
    /// `Value::Null` for a constant-level `exc` record (which carries no
    /// goal); the real goal expr otherwise.
    goal: Value,
    ok: Option<bool>,
    val: Option<Value>,
    near_budget: bool,
    /// `Some(msg)` iff this is an `exc` record (the oracle itself did not
    /// answer cleanly) — never compared, exactly as `oracle_synth.rs`
    /// skips `q:"exc"`.
    exc: Option<String>,
}

impl OracleRecord {
    fn from_json(v: &Value) -> Result<OracleRecord, String> {
        let const_name = v["const"]
            .as_str()
            .ok_or("record missing `const`")?
            .to_string();
        let id = v["id"].as_str().ok_or("record missing `id`")?.to_string();
        Ok(OracleRecord {
            const_name,
            id,
            src: v["src"].as_str().unwrap_or("").to_string(),
            goal: v.get("goal").cloned().unwrap_or(Value::Null),
            ok: v.get("ok").and_then(Value::as_bool),
            val: v.get("val").cloned(),
            near_budget: v
                .get("near_budget")
                .and_then(Value::as_bool)
                .unwrap_or(false),
            exc: v.get("exc").and_then(Value::as_str).map(str::to_string),
        })
    }

    /// A record participates in the green gate iff the oracle answered it
    /// cleanly (`ok` present, no `exc`) and it is not near the oracle's own
    /// heartbeat budget (determinism constraint — its verdict could flip on
    /// an unrelated performance change). Mirrors `oracle_synth.rs`'s
    /// `exc`/`near_budget` skips exactly.
    fn is_comparable(&self) -> bool {
        self.exc.is_none() && !self.near_budget && self.ok.is_some()
    }
}

/// Parse one shard's oracle JSONL and, CRITICALLY, verify it ran to
/// COMPLETION. C1 terminates every complete shard with a sentinel line
/// (`{"sentinel":true,"shard":"I/N","records":N}`, no `const`/`id`) whose
/// `records` is the count of every JSONL line written before it. A
/// truncated shard (crashed/killed mid-run, disk full) simply lacks the
/// sentinel — indistinguishable from a genuinely-complete run by grepping
/// the JSONL, which is the whole reason C1 writes it. C2 MUST refuse to
/// gate against a partial corpus (it would treat every missing query as a
/// regression, or drop constants silently), so a missing sentinel, a
/// `records` count that disagrees with the actual non-sentinel line count,
/// or a sentinel that is not the LAST line is a hard error here.
///
/// `expected_shard` (`Some("I/N")` in shard mode) cross-checks the
/// sentinel's own `shard` field so feeding the wrong shard's oracle to
/// this shard fails loudly rather than diffing against the wrong slice.
fn parse_oracle_shard(
    text: &str,
    expected_shard: Option<&str>,
) -> Result<Vec<OracleRecord>, String> {
    let lines: Vec<&str> = text
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    let mut records = Vec::new();
    let mut sentinel: Option<(String, usize)> = None;
    let mut sentinel_idx: Option<usize> = None;
    for (i, line) in lines.iter().enumerate() {
        let v: Value =
            serde_json::from_str(line).map_err(|e| format!("line {}: invalid JSON: {e}", i + 1))?;
        if v.get("sentinel").and_then(Value::as_bool) == Some(true) {
            if sentinel.is_some() {
                return Err("more than one sentinel line — corrupt/concatenated oracle".to_string());
            }
            let shard = v["shard"]
                .as_str()
                .ok_or("sentinel line missing `shard`")?
                .to_string();
            let n = v["records"]
                .as_u64()
                .ok_or("sentinel line missing/bad `records`")? as usize;
            sentinel = Some((shard, n));
            sentinel_idx = Some(i);
        } else {
            records.push(OracleRecord::from_json(&v).map_err(|e| format!("line {}: {e}", i + 1))?);
        }
    }
    let (shard, declared) = sentinel.ok_or_else(|| {
        "oracle JSONL has NO completion sentinel line — the C1 shard was TRUNCATED (crashed/killed \
         mid-run, disk full); refusing to diff leanr against a partial corpus, which would report \
         every un-dumped query as a regression"
            .to_string()
    })?;
    // The sentinel is the LAST line of a complete file; anything after it
    // means the file was concatenated or corrupted.
    if sentinel_idx != Some(lines.len() - 1) {
        return Err(
            "oracle sentinel is not the last line — the file continues past it \
             (corrupt/concatenated); refusing to gate"
                .to_string(),
        );
    }
    if declared != records.len() {
        return Err(format!(
            "oracle sentinel declares {declared} records but {} non-sentinel lines are present — \
             the C1 shard was TRUNCATED; refusing to gate against a partial corpus",
            records.len()
        ));
    }
    if let Some(exp) = expected_shard {
        if shard != exp {
            return Err(format!(
                "oracle sentinel shard {shard:?} != this run's shard {exp:?} — wrong oracle file \
                 for this shard; refusing to diff against the wrong slice"
            ));
        }
    }
    Ok(records)
}

// ===== the per-constant green diff (delta (c)) =====

/// leanr's answer for ONE mined query, reduced to exactly what the gate
/// compares against the oracle record. `Synth` carries the canonical
/// (encoded) instance term, so a wrong-but-existing instance is caught,
/// not just a wrong verdict — the same non-verdict-only discipline
/// `oracle_synth.rs` documents.
#[derive(Debug, Clone, PartialEq)]
enum LeanrAns {
    /// leanr synthesized an instance; the canonical JSON encoding of the term.
    Synth(Value),
    /// leanr found no instance (`Ok(None)`).
    NoInstance,
    /// leanr itself errored (a `MetaError`) — always a divergence, since the
    /// oracle answered this record cleanly (a comparable record has `ok`).
    Errored,
    /// The decoded goal, re-encoded under a fresh `EncSt`, did NOT
    /// round-trip to the record's committed `goal` JSON (the
    /// `oracle_synth.rs:250-258` check). This means the SAME `EncSt` that
    /// numbered the goal — and that `Synth`'s term would have been encoded
    /// under — has already diverged from the oracle dumper's own
    /// numbering, so trusting a `val` comparison made under it "could
    /// silently agree for the wrong reason" (`oracle_synth.rs`'s own
    /// words). `query_agrees` never agrees with this variant (it falls
    /// through the same wildcard `Errored` does), so a constant that hits
    /// this is reported not-green rather than gated on an untrustworthy
    /// `val` — a phantom non-green, not a hidden real regression. Carries
    /// both sides so the sweep's log line can show the actual mismatch.
    GoalMismatch { got: Value, want: Value },
}

/// Does leanr's answer for ONE comparable oracle record agree with it?
/// `ok:true` demands leanr `Synth`esize the SAME canonical term; `ok:false`
/// demands leanr find `NoInstance`; a leanr error never agrees. `exc`/
/// `near_budget` records must be filtered out by the caller before reaching
/// here (their `ok` is `None`, which this treats as non-agreeing so a
/// mis-filtered record fails loudly rather than passing vacuously).
/// `GoalMismatch` also never agrees (falls through the same wildcards as
/// `Errored`) — see its doc comment on `LeanrAns`: comparing `val` at all
/// under a numbering that failed to round-trip is exactly what must NOT
/// happen, so this variant is deliberately never routed into the `Synth`
/// arm below.
fn query_agrees(oracle: &OracleRecord, got: &LeanrAns) -> bool {
    match oracle.ok {
        Some(true) => match got {
            LeanrAns::Synth(v) => oracle.val.as_ref() == Some(v),
            _ => false,
        },
        Some(false) => matches!(got, LeanrAns::NoInstance),
        None => false,
    }
}

/// A constant is GREEN iff it has AT LEAST ONE comparable mined query and
/// EVERY comparable query agrees with the oracle (verdict + canonical
/// term). A single divergence — or a comparable oracle query with no
/// matching leanr answer — makes it not green.
///
/// The `>= 1 comparable query` requirement is DELIBERATE and flagged (it is
/// the one clarification of the brief's "every mined query agrees", which
/// read purely universally would make every constant with no query
/// vacuously green and balloon the ratcheted pass-list to the entire
/// ~931k-constant environment — a discovery sweep must ratchet only
/// constants that produced a positive synthesis signal). A constant whose
/// queries are all `exc`/`near_budget` therefore is NOT green: it carries
/// no comparable evidence this run.
fn constant_is_green(_const: &str, oracle: &[OracleRecord], leanr: &[(String, LeanrAns)]) -> bool {
    let ans_by_id: HashMap<&str, &LeanrAns> =
        leanr.iter().map(|(id, a)| (id.as_str(), a)).collect();
    let mut compared = 0usize;
    for rec in oracle {
        if !rec.is_comparable() {
            continue;
        }
        // A comparable oracle query with no matching leanr answer is a
        // divergence, not a skip — the leanr side failed to answer a query
        // the oracle answered cleanly.
        let Some(got) = ans_by_id.get(rec.id.as_str()) else {
            return false;
        };
        compared += 1;
        if !query_agrees(rec, got) {
            return false;
        }
    }
    // Green requires positive evidence: at least one comparable query, all
    // agreeing (see the doc comment for why the vacuous case is excluded).
    compared > 0
}

// ===== the leanr synthesis run for one query =====

/// Run leanr's `synth_instance` on one mined goal, fresh `MetaCtx` seeded on
/// a fresh scratch `Store` (the `oracle_synth.rs` precedent: queries must be
/// independent — synthesis has its own table/answer cache — so no state
/// leaks between them). The mined goal is closed w.r.t. bvars AND mvars by
/// C1's construction (`dump_synth_mathlib.lean`, MINING ALGORITHM + FATAL
/// GUARDS), so — unlike `oracle_synth.rs` — there are no goal mvars to
/// declare. The `EncSt` is seeded by encoding `goal` first, and — matching
/// `oracle_synth.rs:250-258`'s idiom exactly — that re-encoding MUST
/// round-trip to the committed `goal_json` before the answer is encoded
/// under the same `est`; a re-encoding that disagrees means `est`'s
/// numbering has already diverged from the oracle dumper's, and comparing
/// `val` under it "could silently agree for the wrong reason"
/// (`oracle_synth.rs`'s own comment). `oracle_synth.rs` is a single
/// hand-curated differential test, so it can afford to `assert!`
/// (via its `failures` vec + a final assert) and fail the whole run; this
/// is a Mathlib-scale nightly sweep over ~931k constants, where one bad
/// record must not abort the shard, so a mismatch here is returned as
/// `LeanrAns::GoalMismatch` — a divergence for THIS query/constant, loudly
/// logged by the caller, but not a panic.
#[allow(clippy::too_many_arguments)]
fn run_leanr_query(
    env: &Environment,
    reducibility: &[ReducibilityEntry],
    matchers: &[MatcherEntry],
    instances: &[InstanceEntry],
    default_instances: &[DefaultInstanceEntry],
    projection_fns: &[ProjectionFnInfo],
    goal_json: &Value,
) -> LeanrAns {
    let view = env.view();
    let base = Some(view.store);
    let mut scratch = Store::scratch();
    let mut fv = HashMap::new();
    let mut mv: HashMap<u64, NameId> = HashMap::new();
    let goal = decode_expr(&mut scratch, base, goal_json, &mut fv, &mut mv);
    let mut ctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
    );
    let synthd: Result<Option<leanr_kernel::bank::ExprId>, ()> = match ctx.synth_instance(goal) {
        Ok(Some(v)) => match ctx.instantiate_mvars(v) {
            Ok(v) => Ok(Some(v)),
            Err(_) => Err(()),
        },
        Ok(None) => Ok(None),
        Err(_) => Err(()),
    };
    drop(ctx);
    match synthd {
        Err(()) => LeanrAns::Errored,
        Ok(None) => LeanrAns::NoInstance,
        Ok(Some(v)) => {
            let mut est = EncSt::default();
            let seed = encode_expr(&scratch, base, goal, &mut est);
            if seed != *goal_json {
                return LeanrAns::GoalMismatch {
                    got: seed,
                    want: goal_json.clone(),
                };
            }
            LeanrAns::Synth(encode_expr(&scratch, base, v, &mut est))
        }
    }
}

// ===== the #[ignore]d full sweep =====

#[test]
#[ignore = "needs the pinned Mathlib .olean closure (LEANR_OLEAN_PATH) and a C1 oracle dump \
            (LEANR_SYNTH_ORACLE); Mathlib-scale, nightly-only. Built by CI, never run there."]
fn synth_sweep_ratchet() {
    // All mode flags read up front so the mutual-exclusion asserts fire
    // before any expensive work and, critically, before anything can write
    // the pass-list. Mirrors `mathlib_sweep.rs` exactly, LEANR_SYNTH_*
    // substituted for LEANR_SWEEP_*.
    let passlist_only = std::env::var("LEANR_SYNTH_PASSLIST_ONLY").as_deref() == Ok("1");
    let passlist_update = std::env::var("LEANR_SYNTH_PASSLIST_UPDATE").as_deref() == Ok("1");
    let shard_raw = non_empty_env("LEANR_SYNTH_SHARD");
    let green_out = non_empty_env("LEANR_SYNTH_GREEN_OUT").map(PathBuf::from);
    let manifest_out = non_empty_env("LEANR_SYNTH_MANIFEST_OUT").map(PathBuf::from);
    let merge_dir = non_empty_env("LEANR_SYNTH_MERGE").map(PathBuf::from);

    assert!(
        !(passlist_only && passlist_update),
        "LEANR_SYNTH_PASSLIST_ONLY=1 with LEANR_SYNTH_PASSLIST_UPDATE=1 is rejected: rewriting the \
         pass-list from a pass-list-only run would freeze growth and could silently drop a \
         regressed entry. Use a full merge/update run to rewrite the synth pass-list."
    );
    assert!(
        !(shard_raw.is_some() && passlist_update),
        "LEANR_SYNTH_SHARD with LEANR_SYNTH_PASSLIST_UPDATE=1 is rejected: a shard sweeps only 1/N \
         of the constants, so rewriting the pass-list from its partial green list would drop every \
         entry outside this shard's slice. Shards emit a green list (LEANR_SYNTH_GREEN_OUT); only \
         LEANR_SYNTH_MERGE gates and rewrites, over the union of all shards."
    );
    assert!(
        !(shard_raw.is_some() && passlist_only),
        "LEANR_SYNTH_SHARD with LEANR_SYNTH_PASSLIST_ONLY=1 is rejected: passlist-only mode's swept \
         set IS the committed pass-list and its gating is deliberately total, which is precisely \
         what a shard cannot provide. Shard the full constant sweep instead."
    );
    assert!(
        !(shard_raw.is_some() && merge_dir.is_some()),
        "LEANR_SYNTH_SHARD with LEANR_SYNTH_MERGE is rejected: they are the two halves of the \
         sharded nightly (produce one green list vs. consume all of them), never one run."
    );
    assert!(
        !(merge_dir.is_some() && passlist_only),
        "LEANR_SYNTH_MERGE with LEANR_SYNTH_PASSLIST_ONLY=1 is rejected: merge mode's green set \
         comes from the shard artifacts, not from a sweep, so passlist-only has nothing to mean \
         here."
    );
    assert!(
        !(passlist_only && green_out.is_some()),
        "LEANR_SYNTH_GREEN_OUT with LEANR_SYNTH_PASSLIST_ONLY=1 is rejected: a passlist-only run's \
         green list is at most the committed pass-list it was handed, so emitting it as a \
         shard-style green list would invite merging a slice that discovered nothing."
    );
    assert!(
        !(shard_raw.is_some() && green_out.is_none()),
        "LEANR_SYNTH_SHARD requires LEANR_SYNTH_GREEN_OUT=<path>: a shard does not gate, so its \
         green list is its ONLY output — a shard that wrote nothing would silently contribute an \
         empty slice to the merge."
    );
    assert!(
        !(shard_raw.is_some() && manifest_out.is_none()),
        "LEANR_SYNTH_SHARD requires LEANR_SYNTH_MANIFEST_OUT=<path>: the merge job takes its \
         existence set from the UNION of the shards' manifests (it has no environment of its own), \
         so a shard without a manifest would make its slice's pass-list entries look removed and \
         silently absorb any real regression among them."
    );
    assert!(
        !(shard_raw.is_none() && manifest_out.is_some()),
        "LEANR_SYNTH_MANIFEST_OUT without LEANR_SYNTH_SHARD is rejected: a manifest is a shard's \
         receipt (its spec, the pass-list entries it observed in its environment, and how much it \
         swept), and only shard mode can honestly produce one."
    );

    let shard: Option<(usize, usize)> = shard_raw.as_deref().map(|raw| {
        parse_shard_spec(raw)
            .unwrap_or_else(|e| panic!("LEANR_SYNTH_SHARD={raw:?} is malformed: {e}"))
    });

    // Read the committed pass-list once, up front (same discipline as
    // `mathlib_sweep.rs`): passlist-only mode's swept set IS this file, so
    // an unreadable/empty file must fail loudly rather than gate vacuously.
    let committed: BTreeSet<String> = if passlist_only {
        let text = std::fs::read_to_string(passlist_path()).expect(
            "failed to read the committed synth pass-list \
             (tests/fixtures/meta/synth-passlist.txt) in passlist-only mode — this mode's swept \
             set IS this file, so an unreadable file must fail loudly rather than gate zero \
             constants as a vacuous pass",
        );
        let set: BTreeSet<String> = text
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .map(String::from)
            .collect();
        assert!(
            !set.is_empty(),
            "committed synth pass-list is empty in passlist-only mode — refusing to gate vacuously"
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

    // Merge mode: union the shards' green lists, then run the SAME gate +
    // reconcile + rewrite path a full update run does, `truncated = false`.
    // No environment is loaded — the "does this constant still exist
    // upstream?" oracle is the union of the shards' manifests, not a local
    // environment (mirrors `mathlib_sweep.rs`'s filesystem-free merge).
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
            "[merge] {} shard manifest(s), {} constant(s) swept in total, {} of {} committed \
             pass-list entries observed present in some shard's environment",
            manifests.len(),
            manifests.iter().map(|m| m.constants_swept).sum::<usize>(),
            committed.iter().filter(|f| present.contains(*f)).count(),
            committed.len(),
        );
        let exists = |c: &str| present.contains(c);
        let before = committed.len();
        let newly_green = gate_and_maybe_rewrite(GateInput {
            exists: &exists,
            committed: &committed,
            swept: &green,
            green: &green,
            truncated: false,
            passlist_update: true,
            mode: "merge",
            constants_swept: green.len(),
        });
        eprintln!(
            "[merge] pass-list growth: {before} -> {} entries ({newly_green} newly green)",
            green.len()
        );
        return;
    }

    // Every sweeping mode needs the oracle dump and the olean closure.
    let oracle_path = PathBuf::from(non_empty_env("LEANR_SYNTH_ORACLE").expect(
        "LEANR_SYNTH_ORACLE is required in every sweeping mode: it is the C1 oracle JSONL this \
         shard diffs leanr's synthesis against",
    ));
    let lean_path = std::env::var("LEANR_OLEAN_PATH").expect("LEANR_OLEAN_PATH");
    // LEANR_MATHLIB_DIR is read for env-parity with `mathlib_sweep.rs` but
    // C2 has NO source tree to walk: its corpus is the olean closure of
    // `pinned_modules()` (loaded via LEANR_OLEAN_PATH), and "does this
    // constant still exist?" is answered by the environment, not the
    // filesystem. Logged if set so a caller expecting it to matter is not
    // silently surprised.
    if let Some(dir) = non_empty_env("LEANR_MATHLIB_DIR") {
        eprintln!(
            "[sweep] LEANR_MATHLIB_DIR={dir} is set but unused (C2's corpus is the olean closure)"
        );
    }

    let roots: Vec<PathBuf> = lean_path
        .split(':')
        .filter(|s| !s.is_empty())
        .map(Into::into)
        .collect();
    assert!(
        !roots.is_empty(),
        "LEANR_OLEAN_PATH resolved to no search roots ({lean_path:?}) — the closure would fail to \
         load and the sweep would report 0 green as a PASS."
    );
    let sp = SearchPath::new(roots);

    // ONE load_closure over the whole pinned target set (delta (b), the
    // `check_sweep.rs` pattern): every shard builds the IDENTICAL
    // environment, so its constant list — and its `present` set — matches
    // every other shard's, which is what `validate_shard_manifests` relies
    // on.
    let targets: Vec<Arc<Name>> = pinned_modules().iter().map(|m| dotted_to_name(m)).collect();
    let mut env = Environment::default();
    let modules = load_closure(&sp, &targets, env.store_mut())
        .unwrap_or_else(|e| panic!("closure of the pinned Mathlib module set failed to load: {e}"));

    // Fold the union of constants and every extension table synthesis reads.
    // Module oleans carry disjoint constant sets; first-seen wins on a rare
    // cross-module collision (matching `check_sweep.rs`).
    let mut constants: HashMap<NameId, leanr_kernel::ConstantInfo> = HashMap::new();
    let mut reducibility: Vec<ReducibilityEntry> = Vec::new();
    let mut matchers: Vec<MatcherEntry> = Vec::new();
    let mut instances: Vec<InstanceEntry> = Vec::new();
    let mut default_instances: Vec<DefaultInstanceEntry> = Vec::new();
    let mut projection_fns: Vec<ProjectionFnInfo> = Vec::new();
    for (_, md) in modules {
        for ci in md.constants {
            constants.entry(ci.name()).or_insert(ci);
        }
        reducibility.extend(md.reducibility);
        matchers.extend(md.matchers);
        instances.extend(md.instances);
        default_instances.extend(md.default_instances);
        projection_fns.extend(md.projection_fns);
    }
    let all_ids: Vec<NameId> = constants.keys().copied().collect();
    leanr_kernel::replay(&mut env, constants).unwrap_or_else(|e| panic!("replay failed: {e}"));

    // ===== SORT KEY + STRIDE — MUST MIRROR C1 EXACTLY =====
    //
    // Sort every constant in the environment by its RENDERED name string
    // (`Name::Display` == Lean's `n.toString (escape := false)`), ASCENDING,
    // by Rust `str: Ord` (byte-wise UTF-8). That is provably identical to
    // Lean's `String.lt` (codepoint-wise `List Char`) for valid UTF-8
    // because UTF-8 is monotonic in codepoint under byte comparison — the
    // exact equivalence `dump_synth_mathlib.lean`'s header states. A shard
    // `I/N` (1-based `I`) then selects the constants at `idx % N == I - 1`
    // (0-based `idx`) via `shard_slice`, the SAME stride C1 applies.
    let mut named: Vec<(String, NameId)> = {
        let view = env.view();
        all_ids
            .iter()
            .map(|&nid| (view.store.to_name(None, Some(nid)).to_string(), nid))
            .collect()
    };
    named.sort_by(|a, b| a.0.cmp(&b.0));
    // Tie guard (believed vacuous — distinct top-level declaration names do
    // not render to the same string; the elaborator's own redeclaration
    // check is string-based). If it ever fires, `idx` assignment would
    // depend on an undefined tie-break and silently diverge from C1, so
    // flag it LOUDLY rather than let it pass (the header's explicit
    // instruction).
    for w in named.windows(2) {
        assert!(
            w[0].0 != w[1].0,
            "two distinct constants render to the same name {:?} — the sort/stride tie-break is \
             undefined and would silently diverge from C1's `idx` assignment. Flag this seam.",
            w[0].0
        );
    }
    let env_names: BTreeSet<String> = named.iter().map(|(s, _)| s.clone()).collect();

    // The work set of constants for this run (delta (a)):
    //   - shard: the stride slice of the FULL sorted list (so `idx` matches
    //     C1's stride over the same list; LIMIT is not applied — a shard is
    //     already a fragment);
    //   - passlist-only: the committed pass-list constants still present in
    //     the environment (a missing one is a loud, distinct failure, not a
    //     regression — it needs a conscious synth passlist update);
    //   - full/bounded: the whole sorted list, optionally truncated by
    //     LEANR_SYNTH_LIMIT for a smoke run (`truncated` logged, never
    //     silent).
    let (work, truncated): (Vec<(String, NameId)>, bool) = if let Some((i, n)) = shard {
        (shard_slice(&named, i, n), false)
    } else if passlist_only {
        let mut resolved = Vec::new();
        let mut missing = Vec::new();
        for c in &committed {
            match named.iter().find(|(s, _)| s == c) {
                Some(pair) => resolved.push(pair.clone()),
                None => missing.push(c.clone()),
            }
        }
        assert!(
            missing.is_empty(),
            "synth pass-list entries missing from the environment (renamed/removed upstream — NOT \
             a synthesis regression; needs a conscious synth passlist update): {missing:#?}"
        );
        (resolved, false)
    } else {
        let limit: usize = std::env::var("LEANR_SYNTH_LIMIT")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(usize::MAX);
        let total = named.len();
        let mut w = named.clone();
        w.truncate(limit);
        let truncated = w.len() < total;
        if truncated {
            eprintln!(
                "[sweep] LEANR_SYNTH_LIMIT={limit}: swept {} of {total} constants (bounded smoke \
                 run — gating only the swept prefix)",
                w.len()
            );
        }
        (w, truncated)
    };

    if let Some((i, n)) = shard {
        assert!(
            !work.is_empty() || named.len() < n,
            "shard {i}/{n} swept 0 of {} constants: its slice is empty even though there are at \
             least {n} constants to deal out. It would emit an empty green list the merge cannot \
             tell from a mass regression.",
            named.len()
        );
    }

    let swept: BTreeSet<String> = work.iter().map(|(s, _)| s.clone()).collect();

    // Parse + truncation-check the oracle corpus, then group by constant.
    let expected_shard = shard.map(|(i, n)| format!("{i}/{n}"));
    let oracle_text = std::fs::read_to_string(&oracle_path).unwrap_or_else(|e| {
        panic!(
            "failed to read the C1 oracle JSONL {}: {e}",
            oracle_path.display()
        )
    });
    let records = parse_oracle_shard(&oracle_text, expected_shard.as_deref())
        .unwrap_or_else(|e| panic!("oracle {} is unusable: {e}", oracle_path.display()));
    let mut by_const: BTreeMap<String, Vec<OracleRecord>> = BTreeMap::new();
    for r in records {
        by_const.entry(r.const_name.clone()).or_default().push(r);
    }

    // The green diff (delta (c)), constant by constant, sequentially. C1
    // confirmed ~931k constants/shard, so this is a heavy nightly loop;
    // parallelizing it (each query is independent, the tables are shared
    // read-only) is a NAMED SEAM left to a follow-up rather than pulling in
    // rayon here — flagged, not silent.
    let total = work.len();
    let mut green: BTreeSet<String> = BTreeSet::new();
    for (done, (name, _nid)) in work.iter().enumerate() {
        // A constant C1 mined no records for produced no synthesis signal;
        // it cannot be green (see `constant_is_green`'s `>= 1 comparable`
        // rule) so skip it entirely.
        let Some(recs) = by_const.get(name) else {
            continue;
        };
        let mut leanr: Vec<(String, LeanrAns)> = Vec::new();
        for r in recs {
            if !r.is_comparable() {
                continue;
            }
            let ans = run_leanr_query(
                &env,
                &reducibility,
                &matchers,
                &instances,
                &default_instances,
                &projection_fns,
                &r.goal,
            );
            // Loud, per-query: a `GoalMismatch` means this query's `val`
            // comparison (had we made one) would have run under a numbering
            // that already diverged from the oracle dumper's — see
            // `LeanrAns::GoalMismatch`'s doc comment. It never agrees
            // (`query_agrees`), so `name` will report not-green; this line
            // is what lets a human tell that apart from a true synthesis
            // regression.
            if let LeanrAns::GoalMismatch { got, want } = &ans {
                eprintln!(
                    "[sweep] {name} {}: GOAL ROUND-TRIP MISMATCH — re-encoded goal {got} != \
                     oracle goal {want}; EncSt numbering diverged from the oracle dumper \
                     (oracle_synth.rs:250-258), refusing to trust a `val` comparison under it",
                    r.id
                );
            }
            leanr.push((r.id.clone(), ans));
        }
        if constant_is_green(name, recs, &leanr) {
            green.insert(name.clone());
        }
        if (done + 1).is_multiple_of(10_000) || done + 1 == total {
            eprintln!(
                "[sweep] {}/{total} constants, {} green so far",
                done + 1,
                green.len()
            );
        }
    }

    if let Some(path) = &green_out {
        write_green_list(path, &green);
    }

    // Shard mode STOPS before gating (it saw only 1/N of the constants).
    if let Some((i, n)) = shard {
        let present: BTreeSet<String> = committed
            .iter()
            .filter(|c| env_names.contains(*c))
            .cloned()
            .collect();
        let manifest = ShardManifest {
            shard: i,
            shard_count: n,
            constants_swept: work.len(),
            present,
        };
        if let Some(path) = &manifest_out {
            write_shard_manifest(path, &manifest);
        }
        eprintln!(
            "sweep[shard {i}/{n}]: {} of {} constants, {} green, {} of {} pass-list entries present \
             in the environment (no gate: the merge job gates the union)",
            work.len(),
            named.len(),
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
    let exists = |c: &str| env_names.contains(c);
    gate_and_maybe_rewrite(GateInput {
        exists: &exists,
        committed: &committed,
        swept: &swept,
        green: &green,
        truncated,
        passlist_update,
        mode,
        constants_swept: work.len(),
    });
}

// ===== gate / reconcile / rewrite (transcribed from mathlib_sweep.rs) =====

/// Everything a sweep does once it has a green set: gate, reconcile,
/// report, and (in update/merge mode) rewrite the pass-list. Extracted so
/// merge mode runs literally this code, not a shell reimplementation — the
/// sharded nightly is only trustworthy if the union it gates is gated by
/// the same logic, with the same missing-vs-regressed split, as an
/// unsharded full sweep. Returns the newly-green count.
struct GateInput<'a> {
    /// "Does this pass-list entry (a constant name) still exist upstream?"
    /// — a membership test against this run's environment in sweeping
    /// modes, and the union of the shards' manifests in merge mode (which
    /// has no environment of its own). Injected exactly as in
    /// `mathlib_sweep.rs`, for the same reason: merge must NOT consult a
    /// local environment it never built.
    exists: &'a dyn Fn(&str) -> bool,
    committed: &'a BTreeSet<String>,
    /// Constants actually swept this run; only consulted when `truncated`.
    swept: &'a BTreeSet<String>,
    green: &'a BTreeSet<String>,
    /// True only for bounded (LEANR_SYNTH_LIMIT) runs.
    truncated: bool,
    passlist_update: bool,
    mode: &'a str,
    constants_swept: usize,
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
        constants_swept,
    } = input;

    let committed_swept = committed.iter().filter(|c| swept.contains(*c)).count();
    let not_green: Vec<&String> = committed
        .iter()
        .filter(|c| (!truncated || swept.contains(*c)) && !green.contains(*c))
        .collect();
    // A committed entry that isn't green is either upstream churn (the
    // constant was renamed/removed — nothing to regress) or a genuine
    // synthesis regression (the constant is still there, its synthesis just
    // no longer agrees with the oracle). Only the update path (and merge,
    // which is that same path fed by the shards) may tell them apart and
    // drop the former — its whole job is to reconcile against upstream. The
    // plain gate keeps failing on a missing constant with zero exceptions.
    let regressions: Vec<&String> = if passlist_update {
        let (missing, true_regressions) = split_missing_from_regressions(exists, not_green);
        if !missing.is_empty() {
            eprintln!(
                "[sweep] dropping {} pass-list entries whose constants no longer exist:",
                missing.len()
            );
            for c in &missing {
                eprintln!("[sweep]   {c}");
            }
        }
        true_regressions
    } else {
        not_green
    };
    let newly_green: Vec<_> = green.iter().filter(|c| !committed.contains(*c)).collect();
    eprintln!(
        "sweep[{mode}]: {} constants, {} green, {} on pass-list, {}/{} pass-list entries swept, {} \
         regressions, {} newly green",
        constants_swept,
        green.len(),
        committed.len(),
        committed_swept,
        committed.len(),
        regressions.len(),
        newly_green.len()
    );

    // Gate BEFORE writing, even in update mode: rewriting from `green`
    // unconditionally would re-baseline over any TRUE regression. Upstream
    // churn has already been reconciled out (loudly) above, so a non-empty
    // `regressions` here means a real synthesis regression, full stop. In
    // the sharded nightly this assert is the alarm — the one place a real
    // regression turns into a red workflow run.
    assert!(
        regressions.is_empty(),
        "synth pass-list regressions: {regressions:#?}"
    );

    if passlist_update {
        let mut out = String::from(
            "# Mathlib constants whose typeclass synthesis matches the oracle (M4a plan-4 nightly \
             synthesis ratchet).\n\
             # Regenerate: the nightly synthesis sweep merge job. NEVER hand-edit to hide a \
             regression.\n",
        );
        for c in green {
            out.push_str(c);
            out.push('\n');
        }
        std::fs::write(passlist_path(), out).unwrap();
    }

    newly_green.len()
}

/// Split a not-green pass-list entry set into (removed-upstream, true
/// regression) by asking `exists` about each constant name. Pulled out so
/// it's unit-testable without an environment; `exists` is a parameter, not
/// hardcoded, because merge mode's answer comes from the shard manifests,
/// not a local environment.
fn split_missing_from_regressions<'a>(
    exists: &dyn Fn(&str) -> bool,
    not_green: Vec<&'a String>,
) -> (Vec<&'a String>, Vec<&'a String>) {
    not_green.into_iter().partition(|c| !exists(c))
}

// ===== env helpers (verbatim from mathlib_sweep.rs) =====

fn non_empty_env(key: &str) -> Option<String> {
    std::env::var(key).ok().filter(|s| !s.trim().is_empty())
}

/// Parse a 1-based `I/N` shard spec. `Err(reason)` rather than panicking or
/// defaulting: a mistyped spec that quietly swept the wrong slice would
/// produce a green list wrong in a way the merge cannot detect.
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
/// congruent to `I-1` mod `N`. Striding (not chunking) matches C1's own
/// `idx % N == I - 1` and deals cost-neighbours out round-robin.
fn shard_slice<T: Clone>(items: &[T], i: usize, n: usize) -> Vec<T> {
    items
        .iter()
        .enumerate()
        .filter(|(idx, _)| idx % n == i - 1)
        .map(|(_, t)| t.clone())
        .collect()
}

fn dotted_to_name(dotted: &str) -> Arc<Name> {
    let mut n = Arc::new(Name::Anonymous);
    for part in dotted.split('.') {
        n = Arc::new(Name::Str {
            parent: n,
            part: part.to_string(),
        });
    }
    n
}

// ===== green list + shard manifest artifacts (transcribed) =====

fn write_green_list(path: &Path, green: &BTreeSet<String>) {
    if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
        std::fs::create_dir_all(parent).unwrap_or_else(|e| {
            panic!(
                "failed to create the LEANR_SYNTH_GREEN_OUT parent dir ({}): {e}",
                parent.display()
            )
        });
    }
    let mut out = String::new();
    for c in green {
        out.push_str(c);
        out.push('\n');
    }
    std::fs::write(path, out).unwrap_or_else(|e| {
        panic!(
            "failed to write the green list to LEANR_SYNTH_GREEN_OUT ({}): {e}",
            path.display()
        )
    });
}

/// Union every `*.txt` green list in `dir`. An empty/unreadable directory
/// is a hard error: merge rewrites the pass-list from this union, so an
/// empty union would gate every committed entry as a regression.
fn read_shard_green_lists(dir: &Path) -> (BTreeSet<String>, Vec<PathBuf>) {
    let rd = std::fs::read_dir(dir).unwrap_or_else(|e| {
        panic!(
            "LEANR_SYNTH_MERGE directory ({}) is not readable: {e}",
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
        "no *.txt shard green lists found in the LEANR_SYNTH_MERGE directory ({}) — refusing to \
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

/// A shard's receipt, and the merge job's only source of truth about which
/// pass-list entries still exist. The merge runs with NO environment: each
/// shard records the committed pass-list entries it observed present in its
/// (identical, per delta (b)) environment; merge takes the union and
/// cross-checks the receipts against each other.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ShardManifest {
    shard: usize,
    shard_count: usize,
    /// How many constants this shard's slice contained. Zero means the
    /// shard swept nothing at all — a vacuously empty green list.
    constants_swept: usize,
    /// The committed pass-list entries this shard observed present in its
    /// environment.
    present: BTreeSet<String>,
}

fn render_shard_manifest(m: &ShardManifest) -> String {
    let mut out = String::from(
        "# leanr synth shard manifest v1 — a shard's receipt for the merge job.\n\
         # Machine input for the synth sweep merge; see synth_sweep.rs.\n",
    );
    out.push_str(&format!("shard {}/{}\n", m.shard, m.shard_count));
    out.push_str(&format!("constants_swept {}\n", m.constants_swept));
    for c in &m.present {
        out.push_str("present ");
        out.push_str(c);
        out.push('\n');
    }
    out
}

fn parse_shard_manifest(text: &str) -> Result<ShardManifest, String> {
    let mut shard: Option<(usize, usize)> = None;
    let mut constants_swept: Option<usize> = None;
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
        match key {
            "shard" => {
                if shard.is_some() {
                    return Err("duplicate `shard` line".to_string());
                }
                shard = Some(parse_shard_spec(value).map_err(|e| format!("`shard {value}`: {e}"))?);
            }
            "constants_swept" => {
                if constants_swept.is_some() {
                    return Err("duplicate `constants_swept` line".to_string());
                }
                constants_swept = Some(
                    value
                        .parse::<usize>()
                        .map_err(|e| format!("`constants_swept {value:?}` is not a count: {e}"))?,
                );
            }
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
        constants_swept: constants_swept.ok_or("missing `constants_swept` line")?,
        present,
    })
}

fn write_shard_manifest(path: &Path, m: &ShardManifest) {
    if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
        std::fs::create_dir_all(parent).unwrap_or_else(|e| {
            panic!(
                "failed to create the LEANR_SYNTH_MANIFEST_OUT parent dir ({}): {e}",
                parent.display()
            )
        });
    }
    std::fs::write(path, render_shard_manifest(m)).unwrap_or_else(|e| {
        panic!(
            "failed to write the shard manifest to LEANR_SYNTH_MANIFEST_OUT ({}): {e}",
            path.display()
        )
    });
}

fn read_shard_manifests(dir: &Path) -> Vec<ShardManifest> {
    let rd = std::fs::read_dir(dir).unwrap_or_else(|e| {
        panic!(
            "LEANR_SYNTH_MERGE directory ({}) is not readable: {e}",
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
/// entries — the existence oracle merge mode gates with. Exactly one
/// manifest per `1..=N`, none vacuous, every `present` equal to the union,
/// and the all-blind guard (see `mathlib_sweep.rs` for the full rationale
/// each check encodes).
fn validate_shard_manifests(
    manifests: &[ShardManifest],
    committed: &BTreeSet<String>,
) -> Result<BTreeSet<String>, String> {
    if manifests.is_empty() {
        return Err(
            "no *.manifest shard receipts found — refusing to merge without evidence of which \
             pass-list entries still exist upstream, since with none every entry would look \
             removed and any real regression would be reconciled away"
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
             reconciled out of the baseline as removals."
        ));
    }
    let expected: BTreeSet<usize> = (1..=n).collect();
    if indices != expected {
        let missing: Vec<usize> = expected.difference(&indices).copied().collect();
        let unexpected: Vec<usize> = indices.difference(&expected).copied().collect();
        return Err(format!(
            "shard manifests are not exactly 1..={n}: missing {missing:?}, unexpected \
             {unexpected:?}. Every pass-list entry only a missing shard could vouch for would look \
             removed, so its regression would be silently absorbed. Re-run the failed shard(s)."
        ));
    }
    if let Some(m) = manifests.iter().find(|m| m.constants_swept == 0) {
        return Err(format!(
            "shard {}/{n} swept 0 constants — it produced a vacuously empty green list (an empty \
             LEANR_OLEAN_PATH or an empty slice does exactly this while still exiting 0), and \
             merging it would read its whole slice as a mass regression",
            m.shard
        ));
    }
    let present: BTreeSet<String> = manifests
        .iter()
        .flat_map(|m| m.present.iter().cloned())
        .collect();
    // Every shard builds the SAME environment (delta (b)) and tests the SAME
    // committed pass-list against it, so under correct operation every
    // shard's `present` IS the full set == the union. Any shard whose
    // observed-present set differs has an incomplete/stale view (a bad
    // closure) and merging it would absorb its blind spot's regressions as
    // removals.
    if let Some(m) = manifests.iter().find(|m| m.present != present) {
        return Err(format!(
            "shard {}/{n} observed {} committed pass-list entries in its environment, but the \
             union across all shards is {} — every shard builds the SAME environment and tests the \
             SAME pass-list, so any shard whose observed-present set differs has an incomplete or \
             stale view of it, and merging it would silently absorb its blind spot's regressions \
             as removals. Re-run the disagreeing shard(s).",
            m.shard,
            m.present.len(),
            present.len()
        ));
    }
    // The one shape the equality check cannot see: ALL shards blind
    // together (every `present` is `{}`, which trivially equals the `{}`
    // union). A non-empty committed pass-list observed wholly absent by
    // every shard is correlated total blindness (the closure never loaded),
    // not a genuine upstream removal of the entire pass-list.
    if present.is_empty() && !committed.is_empty() {
        return Err(format!(
            "every one of the {} shard manifest(s) observed 0 of the {} committed pass-list \
             entries in its environment — since all shards run identical steps against one pinned \
             module set, this is not {} independent coincidences but a single correlated cause, \
             most likely that the shards ran without the olean closure actually loading. Refusing \
             to reconcile the entire pass-list away as removals.",
            manifests.len(),
            committed.len(),
            manifests.len()
        ));
    }
    Ok(present)
}

// ===================================================================
// Unit tests — what CI actually exercises (the sweep above is #[ignore]d).
// ===================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn a_term() -> Value {
        json!({"k": "const", "n": "inst", "us": []})
    }

    /// A comparable ordinary oracle record: `ok`, and (when ok) a `val`
    /// leanr must reproduce exactly.
    fn oracle_rec(id: &str, ok: bool) -> OracleRecord {
        OracleRecord {
            const_name: "c".to_string(),
            id: id.to_string(),
            src: "binder".to_string(),
            goal: json!({"k": "const", "n": "G", "us": []}),
            ok: Some(ok),
            val: if ok { Some(a_term()) } else { None },
            near_budget: false,
            exc: None,
        }
    }

    /// STEP 1 (RED then GREEN): a constant with two queries, one agreeing
    /// and one diverging, is NOT green.
    #[test]
    fn green_requires_all_queries_agree() {
        let recs = vec![oracle_rec("c/synth/0", true), oracle_rec("c/synth/1", true)];
        // Query 0 agrees (same term); query 1 diverges (oracle ok=true but
        // leanr found no instance).
        let leanr = vec![
            ("c/synth/0".to_string(), LeanrAns::Synth(a_term())),
            ("c/synth/1".to_string(), LeanrAns::NoInstance),
        ];
        assert!(!constant_is_green("c", &recs, &leanr));

        // Both agree -> green.
        let leanr_ok = vec![
            ("c/synth/0".to_string(), LeanrAns::Synth(a_term())),
            ("c/synth/1".to_string(), LeanrAns::Synth(a_term())),
        ];
        assert!(constant_is_green("c", &recs, &leanr_ok));

        // A wrong-but-existing instance (right verdict, wrong term) is a
        // divergence — the non-verdict-only discipline.
        let leanr_wrong_term = vec![
            ("c/synth/0".to_string(), LeanrAns::Synth(a_term())),
            (
                "c/synth/1".to_string(),
                LeanrAns::Synth(json!({"k": "const", "n": "otherInst", "us": []})),
            ),
        ];
        assert!(!constant_is_green("c", &recs, &leanr_wrong_term));

        // A comparable oracle query with no leanr answer at all diverges.
        let leanr_missing = vec![("c/synth/0".to_string(), LeanrAns::Synth(a_term()))];
        assert!(!constant_is_green("c", &recs, &leanr_missing));
    }

    /// A goal round-trip mismatch (`LeanrAns::GoalMismatch`, the C2 review
    /// fix) is caught: it never agrees with EITHER verdict, even when the
    /// mismatched re-encoding happens to carry a `got` that coincidentally
    /// equals what a naive `val`-only comparison would have accepted. This
    /// is the property `oracle_synth.rs:250-258`'s round-trip check exists
    /// to guarantee — an `EncSt` that didn't round-trip must never be
    /// trusted to compare `val` "for the wrong reason".
    #[test]
    fn goal_round_trip_mismatch_never_agrees() {
        let mismatch = LeanrAns::GoalMismatch {
            // Deliberately equal to `a_term()`: even a `val` that LOOKS
            // right must not be trusted once the goal itself failed to
            // round-trip.
            got: a_term(),
            want: json!({"k": "const", "n": "G", "us": []}),
        };
        let ok_rec = oracle_rec("c/synth/0", true);
        let neg_rec = oracle_rec("c/synth/0", false);
        assert!(!query_agrees(&ok_rec, &mismatch));
        assert!(!query_agrees(&neg_rec, &mismatch));

        // And it makes the whole constant NOT green — a phantom
        // non-green, exactly like `Errored`, rather than a silent
        // wrong-reason agreement.
        assert!(!constant_is_green(
            "c",
            &[ok_rec],
            &[("c/synth/0".to_string(), mismatch)]
        ));
    }

    /// `ok:false` records agree only with `NoInstance`; `exc`/`near_budget`
    /// records are skipped; a constant with only skipped records is NOT
    /// green (no comparable evidence).
    #[test]
    fn negative_verdicts_and_skips_are_handled() {
        let neg = oracle_rec("c/synth/0", false);
        assert!(query_agrees(&neg, &LeanrAns::NoInstance));
        assert!(!query_agrees(&neg, &LeanrAns::Synth(a_term())));
        // leanr erroring never agrees, even on a negative verdict.
        assert!(!query_agrees(&neg, &LeanrAns::Errored));

        // A negative record leanr also reports NoInstance for -> green.
        assert!(constant_is_green(
            "c",
            std::slice::from_ref(&neg),
            &[("c/synth/0".to_string(), LeanrAns::NoInstance)]
        ));

        // exc record: skipped from the gate; a constant with ONLY an exc
        // record has no comparable query -> NOT green.
        let exc = OracleRecord {
            exc: Some("internal exception".to_string()),
            ok: None,
            val: None,
            ..oracle_rec("c/synth/0", false)
        };
        assert!(!exc.is_comparable());
        assert!(!constant_is_green("c", &[exc], &[]));

        // near_budget record: same — skipped, no comparable query.
        let nb = OracleRecord {
            near_budget: true,
            ..oracle_rec("c/synth/0", true)
        };
        assert!(!nb.is_comparable());
        assert!(!constant_is_green("c", &[nb], &[]));

        // A constant-level const-exc record (src:"const", no goal/ok) is
        // also never comparable.
        let const_exc = OracleRecord {
            id: "c/const-exc".to_string(),
            src: "const".to_string(),
            goal: Value::Null,
            ok: None,
            val: None,
            exc: Some("heartbeats".to_string()),
            ..oracle_rec("c", false)
        };
        assert!(!const_exc.is_comparable());
    }

    /// The sentinel/truncation guard: a complete corpus parses; a missing
    /// sentinel, a wrong `records` count, or trailing lines after the
    /// sentinel all fail loudly. `exc`/`near_budget` lines count toward
    /// `records` exactly as C1 counts them.
    #[test]
    fn oracle_parse_verifies_the_completion_sentinel() {
        let complete = concat!(
            r#"{"const":"c","id":"c/synth/0","src":"binder","goal":{"k":"const","n":"G","us":[]},"ok":true,"val":{"k":"const","n":"inst","us":[]},"near_budget":false}"#,
            "\n",
            r#"{"const":"c","id":"c/synthapp/0","src":"app","goal":{"k":"const","n":"H","us":[]},"exc":"boom"}"#,
            "\n",
            r#"{"sentinel":true,"shard":"3/12","records":2}"#,
            "\n",
        );
        let recs = parse_oracle_shard(complete, Some("3/12")).expect("complete corpus parses");
        assert_eq!(recs.len(), 2);
        assert!(recs[0].is_comparable());
        assert!(!recs[1].is_comparable(), "the exc record is not comparable");

        // No sentinel at all -> truncated.
        let no_sentinel = concat!(
            r#"{"const":"c","id":"c/synth/0","src":"binder","goal":{"k":"const","n":"G","us":[]},"ok":true,"val":{"k":"const","n":"inst","us":[]},"near_budget":false}"#,
            "\n",
        );
        let e = parse_oracle_shard(no_sentinel, None).unwrap_err();
        assert!(
            e.contains("no completion sentinel") || e.contains("NO completion sentinel"),
            "got: {e}"
        );

        // Sentinel present but count disagrees -> truncated.
        let bad_count = concat!(
            r#"{"const":"c","id":"c/synth/0","src":"binder","goal":{"k":"const","n":"G","us":[]},"ok":true,"val":{"k":"const","n":"inst","us":[]},"near_budget":false}"#,
            "\n",
            r#"{"sentinel":true,"shard":"3/12","records":5}"#,
            "\n",
        );
        let e = parse_oracle_shard(bad_count, None).unwrap_err();
        assert!(e.contains("declares 5 records but 1"), "got: {e}");

        // A line after the sentinel -> corrupt/concatenated.
        let trailing = concat!(
            r#"{"const":"c","id":"c/synth/0","src":"binder","goal":{"k":"const","n":"G","us":[]},"ok":true,"val":{"k":"const","n":"inst","us":[]},"near_budget":false}"#,
            "\n",
            r#"{"sentinel":true,"shard":"3/12","records":1}"#,
            "\n",
            r#"{"const":"c","id":"c/synth/1","src":"binder","goal":{"k":"const","n":"G","us":[]},"ok":true,"near_budget":false}"#,
            "\n",
        );
        let e = parse_oracle_shard(trailing, None).unwrap_err();
        assert!(e.contains("not the last line"), "got: {e}");

        // Wrong shard id -> refuse to diff against the wrong slice.
        let e = parse_oracle_shard(complete, Some("4/12")).unwrap_err();
        assert!(e.contains("!= this run's shard"), "got: {e}");
    }

    /// The property that makes the sharded merge sound: the shards PARTITION
    /// the constant list (every constant in exactly one shard; their union
    /// is the whole list), balanced to within one element.
    #[test]
    fn shard_slices_partition_the_constant_list() {
        let items: Vec<usize> = (0..97).collect();
        for n in 1..=13usize {
            let mut seen: Vec<usize> = Vec::new();
            for i in 1..=n {
                let slice = shard_slice(&items, i, n);
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
                "N={n}: a constant landed in more than one shard"
            );
            assert_eq!(
                sorted, items,
                "N={n}: the union of all shards lost a constant"
            );
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
            assert!(parse_shard_spec(bad).is_err(), "{bad:?} must be rejected");
        }
    }

    #[test]
    fn split_missing_from_regressions_separates_removed_constants_from_true_regressions() {
        let present = "Foo.stillHere".to_string();
        let removed = "Foo.renamedAway".to_string();
        let not_green = vec![&present, &removed];
        // Only `Foo.stillHere` still exists in the (mock) environment.
        let exists = |c: &str| c == "Foo.stillHere";
        let (missing, true_regressions) = split_missing_from_regressions(&exists, not_green);
        assert_eq!(
            missing,
            vec![&removed],
            "the removed constant must be reconciled out"
        );
        assert_eq!(
            true_regressions,
            vec![&present],
            "a constant that still exists but isn't green stays a hard regression"
        );
    }

    fn manifest_fixture(shard: usize, shard_count: usize, present: &[&str]) -> ShardManifest {
        ShardManifest {
            shard,
            shard_count,
            constants_swept: 5000,
            present: present.iter().map(|s| (*s).to_string()).collect(),
        }
    }

    #[test]
    fn shard_manifest_round_trips_through_its_artifact_form() {
        let m = manifest_fixture(3, 12, &["Foo.bar", "Nat.add"]);
        assert_eq!(
            parse_shard_manifest(&render_shard_manifest(&m)),
            Ok(m.clone())
        );

        let empty = manifest_fixture(1, 1, &[]);
        assert_eq!(
            parse_shard_manifest(&render_shard_manifest(&empty)),
            Ok(empty)
        );

        for bad in [
            "",                                                   // no shard line
            "shard 3/12\n",                                       // no constants_swept
            "shard 13/12\nconstants_swept 5\n",                   // bad spec
            "shard 3/12\nshard 4/12\nconstants_swept 5\n",        // duplicate shard
            "shard 3/12\nconstants_swept 5\nconstants_swept 6\n", // duplicate count
            "shard 3/12\nconstants_swept x\n",                    // not a count
            "shard 3/12\nconstants_swept 5\nbogus k\n",           // unknown key
            "shard 3/12\nconstants_swept 5\nlonely\n",            // not key/value
        ] {
            assert!(
                parse_shard_manifest(bad).is_err(),
                "{bad:?} must be rejected"
            );
        }
    }

    #[test]
    fn merged_green_lists_union_shard_outputs() {
        let dir = std::env::temp_dir().join(format!(
            "leanr-synth-merge-test-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();

        let a: BTreeSet<String> = ["Foo.b", "Foo.a"]
            .iter()
            .map(|s| (*s).to_string())
            .collect();
        let b: BTreeSet<String> = ["Foo.c", "Foo.a"]
            .iter()
            .map(|s| (*s).to_string())
            .collect();
        write_green_list(&dir.join("shard-1.txt"), &a);
        write_green_list(&dir.join("shard-2.txt"), &b);
        std::fs::write(dir.join("notes.md"), "Foo.notGreen\n").unwrap();

        let (union, sources) = read_shard_green_lists(&dir);
        assert_eq!(sources.len(), 2, "only the *.txt green lists count");
        assert_eq!(
            union.into_iter().collect::<Vec<_>>(),
            vec!["Foo.a", "Foo.b", "Foo.c"],
            "the union must be deduplicated and sorted"
        );

        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn shard_manifest_validation_requires_exactly_one_per_shard() {
        let committed: BTreeSet<String> = ["Foo.a".to_string()].into_iter().collect();
        let full: Vec<ShardManifest> = (1..=4)
            .map(|i| manifest_fixture(i, 4, &["Foo.a"]))
            .collect();
        assert_eq!(
            validate_shard_manifests(&full, &committed),
            Ok(["Foo.a".to_string()].into_iter().collect())
        );

        let err = |ms: &[ShardManifest]| validate_shard_manifests(ms, &committed).unwrap_err();
        assert!(err(&[]).contains("no *.manifest"));

        let mut missing = full.clone();
        missing.remove(2); // shard 3 never uploaded
        let e = err(&missing);
        assert!(
            e.contains("not exactly 1..=4") && e.contains("missing [3]"),
            "got: {e}"
        );

        // Right COUNT, wrong SET: shard 2 twice, shard 3 absent.
        let mut dup = full.clone();
        dup[2] = manifest_fixture(2, 4, &["Foo.a"]);
        assert_eq!(dup.len(), full.len());
        assert!(err(&dup).contains("duplicate shard manifests"));

        let mut mixed = full.clone();
        mixed[1] = manifest_fixture(2, 12, &["Foo.a"]);
        assert!(err(&mixed).contains("disagree on the shard count"));
    }

    #[test]
    fn shard_manifest_validation_rejects_partial_and_total_blindness() {
        let committed: BTreeSet<String> = [
            "Foo.a".to_string(),
            "Foo.b".to_string(),
            "Foo.c".to_string(),
        ]
        .into_iter()
        .collect();

        // Disjoint views: union non-empty (old check passed), but shards
        // disagree.
        let disjoint = vec![
            manifest_fixture(1, 2, &["Foo.a"]),
            manifest_fixture(2, 2, &["Foo.b"]),
        ];
        let e = validate_shard_manifests(&disjoint, &committed).unwrap_err();
        assert!(
            e.contains("shard 1/2") && e.contains("union across all shards is 2"),
            "got: {e}"
        );

        // Vacuous shard (swept 0 constants).
        let mut vacuous = vec![
            manifest_fixture(1, 2, &["Foo.a"]),
            manifest_fixture(2, 2, &["Foo.a"]),
        ];
        vacuous[1].constants_swept = 0;
        let e = validate_shard_manifests(&vacuous, &committed).unwrap_err();
        assert!(e.contains("shard 2/2 swept 0 constants"), "got: {e}");

        // One shard blind, sibling not: disagreement.
        let one_blind = vec![
            manifest_fixture(1, 2, &["Foo.a"]),
            manifest_fixture(2, 2, &[]),
        ];
        let e = validate_shard_manifests(&one_blind, &committed).unwrap_err();
        assert!(
            e.contains("shard 2/2 observed 0 committed pass-list entries"),
            "got: {e}"
        );

        // ALL shards blind together: the correlated-total-blindness guard.
        let all_blind = vec![manifest_fixture(1, 2, &[]), manifest_fixture(2, 2, &[])];
        let e = validate_shard_manifests(&all_blind, &committed).unwrap_err();
        assert!(
            e.contains("every one of the 2 shard manifest(s)")
                && e.contains("0 of the 3 committed pass-list entries"),
            "got: {e}"
        );

        // But a genuinely-empty committed pass-list is not a shard fault.
        assert_eq!(
            validate_shard_manifests(&all_blind, &BTreeSet::new()),
            Ok(BTreeSet::new())
        );
    }
}
