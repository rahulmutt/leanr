//! Tier-1 SYNTHESIS differential gate (M4a plan-4 spec § The gate):
//! every committed typeclass-synthesis query must agree with the oracle
//! — VERDICT *and* canonicalized instance TERM. Hermetic: the committed
//! `Synth0.olean` and `synth-queries.jsonl` are the entire input; CI
//! never installs Lean (docs/ORACLE.md).
//!
//! Sibling of `oracle_fast.rs`, sharing its decode/encode helpers via
//! `tests/support/mod.rs`. The corpus's record shape and every
//! canonicalization rule are documented in
//! `tests/fixtures/meta/dump_synth.lean`'s module header (the
//! authoritative counterpart).
//!
//! This is a REGRESSION gate: "nothing that used to agree now
//! disagrees." It is deliberately NOT verdict-only — comparing just
//! `ok` would pass against an engine that picks a different (but
//! existing) instance for `Mul N`, which is exactly the failure mode
//! the `DiscrTree` match-order work had to get right.

use std::collections::HashMap;

use leanr_kernel::bank::{ExprId, NameId, Store};
use leanr_kernel::EnvView;
use leanr_meta::{Config, MVarDecl, MVarId, MVarKind, MetaCtx};

mod support;
use support::{decode_expr, encode_expr, fixture, replay_fixture, EncSt};

/// Committed corpus records that this gate does NOT compare, each with
/// the DOCUMENTED seam that makes leanr's answer differ from the
/// oracle's and the seam's owner. Nothing here is a weakened
/// comparison, a deleted query, or a re-baselined expectation: the
/// oracle's answer stays recorded in `synth-queries.jsonl` exactly as
/// dumped, the query keeps being asked at every `fixtures:regen`, and
/// the divergence is named out loud rather than hidden. An entry may be
/// added ONLY for a seam already documented in the engine itself.
///
/// If a seam is closed, the corresponding entry must be REMOVED (the
/// `compared` count assertion at the end of the gate is what forces
/// that to be a deliberate edit rather than a silent drift).
const SEAM_EXCLUSIONS: &[(&str, &str)] = &[(
    "mvarGoal/synth/0",
    "NAMED SEAM `withNewMCtxDepth (allowLevelAssignments := true)` — no mctx-depth model in \
     this crate. Owner: M4b. Cited at `synth.rs::synth_instance_main` (\"`preprocess`/\
     `preprocessOutParam`, and `withNewMCtxDepth (allowLevelAssignments := true)` — NAMED \
     SEAM, no field/mechanism in this crate at all ... Owner M4b, citing \
     SynthInstance.lean:958-968\") and at `level.rs`'s \"Depth / read-only seam\". \
     Mechanism, confirmed by instrumenting the engine: the goal is `OfN ?n N` with `?n` \
     minted OUTSIDE the search. The oracle runs `SynthInstance.main` under \
     `withNewMCtxDepth`, so `?n` sits at a LOWER depth than the search's, and \
     `AbstractMVars` leaves lower-depth metavariables alone (`AbstractMVars.lean:91`, \
     `decl.depth != (← getMCtx).depth => return e`; the level twin at :59-60 says \
     \"metavariables from lower depths are treated as constants\"). The oracle's answer \
     therefore abstracts NOTHING, passes `wakeUp`'s root check `answer.result.numMVars == 0` \
     (SynthInstance.lean:428), and comes back as `instOfNN ?n`. leanr has no depth notion, \
     so `?n` is an ordinary current-depth mvar: `mk_answer`'s `abstract_mvars` abstracts it, \
     `num_mvars() == 1`, and `wake_up`'s identical root check rejects the answer — leanr \
     returns `Ok(None)` where the oracle returns `Some (instOfNN ?n)`. leanr's side is \
     INCOMPLETENESS (a refused answer), never a wrong answer, so it stays within the \
     crate's soundness contract.",
)];

#[test]
fn oracle_synth_gate() {
    let support::Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
    } = replay_fixture("Synth0.olean");

    let queries =
        std::fs::read_to_string(fixture("synth-queries.jsonl")).expect("committed queries");
    let mut failures = Vec::new();
    let mut compared = 0usize;
    let mut skipped_exc = Vec::new();
    let mut skipped_near_budget = Vec::new();
    let mut skipped_seam = Vec::new();

    for line in queries.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("committed JSONL is valid");
        let id = q["id"].as_str().expect("id field");
        let kind = q["q"].as_str().expect("q field");

        // `exc` records: the ORACLE itself did not answer cleanly (it
        // threw), so there is no verdict to agree with and the record is
        // NOT part of the gate. It is still COMMITTED and enumerated
        // here — never silently dropped from the curated list — so the
        // question keeps being asked at every `fixtures:regen` and a
        // future oracle/leanr change that makes it answerable shows up
        // as a corpus diff.
        //
        // The one such record today is `stuck/synth/0` (`Add ?a`, `?a`
        // minted OUTSIDE the search). It is the DOCUMENTED
        // `isDefEqStuckEx` seam: `synthInstanceCore?`
        // (`SynthInstance.lean:958-968`) runs `main` under
        // `withNewMCtxDepth` with `isDefEqStuckEx := true`, so the
        // oracle's first unification throws `isDefEqStuckException`;
        // this crate has no `Config` field for `isDefEqStuckEx` at all
        // and no mctx-depth model, so `?a` is simply assignable here and
        // leanr answers `instAddN` instead of getting stuck. Seam owner:
        // M4b — see `synth.rs::synth_instance_main`'s own
        // `isDefEqStuckEx := true -- NAMED SEAM, not settable` comment
        // and `config.rs`'s matching note. Excluding it is NOT a
        // weakening of a comparison leanr could pass; there is no
        // oracle verdict to compare against.
        if kind == "exc" {
            skipped_exc.push(format!("{id}: {}", q["msg"]));
            continue;
        }
        assert_eq!(
            kind, "synth",
            "oracle_synth_gate: unknown query kind {kind:?} for {id}"
        );
        // Determinism constraint (global constraints § Determinism):
        // records the oracle answered close to its own `maxHeartbeats`
        // are recorded but excluded — their verdict could flip on an
        // unrelated performance change. See `dump_synth.lean`'s header
        // for how the flag is computed.
        if q["near_budget"].as_bool().unwrap_or(false) {
            skipped_near_budget.push(id.to_string());
            continue;
        }
        if let Some((_, why)) = SEAM_EXCLUSIONS.iter().find(|(k, _)| *k == id) {
            skipped_seam.push(format!("{id}: {why}"));
            continue;
        }

        // A fresh EnvView/Store/MetaCtx per query: queries must be
        // independent (caching across queries would make failures
        // order-dependent) — the same contract point `oracle_fast.rs`
        // states, and a sharper one here since synthesis has its own
        // table/answer cache.
        let view: EnvView = env.view();
        let base = Some(view.store);
        let mut scratch = Store::scratch();
        let mut fv = HashMap::new();
        let mut mv: HashMap<u64, NameId> = HashMap::new();
        let goal = decode_expr(&mut scratch, base, &q["goal"], &mut fv, &mut mv);
        // Goal-mvar TYPES come from the record's own `mvars` array (the
        // canonical expr scheme has no mvar-type field, and unlike
        // `oracle_fast.rs`'s `defeq_mvar` arm there is no structurally
        // parallel side to re-derive them from) — see `dump_synth.lean`'s
        // header. Decoded here, before `ctx` takes `scratch` by `&mut`.
        let mvar_decls: Vec<(u64, ExprId)> = q["mvars"]
            .as_array()
            .expect("mvars field")
            .iter()
            .map(|m| {
                let i = m["i"].as_u64().expect("mvars[].i field");
                let ty = decode_expr(&mut scratch, base, &m["t"], &mut fv, &mut mv);
                (i, ty)
            })
            .collect();

        let mut ctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            &reducibility,
            &matchers,
            &instances,
            &default_instances,
            &projection_fns,
        );
        // DECLARE every goal mvar (ledger note, task B6): `decode_expr`
        // interns an mvar node but never declares it, and an undeclared
        // mvar makes `synth_pending` raise `MetaError::MVar` rather than
        // behaving like an ordinary unassigned metavariable. The
        // transparency/config the search runs under is NOT set here:
        // `synth_instance` installs the oracle's own `withConfig`
        // wrapper itself (`synth.rs::synth_instance_main`), so the gate
        // must pass `Config::default()` and let it do that — mirroring
        // `synthInstanceCore?`, which likewise ignores the ambient
        // config.
        let mut decl_failed = false;
        for (idx, ty) in mvar_decls {
            let Some(&nid) = mv.get(&idx) else {
                failures.push(format!(
                    "{id}: mvars[].i={idx} does not name a decoded mvar from `goal`"
                ));
                decl_failed = true;
                continue;
            };
            if ctx.mctx().decl(MVarId(nid)).is_some() {
                continue;
            }
            ctx.mctx_mut().declare(
                MVarId(nid),
                MVarDecl {
                    user_name: None,
                    ty,
                    lctx: Default::default(),
                    kind: MVarKind::Natural,
                },
            );
        }
        if decl_failed {
            continue;
        }

        let result = ctx.synth_instance(goal);
        // `synth_instance` returns a term already instantiated and
        // mvar-free on the expr side EXCEPT for mvars that came in with
        // the goal (`mvarGoal/synth/0`'s answer mentions `?0`), so a
        // final `instantiate_mvars` is still the honest thing to encode.
        let result = match result {
            Ok(Some(v)) => match ctx.instantiate_mvars(v) {
                Ok(v) => Ok(Some(v)),
                Err(e) => {
                    failures.push(format!(
                        "{id}: instantiate_mvars on the answer errored: {e:?}"
                    ));
                    continue;
                }
            },
            Ok(None) => Ok(None),
            Err(e) => Err(e),
        };
        // End the mutable borrow of `scratch` before reading it back.
        drop(ctx);

        let want_ok = q["ok"].as_bool().expect("ok field");
        match result {
            Err(e) => {
                failures.push(format!(
                    "{id}: leanr errored: {e:?}; oracle ok={want_ok} val={}",
                    q["val"]
                ));
            }
            Ok(got) => {
                compared += 1;
                if got.is_some() != want_ok {
                    failures.push(format!(
                        "{id}: leanr ok={} oracle ok={want_ok}",
                        got.is_some()
                    ));
                    continue;
                }
                let Some(val) = got else { continue };
                // Same `EncSt` threading as the dumper: seed the
                // numbering state by encoding `goal` FIRST (which also
                // round-trip-checks the decode against the committed
                // `goal`), then encode the answer with that SAME state
                // before comparing to `val`. A fresh state per answer
                // would renumber `mvarGoal/synth/0`'s `?0` independently
                // and could silently agree for the wrong reason.
                let mut est = EncSt::default();
                let goal_reencoded = encode_expr(&scratch, base, goal, &mut est);
                if goal_reencoded != q["goal"] {
                    failures.push(format!(
                        "{id}: re-encoded `goal` does not round-trip: got={goal_reencoded} \
                         original={}",
                        q["goal"]
                    ));
                    continue;
                }
                let got_val = encode_expr(&scratch, base, val, &mut est);
                let want_val = &q["val"];
                if &got_val != want_val {
                    failures.push(format!("{id}: leanr val={got_val} oracle val={want_val}"));
                }
            }
        }
    }

    assert!(
        failures.is_empty(),
        "{} divergences:\n{}\n(skipped `exc` records: {:?}; skipped near-budget: {:?}; \
         seam-excluded: {:?})",
        failures.len(),
        failures.join("\n"),
        skipped_exc,
        skipped_near_budget,
        skipped_seam
    );
    // Every declared seam exclusion must correspond to a record that is
    // actually PRESENT in the corpus — otherwise a stale entry here
    // would silently keep excluding a query id that no longer exists (or
    // was renamed), which is the same failure mode as dropping it.
    assert_eq!(
        skipped_seam.len(),
        SEAM_EXCLUSIONS.len(),
        "every SEAM_EXCLUSIONS entry must match exactly one committed record; matched: \
         {skipped_seam:?}"
    );
    // A gate that silently stopped asking is worse than no gate: pin the
    // number of records actually COMPARED, so deleting or `exc`-ing a
    // curated query fails here instead of quietly shrinking the corpus.
    assert_eq!(
        compared, 13,
        "expected 13 compared synthesis records (skipped `exc`: {skipped_exc:?}; \
         skipped near-budget: {skipped_near_budget:?}; seam-excluded: \
         {skipped_seam:?}) — if the curated list in dump_synth.lean grew or shrank \
         deliberately, update this count"
    );
}

/// Pins what leanr ACTUALLY does on the one seam-excluded record
/// (`SEAM_EXCLUSIONS`'s `mvarGoal/synth/0`), so the exclusion above is a
/// documented, bounded divergence rather than an unexamined hole:
///
/// 1. leanr returns `Ok(None)` — INCOMPLETENESS (a refused answer),
///    never a wrong instance and never an unsoundness. If this ever
///    starts producing `Ok(Some(_))`, the term it produces has to be
///    checked against the oracle's `instOfNN ?n`, and the exclusion
///    removed; this assertion is what forces that conversation.
/// 2. It is NOT an `Err`. In particular the goal metavariable IS
///    declared by the gate before the call (task-B6 ledger note:
///    `decode_expr` interns an mvar node without declaring it, and
///    `synth_pending` raises `MetaError::MVar` on an undeclared one), so
///    the search really did run — instrumenting the engine confirmed it
///    reaches `wake_up` with a resolved candidate and rejects the answer
///    only at the `num_mvars() == 0` root check.
#[test]
fn seam_excluded_mvar_goal_is_incompleteness_not_an_error() {
    let support::Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
    } = replay_fixture("Synth0.olean");
    let queries =
        std::fs::read_to_string(fixture("synth-queries.jsonl")).expect("committed queries");
    let mut seen = 0usize;
    for line in queries.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("committed JSONL is valid");
        if q["id"].as_str() != Some("mvarGoal/synth/0") {
            continue;
        }
        seen += 1;
        // The corpus still records the ORACLE's answer, untouched.
        assert_eq!(q["ok"].as_bool(), Some(true));
        assert_eq!(q["val"]["f"]["n"].as_str(), Some("instOfNN"));

        let view: EnvView = env.view();
        let base = Some(view.store);
        let mut scratch = Store::scratch();
        let mut fv = HashMap::new();
        let mut mv: HashMap<u64, NameId> = HashMap::new();
        let goal = decode_expr(&mut scratch, base, &q["goal"], &mut fv, &mut mv);
        let ty = decode_expr(&mut scratch, base, &q["mvars"][0]["t"], &mut fv, &mut mv);
        let idx = q["mvars"][0]["i"].as_u64().expect("mvars[0].i");
        let nid = mv[&idx];
        let mut ctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            &reducibility,
            &matchers,
            &instances,
            &default_instances,
            &projection_fns,
        );
        ctx.mctx_mut().declare(
            MVarId(nid),
            MVarDecl {
                user_name: None,
                ty,
                lctx: Default::default(),
                kind: MVarKind::Natural,
            },
        );
        let got = ctx.synth_instance(goal);
        assert!(
            matches!(got, Ok(None)),
            "seam behavior changed: leanr now answers {got:?} for `OfN ?n N` (oracle: \
             `some (instOfNN ?n)`). Re-examine SEAM_EXCLUSIONS — if the mctx-depth seam \
             closed, DELETE the exclusion and let the gate compare the term."
        );
    }
    assert_eq!(seen, 1, "mvarGoal/synth/0 must be present in the corpus");
}

/// Sibling of `seam_excluded_mvar_goal_is_incompleteness_not_an_error`,
/// but for the `exc` record (`stuck/synth/0`, `Add ?a` with `?a : Type`
/// minted OUTSIDE the search) rather than a `SEAM_EXCLUSIONS` entry —
/// `oracle_synth_gate` above SKIPS `exc` records outright (there is no
/// oracle verdict to agree with), which means nothing today pins what
/// leanr itself does there. Without this test, closing the
/// `isDefEqStuckEx` seam (giving this crate a `Config` field for it plus
/// an mctx-depth model) could silently change leanr's answer with
/// nothing failing.
///
/// THIS TEST PINS CURRENT, DIVERGENT BEHAVIOR — it is not a correctness
/// claim. The oracle THROWS `isDefEqStuckException` on this exact goal:
/// `synthInstanceCore?` runs `SynthInstance.main` under
/// `withNewMCtxDepth` with `isDefEqStuckEx := true`
/// (`SynthInstance.lean:963`), so the first unification against the
/// lower-depth `?a` throws instead of assigning
/// (`SynthInstance.lean:1052`). leanr has neither `isDefEqStuckEx` nor a
/// depth model (same gap `SEAM_EXCLUSIONS`'s `mvarGoal/synth/0` entry and
/// `synth.rs::synth_instance_main`'s own comment document), so it simply
/// assigns `?a := N` and answers `instAddN`.
///
/// When the `isDefEqStuckEx` seam is closed, THIS TEST MUST BE UPDATED
/// to expect stuck-not-an-answer (`Err` carrying whatever this crate's
/// analogue of `isDefEqStuckException` becomes, once one exists) rather
/// than `Ok(Some(instAddN))` — the failure message below says so.
#[test]
fn exc_record_stuck_synth_0_pins_leanrs_current_divergent_answer() {
    let support::Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
    } = replay_fixture("Synth0.olean");
    let queries =
        std::fs::read_to_string(fixture("synth-queries.jsonl")).expect("committed queries");
    let mut seen = 0usize;
    for line in queries.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("committed JSONL is valid");
        if q["id"].as_str() != Some("stuck/synth/0") {
            continue;
        }
        seen += 1;
        // The corpus records that the ORACLE did not answer cleanly —
        // this is an `exc` record, not a verdict to agree with.
        assert_eq!(q["q"].as_str(), Some("exc"));
        assert_eq!(q["msg"].as_str(), Some("internal exception #7"));

        let view: EnvView = env.view();
        let base = Some(view.store);
        let mut scratch = Store::scratch();
        let mut fv = HashMap::new();
        let mut mv: HashMap<u64, NameId> = HashMap::new();
        let goal = decode_expr(&mut scratch, base, &q["goal"], &mut fv, &mut mv);
        let ty = decode_expr(&mut scratch, base, &q["mvars"][0]["t"], &mut fv, &mut mv);
        let idx = q["mvars"][0]["i"].as_u64().expect("mvars[0].i");
        let nid = mv[&idx];
        let mut ctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            &reducibility,
            &matchers,
            &instances,
            &default_instances,
            &projection_fns,
        );
        ctx.mctx_mut().declare(
            MVarId(nid),
            MVarDecl {
                user_name: None,
                ty,
                lctx: Default::default(),
                kind: MVarKind::Natural,
            },
        );
        let got = ctx.synth_instance(goal);
        let got = match got {
            Ok(Some(v)) => match ctx.instantiate_mvars(v) {
                Ok(v) => Ok(Some(v)),
                Err(e) => panic!(
                    "{}: instantiate_mvars on the answer errored: {e:?}",
                    q["id"]
                ),
            },
            other => other,
        };
        drop(ctx);
        let got_name = match got {
            Ok(Some(v)) => {
                let mut est = EncSt::default();
                let goal_reencoded = encode_expr(&scratch, base, goal, &mut est);
                assert_eq!(
                    goal_reencoded, q["goal"],
                    "stuck/synth/0: re-encoded `goal` does not round-trip"
                );
                let got_val = encode_expr(&scratch, base, v, &mut est);
                got_val["n"].as_str().map(str::to_string)
            }
            _ => None,
        };
        assert_eq!(
            (got.is_ok(), got_name.as_deref()),
            (true, Some("instAddN")),
            "leanr's answer for `Add ?a` (`stuck/synth/0`) changed to {got:?}/{got_name:?} — \
             this test PINS the CURRENT DIVERGENT behavior (oracle throws \
             isDefEqStuckException here: SynthInstance.lean:963 `isDefEqStuckEx := true`, \
             :1052 where the stuck unification actually throws). If this changed because the \
             `isDefEqStuckEx` seam closed, UPDATE this test to expect stuck-not-an-answer \
             instead of silently accepting whatever leanr now returns."
        );
    }
    assert_eq!(seen, 1, "stuck/synth/0 must be present in the corpus");
}
