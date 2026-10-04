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

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId, Store};
use leanr_kernel::{BinderInfo, EnvView};
use leanr_meta::{
    Config, EnvExtensions, LOption, LocalCtxSnapshot, MVarDecl, MVarId, MVarKind, MetaCtx,
    MetaError,
};

mod support;
use support::{decode_expr, encode_expr, fixture, replay_fixture, synth_name, EncSt};

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
// `mvarGoal/synth/0` (`OfN ?n N`) was the one entry. It closed in
// synth-real-depth Task 1: under real depth `abstract_mvars` leaves the
// caller's lower-depth `?n` alone (`AbstractMVars.lean:89-93`), so the
// answer `instOfNN ?n` passes `wake_up`'s root check, as in the oracle.
const SEAM_EXCLUSIONS: &[(&str, &str)] = &[];

#[test]
fn oracle_synth_gate() {
    let support::Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
        classes,
        coe_decls,
        aux_recs,
        elab_as_elim,
        ..
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
        // minted OUTSIDE the search): the oracle's search runs under
        // `withNewMCtxDepth` with `isDefEqStuckEx := true`
        // (`SynthInstance.lean:963`, `:978`) and its first unification
        // throws `isDefEqStuck`. leanr now throws `IsDefEqStuck` there
        // too — `exc_record_stuck_synth_0_is_stuck_in_leanr_too` pins it.
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
        // `ctx` is constructed BEFORE `goal`/`mvars` are decoded (unlike
        // `oracle_fast.rs`'s parallel gate) because the local context the
        // goal is asked in (`fvars`, local-instances slice, below) must be
        // pushed before `goal` is decoded, and pushing it needs `ctx`.
        // `decode_expr` reborrows `scratch` via `ctx.store_mut()` from
        // here on instead of taking it directly, since `ctx` now holds
        // the exclusive `&mut Store` for the rest of this query.
        let mut ctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            EnvExtensions {
                reducibility: &reducibility,
                matchers: &matchers,
                instances: &instances,
                default_instances: &default_instances,
                projection_fns: &projection_fns,
                classes: &classes,
                coe_decls: &coe_decls,
                aux_recs: &aux_recs,
                elab_as_elim: &elab_as_elim,
                structures: &[],
            },
        );
        // The local context the goal is asked in (local-instances
        // slice). Pushed BEFORE `goal` is decoded, and seeded into `fv`,
        // so the goal's own `{"k":"fvar","i":N}` references resolve to
        // declarations that really exist rather than to freshly interned
        // dangling names. Ascending by `i`, because entry `i`'s type may
        // mention any earlier entry.
        //
        // These go through `push_local_decl`/`push_let_decl` — the very
        // chokepoints that install local instances — so the fixture's
        // local context IS the producer under test. There is no
        // test-only path that could install an instance a real run
        // would not.
        let empty_fvars = Vec::new();
        let fvar_specs = q
            .get("fvars")
            .and_then(|v| v.as_array())
            .unwrap_or(&empty_fvars);
        let lctx_cp = ctx.lctx_checkpoint();
        for spec in fvar_specs {
            let idx = spec["i"].as_u64().expect("fvars[].i field");
            let ty = decode_expr(ctx.store_mut(), base, &spec["t"], &mut fv, &mut mv);
            let bi = match spec["bi"].as_str().expect("fvars[].bi field") {
                "default" => BinderInfo::Default,
                "implicit" => BinderInfo::Implicit,
                "strictImplicit" => BinderInfo::StrictImplicit,
                "instImplicit" => BinderInfo::InstImplicit,
                other => panic!("{id}: unknown binder info {other:?}"),
            };
            let name = synth_name(ctx.store_mut(), base, "#f", idx);
            let fvar = match spec.get("v") {
                None => ctx
                    .push_local_decl(Some(name), ty, bi)
                    .unwrap_or_else(|e| panic!("{id}: push_local_decl: {e:?}")),
                Some(v) => {
                    let value = decode_expr(ctx.store_mut(), base, v, &mut fv, &mut mv);
                    // The corpus's fvar spec carries no `nondep` bit
                    // (`dump_synth.lean`'s `fvars` schema), so every
                    // corpus ldecl is a `let`.
                    ctx.push_let_decl(Some(name), ty, value, false)
                        .unwrap_or_else(|e| panic!("{id}: push_let_decl: {e:?}"))
                }
            };
            let nid = match ctx.store().expr_node(base, fvar) {
                Node::FVar { id: Some(id) } => id,
                other => panic!("{id}: push returned a non-fvar {other:?}"),
            };
            // Seed the decode map so `goal` resolves index -> this decl.
            let previous = fv.insert(idx, nid);
            assert!(
                previous.is_none(),
                "{id}: fvars[].i={idx} is declared twice, or `goal` was \
                 decoded before the context was pushed"
            );
        }
        let goal = decode_expr(ctx.store_mut(), base, &q["goal"], &mut fv, &mut mv);
        // Goal-mvar TYPES come from the record's own `mvars` array (the
        // canonical expr scheme has no mvar-type field, and unlike
        // `oracle_fast.rs`'s `defeq_mvar` arm there is no structurally
        // parallel side to re-derive them from) — see `dump_synth.lean`'s
        // header.
        let mvar_decls: Vec<(u64, ExprId)> = q["mvars"]
            .as_array()
            .expect("mvars field")
            .iter()
            .map(|m| {
                let i = m["i"].as_u64().expect("mvars[].i field");
                let ty = decode_expr(ctx.store_mut(), base, &m["t"], &mut fv, &mut mv);
                (i, ty)
            })
            .collect();

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
        // Canonical index -> `NameId`, in declaration order, so the
        // post-synthesis `assigns` gate below can re-derive each goal
        // mvar's `ExprId` without re-decoding `mvars` a second time.
        let mut declared_mvars: Vec<(u64, NameId)> = Vec::new();
        for (idx, ty) in mvar_decls {
            let Some(&nid) = mv.get(&idx) else {
                failures.push(format!(
                    "{id}: mvars[].i={idx} does not name a decoded mvar from `goal`"
                ));
                decl_failed = true;
                continue;
            };
            declared_mvars.push((idx, nid));
            if ctx.mctx().decl(MVarId(nid)).is_some() {
                continue;
            }
            // `LocalCtxSnapshot::empty()` is a STANDING ASSUMPTION, not
            // a neutral default: `synth_pending` and friends reach a
            // goal mvar through `with_mvar_context`, which installs this
            // snapshot's `lctx` AND its local instances as the ambient
            // ones. For a record that declares `fvars`, an empty
            // snapshot means the nested synthesis runs with the
            // fixture's local context — and therefore its local
            // instances — thrown away, silently answering against a
            // strictly smaller instance set than the oracle's.
            //
            // No committed record combines `fvars` with `mvars`, so this
            // is unreachable today; the assertion below is what keeps it
            // that way. The first record that needs both must give each
            // goal mvar a real context (`ctx.current_lctx()` is the
            // ambient one at this point, and is the right starting
            // answer only if the oracle really asked that mvar in the
            // full fixture context — the dump carries no per-mvar
            // `lctx` field to check that against, so it is a decision
            // for that slice, not a default to fall into).
            assert!(
                fvar_specs.is_empty(),
                "{id}: this record declares both `fvars` and `mvars`, and the \
                 gate declares every goal mvar with an EMPTY local context — \
                 so the fixture's local instances would be invisible to any \
                 nested synthesis. Give the mvar a real `lctx` before adding \
                 this record."
            );
            ctx.mctx_mut().declare(
                MVarId(nid),
                MVarDecl {
                    user_name: None,
                    ty,
                    lctx: LocalCtxSnapshot::empty(),
                    kind: MVarKind::Natural,
                    num_scope_args: 0,
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
        // Post-synthesis state of every goal mvar, in the record's own
        // index order. `assignment` is `mctx`'s existing accessor
        // (`mvar_ctx.rs:91`); an unassigned mvar contributes nothing,
        // matching the dumper.
        let mut assigned: Vec<(u64, ExprId)> = Vec::new();
        for (idx, nid) in &declared_mvars {
            if ctx.mctx().assignment(MVarId(*nid)).is_none() {
                continue;
            }
            let m = ctx
                .store_mut()
                .expr_mvar(base, Some(*nid))
                .expect("intern mvar");
            match ctx.instantiate_mvars(m) {
                Ok(v) => assigned.push((*idx, v)),
                Err(e) => {
                    failures.push(format!("{id}: instantiate_mvars on goal mvar {idx}: {e:?}"));
                }
            }
        }
        assigned.sort_by_key(|(i, _)| *i);
        // Undo the `fvars` push above before the next iteration reuses
        // this `MetaCtx`'s local-name/lctx bookkeeping — queries must
        // stay independent (same contract this loop already states for
        // `view`/`Store`/`MetaCtx` themselves).
        ctx.lctx_restore(lctx_cp);
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
                // `got` is `None` here exactly when `ok:false`, and this
                // `continue` skips `assigns` entirely for such records —
                // deliberately: the one committed `ok:false` outParam
                // record has a ground goal with no mvars, so there is
                // nothing for `assigns` to say, and `is_def_eq` rolls
                // back on both its `Ok(false)` and `Err` arms, so leanr
                // cannot have left a spurious assignment on a goal mvar
                // for a failed synthesis anyway. If a future `ok:false`
                // record ever DOES mention a goal mvar, this arm would
                // need to compare `assigns` too.
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
                // `assigns`: the post-synthesis state of every goal
                // mvar. Comparing it is what makes M4b-3 P2b-i's
                // `assignOutParams` visible at all — `ok` and `val` are
                // identical whether or not the caller's output parameter
                // was assigned, and so is the term the gate compares.
                //
                // Encoded BEFORE `val`, pinning the invariant this gate
                // must keep against `dump_synth.lean`'s own `EncSt`
                // threading: the dumper encodes `goal` (`st0`), folds
                // `mvars[].t` to reach `st1`, then encodes BOTH `assigns`
                // and `val` off that SAME `st1` as siblings (`val` via
                // `.run' st1`, `assignsJ` via its own fold starting at
                // `st1`) — neither one's numbering leaks into the other.
                // Encoding `got_val` first and only then `got_assigns`
                // off the state `got_val` already advanced would make
                // `assigns` see numbering `val` introduced, which the
                // dumper's side never does; every committed `assigns`
                // value is ground today, so that ordering bug is
                // currently invisible, not absent.
                let mut got_assigns = Vec::new();
                for (idx, v) in assigned.iter() {
                    got_assigns.push(serde_json::json!({
                        "i": idx,
                        "e": encode_expr(&scratch, base, *v, &mut est),
                    }));
                }
                let want_assigns = q["assigns"].as_array().cloned().unwrap_or_default();
                if got_assigns != want_assigns {
                    failures.push(format!(
                        "{id}: leanr assigns={got_assigns:?} oracle assigns={want_assigns:?}"
                    ));
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
        compared, 39,
        "expected 39 compared synthesis records (38 -> 39: synth-real-depth Task 3 added noInstMVar/synth/0; 37 -> 38: synth-real-depth Task 1 closed the mvarGoal/synth/0 seam exclusion; skipped `exc`: {skipped_exc:?}; \
         skipped near-budget: {skipped_near_budget:?}; seam-excluded: \
         {skipped_seam:?}) — if the curated list in dump_synth.lean grew or shrank \
         deliberately, update this count; M4b-3 P4 task 1 added the six coe* records, \
         local-instances task 1 added `fvarCtx/synth/0`, local-instances task 8 added the \
         five differential records (`noInstLocal`, `localBeatsGlobal`, `letLocal`, \
         `noInstParamLocal`, `nonClassFvar`), synth pi-goals task 3 added the seven `pi*` \
         records"
    );
}

/// Replays `Synth0.olean`, finds the committed record `id`, decodes its
/// `goal`, and DECLARES its first goal mvar at depth 0 before handing the
/// context to `f` (`decode_expr` interns mvar nodes without declaring
/// them, and an undeclared mvar is not one the search can reason about).
fn with_synth0_record<R>(
    id: &str,
    f: impl FnOnce(&mut MetaCtx<'_>, &serde_json::Value, ExprId, MVarId) -> R,
) -> R {
    let support::Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
        classes,
        coe_decls,
        aux_recs,
        elab_as_elim,
        ..
    } = replay_fixture("Synth0.olean");
    let queries =
        std::fs::read_to_string(fixture("synth-queries.jsonl")).expect("committed queries");
    let q: serde_json::Value = queries
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str::<serde_json::Value>(l).expect("valid JSONL"))
        .find(|q| q["id"].as_str() == Some(id))
        .unwrap_or_else(|| panic!("{id} must be present in the corpus"));
    let view: EnvView = env.view();
    let base = Some(view.store);
    let mut scratch = Store::scratch();
    let mut fv = HashMap::new();
    let mut mv: HashMap<u64, NameId> = HashMap::new();
    let goal = decode_expr(&mut scratch, base, &q["goal"], &mut fv, &mut mv);
    let ty = decode_expr(&mut scratch, base, &q["mvars"][0]["t"], &mut fv, &mut mv);
    let nid = mv[&q["mvars"][0]["i"].as_u64().expect("mvars[0].i")];
    let mut ctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        EnvExtensions {
            reducibility: &reducibility,
            matchers: &matchers,
            instances: &instances,
            default_instances: &default_instances,
            projection_fns: &projection_fns,
            classes: &classes,
            coe_decls: &coe_decls,
            aux_recs: &aux_recs,
            elab_as_elim: &elab_as_elim,
            structures: &[],
        },
    );
    ctx.mctx_mut().declare(
        MVarId(nid),
        MVarDecl {
            user_name: None,
            ty,
            lctx: LocalCtxSnapshot::empty(),
            kind: MVarKind::Natural,
            num_scope_args: 0,
        },
    );
    f(&mut ctx, &q, goal, MVarId(nid))
}

/// `stuck/synth/0` (`Add ?a`, `?a : Type` minted OUTSIDE the search) is
/// an `exc` record: the oracle throws `isDefEqStuck`
/// (`SynthInstance.lean:963` sets `isDefEqStuckEx`; the throw is
/// `ExprDefEq.lean:1952-1956`). The gate skips `exc` records, so this
/// test is what pins leanr's side: the same `IsDefEqStuck`, with `?a`
/// left unassigned.
#[test]
fn exc_record_stuck_synth_0_is_stuck_in_leanr_too() {
    with_synth0_record("stuck/synth/0", |ctx, q, goal, a| {
        assert_eq!(q["q"].as_str(), Some("exc"));
        assert_eq!(q["msg"].as_str(), Some("internal exception #7"));
        assert_eq!(ctx.synth_instance(goal), Err(MetaError::IsDefEqStuck));
        assert!(!ctx.mctx().is_assigned(a));
    });
}

/// Residue 3 of synth-real-depth: `NoInst ?a` with ZERO candidates. The
/// oracle's `synthInstance?` answers `none` (`"ok":false` in the corpus):
/// with no candidate, no unification runs and nothing gets stuck. So
/// `trySynthInstance` (`SynthInstance.lean:1014-1017`) is `.none`, not
/// `.undef`. The old syntactic pre-test answered `Undef` here.
#[test]
fn no_inst_mvar_goal_is_none_not_undef() {
    with_synth0_record("noInstMVar/synth/0", |ctx, q, goal, _a| {
        assert_eq!(q["ok"].as_bool(), Some(false));
        assert_eq!(ctx.try_synth_instance(goal), Ok(LOption::None));
    });
}
