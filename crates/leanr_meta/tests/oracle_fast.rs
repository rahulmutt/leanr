//! Tier-1 differential gate (plan-2 spec § The gate): every committed
//! query must agree with the oracle byte-for-byte after
//! canonicalization. Hermetic — the committed .olean and .jsonl are
//! the entire input; CI never installs Lean (docs/ORACLE.md).
//!
//! This is a REGRESSION gate: "nothing that used to agree now
//! disagrees." Discovery at Mathlib scale is plan 4's nightly.
//!
//! The canonical JSON scheme this gate decodes/encodes is documented in
//! `tests/fixtures/meta/dump_defeq.lean`'s module header (the
//! authoritative counterpart); its Rust implementation
//! (`decode_expr`/`encode_expr`/`EncSt`/`transparency_of`) lives in
//! `tests/support/mod.rs`, shared with `oracle_synth.rs`.

use std::collections::HashMap;

use leanr_kernel::bank::{ExprId, NameId, Store};
use leanr_kernel::EnvView;
use leanr_meta::{Config, MVarDecl, MVarId, MVarKind, MetaCtx};
use serde_json::{json, Value};

// The canonical-scheme decode/encode helpers (`decode_expr`/
// `encode_expr`/`EncSt`/`transparency_of`/`fixture`/`replay_fixture`)
// live in `tests/support/mod.rs` — extracted verbatim from this file by
// M4a plan-4 task B7 so `oracle_synth.rs` shares ONE implementation of
// the scheme with this gate rather than a copy that could drift.
mod support;
use support::{decode_expr, encode_expr, fixture, replay_fixture, transparency_of, EncSt};

/// profile -> config flags (mirrors `dump_defeq.lean::withProfile`):
/// `"approx"` turns the four false-defaulting `*_approx` flags on;
/// every other profile string (just `"default"` in the committed
/// corpus) leaves `Config::default()` untouched.
fn apply_profile(cfg: &mut Config, prof: &str) {
    if prof == "approx" {
        cfg.fo_approx = true;
        cfg.ctx_approx = true;
        cfg.quasi_pattern_approx = true;
        cfg.const_approx = true;
    }
}

/// Walk the RAW (pre-decode) `a`/`b` JSON trees of a `defeq_mvar`
/// record in parallel, collecting `(mvar canonical index, the
/// CORRESPONDING subtree of `b`)` wherever `a` is `{"k":"mvar",...}`.
/// The dumper's own construction (`dump_defeq.lean`'s new
/// `defeqMvarQueries` loop) guarantees `a` and `b` are structurally
/// IDENTICAL everywhere except at the one substituted argument
/// position, so this always finds exactly the site(s) that need a
/// declaration. This is the gate's stand-in for the dumper's own
/// `mkFreshExprMVar (← inferType arg)`: the canonical JSON scheme
/// (`dump_defeq.lean`'s module header) carries no explicit mvar-type
/// field, so the gate must re-derive "what type was this mvar created
/// at" from the shape of the untouched `b` side instead.
fn json_mvar_types<'a>(a: &'a Value, b: &'a Value, out: &mut Vec<(u64, &'a Value)>) {
    if a["k"].as_str() == Some("mvar") {
        if let Some(i) = a["i"].as_u64() {
            out.push((i, b));
        }
        return;
    }
    match a["k"].as_str() {
        Some("app") => {
            json_mvar_types(&a["f"], &b["f"], out);
            json_mvar_types(&a["a"], &b["a"], out);
        }
        Some("lam") | Some("pi") => {
            json_mvar_types(&a["t"], &b["t"], out);
            json_mvar_types(&a["b"], &b["b"], out);
        }
        Some("let") => {
            json_mvar_types(&a["t"], &b["t"], out);
            json_mvar_types(&a["v"], &b["v"], out);
            json_mvar_types(&a["b"], &b["b"], out);
        }
        Some("proj") => {
            json_mvar_types(&a["e"], &b["e"], out);
        }
        // Leaves (`sort`/`const`/`bvar`/`fvar`/`lit`/`str`) and any
        // shape mismatch not caused by a substituted mvar: nothing to
        // recurse into.
        _ => {}
    }
}

#[test]
fn oracle_fast_gate() {
    let support::Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
    } = replay_fixture("Meta0.olean");

    let queries =
        std::fs::read_to_string(fixture("meta-queries.jsonl")).expect("committed queries");
    let mut failures = Vec::new();
    for line in queries.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("committed JSONL is valid");
        let id = q["id"].as_str().expect("id field");
        let kind = q["q"].as_str().expect("q field");
        let tr = q["tr"].as_str().expect("tr field");

        // A fresh EnvView/Store/MetaCtx per query: queries must be
        // independent (caching across queries would make failures
        // order-dependent) — controller-mandated contract point.
        let view: EnvView = env.view();
        let base = Some(view.store);

        // `defeq_mvar` records (task 5): like `defeq`, but the gate
        // must ALSO compare the recorded assignments — "not verdict-
        // only" (the brief's own words). Own branch, same reasons as
        // `defeq`'s below.
        if kind == "defeq_mvar" {
            let prof = q["prof"].as_str().expect("prof field");
            let mut scratch = Store::scratch();
            let mut fv = HashMap::new();
            let mut mv: HashMap<u64, NameId> = HashMap::new();
            let a = decode_expr(&mut scratch, base, &q["a"], &mut fv, &mut mv);
            let b = decode_expr(&mut scratch, base, &q["b"], &mut fv, &mut mv);
            // Decode each undeclared mvar's "type source" fragment
            // (`json_mvar_types`'s own doc comment) NOW, while `scratch`
            // is still directly reachable — `ctx` will hold it by
            // `&mut` from here on, and `infer_type` (needed to turn a
            // type-source fragment into an actual type) is only
            // reachable through `ctx` once it exists.
            let mut mvar_type_sources: Vec<(u64, ExprId)> = Vec::new();
            let mut pairs: Vec<(u64, &Value)> = Vec::new();
            json_mvar_types(&q["a"], &q["b"], &mut pairs);
            for (idx, b_json) in pairs {
                let ty_source = decode_expr(&mut scratch, base, b_json, &mut fv, &mut mv);
                mvar_type_sources.push((idx, ty_source));
            }
            let mut cfg = Config {
                transparency: transparency_of(tr),
                ..Config::default()
            };
            apply_profile(&mut cfg, prof);
            let mut ctx = MetaCtx::new(
                view,
                &mut scratch,
                cfg,
                &reducibility,
                &matchers,
                &instances,
                &default_instances,
                &projection_fns,
            );
            // Declare every mvar `a` introduced (unlike `whnf`/`infer`/
            // `defeq`, `decode_expr` alone never declares an mvar into
            // `ctx.mctx()` — no prior query kind ever needed it to be
            // ASSIGNABLE, only comparable) — the gate's stand-in for the
            // dumper's own `mkFreshExprMVar (← inferType arg)`.
            let mut decl_failed = false;
            for (idx, ty_source) in mvar_type_sources {
                let Some(&nid) = mv.get(&idx) else { continue };
                let mid = MVarId(nid);
                if ctx.mctx().decl(mid).is_some() {
                    continue;
                }
                match ctx.infer_type(ty_source) {
                    Ok(ty) => {
                        ctx.mctx_mut().declare(
                            mid,
                            MVarDecl {
                                user_name: None,
                                ty,
                                lctx: Default::default(),
                                kind: MVarKind::Natural,
                            },
                        );
                    }
                    Err(e) => {
                        failures.push(format!(
                            "{id} (tr={tr},prof={prof}): could not infer a type to declare \
                             mvar {idx} ({e:?})"
                        ));
                        decl_failed = true;
                    }
                }
            }
            if decl_failed {
                continue;
            }
            // Collect `(canonical index, instantiated assignment)` pairs
            // while `ctx` is still alive (it holds `scratch` by `&mut`,
            // so no encoding can happen until it is dropped) — the
            // encoding pass runs afterward, once `scratch` is free
            // again, mirroring `oracle_fast_gate`'s own `whnf`/`infer`
            // arm below (`drop(ctx)` before `encode_expr`).
            let mut assign_results: Vec<Result<(u64, ExprId), String>> = Vec::new();
            let verdict = ctx.is_def_eq(a, b);
            if let Ok(true) = verdict {
                let want_assign = q["assign"].as_array().expect("assign field").clone();
                for entry in &want_assign {
                    let m = entry["m"].as_u64().expect("assign.m field");
                    let Some(&nid) = mv.get(&m) else {
                        assign_results.push(Err(format!(
                            "assign.m={m} does not name a decoded mvar from a/b"
                        )));
                        continue;
                    };
                    let Some(assigned) = ctx.mctx().assignment(MVarId(nid)) else {
                        assign_results.push(Err(format!(
                            "mvar {m} was never assigned (oracle assigned it)"
                        )));
                        continue;
                    };
                    match ctx.instantiate_mvars(assigned) {
                        Ok(v) => assign_results.push(Ok((m, v))),
                        Err(e) => {
                            assign_results.push(Err(format!("instantiate_mvars errored: {e:?}")))
                        }
                    }
                }
            }
            drop(ctx);

            match verdict {
                Ok(got) => {
                    let want = q["eq"].as_bool().expect("eq field");
                    if got != want {
                        failures.push(format!(
                            "{id} (tr={tr},prof={prof}): leanr={got} oracle={want}"
                        ));
                        continue;
                    }
                    if !got {
                        // No assignment to compare when the verdict
                        // itself is `false` — the committed `assign`
                        // array is empty in that case too (the dumper
                        // only reads back an assignment when `eqR` was
                        // `true`).
                        continue;
                    }
                    let want_assign = q["assign"].as_array().expect("assign field");
                    // Same threading as the dumper's `emitDefeqMvar` call
                    // site: seed `EncSt` by encoding `a` then `b` (the
                    // decoded `a`/`b`, exactly what was just compared)
                    // before encoding each assigned value.
                    let mut est = EncSt::default();
                    encode_expr(&scratch, base, a, &mut est);
                    encode_expr(&scratch, base, b, &mut est);
                    for (entry, result) in want_assign.iter().zip(assign_results.iter()) {
                        let m = entry["m"].as_u64().expect("assign.m field");
                        let want_v = &entry["v"];
                        match result {
                            Ok((_, instantiated)) => {
                                let got_v = encode_expr(&scratch, base, *instantiated, &mut est);
                                if &got_v != want_v {
                                    failures.push(format!(
                                        "{id} (tr={tr},prof={prof}): mvar {m} assignment \
                                         leanr={got_v} oracle={want_v}"
                                    ));
                                }
                            }
                            Err(msg) => {
                                failures.push(format!("{id} (tr={tr},prof={prof}): {msg}"));
                            }
                        }
                    }
                }
                Err(e) => {
                    failures.push(format!("{id} (tr={tr},prof={prof}): leanr errored: {e:?}"))
                }
            }
            continue;
        }

        // `defeq` records carry `a`/`b`/`eq`/`prof`, not `in`/`out`, and
        // are gated with a config profile the `whnf`/`infer` records
        // never see — handled in its own branch, consuming `view` into
        // its own `MetaCtx` and `continue`ing so the `in`/`out` decode
        // below (which only `whnf`/`infer` need) never runs for it.
        if kind == "defeq" {
            let prof = q["prof"].as_str().expect("prof field");
            let mut scratch = Store::scratch();
            let mut fv = HashMap::new();
            let mut mv = HashMap::new();
            let a = decode_expr(&mut scratch, base, &q["a"], &mut fv, &mut mv);
            let b = decode_expr(&mut scratch, base, &q["b"], &mut fv, &mut mv);
            let mut cfg = Config {
                transparency: transparency_of(tr),
                ..Config::default()
            };
            apply_profile(&mut cfg, prof);
            let mut ctx = MetaCtx::new(
                view,
                &mut scratch,
                cfg,
                &reducibility,
                &matchers,
                &instances,
                &default_instances,
                &projection_fns,
            );
            match ctx.is_def_eq(a, b) {
                Ok(got) => {
                    let want = q["eq"].as_bool().expect("eq field");
                    if got != want {
                        failures.push(format!(
                            "{id} (tr={tr},prof={prof}): leanr={got} oracle={want}"
                        ));
                    }
                }
                Err(e) => {
                    failures.push(format!("{id} (tr={tr},prof={prof}): leanr errored: {e:?}"))
                }
            }
            continue;
        }

        let mut scratch = Store::scratch();
        let mut fvars = HashMap::new();
        let mut mvars = HashMap::new();
        let in_id = decode_expr(&mut scratch, base, &q["in"], &mut fvars, &mut mvars);

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
        ctx.set_transparency(transparency_of(tr));

        let result = match kind {
            "whnf" => ctx.whnf(in_id),
            "infer" => ctx.infer_type(in_id),
            other => panic!("oracle_fast_gate: unknown query kind {other:?} for {id}"),
        };
        let result = match result {
            Ok(r) => r,
            Err(e) => {
                failures.push(format!(
                    "{id} (tr={tr}): leanr errored: {e:?}; oracle out={}",
                    q["out"]
                ));
                continue;
            }
        };
        // End the mutable borrow of `scratch` before reading it back.
        drop(ctx);

        // Mirror `dump_defeq.lean`'s `encPair`: encode the decoded
        // `in` FIRST to seed the numbering state (this also doubles as
        // a round-trip check — re-encoding `in` must reproduce the
        // committed `in` byte-for-byte), then encode `result` with
        // that SAME (now-seeded) state before comparing to `out`. See
        // `EncSt`'s doc comment for why a fresh state per `result`
        // would be wrong.
        let mut est = EncSt::default();
        let in_reencoded = encode_expr(&scratch, base, in_id, &mut est);
        if in_reencoded != q["in"] {
            failures.push(format!(
                "{id} (tr={tr}): re-encoded `in` does not round-trip: got={in_reencoded} original={}",
                q["in"]
            ));
            continue;
        }
        let got = encode_expr(&scratch, base, result, &mut est);
        let want = &q["out"];
        if &got != want {
            failures.push(format!("{id} (tr={tr}): leanr={got} oracle={want}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} divergences:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// ===== helper self-check: the corpus never exercises fvar/mvar/lit/str,
// so this round-trips the scheme's remaining shapes directly against the
// store, independent of the committed fixture. =====
#[test]
fn decode_encode_roundtrip_covers_the_full_scheme() {
    let mut scratch = Store::scratch();
    let base: Option<&Store> = None;

    let mut fvars = HashMap::new();
    let mut mvars = HashMap::new();
    let src = json!({
        "k": "let",
        "t": {"k": "sort", "u": {"k": "succ", "u": {"k": "max", "a": {"k": "zero"}, "b": {"k": "param", "n": "u"}}}},
        "v": {
            "k": "app",
            "f": {
                "k": "lam",
                "bi": "i",
                "t": {
                    "k": "pi",
                    "bi": "c",
                    "t": {"k": "const", "n": "Foo.Bar", "us": [{"k": "imax", "a": {"k": "zero"}, "b": {"k": "param", "n": "v"}}]},
                    "b": {"k": "bvar", "i": 0},
                },
                "b": {"k": "mvar", "i": 0},
            },
            "a": {"k": "proj", "s": "Foo.Bar", "i": 2, "e": {"k": "str", "v": "hello"}},
        },
        "b": {"k": "app", "f": {"k": "fvar", "i": 0}, "a": {"k": "lit", "n": "123456789012345678901234567890"}},
        "nd": true,
    });
    let id = decode_expr(&mut scratch, base, &src, &mut fvars, &mut mvars);
    let mut est = EncSt::default();
    let back = encode_expr(&scratch, base, id, &mut est);
    assert_eq!(
        back, src,
        "decode/encode must round-trip the canonical scheme exactly"
    );
}

/// Pins the `encPair` threading contract `EncSt`'s doc comment
/// describes (dump_defeq.lean:155-158): encoding `in` and `out` shares
/// ONE numbering state, so an mvar/fvar appearing only in `out` gets
/// the NEXT index after every occurrence already numbered while
/// encoding `in` (never a fresh 0), while a value shared between `in`
/// and `out` keeps its `in`-side index. This is exactly the case that
/// would have caught the original bug (a fresh `EncSt` per `result`
/// instead of one threaded from `in`) — no committed record currently
/// has an out-only mvar/fvar, so that bug was otherwise silent.
#[test]
fn encode_threads_numbering_from_in_into_out_like_the_oracles_enc_pair() {
    // Constructed so a fresh-`EncSt`-per-`out` bug and the correct
    // threaded-from-`in` behavior produce DIFFERENT JSON, not just
    // coincidentally-equal output — see this test's own inline trace
    // for why a naive "in = single shared var" case would NOT have
    // caught the original bug.
    let mut scratch = Store::scratch();
    let base: Option<&Store> = None;
    let mut fvars = HashMap::new();
    let mut mvars = HashMap::new();

    // `in` = #f0 (fvar A, the only var in `in`).
    let in_src = json!({"k": "fvar", "i": 0});
    let in_id = decode_expr(&mut scratch, base, &in_src, &mut fvars, &mut mvars);

    // `out` = (?0 #f1) #f0 — `?0` (mvar M) and `#f1` (fvar B) are
    // OUT-ONLY; `#f0` (fvar A) is the SAME fvar shared with `in`, but
    // it occurs SECOND in `out`'s own traversal, AFTER the out-only
    // `#f1`. This ordering is what makes threaded-from-`in` and
    // fresh-per-`out` numbering actually disagree (see below).
    let out_src = json!({
        "k": "app",
        "f": {"k": "app", "f": {"k": "mvar", "i": 0}, "a": {"k": "fvar", "i": 1}},
        "a": {"k": "fvar", "i": 0},
    });
    let out_id = decode_expr(&mut scratch, base, &out_src, &mut fvars, &mut mvars);

    // ONE shared state, `in` encoded first (exactly `oracle_fast_gate`'s
    // own sequencing) — `in`'s fvar A already claims index 0 before
    // `out` is ever encoded.
    let mut est = EncSt::default();
    let in_json = encode_expr(&scratch, base, in_id, &mut est);
    assert_eq!(
        in_json, in_src,
        "re-encoding `in` alone must round-trip exactly"
    );

    let out_json = encode_expr(&scratch, base, out_id, &mut est);
    // Correct (threaded) numbering: `?0`/mvar M is the first mvar
    // anywhere in the pair -> 0. `#f1`/fvar B is the first OUT-ONLY
    // fvar, encountered with `est.fvars` already holding `{A: 0}` ->
    // the NEXT index, 1 (a non-zero index for an out-only fvar, as
    // requested). `#f0`/fvar A reuses its `in`-side index, 0.
    let expected_out = json!({
        "k": "app",
        "f": {"k": "app", "f": {"k": "mvar", "i": 0}, "a": {"k": "fvar", "i": 1}},
        "a": {"k": "fvar", "i": 0},
    });
    assert_eq!(
        out_json, expected_out,
        "an out-only fvar must continue numbering from where `in` left off, not restart at 0"
    );

    // The bug this pins: a FRESH `EncSt` per `out` (ignoring `in`
    // entirely) would instead number fvar B (the first fvar `out`'s
    // OWN traversal meets) as 0, and fvar A (met second, and not
    // recognized as already-numbered since the fresh state never saw
    // `in`) as 1 — swapped relative to the correct answer above, not a
    // coincidental match. Spelled out explicitly so a future edit that
    // reintroduces the bug fails LOUDLY here, not just silently once a
    // real corpus record happens to exercise it.
    let mut buggy_fresh_state = EncSt::default();
    let buggy_out_json = encode_expr(&scratch, base, out_id, &mut buggy_fresh_state);
    let wrong_answer = json!({
        "k": "app",
        "f": {"k": "app", "f": {"k": "mvar", "i": 0}, "a": {"k": "fvar", "i": 0}},
        "a": {"k": "fvar", "i": 1},
    });
    assert_eq!(
        buggy_out_json, wrong_answer,
        "sanity check on the test's own construction: a fresh-per-out state really does \
         disagree with the threaded answer above (if this fails, the test no longer \
         distinguishes the two, and must be redesigned)"
    );
    assert_ne!(
        out_json, buggy_out_json,
        "threaded and fresh-per-out numbering must disagree for this construction"
    );
}

/// The canonical scheme's `lmvar` node (M4b-1 Task 2): a universe-
/// polymorphic constant elaborates to a term carrying an unassigned
/// level metavariable, which `encode_level` previously had no case for.
/// Builds `max(max(?u0, ?u1), ?u0)` — two distinct level mvars plus a
/// second occurrence of the first — so first-occurrence numbering
/// (`?u0` -> 0, `?u1` -> 1, reuse -> 0) and decode/re-encode round-trip
/// sharing are both exercised, mirroring the expr-mvar numbering test
/// above (`encode_threads_numbering_from_in_into_out_like_the_oracles_enc_pair`)
/// for the level side.
#[test]
fn encode_decode_level_mvar_roundtrips() {
    let mut scratch = Store::scratch();
    // Build `max(max(?u0, ?u1), ?u0)` where ?u0/?u1 are two distinct
    // mvars, plus a second occurrence of ?u0, so numbering + sharing
    // are both exercised.
    let n0 = support::synth_name(&mut scratch, None, "u", 0);
    let n1 = support::synth_name(&mut scratch, None, "u", 1);
    let u0 = scratch.level_mvar(None, Some(n0)).unwrap();
    let u1 = scratch.level_mvar(None, Some(n1)).unwrap();
    let m = scratch.level_max(None, u0, u1).unwrap();
    let mm = scratch.level_max(None, m, u0).unwrap(); // ?u0 appears again
    let level_json = {
        let mut st = EncSt::default();
        support::encode_level(&scratch, None, mm, &mut st)
    };
    // First occurrence order: ?u0 -> 0, ?u1 -> 1, reuse -> 0.
    assert_eq!(
        level_json,
        json!({"k":"max",
               "a":{"k":"max","a":{"k":"lmvar","i":0},"b":{"k":"lmvar","i":1}},
               "b":{"k":"lmvar","i":0}})
    );
    // Decode back and re-encode: must be identical (round-trip).
    let mut lm = HashMap::new();
    let back = support::decode_level(&mut scratch, None, &level_json, &mut lm);
    let mut st2 = EncSt::default();
    assert_eq!(
        support::encode_level(&scratch, None, back, &mut st2),
        level_json
    );
}
