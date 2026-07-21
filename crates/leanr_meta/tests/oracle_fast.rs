//! Tier-1 differential gate (plan-2 spec § The gate): every committed
//! query must agree with the oracle byte-for-byte after
//! canonicalization. Hermetic — the committed .olean and .jsonl are
//! the entire input; CI never installs Lean (docs/ORACLE.md).
//!
//! This is a REGRESSION gate: "nothing that used to agree now
//! disagrees." Discovery at Mathlib scale is plan 4's nightly.
//!
//! The three helpers below (`decode_expr`/`encode_expr`/
//! `transparency_of`) implement the canonical JSON scheme documented in
//! `tests/fixtures/meta/dump_defeq.lean`'s module header — that file is
//! the authoritative counterpart; this file's scheme comments restate
//! just enough to make each match arm legible without cross-referencing
//! it constantly.

use std::collections::HashMap;
use std::path::PathBuf;

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId, Store};
use leanr_kernel::{BinderInfo, ConstantInfo, EnvView, Environment, Nat};
use leanr_meta::{Config, MetaCtx, TransparencyMode};
use leanr_olean::ModuleData;
use serde_json::{json, Value};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/meta")
        .join(name)
}

// ===== decode: JSON -> ExprId (interning through the store) =====

/// Split a dotted `Name.toString (escape := false)` string back into its
/// components and intern the chain (`decode_name`'s inverse is
/// `name_to_string` below). Every name in the committed corpus is a
/// plain dotted identifier chain (no numeric components, no escaping),
/// so a `'.'` split suffices — this is the committed-fixture side of the
/// contract, not a general Lean-name parser.
fn decode_name(scratch: &mut Store, base: Option<&Store>, s: &str) -> NameId {
    let mut id: Option<NameId> = None;
    for part in s.split('.') {
        let sid = scratch
            .intern_str(base, part)
            .expect("interning a committed-fixture name component is infallible");
        id = Some(
            scratch
                .name_str(base, id, sid)
                .expect("interning a committed-fixture name component is infallible"),
        );
    }
    id.expect("decode_name: empty name string in committed fixture")
}

/// `?0`, `?1`, ... / `#f0`, `#f1`, ... — deterministic synthetic names
/// for decoded mvar/fvar indices (brief: "mvar/fvar indices intern
/// names ?0, ?1… / #f0… deterministically"). The exact string chosen
/// here is never compared against anything: only identity (same index
/// => same NameId within one decode) matters, since `encode_expr`
/// renumbers its own output independently by first occurrence.
fn synth_name(scratch: &mut Store, base: Option<&Store>, prefix: &str, idx: u64) -> NameId {
    let s = format!("{prefix}{idx}");
    let sid = scratch
        .intern_str(base, &s)
        .expect("interning a synthetic placeholder name is infallible");
    scratch
        .name_str(base, None, sid)
        .expect("interning a synthetic placeholder name is infallible")
}

fn decode_bi(s: &str) -> BinderInfo {
    match s {
        "d" => BinderInfo::Default,
        "i" => BinderInfo::Implicit,
        "s" => BinderInfo::StrictImplicit,
        "c" => BinderInfo::InstImplicit,
        other => {
            panic!("decode_expr: unknown binder-info kind {other:?} (committed fixture malformed)")
        }
    }
}

/// Decimal-string -> `Nat`, built from `Nat::add`/`Nat::mul` so no
/// extra bignum dependency is needed (arbitrary precision, no i64
/// truncation, matching the canonicalization rule for `lit`).
fn decode_nat_decimal(s: &str) -> Nat {
    let mut n = Nat::from(0u64);
    let ten = Nat::from(10u64);
    for c in s.chars() {
        let d = c.to_digit(10).unwrap_or_else(|| {
            panic!("decode_expr: bad decimal digit in lit {s:?} (committed fixture malformed)")
        });
        n = n.mul(&ten).add(&Nat::from(d as u64));
    }
    n
}

fn decode_level(scratch: &mut Store, base: Option<&Store>, v: &Value) -> LevelId {
    let k = v["k"]
        .as_str()
        .unwrap_or_else(|| panic!("decode_level: missing k in {v} (committed fixture malformed)"));
    match k {
        "zero" => scratch.level_zero(base).expect("intern level zero"),
        "succ" => {
            let u = decode_level(scratch, base, &v["u"]);
            scratch.level_succ(base, u).expect("intern level succ")
        }
        "max" => {
            let a = decode_level(scratch, base, &v["a"]);
            let b = decode_level(scratch, base, &v["b"]);
            scratch.level_max(base, a, b).expect("intern level max")
        }
        "imax" => {
            let a = decode_level(scratch, base, &v["a"]);
            let b = decode_level(scratch, base, &v["b"]);
            scratch.level_imax(base, a, b).expect("intern level imax")
        }
        "param" => {
            let n = v["n"].as_str().unwrap_or_else(|| {
                panic!("decode_level: missing n in {v} (committed fixture malformed)")
            });
            let nid = decode_name(scratch, base, n);
            scratch
                .level_param(base, Some(nid))
                .expect("intern level param")
        }
        other => panic!("decode_level: unknown level kind {other:?} (committed fixture malformed)"),
    }
}

/// Recursive descent over the canonical expr scheme (dump_defeq.lean's
/// module header), interning through `scratch` (consulting `base`, the
/// replayed environment's persistent store, first — the same
/// convention every `MetaCtx` method uses). `fvars`/`mvars` number
/// first-occurrence-within-one-`in`-expr indices to synthetic names;
/// they are fresh per query record, matching the corpus's per-record id
/// disambiguation ((id, tr) keying, not id alone).
///
/// Unknown `k` (or any other malformed shape) panics: the committed
/// fixture is trusted input (task brief), so a malformed record is a
/// bug to surface loudly, not data to tolerate.
fn decode_expr(
    scratch: &mut Store,
    base: Option<&Store>,
    v: &Value,
    fvars: &mut HashMap<u64, NameId>,
    mvars: &mut HashMap<u64, NameId>,
) -> ExprId {
    let k = v["k"]
        .as_str()
        .unwrap_or_else(|| panic!("decode_expr: missing k in {v} (committed fixture malformed)"));
    match k {
        "bvar" => {
            let i = v["i"]
                .as_u64()
                .unwrap_or_else(|| panic!("decode_expr: missing/bad i in {v}"));
            let n = Nat::from(i);
            scratch.expr_bvar(base, &n).expect("intern bvar")
        }
        "sort" => {
            let u = decode_level(scratch, base, &v["u"]);
            scratch.expr_sort(base, u).expect("intern sort")
        }
        "const" => {
            let n = v["n"]
                .as_str()
                .unwrap_or_else(|| panic!("decode_expr: missing n in {v}"));
            let nid = decode_name(scratch, base, n);
            let us: Vec<LevelId> = v["us"]
                .as_array()
                .unwrap_or_else(|| panic!("decode_expr: missing us in {v}"))
                .iter()
                .map(|u| decode_level(scratch, base, u))
                .collect();
            let levels = scratch
                .intern_level_list(base, &us)
                .expect("intern level list");
            scratch
                .expr_const(base, Some(nid), levels)
                .expect("intern const")
        }
        "app" => {
            let f = decode_expr(scratch, base, &v["f"], fvars, mvars);
            let a = decode_expr(scratch, base, &v["a"], fvars, mvars);
            scratch.expr_app(base, f, a).expect("intern app")
        }
        "lam" => {
            let bi = decode_bi(
                v["bi"]
                    .as_str()
                    .unwrap_or_else(|| panic!("decode_expr: missing bi in {v}")),
            );
            let t = decode_expr(scratch, base, &v["t"], fvars, mvars);
            let b = decode_expr(scratch, base, &v["b"], fvars, mvars);
            // Binder name erased on decode too: it never survived
            // encoding, so `None` is the only faithful choice.
            scratch.expr_lam(base, None, t, b, bi).expect("intern lam")
        }
        "pi" => {
            let bi = decode_bi(
                v["bi"]
                    .as_str()
                    .unwrap_or_else(|| panic!("decode_expr: missing bi in {v}")),
            );
            let t = decode_expr(scratch, base, &v["t"], fvars, mvars);
            let b = decode_expr(scratch, base, &v["b"], fvars, mvars);
            scratch
                .expr_forall(base, None, t, b, bi)
                .expect("intern pi")
        }
        "let" => {
            let t = decode_expr(scratch, base, &v["t"], fvars, mvars);
            let val = decode_expr(scratch, base, &v["v"], fvars, mvars);
            let b = decode_expr(scratch, base, &v["b"], fvars, mvars);
            let nd = v["nd"]
                .as_bool()
                .unwrap_or_else(|| panic!("decode_expr: missing nd in {v}"));
            scratch
                .expr_let(base, None, t, val, b, nd)
                .expect("intern let")
        }
        "lit" => {
            let s = v["n"]
                .as_str()
                .unwrap_or_else(|| panic!("decode_expr: missing n in {v}"));
            let n = decode_nat_decimal(s);
            scratch.expr_lit_nat(base, &n).expect("intern lit")
        }
        "str" => {
            let s = v["v"]
                .as_str()
                .unwrap_or_else(|| panic!("decode_expr: missing v in {v}"));
            scratch.expr_lit_str(base, s).expect("intern str")
        }
        "proj" => {
            let s = v["s"]
                .as_str()
                .unwrap_or_else(|| panic!("decode_expr: missing s in {v}"));
            let sid = decode_name(scratch, base, s);
            let i = v["i"]
                .as_u64()
                .unwrap_or_else(|| panic!("decode_expr: missing i in {v}"));
            let idx = Nat::from(i);
            let e = decode_expr(scratch, base, &v["e"], fvars, mvars);
            scratch
                .expr_proj(base, Some(sid), &idx, e)
                .expect("intern proj")
        }
        "mvar" => {
            let i = v["i"]
                .as_u64()
                .unwrap_or_else(|| panic!("decode_expr: missing i in {v}"));
            let nid = *mvars
                .entry(i)
                .or_insert_with(|| synth_name(scratch, base, "?", i));
            scratch.expr_mvar(base, Some(nid)).expect("intern mvar")
        }
        "fvar" => {
            let i = v["i"]
                .as_u64()
                .unwrap_or_else(|| panic!("decode_expr: missing i in {v}"));
            let nid = *fvars
                .entry(i)
                .or_insert_with(|| synth_name(scratch, base, "#f", i));
            scratch.expr_fvar(base, Some(nid)).expect("intern fvar")
        }
        other => {
            panic!("decode_expr: unknown expr kind {other:?} in {v} (committed fixture malformed)")
        }
    }
}

// ===== encode: ExprId -> JSON (inverse walk) =====

/// First-occurrence mvar/fvar numbering state for one QUERY RECORD
/// (mirrors the oracle dumper's `EncSt`) — shared across encoding BOTH
/// sides of that record's `in`/`out` pair, exactly like
/// `dump_defeq.lean`'s `encPair` (dump_defeq.lean:155-158: `let (aj,
/// st) := (encExpr a).run {}; let bj := (encExpr b).run' st`, i.e. `in`
/// is encoded into a FRESH state and `out` continues that SAME state,
/// never a fresh one of its own). A value occurring in both `in` and
/// `out` therefore gets the SAME index both times; an mvar/fvar
/// occurring ONLY in `out` gets the NEXT index after every occurrence
/// already numbered while encoding `in` — never index 0. The gate
/// below (`oracle_fast_gate`) reproduces this: it encodes the decoded
/// `in` expr FIRST (seeding the state, and doubling as a round-trip
/// check against the committed `in`) before encoding the computed
/// `result` with that SAME state and comparing it to `out`. A fresh
/// `EncSt` per `result` would silently diverge from the oracle the
/// first time some query's `out` carries an mvar/fvar not already
/// present in `in` — none of the 80 committed records do today, which
/// is exactly why that bug was silent rather than caught by the gate.
#[derive(Default)]
struct EncSt {
    fvars: HashMap<NameId, u64>,
    fnext: u64,
    mvars: HashMap<NameId, u64>,
    mnext: u64,
}

fn name_to_string(store: &Store, base: Option<&Store>, n: Option<NameId>) -> String {
    store.to_name(base, n).to_string()
}

fn nat_to_u64(n: &Nat) -> u64 {
    n.to_usize()
        .unwrap_or_else(|| panic!("encode_expr: index too large to encode as a JSON number"))
        as u64
}

fn encode_bi(bi: BinderInfo) -> &'static str {
    match bi {
        BinderInfo::Default => "d",
        BinderInfo::Implicit => "i",
        BinderInfo::StrictImplicit => "s",
        BinderInfo::InstImplicit => "c",
    }
}

fn encode_level(store: &Store, base: Option<&Store>, l: LevelId) -> Value {
    match *store.level_row(base, l) {
        LevelRow::Zero => json!({"k": "zero"}),
        LevelRow::Succ(u) => json!({"k": "succ", "u": encode_level(store, base, u)}),
        LevelRow::Max(a, b) => {
            json!({"k": "max", "a": encode_level(store, base, a), "b": encode_level(store, base, b)})
        }
        LevelRow::IMax(a, b) => {
            json!({"k": "imax", "a": encode_level(store, base, a), "b": encode_level(store, base, b)})
        }
        LevelRow::Param(n) => json!({"k": "param", "n": name_to_string(store, base, n)}),
        // Not in the canonical scheme (no `lmvar` case) — see
        // dump_defeq.lean's `encLevel` doc comment: a fully-elaborated
        // corpus never carries a level mvar, so hitting one here is a
        // real gap, not a cosmetic one.
        LevelRow::MVar(_) => {
            panic!("encode_level: unexpected level mvar (not in the canonical scheme)")
        }
    }
}

/// Inverse of `decode_expr`: recursive descent over an `ExprId`,
/// erasing binder names and `MData` (recursing straight through it),
/// numbering mvars/fvars by first occurrence within this call's walk.
fn encode_expr(store: &Store, base: Option<&Store>, e: ExprId, st: &mut EncSt) -> Value {
    match store.expr_node(base, e) {
        Node::BVar { idx } => json!({"k": "bvar", "i": idx}),
        Node::BVarBig { idx } => {
            let n = store.nat_at(base, idx);
            json!({"k": "bvar", "i": nat_to_u64(n)})
        }
        Node::FVar { id } => {
            let nid = id.expect("encode_expr: anonymous fvar (should be impossible)");
            let i = *st.fvars.entry(nid).or_insert_with(|| {
                let n = st.fnext;
                st.fnext += 1;
                n
            });
            json!({"k": "fvar", "i": i})
        }
        Node::MVar { id } => {
            let nid = id.expect("encode_expr: anonymous mvar (should be impossible)");
            let i = *st.mvars.entry(nid).or_insert_with(|| {
                let n = st.mnext;
                st.mnext += 1;
                n
            });
            json!({"k": "mvar", "i": i})
        }
        Node::Sort { level } => json!({"k": "sort", "u": encode_level(store, base, level)}),
        Node::Const { name, levels } => {
            let n = name_to_string(store, base, name);
            let us: Vec<Value> = store
                .level_list_at(base, levels)
                .iter()
                .map(|&l| encode_level(store, base, l))
                .collect();
            json!({"k": "const", "n": n, "us": us})
        }
        Node::App { f, arg } => {
            json!({"k": "app", "f": encode_expr(store, base, f, st), "a": encode_expr(store, base, arg, st)})
        }
        Node::Lam {
            binder_type,
            body,
            binder_info,
            ..
        } => {
            json!({
                "k": "lam",
                "bi": encode_bi(binder_info),
                "t": encode_expr(store, base, binder_type, st),
                "b": encode_expr(store, base, body, st),
            })
        }
        Node::Forall {
            binder_type,
            body,
            binder_info,
            ..
        } => {
            json!({
                "k": "pi",
                "bi": encode_bi(binder_info),
                "t": encode_expr(store, base, binder_type, st),
                "b": encode_expr(store, base, body, st),
            })
        }
        Node::LetE {
            ty,
            value,
            body,
            non_dep,
            ..
        } => {
            json!({
                "k": "let",
                "t": encode_expr(store, base, ty, st),
                "v": encode_expr(store, base, value, st),
                "b": encode_expr(store, base, body, st),
                "nd": non_dep,
            })
        }
        Node::LitNat { v } => {
            let n = store.nat_at(base, v);
            json!({"k": "lit", "n": n.to_string()})
        }
        Node::LitStr { v } => {
            let s = store.str_at(base, v);
            json!({"k": "str", "v": s})
        }
        // mdata ERASED: recurse straight through, same as the oracle side.
        Node::MData { expr, .. } => encode_expr(store, base, expr, st),
        Node::Proj {
            type_name,
            idx,
            structure,
        } => {
            let s = name_to_string(store, base, type_name);
            json!({"k": "proj", "s": s, "i": idx, "e": encode_expr(store, base, structure, st)})
        }
        Node::ProjBig {
            type_name,
            idx,
            structure,
        } => {
            let s = name_to_string(store, base, type_name);
            let n = store.nat_at(base, idx);
            json!({"k": "proj", "s": s, "i": nat_to_u64(n), "e": encode_expr(store, base, structure, st)})
        }
    }
}

fn transparency_of(s: &str) -> TransparencyMode {
    match s {
        "none" => TransparencyMode::None,
        "reducible" => TransparencyMode::Reducible,
        "instances" => TransparencyMode::Instances,
        "implicit" => TransparencyMode::Implicit,
        "default" => TransparencyMode::Default,
        "all" => TransparencyMode::All,
        other => {
            panic!("transparency_of: unknown transparency {other:?} (committed fixture malformed)")
        }
    }
}

#[test]
fn oracle_fast_gate() {
    let bytes = std::fs::read(fixture("Meta0.olean")).expect("committed fixture");
    let mut env = Environment::default();
    let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
    assert!(md.imports.is_empty(), "Meta0 must stay import-free");
    let reducibility = md.reducibility;
    let matchers = md.matchers;
    let constants: HashMap<NameId, ConstantInfo> = md
        .constants
        .iter()
        .cloned()
        .map(|c| (c.name(), c))
        .collect();
    leanr_kernel::replay(&mut env, constants).expect("replay");

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
