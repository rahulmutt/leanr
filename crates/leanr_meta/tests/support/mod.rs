//! Shared decode/encode helpers for the tier-1 differential gates
//! (`oracle_fast.rs`, `oracle_synth.rs`).
//!
//! These implement the canonical JSON scheme documented in
//! `tests/fixtures/meta/dump_defeq.lean`'s module header — that file is
//! the authoritative counterpart, and `tests/fixtures/meta/
//! dump_synth.lean` re-uses the identical scheme, which is precisely
//! why the Rust side is ONE module rather than a copy per gate: two
//! copies could drift apart while both stayed green against their own
//! corpus. The scheme comments below restate just enough to make each
//! match arm legible without cross-referencing the Lean side
//! constantly.
//!
//! Extracted verbatim from `oracle_fast.rs` (M4a plan-4 task B7); no
//! behavior change — `oracle_fast.rs` still round-trips and gates
//! exactly as before, it just `use`s these from here.

// Each integration-test binary compiles this whole module but uses only
// the part its own gate needs (`oracle_synth.rs` has no `defeq` records,
// so it never calls `decode_nat_decimal` through a `lit` node, etc.).
// Without this, `cargo clippy --all-targets -- -D warnings` fails on
// per-binary dead code that is not dead in the module's own terms.
#![allow(dead_code)]

use std::collections::HashMap;
use std::path::PathBuf;

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId, Store};
use leanr_kernel::{BinderInfo, ConstantInfo, Environment, Nat};
use leanr_meta::TransparencyMode;
use leanr_olean::{
    DefaultInstanceEntry, InstanceEntry, MatcherEntry, ModuleData, ProjectionFnInfo,
    ReducibilityEntry,
};
use serde_json::{json, Value};

/// One replayed, import-free `prelude`-mode fixture module: the kernel
/// `Environment` plus every environment-extension table `MetaCtx::new`
/// needs. Both gates load their fixture exactly this way (`Meta0.olean`
/// / `Synth0.olean`), so the "decode, assert import-free, replay" step
/// lives here rather than being written twice.
///
/// `env` is returned by value because `MetaCtx::new` borrows an
/// `EnvView` out of it, so the caller must own it for the whole gate.
pub struct Replayed {
    pub env: Environment,
    pub reducibility: Vec<ReducibilityEntry>,
    pub matchers: Vec<MatcherEntry>,
    pub instances: Vec<InstanceEntry>,
    pub default_instances: Vec<DefaultInstanceEntry>,
    pub projection_fns: Vec<ProjectionFnInfo>,
}

/// Decode `tests/fixtures/<subdir>/<name>`, assert it is import-free
/// (the hermeticity contract: the committed `.olean` is the ENTIRE
/// input — nothing is loaded from a search path, and CI never installs
/// Lean), and replay its constants into a fresh `Environment`.
pub fn replay_fixture_in(subdir: &str, name: &str) -> Replayed {
    let bytes = std::fs::read(fixture_in(subdir, name)).expect("committed fixture");
    let mut env = Environment::default();
    let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
    assert!(md.imports.is_empty(), "{name} must stay import-free");
    let constants: HashMap<NameId, ConstantInfo> = md
        .constants
        .iter()
        .cloned()
        .map(|c| (c.name(), c))
        .collect();
    leanr_kernel::replay(&mut env, constants).expect("replay");
    Replayed {
        env,
        reducibility: md.reducibility,
        matchers: md.matchers,
        instances: md.instances,
        default_instances: md.default_instances,
        projection_fns: md.projection_fns,
    }
}

/// `replay_fixture_in("meta", name)` — the gate helpers' original
/// subdir, kept as the unparameterized default so existing callers
/// (`oracle_fast.rs`, `oracle_synth.rs`, `synth_sweep.rs`) are
/// unbroken.
pub fn replay_fixture(name: &str) -> Replayed {
    replay_fixture_in("meta", name)
}

/// `tests/fixtures/<subdir>/<name>` — the subdir-parameterized form so
/// a later crate (`leanr_elab`) can point this shared loader at
/// `tests/fixtures/elab` instead of `tests/fixtures/meta`.
pub fn fixture_in(subdir: &str, name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(subdir)
        .join(name)
}

pub fn fixture(name: &str) -> PathBuf {
    fixture_in("meta", name)
}

// ===== decode: JSON -> ExprId (interning through the store) =====

/// Split a dotted `Name.toString (escape := false)` string back into its
/// components and intern the chain (`decode_name`'s inverse is
/// `name_to_string` below). Every name in the committed corpus is a
/// plain dotted identifier chain (no numeric components, no escaping),
/// so a `'.'` split suffices — this is the committed-fixture side of the
/// contract, not a general Lean-name parser.
pub fn decode_name(scratch: &mut Store, base: Option<&Store>, s: &str) -> NameId {
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
pub fn synth_name(scratch: &mut Store, base: Option<&Store>, prefix: &str, idx: u64) -> NameId {
    let s = format!("{prefix}{idx}");
    let sid = scratch
        .intern_str(base, &s)
        .expect("interning a synthetic placeholder name is infallible");
    scratch
        .name_str(base, None, sid)
        .expect("interning a synthetic placeholder name is infallible")
}

pub fn decode_bi(s: &str) -> BinderInfo {
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
pub fn decode_nat_decimal(s: &str) -> Nat {
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

/// `lvars` numbers first-occurrence-within-one-decode level-mvar
/// indices to synthetic names, exactly like `decode_expr`'s
/// `fvars`/`mvars` (brief: "interning a fresh level mvar per distinct
/// `i`").
pub fn decode_level(
    scratch: &mut Store,
    base: Option<&Store>,
    v: &Value,
    lvars: &mut HashMap<u64, NameId>,
) -> LevelId {
    let k = v["k"]
        .as_str()
        .unwrap_or_else(|| panic!("decode_level: missing k in {v} (committed fixture malformed)"));
    match k {
        "zero" => scratch.level_zero(base).expect("intern level zero"),
        "succ" => {
            let u = decode_level(scratch, base, &v["u"], lvars);
            scratch.level_succ(base, u).expect("intern level succ")
        }
        "max" => {
            let a = decode_level(scratch, base, &v["a"], lvars);
            let b = decode_level(scratch, base, &v["b"], lvars);
            scratch.level_max(base, a, b).expect("intern level max")
        }
        "imax" => {
            let a = decode_level(scratch, base, &v["a"], lvars);
            let b = decode_level(scratch, base, &v["b"], lvars);
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
        "lmvar" => {
            let i = v["i"].as_u64().unwrap_or_else(|| {
                panic!("decode_level: missing i in {v} (committed fixture malformed)")
            });
            let nid = *lvars
                .entry(i)
                .or_insert_with(|| synth_name(scratch, base, "u", i));
            scratch
                .level_mvar(base, Some(nid))
                .expect("intern level mvar")
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
pub fn decode_expr(
    scratch: &mut Store,
    base: Option<&Store>,
    v: &Value,
    fvars: &mut HashMap<u64, NameId>,
    mvars: &mut HashMap<u64, NameId>,
) -> ExprId {
    // Level-mvar numbering (`lvars`) is scoped to this one top-level
    // call rather than threaded through the public signature: unlike
    // `fvars`/`mvars`, which every caller already threads across a
    // record's `in`/`out` pair from outside, no caller in this crate
    // needs level-mvar identity shared across separate `decode_expr`
    // calls today (the committed corpus has no level mvars at all —
    // brief/Task 2), and widening this signature would break every
    // other call site of this shared helper (`oracle_synth.rs`,
    // `synth_sweep.rs`), which are out of scope for this task.
    let mut lvars = HashMap::new();
    decode_expr_inner(scratch, base, v, fvars, mvars, &mut lvars)
}

fn decode_expr_inner(
    scratch: &mut Store,
    base: Option<&Store>,
    v: &Value,
    fvars: &mut HashMap<u64, NameId>,
    mvars: &mut HashMap<u64, NameId>,
    lvars: &mut HashMap<u64, NameId>,
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
            let u = decode_level(scratch, base, &v["u"], lvars);
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
                .map(|u| decode_level(scratch, base, u, lvars))
                .collect();
            let levels = scratch
                .intern_level_list(base, &us)
                .expect("intern level list");
            scratch
                .expr_const(base, Some(nid), levels)
                .expect("intern const")
        }
        "app" => {
            let f = decode_expr_inner(scratch, base, &v["f"], fvars, mvars, lvars);
            let a = decode_expr_inner(scratch, base, &v["a"], fvars, mvars, lvars);
            scratch.expr_app(base, f, a).expect("intern app")
        }
        "lam" => {
            let bi = decode_bi(
                v["bi"]
                    .as_str()
                    .unwrap_or_else(|| panic!("decode_expr: missing bi in {v}")),
            );
            let t = decode_expr_inner(scratch, base, &v["t"], fvars, mvars, lvars);
            let b = decode_expr_inner(scratch, base, &v["b"], fvars, mvars, lvars);
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
            let t = decode_expr_inner(scratch, base, &v["t"], fvars, mvars, lvars);
            let b = decode_expr_inner(scratch, base, &v["b"], fvars, mvars, lvars);
            scratch
                .expr_forall(base, None, t, b, bi)
                .expect("intern pi")
        }
        "let" => {
            let t = decode_expr_inner(scratch, base, &v["t"], fvars, mvars, lvars);
            let val = decode_expr_inner(scratch, base, &v["v"], fvars, mvars, lvars);
            let b = decode_expr_inner(scratch, base, &v["b"], fvars, mvars, lvars);
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
            let e = decode_expr_inner(scratch, base, &v["e"], fvars, mvars, lvars);
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
pub struct EncSt {
    pub fvars: HashMap<NameId, u64>,
    pub fnext: u64,
    pub mvars: HashMap<NameId, u64>,
    pub mnext: u64,
    // Level-mvar side of the same first-occurrence scheme (M4b-1 Task
    // 2). Keyed by `Option<NameId>` rather than `NameId` because
    // `LevelRow::MVar` — unlike `Node::MVar` — allows an anonymous
    // (`None`) name (see `leanr_kernel::bank::levels`'s module doc
    // comment); that is also exactly what the store's own hash-consing
    // does (`Store::level_mvar` hashes `Option<NameId>` directly), so
    // two anonymous level mvars are indistinguishable at the `LevelId`
    // level too and collapsing them to one index here is consistent,
    // not a loss of information this layer could otherwise preserve.
    pub lvars: HashMap<Option<NameId>, u64>,
    pub lnext: u64,
}

impl EncSt {
    /// First-occurrence index for a level mvar, assigning the next
    /// unused index on first sight — the level-side counterpart of how
    /// `encode_expr`'s `Node::MVar`/`Node::FVar` arms number `mvars`/
    /// `fvars` inline.
    pub fn level_mvar_index(&mut self, n: Option<NameId>) -> u64 {
        *self.lvars.entry(n).or_insert_with(|| {
            let i = self.lnext;
            self.lnext += 1;
            i
        })
    }
}

pub fn name_to_string(store: &Store, base: Option<&Store>, n: Option<NameId>) -> String {
    store.to_name(base, n).to_string()
}

pub fn nat_to_u64(n: &Nat) -> u64 {
    n.to_usize()
        .unwrap_or_else(|| panic!("encode_expr: index too large to encode as a JSON number"))
        as u64
}

pub fn encode_bi(bi: BinderInfo) -> &'static str {
    match bi {
        BinderInfo::Default => "d",
        BinderInfo::Implicit => "i",
        BinderInfo::StrictImplicit => "s",
        BinderInfo::InstImplicit => "c",
    }
}

/// `st` numbers level mvars by first occurrence exactly like
/// `encode_expr` numbers expr mvars/fvars (`EncSt::level_mvar_index`) —
/// shared across a whole query record's `in`/`out` pair the same way
/// (M4b-1 Task 2: a universe-polymorphic constant elaborates to a term
/// carrying an unassigned level mvar, which this `lmvar` node now
/// represents).
pub fn encode_level(store: &Store, base: Option<&Store>, l: LevelId, st: &mut EncSt) -> Value {
    match *store.level_row(base, l) {
        LevelRow::Zero => json!({"k": "zero"}),
        LevelRow::Succ(u) => json!({"k": "succ", "u": encode_level(store, base, u, st)}),
        LevelRow::Max(a, b) => {
            json!({"k": "max", "a": encode_level(store, base, a, st), "b": encode_level(store, base, b, st)})
        }
        LevelRow::IMax(a, b) => {
            json!({"k": "imax", "a": encode_level(store, base, a, st), "b": encode_level(store, base, b, st)})
        }
        LevelRow::Param(n) => json!({"k": "param", "n": name_to_string(store, base, n)}),
        LevelRow::MVar(n) => json!({"k": "lmvar", "i": st.level_mvar_index(n)}),
    }
}

/// Inverse of `decode_expr`: recursive descent over an `ExprId`,
/// erasing binder names and `MData` (recursing straight through it),
/// numbering mvars/fvars by first occurrence within this call's walk.
pub fn encode_expr(store: &Store, base: Option<&Store>, e: ExprId, st: &mut EncSt) -> Value {
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
        Node::Sort { level } => json!({"k": "sort", "u": encode_level(store, base, level, st)}),
        Node::Const { name, levels } => {
            let n = name_to_string(store, base, name);
            let us: Vec<Value> = store
                .level_list_at(base, levels)
                .iter()
                .map(|&l| encode_level(store, base, l, st))
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

pub fn transparency_of(s: &str) -> TransparencyMode {
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
