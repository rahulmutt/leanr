//! Integration: decode fixture `.olean`s and replay them through the
//! kernel (Task 12). This is where decoded modules meet the checker.

use std::collections::HashMap;
use std::collections::HashSet;
use std::path::PathBuf;
use std::sync::Arc;

use leanr_kernel::{ConstantInfo, Declaration, Environment, Name};
use leanr_olean::{load_closure, ModuleData, PartKind, SearchPath};

fn fixture_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

fn constants_of(md: ModuleData) -> HashMap<Arc<Name>, ConstantInfo> {
    md.constants
        .into_iter()
        .map(|c| (Arc::clone(c.name()), c))
        .collect()
}

/// Hermetic (runs in CI): the import-free `Prelude0` fixture replays from
/// an empty environment. No toolchain needed at test time — the committed
/// `.olean` is the entire input.
#[test]
fn prelude0_replays_from_empty_env() {
    let bytes = std::fs::read(fixture_path("Prelude0.olean")).unwrap();
    let m = ModuleData::parse(&bytes).unwrap();
    assert!(m.imports.is_empty(), "Prelude0 imports nothing");

    let constants = constants_of(m);
    let mut env = Environment::default();
    let stats = leanr_kernel::replay(&mut env, constants).unwrap();
    // N block, Truth block, N.add, triv, and the two generated `recOn`
    // definitions — at least the three the fixture explicitly declares.
    assert!(
        stats.checked >= 3,
        "expected >= 3 checked, got {}",
        stats.checked
    );
    assert_eq!(stats.skipped_unsafe, 0);
}

/// TDD anchor for M1b Task 14 (`leanr check`): exercises the exact library
/// path the CLI subcommand drives — `SearchPath::new` + `load_closure` +
/// `replay` — over the committed, import-free `Prelude0` fixture from an
/// explicit root (the fixtures dir), mirroring
/// `leanr check Prelude0 --path tests/fixtures`. Hermetic (runs in CI): no
/// toolchain needed, the committed `.olean` is the entire input.
#[test]
fn check_library_path_replays_prelude0_from_explicit_root() {
    let sp = SearchPath::new(vec![fixtures_dir()]);
    let modules = load_closure(&sp, &[name("Prelude0")]).unwrap();
    assert_eq!(
        modules.len(),
        1,
        "Prelude0 has no imports, so its closure is itself"
    );

    let mut constants: HashMap<Arc<Name>, ConstantInfo> = HashMap::new();
    for (_, md) in modules {
        for c in md.constants {
            constants.entry(Arc::clone(c.name())).or_insert(c);
        }
    }

    let mut env = Environment::default();
    let stats = leanr_kernel::replay(&mut env, constants).unwrap();
    assert!(
        stats.checked >= 3,
        "expected >= 3 checked, got {}",
        stats.checked
    );
    assert_eq!(stats.skipped_unsafe, 0);
}

/// Hermetic (runs in CI): the `module`-mode `ModPriv` fixture decodes from
/// its committed companion parts and replays from an empty environment.
///
/// This is the M1b Task 13a acceptance in miniature: `bump` (public) calls
/// `secret` (private), which lives ONLY in `ModPriv.olean.private` as
/// `_private.ModPriv.0.secret`. In the base `ModPriv.olean`, `bump`/`triv`
/// are bare `axiom` stubs; the checkable `def`/`thm` bodies (and the private
/// helper) come from the `.private` part. Decoding all parts together and
/// replaying proves the merged, multi-region constant set is self-contained
/// — no toolchain needed at test time.
#[test]
fn modpriv_parts_replay_from_empty_env() {
    let read = |name: &str| std::fs::read(fixture_path(name)).unwrap();
    let base = read("ModPriv.olean");
    let server = read("ModPriv.olean.server");
    let private = read("ModPriv.olean.private");

    let md = ModuleData::parse_parts(&[
        (PartKind::Base, &base),
        (PartKind::Server, &server),
        (PartKind::Private, &private),
    ])
    .expect("parts decode");
    assert!(md.is_module, "ModPriv is a module");
    assert!(md.imports.is_empty(), "prelude module imports nothing");

    // The private helper must be present in the merged set.
    let names: Vec<String> = md.constants.iter().map(|c| c.name().to_string()).collect();
    assert!(
        names.iter().any(|n| n == "_private.ModPriv.0.secret"),
        "private helper missing from merged constants: {names:?}"
    );
    // The public interface must be the checkable body, not the base axiom stub.
    let bump = md
        .constants
        .iter()
        .find(|c| c.name().to_string() == "bump")
        .expect("bump present");
    assert_eq!(
        bump.kind(),
        "def",
        "bump must be the private `def`, not an axiom stub"
    );

    let constants = constants_of(md);
    let mut env = Environment::default();
    let stats = leanr_kernel::replay(&mut env, constants).unwrap();
    assert!(
        stats.checked >= 5,
        "expected >= 5 checked, got {}",
        stats.checked
    );
    assert_eq!(stats.skipped_unsafe, 0);
}

/// Toolchain-dependent (local, like the M1a sweep): the M1a fixtures
/// `Sample`/`SampleRich` import `Init`, whose transitive closure lives in
/// the pinned toolchain. The module-aware loader ([`load_closure`], M1b
/// Tasks 13 + 13a) resolves that closure and, for each module-mode toolchain
/// olean, merges its `.olean.private`/`.olean.server` companion parts so
/// `_private.*` helpers resolve. Skipped when `LEANR_SWEEP_DIR` is unset
/// (i.e. in CI); run locally with `LEANR_SWEEP_DIR=$(lean --print-libdir)`.
///
/// STATUS (M1b Task 13a): the decoder half is DONE — the loader now decodes
/// every module's multi-region parts, so replay no longer hits
/// `UnknownConstant` on `_private.*` helpers (the Task-12/13 gap). Two
/// SEPARATE, pre-existing `leanr_kernel` issues (out of Task 13a's scope,
/// which forbids kernel changes) currently block a *full* stdlib-closure
/// replay, in order:
///
/// 1. Quotient init: `quot::check_eq_type` compares the decoded `Eq` type with
///    `Expr::structural_eq` (binder-name/info-SENSITIVE), but the oracle uses
///    `is_equal` = `expr_eq_fn<false>` (src/kernel/expr_eq_fn.cpp:107/118-119),
///    which IGNORES binder names/info. Real `Eq`'s arrow binders differ
///    cosmetically from the freshly built expected type, so the strict check
///    wrongly rejects. (Verified: relaxing that one comparison lets the whole
///    `Init.Prelude` closure replay — 1975 checked, 53 skipped.)
/// 2. A deep real definition (`Nat.Linear.ExprCnstr.denote_toNormPoly`)
///    exceeds `RecGuard`'s `MAX_REC_DEPTH` during replay (kernel recursion
///    cap; Task-16 hardening territory).
///
/// Both are diagnosed in `.superpowers/sdd/task-13a-report.md`. The hermetic
/// `modpriv_parts_replay_from_empty_env` test above is the in-scope,
/// CI-green acceptance for the multi-region decoder + replay.
#[test]
#[ignore = "needs the pinned toolchain AND pre-existing kernel fixes (quot Eq-eq + rec depth); see doc"]
fn fixture_modules_replay_clean_with_closure() {
    let dir = std::env::var("LEANR_SWEEP_DIR")
        .expect("LEANR_SWEEP_DIR must point at the toolchain lib/lean dir");
    // The fixtures resolve from the fixtures dir; their imports resolve from
    // the toolchain lib dir. `load_closure` walks the whole import DAG and
    // loads every module's companion parts.
    let sp = SearchPath::new(vec![fixtures_dir(), PathBuf::from(&dir)]);
    let targets = [name("Sample"), name("SampleRich")];
    let modules = load_closure(&sp, &targets).expect("closure loads");

    // Union every module's constants (module oleans carry only their own
    // module's constants, so the closure's constant sets are disjoint).
    let mut constants: HashMap<Arc<Name>, ConstantInfo> = HashMap::new();
    for (_, md) in modules {
        for c in md.constants {
            constants.entry(Arc::clone(c.name())).or_insert(c);
        }
    }

    let mut env = Environment::default();
    let stats = leanr_kernel::replay(&mut env, constants)
        .unwrap_or_else(|e| panic!("closure failed to replay: {e}"));
    assert!(stats.checked > 0, "checked nothing");
}

// ---------------------------------------------------------------------------
// M1b Task 15: mutation-differential harness vs the oracle kernel.
//
// `tests/fixtures/mutate.lean` (run via `mise run fixtures:mutations`)
// generates, from a target module, a set of structurally mutated defs/theorems,
// records the REAL Lean kernel's per-mutant accept/reject verdict
// (`Environment.addDeclCore … doCheck := true`, the `lean_add_decl` extern),
// and writes them into a single-region `.olean` plus a `…-verdicts.jsonl`.
// These tests decode that `.olean` and, for each verdict line, replay JUST that
// mutant against the (trusted) import base through leanr's `Environment::add_decl`
// and assert leanr's verdict matches the oracle's, name by name. Any mismatch is
// a REAL FINDING (a kernel-port bug), not something to paper over.
// ---------------------------------------------------------------------------

/// A committed mutant is always a def or theorem (the harness only mutates
/// those); turn its decoded `ConstantInfo` back into the `Declaration` the
/// oracle handed to `addDeclCore`.
fn mutant_to_declaration(ci: &ConstantInfo) -> Declaration {
    match ci {
        ConstantInfo::Defn(v) => Declaration::Defn(v.clone()),
        ConstantInfo::Thm(v) => Declaration::Thm(v.clone()),
        other => panic!("mutant {} is {}, not a def/thm", other.name(), other.kind()),
    }
}

/// Parse a `…-verdicts.jsonl`: skip the header object (no `"name"` field),
/// return `(mutant name, oracle verdict)` for every mutant line.
fn parse_verdicts(text: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let v: serde_json::Value =
            serde_json::from_str(line).unwrap_or_else(|e| panic!("bad jsonl line {line:?}: {e}"));
        if let (Some(n), Some(verd)) = (v.get("name"), v.get("verdict")) {
            out.push((
                n.as_str().expect("name is a string").to_string(),
                verd.as_str().expect("verdict is a string").to_string(),
            ));
        }
        // otherwise it's the header line — skip.
    }
    out
}

/// The differential core: build a trusted base env from `base` (the mutated
/// module's import closure — imported, not re-checked, exactly like the
/// oracle's `kenv`), then for each verdict line clone the base, admit ONLY that
/// mutant through leanr's checking `add_decl`, and require leanr's accept/reject
/// to equal the oracle's. Also enforces the harness invariant of >= 5 accepts
/// and >= 5 rejects.
fn assert_verdicts_match(base: Vec<ConstantInfo>, mutants: Vec<ConstantInfo>, text: &str) {
    let verdicts = parse_verdicts(text);
    assert!(!verdicts.is_empty(), "no mutant verdict lines in jsonl");

    let base_env = Environment::from_modules([base]).expect("base env builds from import closure");
    let by_name: HashMap<String, &ConstantInfo> =
        mutants.iter().map(|c| (c.name().to_string(), c)).collect();

    let mut accepts = 0usize;
    let mut rejects = 0usize;
    let mut disagreements: Vec<String> = Vec::new();
    for (name, oracle) in &verdicts {
        let ci = by_name
            .get(name)
            .unwrap_or_else(|| panic!("mutant {name} is in the jsonl but missing from the olean"));
        let decl = mutant_to_declaration(ci);
        let mut env = base_env.clone();
        let leanr = match env.add_decl(decl) {
            Ok(()) => "accept",
            Err(_) => "reject",
        };
        match oracle.as_str() {
            "accept" => accepts += 1,
            "reject" => rejects += 1,
            other => panic!("mutant {name}: unknown oracle verdict {other:?}"),
        }
        if leanr != oracle {
            disagreements.push(format!("  {name}: leanr={leanr} oracle={oracle}"));
        }
    }

    assert!(
        disagreements.is_empty(),
        "leanr disagreed with the oracle kernel on {} mutant(s):\n{}",
        disagreements.len(),
        disagreements.join("\n")
    );
    assert!(accepts >= 5, "harness needs >= 5 accepts, got {accepts}");
    assert!(rejects >= 5, "harness needs >= 5 rejects, got {rejects}");
}

/// Hermetic (runs in CI): mutate the import-free `MutBase` module and check
/// leanr agrees with the oracle on every mutant. No toolchain needed at test
/// time — `MutBase.olean` (base), `Mutations0.olean` (mutants) and
/// `mutations0-verdicts.jsonl` (oracle verdicts) are the entire input.
#[test]
fn mutation_verdicts_hermetic() {
    let base_bytes = std::fs::read(fixture_path("MutBase.olean"))
        .expect("MutBase.olean missing — run `mise run fixtures:mutations`");
    let mut_bytes = std::fs::read(fixture_path("Mutations0.olean"))
        .expect("Mutations0.olean missing — run `mise run fixtures:mutations`");
    let text = std::fs::read_to_string(fixture_path("mutations0-verdicts.jsonl"))
        .expect("mutations0-verdicts.jsonl missing — run `mise run fixtures:mutations`");

    let base = ModuleData::parse(&base_bytes)
        .expect("MutBase decodes")
        .constants;
    let mutants = ModuleData::parse(&mut_bytes)
        .expect("Mutations0 decodes")
        .constants;
    assert_verdicts_match(base, mutants, &text);
}

/// Toolchain-dependent (local, like the M1a sweep): mutate `Init.Core` and
/// check leanr agrees with the oracle. The base is `Init.Core`'s whole import
/// closure, loaded as trusted context from the pinned toolchain lib dir (never
/// re-checked — so the Task-16 deep-recursion blocker, which only bites when a
/// deep definition is *type-checked*, is not exercised here; only the shallow
/// renamed mutants are checked). Skipped when `LEANR_SWEEP_DIR` is unset (CI);
/// run locally with `LEANR_SWEEP_DIR=$(lean --print-libdir)`.
#[test]
#[ignore = "needs the pinned toolchain (LEANR_SWEEP_DIR); the hermetic variant is the CI acceptance"]
fn mutation_verdicts_toolchain() {
    let dir = std::env::var("LEANR_SWEEP_DIR")
        .expect("LEANR_SWEEP_DIR must point at the toolchain lib/lean dir");
    let mut_bytes = std::fs::read(fixture_path("Mutations.olean"))
        .expect("Mutations.olean missing — run `mise run fixtures:mutations`");
    let text = std::fs::read_to_string(fixture_path("mutations-verdicts.jsonl"))
        .expect("mutations-verdicts.jsonl missing — run `mise run fixtures:mutations`");

    let sp = SearchPath::new(vec![PathBuf::from(&dir)]);
    let modules = load_closure(&sp, &[name("Init.Core")]).expect("Init.Core closure loads");
    let mut base: Vec<ConstantInfo> = Vec::new();
    let mut seen: HashSet<Arc<Name>> = HashSet::new();
    for (_, md) in modules {
        for c in md.constants {
            if seen.insert(Arc::clone(c.name())) {
                base.push(c);
            }
        }
    }
    let mutants = ModuleData::parse(&mut_bytes)
        .expect("Mutations decodes")
        .constants;
    assert_verdicts_match(base, mutants, &text);
}

/// Build a dotted module name, e.g. `Init.Data.Nat`.
fn name(dotted: &str) -> Arc<Name> {
    let mut n = Arc::new(Name::Anonymous);
    for part in dotted.split('.') {
        n = Arc::new(Name::Str {
            parent: n,
            part: part.to_string(),
        });
    }
    n
}

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures")
}
