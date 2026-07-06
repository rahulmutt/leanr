//! Dual-checker fixture gate (term-bank kernel migration, Task 7).
//!
//! The pre-flip proof that the id kernel (`leanr_kernel::bank`) is
//! verdict-identical to the Arc kernel on every real fixture: each test
//! decodes a fixture module set ONCE, replays it through both kernels,
//! and asserts the verdicts are equal in full —
//!
//! - both `Ok` with equal `checked` / `skipped_unsafe` counts, or
//! - both `Err` with `assert_eq!` on the `KernelError` (same variant AND
//!   payload — `KernelError` is the same type on both sides) and on the
//!   failing `decl` name (`Arc<Name>` on both sides).
//!
//! Every fixture module set `check_fixtures.rs` replays has a dual twin
//! here, including the hermetic mutation fixtures and the two
//! toolchain-dependent (`#[ignore]`d, `LEANR_SWEEP_DIR`-gated) sets.
//!
//! Judgment call (sanctioned by the task brief): the small fixture
//! helpers (`fixture_path`, `fixtures_dir`, `name`, `parse_verdicts`,
//! the mutant→declaration converters) are DUPLICATED from
//! `check_fixtures.rs` instead of extracted into a shared
//! `tests/common/mod.rs`, so `check_fixtures.rs` stays byte-identical.
//! This whole file is deleted in Task 8's flip (the same commit that
//! ports `check_fixtures.rs` to the id kernel), so the duplication is
//! deliberately short-lived.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use leanr_kernel::bank::decl::{ConstantInfo as IdConstantInfo, Declaration as IdDeclaration};
use leanr_kernel::bank::env::Environment as IdEnvironment;
use leanr_kernel::bank::NameId;
use leanr_kernel::{ConstantInfo, Declaration, Environment, Name, ReplayStats};
use leanr_olean::{load_closure, ModuleData, PartKind, SearchPath};

// ---------------------------------------------------------------------------
// Fixture plumbing (duplicated from check_fixtures.rs — see module doc).
// ---------------------------------------------------------------------------

fn fixture_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures")
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

// ---------------------------------------------------------------------------
// The dual harness.
// ---------------------------------------------------------------------------

/// Build both kernels' replay inputs from a single decoded module,
/// mirroring `check_fixtures::constants_of` exactly on the Arc side
/// (`collect`, intra-module last-wins). The id side's `intern_module`
/// inserts in the same order, so its semantics are identical.
fn single_module_inputs(
    constants: Vec<ConstantInfo>,
) -> (
    HashMap<Arc<Name>, ConstantInfo>,
    IdEnvironment,
    HashMap<NameId, IdConstantInfo>,
) {
    let arc_constants: HashMap<Arc<Name>, ConstantInfo> = constants
        .iter()
        .map(|c| (Arc::clone(c.name()), c.clone()))
        .collect();
    let mut id_env = IdEnvironment::default();
    let id_constants = id_env
        .intern_module(constants)
        .expect("fixture module interns into the bank");
    (arc_constants, id_env, id_constants)
}

/// Build both kernels' replay inputs from a dependencies-first closure,
/// mirroring `check_fixtures`' per-constant `entry(..).or_insert(..)`
/// fold exactly on BOTH sides (first occurrence wins on cross-module
/// duplicates): the id side bridges one constant at a time so its
/// `or_insert` runs at the same granularity as the Arc fold.
fn closure_inputs(
    modules: Vec<(Arc<Name>, ModuleData)>,
) -> (
    HashMap<Arc<Name>, ConstantInfo>,
    IdEnvironment,
    HashMap<NameId, IdConstantInfo>,
) {
    let mut arc_constants: HashMap<Arc<Name>, ConstantInfo> = HashMap::new();
    let mut id_env = IdEnvironment::default();
    let mut id_constants: HashMap<NameId, IdConstantInfo> = HashMap::new();
    for (_, md) in modules {
        for c in md.constants {
            arc_constants
                .entry(Arc::clone(c.name()))
                .or_insert_with(|| c.clone());
            let bridged = id_env
                .intern_module(vec![c])
                .expect("fixture constant interns into the bank");
            for (k, v) in bridged {
                id_constants.entry(k).or_insert(v);
            }
        }
    }
    (arc_constants, id_env, id_constants)
}

/// The gate: replay the same constant set through both kernels from
/// empty environments and require identical verdicts. Returns the Arc
/// stats when both succeeded so callers can layer `check_fixtures`'
/// original sanity assertions on top; equal-`Err` verdicts also pass the
/// gate (and return `None`).
fn assert_dual_replay_verdicts(
    arc_constants: HashMap<Arc<Name>, ConstantInfo>,
    mut id_env: IdEnvironment,
    id_constants: HashMap<NameId, IdConstantInfo>,
) -> Option<ReplayStats> {
    // Arc path: exactly what check_fixtures.rs does today.
    let mut arc_env = Environment::default();
    let arc_verdict = leanr_kernel::replay(&mut arc_env, arc_constants);

    // Id path: bank env + intern_module fold (done by the caller) +
    // bank replay.
    let id_verdict = leanr_kernel::bank::replay::replay(&mut id_env, id_constants);

    match (arc_verdict, id_verdict) {
        (Ok(a), Ok(b)) => {
            assert_eq!(a.checked, b.checked, "checked count split (arc vs id)");
            assert_eq!(
                a.skipped_unsafe, b.skipped_unsafe,
                "skipped_unsafe count split (arc vs id)"
            );
            Some(a)
        }
        (Err(a), Err(b)) => {
            assert_eq!(a.error, b.error, "error payload split (arc vs id)");
            assert_eq!(a.decl, b.decl, "failing decl split (arc vs id)");
            None
        }
        (a, b) => panic!("verdict split: arc={a:?} id={b:?}"),
    }
}

// ---------------------------------------------------------------------------
// Replay-set duals.
// ---------------------------------------------------------------------------

/// Dual of `prelude0_replays_from_empty_env`.
#[test]
fn dual_prelude0_replays_identically() {
    let bytes = std::fs::read(fixture_path("Prelude0.olean")).unwrap();
    let m = ModuleData::parse(&bytes).unwrap();
    assert!(m.imports.is_empty(), "Prelude0 imports nothing");

    let (arc_constants, id_env, id_constants) = single_module_inputs(m.constants);
    let stats = assert_dual_replay_verdicts(arc_constants, id_env, id_constants)
        .expect("Prelude0 replays Ok (check_fixtures baseline)");
    assert!(
        stats.checked >= 3,
        "expected >= 3 checked, got {}",
        stats.checked
    );
    assert_eq!(stats.skipped_unsafe, 0);
}

/// Dual of `check_library_path_replays_prelude0_from_explicit_root`
/// (same module set as above, but through the `SearchPath` +
/// `load_closure` plumbing the CLI drives).
#[test]
fn dual_prelude0_via_library_path_replays_identically() {
    let sp = SearchPath::new(vec![fixtures_dir()]);
    let modules = load_closure(&sp, &[name("Prelude0")]).unwrap();
    assert_eq!(
        modules.len(),
        1,
        "Prelude0 has no imports, so its closure is itself"
    );

    let (arc_constants, id_env, id_constants) = closure_inputs(modules);
    let stats = assert_dual_replay_verdicts(arc_constants, id_env, id_constants)
        .expect("Prelude0 closure replays Ok (check_fixtures baseline)");
    assert!(
        stats.checked >= 3,
        "expected >= 3 checked, got {}",
        stats.checked
    );
    assert_eq!(stats.skipped_unsafe, 0);
}

/// Dual of `modpriv_parts_replay_from_empty_env` (module-mode multi-part
/// decode: base + server + private regions merged).
#[test]
fn dual_modpriv_parts_replay_identically() {
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

    let (arc_constants, id_env, id_constants) = single_module_inputs(md.constants);
    let stats = assert_dual_replay_verdicts(arc_constants, id_env, id_constants)
        .expect("ModPriv parts replay Ok (check_fixtures baseline)");
    assert!(
        stats.checked >= 5,
        "expected >= 5 checked, got {}",
        stats.checked
    );
    assert_eq!(stats.skipped_unsafe, 0);
}

/// Dual of `fixture_modules_replay_clean_with_closure`. Unlike the Arc
/// original (which requires `Ok` and is ignored because of the
/// documented pre-existing kernel blockers), the DUAL gate only requires
/// the two kernels to agree — equal `Err` verdicts pass too. Still
/// toolchain-gated: skipped when `LEANR_SWEEP_DIR` is unset (CI); run
/// locally with `LEANR_SWEEP_DIR=$(lean --print-libdir)`.
#[test]
#[ignore = "needs the pinned toolchain (LEANR_SWEEP_DIR); hermetic duals are the CI acceptance"]
fn dual_fixture_modules_closure_verdicts_identical() {
    let dir = std::env::var("LEANR_SWEEP_DIR")
        .expect("LEANR_SWEEP_DIR must point at the toolchain lib/lean dir");
    let sp = SearchPath::new(vec![fixtures_dir(), PathBuf::from(&dir)]);
    let targets = [name("Sample"), name("SampleRich")];
    let modules = load_closure(&sp, &targets).expect("closure loads");

    let (arc_constants, id_env, id_constants) = closure_inputs(modules);
    // Verdict equality IS the gate here; no Ok requirement.
    assert_dual_replay_verdicts(arc_constants, id_env, id_constants);
}

// ---------------------------------------------------------------------------
// Mutation-set duals: per-mutant admission against a trusted base, the
// exact per-declaration `add_decl` path check_fixtures' differential
// harness drives — full `Result<(), KernelError>` equality per mutant
// (KernelError is the same type on both sides).
// ---------------------------------------------------------------------------

/// Arc side of `check_fixtures::mutant_to_declaration`.
fn arc_mutant_to_declaration(ci: &ConstantInfo) -> Declaration {
    match ci {
        ConstantInfo::Defn(v) => Declaration::Defn(v.clone()),
        ConstantInfo::Thm(v) => Declaration::Thm(v.clone()),
        other => panic!("mutant {} is {}, not a def/thm", other.name(), other.kind()),
    }
}

/// Id twin of the above, over the bridged `bank::decl` types.
fn id_mutant_to_declaration(ci: &IdConstantInfo) -> IdDeclaration {
    match ci {
        IdConstantInfo::Defn(v) => IdDeclaration::Defn(v.clone()),
        IdConstantInfo::Thm(v) => IdDeclaration::Thm(v.clone()),
        other => panic!("mutant is {}, not a def/thm", other.kind()),
    }
}

/// For every mutant in the verdicts file: admit it through the Arc
/// kernel (clone of the trusted base env) and through the id kernel
/// (rebuilt trusted base — `bank::env::Environment` deliberately has no
/// `Clone`) and require the full `Result<(), KernelError>` to be equal.
/// Also requires the set to exercise BOTH gate arms (>= 5 accepts and
/// >= 5 rejects, the harness invariant check_fixtures enforces).
fn assert_dual_mutation_verdicts(base: Vec<ConstantInfo>, mutants: Vec<ConstantInfo>, text: &str) {
    let verdicts = parse_verdicts(text);
    assert!(!verdicts.is_empty(), "no mutant verdict lines in jsonl");

    let arc_base_env =
        Environment::from_modules([base.clone()]).expect("base env builds from import closure");
    let by_name: HashMap<String, &ConstantInfo> =
        mutants.iter().map(|c| (c.name().to_string(), c)).collect();

    let mut accepts = 0usize;
    let mut rejects = 0usize;
    let mut splits: Vec<String> = Vec::new();
    for (name, _oracle) in &verdicts {
        let ci = by_name
            .get(name)
            .unwrap_or_else(|| panic!("mutant {name} is in the jsonl but missing from the olean"));

        // Arc path: exactly what check_fixtures does per mutant.
        let mut arc_env = arc_base_env.clone();
        let arc_res = arc_env.add_decl(arc_mutant_to_declaration(ci));

        // Id path: fresh trusted base, bridge just this mutant, admit it.
        let mut id_env =
            IdEnvironment::from_modules([base.clone()]).expect("id base env builds from closure");
        let bridged = id_env
            .intern_module(vec![(*ci).clone()])
            .expect("mutant interns into the bank");
        assert_eq!(bridged.len(), 1, "one mutant bridges to one constant");
        let id_ci = bridged.into_values().next().expect("just checked len == 1");
        let id_res = id_env.add_decl(id_mutant_to_declaration(&id_ci));

        match &arc_res {
            Ok(()) => accepts += 1,
            Err(_) => rejects += 1,
        }
        if arc_res != id_res {
            splits.push(format!("  {name}: arc={arc_res:?} id={id_res:?}"));
        }
    }

    assert!(
        splits.is_empty(),
        "id kernel split from Arc kernel on {} mutant(s):\n{}",
        splits.len(),
        splits.join("\n")
    );
    // Both gate arms exercised: accepted mutants prove the both-Ok arm,
    // rejected mutants prove the both-Err (equal error payload) arm.
    assert!(accepts >= 5, "harness needs >= 5 accepts, got {accepts}");
    assert!(rejects >= 5, "harness needs >= 5 rejects, got {rejects}");
}

/// Dual of `mutation_verdicts_hermetic` (runs in CI).
#[test]
fn dual_mutation_verdicts_hermetic() {
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
    assert_dual_mutation_verdicts(base, mutants, &text);
}

/// Dual of `mutation_verdicts_toolchain`. Skipped when `LEANR_SWEEP_DIR`
/// is unset (CI); run locally with `LEANR_SWEEP_DIR=$(lean --print-libdir)`.
/// Note: the id side rebuilds the trusted `Init.Core`-closure base per
/// mutant (no `Clone` on the bank env), so this is slow — acceptable for
/// an ignored, local-only gate that Task 8 deletes.
#[test]
#[ignore = "needs the pinned toolchain (LEANR_SWEEP_DIR); the hermetic dual is the CI acceptance"]
fn dual_mutation_verdicts_toolchain() {
    let dir = std::env::var("LEANR_SWEEP_DIR")
        .expect("LEANR_SWEEP_DIR must point at the toolchain lib/lean dir");
    let mut_bytes = std::fs::read(fixture_path("Mutations.olean"))
        .expect("Mutations.olean missing — run `mise run fixtures:mutations`");
    let text = std::fs::read_to_string(fixture_path("mutations-verdicts.jsonl"))
        .expect("mutations-verdicts.jsonl missing — run `mise run fixtures:mutations`");

    let sp = SearchPath::new(vec![PathBuf::from(&dir)]);
    let modules = load_closure(&sp, &[name("Init.Core")]).expect("Init.Core closure loads");
    let mut base: Vec<ConstantInfo> = Vec::new();
    let mut seen: std::collections::HashSet<Arc<Name>> = std::collections::HashSet::new();
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
    assert_dual_mutation_verdicts(base, mutants, &text);
}
