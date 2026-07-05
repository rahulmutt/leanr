//! Integration: decode fixture `.olean`s and replay them through the
//! kernel (Task 12). This is where decoded modules meet the checker.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use leanr_kernel::{ConstantInfo, Environment, Name};
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
