// Id-native port (migration Task 8): `Environment::from_modules` takes
// the decoder-boundary `Arc*` types (`ArcConstantInfo`/…, aliased here to
// their pre-migration bare names since this file never touches the
// id-native types by name) and bridge-interns them; the environment it
// returns is keyed by `NameId`, not `Arc<Name>`, so name-presence checks
// go through the public `view()`/`store.to_name` bridge instead of a
// `NameId`-less `get(&Arc<Name>)` (which no longer exists — see
// `Environment::get(NameId)`).
use std::sync::Arc;

use leanr_kernel::{
    ArcAxiomVal as AxiomVal, ArcConstantInfo as ConstantInfo, ArcConstantVal as ConstantVal,
    Environment, EnvironmentError, Expr, Level, Name, RecGuard,
};

fn name(s: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: s.to_string(),
    })
}

fn axiom_named(s: &str) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        val: ConstantVal {
            name: name(s),
            level_params: Vec::new(),
            ty: Expr::sort(Arc::new(Level::Zero), &mut RecGuard::new()).unwrap(),
        },
        is_unsafe: false,
    })
}

/// Bridge-side name lookup: `env.view()`/`store.to_name` are the public
/// id -> `Arc<Name>` path (same one `EnvView::get_with`'s error
/// construction uses internally).
fn has_name(env: &Environment, s: &str) -> bool {
    let view = env.view();
    view.consts
        .values()
        .any(|ci| view.store.to_name(None, Some(ci.name())).to_string() == s)
}

#[test]
fn kind_strings_match_the_oracle_dump_script() {
    // Must stay in lockstep with kindStr in tests/fixtures/dump_decls.lean.
    assert_eq!(axiom_named("a").kind(), "axiom");
}

#[test]
fn from_modules_merges_and_indexes_by_name() {
    let env = Environment::from_modules([
        vec![axiom_named("a"), axiom_named("b")],
        vec![axiom_named("c")],
    ])
    .unwrap();
    assert_eq!(env.len(), 3);
    assert!(has_name(&env, "b"));
    assert!(!has_name(&env, "zzz"));
}

#[test]
fn from_modules_rejects_duplicate_names() {
    // Not `.unwrap_err()`: the id-native `Environment` does not derive
    // `Debug` (its persistent bank holds several `bank`-internal types
    // that don't either), so a plain match avoids requiring it just for
    // this assertion.
    let err = match Environment::from_modules([vec![axiom_named("a")], vec![axiom_named("a")]]) {
        Ok(_) => panic!("expected a duplicate-name error"),
        Err(e) => e,
    };
    let msg = format!("{err:?}");
    let EnvironmentError::DuplicateName(n) = err else {
        panic!("expected DuplicateName, got {msg}");
    };
    assert_eq!(n.to_string(), "a");
}
