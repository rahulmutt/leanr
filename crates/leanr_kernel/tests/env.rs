use std::sync::Arc;

use leanr_kernel::{
    AxiomVal, ConstantInfo, ConstantVal, Environment, EnvironmentError, Expr, Level, Name, RecGuard,
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
    assert!(env.get(&name("b")).is_some());
    assert!(env.get(&name("zzz")).is_none());
}

#[test]
fn from_modules_rejects_duplicate_names() {
    let err =
        Environment::from_modules([vec![axiom_named("a")], vec![axiom_named("a")]]).unwrap_err();
    let EnvironmentError::DuplicateName(n) = err;
    assert_eq!(n.to_string(), "a");
}
