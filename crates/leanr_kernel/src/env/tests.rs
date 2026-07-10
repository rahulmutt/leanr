//! `Environment::add_decl` admission-pipeline rejection corpus
//! (migration Task 8: ported from the pre-flip `crate::env::tests` — the
//! Arc environment these once dual-compared against is deleted, so each
//! test now asserts the same expected value directly against the
//! id-native `Environment`; see
//! `git show 9b1c773:crates/leanr_kernel/src/env/tests.rs` for the
//! original). `KernelError` still carries `Arc<Name>` payloads (built at
//! the error site via `to_name`), so every expected-error assertion
//! below is unchanged from the Arc original.
//!
//! Every test builds the shared `crate::testenv::mini::env()` fixture
//! (now id-native: it interns+admits through the real
//! `Environment::from_modules`/`add_decl` path) and interns a new
//! declaration's names/exprs directly into that same `Environment`'s
//! persistent store — legal because `tests` is a child module of `env`,
//! which owns `Environment`'s fields.

use super::*;
use crate::bank::terms::Node;
use crate::decl::InductiveType;
use crate::testenv::{mini, nm, nm2};
use crate::used_consts::used_constants;
use crate::{Expr, ReducibilityHints};
use std::sync::Arc;

// ---- builder helpers ---------------------------------------------------

fn nm_id(env: &mut Environment, s: &str) -> NameId {
    env.store.intern_name(None, &nm(s)).unwrap().unwrap()
}

fn expr_id(env: &mut Environment, e: &Arc<Expr>) -> ExprId {
    env.store.intern_expr(None, e).unwrap()
}

fn cv(env: &mut Environment, name: &str, level_params: Vec<&str>, ty: Arc<Expr>) -> ConstantVal {
    let level_params: Vec<NameId> = level_params.into_iter().map(|p| nm_id(env, p)).collect();
    let name_id = nm_id(env, name);
    let ty_id = expr_id(env, &ty);
    ConstantVal {
        name: name_id,
        level_params,
        ty: ty_id,
    }
}

// ---- ported admission-pipeline tests -----------------------------------

#[test]
fn admits_wellformed_axiom_def_thm_opaque() {
    let mut env = mini::env();
    let len_before = env.len();

    let my_axiom_id = nm_id(&mut env, "myAxiom");
    let val = cv(&mut env, "myAxiom", vec![], mini::sort0());
    env.add_decl(Declaration::Axiom(AxiomVal {
        val,
        is_unsafe: false,
    }))
    .unwrap();

    let my_def_id = nm_id(&mut env, "myDef");
    {
        let val = cv(&mut env, "myDef", vec![], mini::cst("A", vec![]));
        let value = expr_id(&mut env, &mini::cst("a", vec![]));
        env.add_decl(Declaration::Defn(DefinitionVal {
            val,
            value,
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![my_def_id],
        }))
        .unwrap();
    }

    let my_thm_id = nm_id(&mut env, "myThm");
    {
        let val = cv(&mut env, "myThm", vec![], mini::cst("A", vec![]));
        let value = expr_id(&mut env, &mini::cst("a", vec![]));
        env.add_decl(Declaration::Thm(TheoremVal {
            val,
            value,
            all: vec![my_thm_id],
        }))
        .unwrap();
    }

    let my_opaque_id = nm_id(&mut env, "myOpaque");
    {
        let val = cv(&mut env, "myOpaque", vec![], mini::cst("A", vec![]));
        let value = expr_id(&mut env, &mini::cst("a", vec![]));
        env.add_decl(Declaration::Opaque(OpaqueVal {
            val,
            value,
            is_unsafe: false,
            all: vec![my_opaque_id],
        }))
        .unwrap();
    }

    assert_eq!(env.len(), len_before + 4);
    assert!(matches!(env.get(my_axiom_id), Some(ConstantInfo::Axiom(_))));
    assert!(matches!(env.get(my_def_id), Some(ConstantInfo::Defn(_))));
    assert!(matches!(env.get(my_thm_id), Some(ConstantInfo::Thm(_))));
    assert!(matches!(
        env.get(my_opaque_id),
        Some(ConstantInfo::Opaque(_))
    ));
}

#[test]
fn rejects_duplicate_name() {
    let mut env = mini::env();
    let val = cv(&mut env, "A", vec![], mini::sort0());
    let err = env
        .add_decl(Declaration::Axiom(AxiomVal {
            val,
            is_unsafe: false,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::AlreadyDeclared(nm("A")));
}

#[test]
fn rejects_duplicate_univ_param() {
    let mut env = mini::env();
    let val = cv(&mut env, "dupAx", vec!["p", "p"], mini::sort_param("p"));
    let err = env
        .add_decl(Declaration::Axiom(AxiomVal {
            val,
            is_unsafe: false,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::DuplicateUnivParam(nm("p")));
}

#[test]
fn rejects_mvar_in_type_or_value() {
    // In the declared type.
    let mut env = mini::env();
    let val = cv(&mut env, "mvarAx", vec![], Expr::mvar(nm("m")));
    let err = env
        .add_decl(Declaration::Axiom(AxiomVal {
            val,
            is_unsafe: false,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::HasMetavars(nm("mvarAx")));

    // In the value.
    let mut env2 = mini::env();
    let val2 = cv(&mut env2, "mvarDef", vec![], mini::cst("A", vec![]));
    let value2 = expr_id(&mut env2, &Expr::mvar(nm("m")));
    let all2 = vec![nm_id(&mut env2, "mvarDef")];
    let err2 = env2
        .add_decl(Declaration::Defn(DefinitionVal {
            val: val2,
            value: value2,
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: all2,
        }))
        .unwrap_err();
    assert_eq!(err2, KernelError::HasMetavars(nm("mvarDef")));
}

#[test]
fn rejects_fvar_in_type_or_value() {
    // In the declared type.
    let mut env = mini::env();
    let val = cv(&mut env, "fvarAx", vec![], Expr::fvar(nm("x")));
    let err = env
        .add_decl(Declaration::Axiom(AxiomVal {
            val,
            is_unsafe: false,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::HasFVars(nm("fvarAx")));

    // In the value.
    let mut env2 = mini::env();
    let val2 = cv(&mut env2, "fvarDef", vec![], mini::cst("A", vec![]));
    let value2 = expr_id(&mut env2, &Expr::fvar(nm("x")));
    let all2 = vec![nm_id(&mut env2, "fvarDef")];
    let err2 = env2
        .add_decl(Declaration::Defn(DefinitionVal {
            val: val2,
            value: value2,
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: all2,
        }))
        .unwrap_err();
    assert_eq!(err2, KernelError::HasFVars(nm("fvarDef")));
}

#[test]
fn rejects_type_that_is_not_a_sort() {
    // axiom badTy : Nat.zero -- Nat.zero's own type is `Nat`, not a Sort.
    let mut env = mini::env();
    let val = cv(
        &mut env,
        "badTy",
        vec![],
        mini::cstn(nm2("Nat", "zero"), vec![]),
    );
    let err = env
        .add_decl(Declaration::Axiom(AxiomVal {
            val,
            is_unsafe: false,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::TypeExpected);
}

#[test]
fn rejects_ill_typed_value() {
    // def x : A := bt -- `bt : B`, and `A` and `B` are distinct opaque
    // constants (Prop vs Type respectively in `mini::env`), not defeq.
    let mut env = mini::env();
    let val = cv(&mut env, "x", vec![], mini::cst("A", vec![]));
    let value = expr_id(&mut env, &mini::cst("bt", vec![]));
    let all = vec![nm_id(&mut env, "x")];
    let err = env
        .add_decl(Declaration::Defn(DefinitionVal {
            val,
            value,
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::DefTypeMismatch(nm("x")));
}

#[test]
fn rejects_theorem_not_prop() {
    // thm myThmBad : B := bt -- `B : Type`, not a `Prop`.
    let mut env = mini::env();
    let val = cv(&mut env, "myThmBad", vec![], mini::cst("B", vec![]));
    let value = expr_id(&mut env, &mini::cst("bt", vec![]));
    let all = vec![nm_id(&mut env, "myThmBad")];
    let err = env
        .add_decl(Declaration::Thm(TheoremVal { val, value, all }))
        .unwrap_err();
    assert_eq!(err, KernelError::TheoremTypeNotProp(nm("myThmBad")));
}

#[test]
fn rejects_unknown_constant_in_value() {
    let mut env = mini::env();
    let val = cv(&mut env, "y", vec![], mini::cst("A", vec![]));
    let value = expr_id(&mut env, &mini::cst("does_not_exist", vec![]));
    let all = vec![nm_id(&mut env, "y")];
    let err = env
        .add_decl(Declaration::Defn(DefinitionVal {
            val,
            value,
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::UnknownConstant(nm("does_not_exist")));
}

#[test]
fn rejects_unsafe_defn_at_add_decl() {
    let mut env = mini::env();
    let val = cv(&mut env, "unsafeDef", vec![], mini::cst("A", vec![]));
    let value = expr_id(&mut env, &mini::cst("a", vec![]));
    let all = vec![nm_id(&mut env, "unsafeDef")];
    let err = env
        .add_decl(Declaration::Defn(DefinitionVal {
            val,
            value,
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Unsafe,
            all,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::UnsafeConstInSafeDecl(nm("unsafeDef")));
}

#[test]
fn env_unchanged_after_rejection() {
    let mut env = mini::env();
    let len_before = env.len();

    let a_id = nm_id(&mut env, "A");
    let a_before = env.get(a_id).unwrap().clone();

    let val = cv(&mut env, "A", vec![], mini::sort0());
    let err = env
        .add_decl(Declaration::Axiom(AxiomVal {
            val,
            is_unsafe: false,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::AlreadyDeclared(nm("A")));

    assert_eq!(env.len(), len_before);
    let a_after = env.get(a_id).unwrap();
    assert!(
        crate::decl::constant_info_eq(&a_before, a_after),
        "rejected add_decl must not mutate the existing entry"
    );

    // A rejected Defn specifically must not partially extend the
    // environment either: `add_decl` only calls `add_core` once, after
    // every check has succeeded, so a mid-pipeline `DefTypeMismatch`
    // must leave `get`/`len` just as untouched as the AlreadyDeclared
    // case above.
    let z_id = nm_id(&mut env, "z");
    let val2 = cv(&mut env, "z", vec![], mini::cst("A", vec![]));
    let value2 = expr_id(&mut env, &mini::cst("bt", vec![]));
    let err2 = env
        .add_decl(Declaration::Defn(DefinitionVal {
            val: val2,
            value: value2,
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![z_id],
        }))
        .unwrap_err();
    assert_eq!(err2, KernelError::DefTypeMismatch(nm("z")));
    assert_eq!(env.len(), len_before);
    assert!(env.get(z_id).is_none());
}

// ---- promotion-specific region-discipline gate -------------------------

#[test]
fn admitted_inductive_has_no_scratch_ids() {
    let mut env = Environment::default();
    let foo_name = nm_id(&mut env, "Foo");
    let mk_name = nm_id(&mut env, "Foo.mk");
    let ty1 = expr_id(&mut env, &mini::type1());
    let foo_const = expr_id(&mut env, &mini::cstn(nm("Foo"), vec![]));

    env.add_decl(Declaration::Inductive {
        lparams: vec![],
        nparams: Nat::from(0u64),
        types: vec![InductiveType {
            name: foo_name,
            ty: ty1,
            ctors: vec![(mk_name, foo_const)],
        }],
        is_unsafe: false,
    })
    .unwrap();

    for ci in env.constants.values() {
        assert_no_scratch_ids(&env.store, ci);
    }
}

/// Assert every id reachable from `ci` — declaration-position names,
/// `used_constants`'s cross-references, and every id embedded in every
/// `ExprId` field (type, value, recursor-rule right-hand-sides) — is
/// persistent-region. This is the region-discipline gate `add_core`'s
/// `promote_constant_info` must satisfy for every admitted constant.
fn assert_no_scratch_ids(st: &Store, ci: &ConstantInfo) {
    let cv = ci.constant_val();
    assert!(!cv.name.is_scratch(), "ConstantVal.name scratch: {ci:?}");
    for &lp in &cv.level_params {
        assert!(!lp.is_scratch(), "level_params scratch: {ci:?}");
    }
    walk_expr_ids(st, cv.ty);
    for dep in used_constants(st, None, ci) {
        assert!(!dep.is_scratch(), "used_constants dep scratch: {ci:?}");
    }
    match ci {
        ConstantInfo::Axiom(_) => {}
        ConstantInfo::Defn(v) => {
            for &n in &v.all {
                assert!(!n.is_scratch());
            }
            walk_expr_ids(st, v.value);
        }
        ConstantInfo::Thm(v) => {
            for &n in &v.all {
                assert!(!n.is_scratch());
            }
            walk_expr_ids(st, v.value);
        }
        ConstantInfo::Opaque(v) => {
            for &n in &v.all {
                assert!(!n.is_scratch());
            }
            walk_expr_ids(st, v.value);
        }
        ConstantInfo::Quot(_) => {}
        ConstantInfo::Induct(v) => {
            for &n in &v.all {
                assert!(!n.is_scratch());
            }
            for &n in &v.ctors {
                assert!(!n.is_scratch());
            }
        }
        ConstantInfo::Ctor(v) => assert!(!v.induct.is_scratch()),
        ConstantInfo::Rec(v) => {
            for &n in &v.all {
                assert!(!n.is_scratch());
            }
            for r in &v.rules {
                assert!(!r.ctor.is_scratch());
                walk_expr_ids(st, r.rhs);
            }
        }
    }
}

/// Explicit-stack walk over every expr row reachable from `root`,
/// asserting every embedded `NameId`/`LevelId` (including `Const`'s
/// level list) is persistent-region. Mirrors `scratch::promote`'s own
/// traversal shape, minus the actual promotion.
fn walk_expr_ids(st: &Store, root: ExprId) {
    let mut stack = vec![root];
    let mut seen = std::collections::HashSet::new();
    while let Some(e) = stack.pop() {
        assert!(!e.is_scratch(), "expr id scratch: {e:?}");
        if !seen.insert(e) {
            continue;
        }
        match st.expr_node(None, e) {
            Node::BVar { .. }
            | Node::BVarBig { .. }
            | Node::LitNat { .. }
            | Node::LitStr { .. } => {}
            Node::FVar { id } | Node::MVar { id } => {
                if let Some(n) = id {
                    assert!(!n.is_scratch());
                }
            }
            Node::Sort { level } => assert!(!level.is_scratch()),
            Node::Const { name, levels } => {
                if let Some(n) = name {
                    assert!(!n.is_scratch());
                }
                for l in st.level_list_at(None, levels) {
                    assert!(!l.is_scratch());
                }
            }
            Node::App { f, arg } => {
                stack.push(f);
                stack.push(arg);
            }
            Node::Lam {
                binder_name,
                binder_type,
                body,
                ..
            }
            | Node::Forall {
                binder_name,
                binder_type,
                body,
                ..
            } => {
                if let Some(n) = binder_name {
                    assert!(!n.is_scratch());
                }
                stack.push(binder_type);
                stack.push(body);
            }
            Node::LetE {
                decl_name,
                ty,
                value,
                body,
                ..
            } => {
                if let Some(n) = decl_name {
                    assert!(!n.is_scratch());
                }
                stack.push(ty);
                stack.push(value);
                stack.push(body);
            }
            Node::MData { expr, .. } => stack.push(expr),
            Node::Proj {
                type_name,
                structure,
                ..
            }
            | Node::ProjBig {
                type_name,
                structure,
                ..
            } => {
                if let Some(n) = type_name {
                    assert!(!n.is_scratch());
                }
                stack.push(structure);
            }
        }
    }
}

#[test]
fn admit_unchecked_inserts_and_rejects_duplicates() {
    let mut env = Environment::default();
    let arc_ci = crate::testenv::axiom_u();
    let ci = crate::decl::intern_constant_info(env.store_mut(), None, &arc_ci).unwrap();
    let name = ci.name();
    env.admit_unchecked(ci.clone()).unwrap();
    assert!(env.get(name).is_some());
    assert!(matches!(
        env.admit_unchecked(ci),
        Err(EnvironmentError::DuplicateName(_))
    ));
}

// ---- ported from the pre-flip `crates/leanr_kernel/tests/env.rs` ------
//
// That was an external integration-test crate exercising
// `Environment::from_modules` as a "production" bridge entry point.
// Term-bank phase 3's flip made `from_modules`/`intern_module`/
// `intern_declaration` (and the `Arc*` decl types they take) test-only
// (`#[cfg(test)]` — see `decl.rs`'s module doc): an external integration
// test crate compiles the library WITHOUT `--cfg test`, so it can no
// longer see any of them. Moved in-crate, where `#[cfg(test)]` is in
// effect, unchanged otherwise.

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

fn axiom_named(s: &str) -> crate::ArcConstantInfo {
    crate::ArcConstantInfo::Axiom(crate::ArcAxiomVal {
        val: crate::ArcConstantVal {
            name: nm(s),
            level_params: Vec::new(),
            ty: Expr::sort(Arc::new(crate::Level::Zero), &mut crate::RecGuard::new()).unwrap(),
        },
        is_unsafe: false,
    })
}

/// Bridge-side name lookup: `env.view()`/`store.to_name` are the public
/// id -> `Arc<Name>` path (same one `EnvView::get_with`'s error
/// construction uses internally).
fn has_name(env: &Environment, s: &str) -> bool {
    let view = env.view();
    let crate::ConstSource::Plain(consts) = view.consts else {
        unreachable!("has_name: test helper assumes Environment::view()'s Plain source")
    };
    consts
        .values()
        .any(|ci| view.store.to_name(None, Some(ci.name())).to_string() == s)
}

#[test]
fn check_declaration_returns_survivor_without_mutating_env() {
    // A trusted base env with `Nat` admitted, and a simple axiom decl
    // referencing only already-admitted constants.
    let mut env = mini::env();
    let before = env.len();
    let val = cv(&mut env, "myAxiom", vec![], mini::sort0());
    let d = Declaration::Axiom(AxiomVal {
        val,
        is_unsafe: false,
    });

    let mut scratch = crate::bank::Store::scratch();
    let admitted = crate::check_declaration(env.view(), &mut scratch, d).unwrap();

    assert_eq!(admitted.survivors.len(), 1);
    assert!(!admitted.quot_init);
    // check_declaration must NOT have inserted anything into env.
    assert_eq!(env.len(), before);
}
