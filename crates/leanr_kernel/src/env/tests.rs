//! Task 8: the `Declaration` admission-pipeline rejection corpus. Built
//! against the shared `crate::testenv::mini` fixture (promoted here
//! from `tc/tests.rs` in this same task) rather than a fresh ad-hoc
//! environment per test.

use super::*;
use crate::testenv::{mini, nm, nm2};
use crate::{AxiomVal, DefinitionVal, OpaqueVal, TheoremVal};

fn cv(name: &str, level_params: Vec<Arc<Name>>, ty: Arc<Expr>) -> ConstantVal {
    ConstantVal {
        name: nm(name),
        level_params,
        ty,
    }
}

#[test]
fn admits_wellformed_axiom_def_thm_opaque() {
    let mut env = mini::env();
    let len_before = env.len();

    env.add_decl(Declaration::Axiom(AxiomVal {
        val: cv("myAxiom", vec![], mini::sort0()),
        is_unsafe: false,
    }))
    .unwrap();

    env.add_decl(Declaration::Defn(DefinitionVal {
        val: cv("myDef", vec![], mini::cst("A", vec![])),
        value: mini::cst("a", vec![]),
        hints: crate::ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Safe,
        all: vec![nm("myDef")],
    }))
    .unwrap();

    env.add_decl(Declaration::Thm(TheoremVal {
        val: cv("myThm", vec![], mini::cst("A", vec![])),
        value: mini::cst("a", vec![]),
        all: vec![nm("myThm")],
    }))
    .unwrap();

    env.add_decl(Declaration::Opaque(OpaqueVal {
        val: cv("myOpaque", vec![], mini::cst("A", vec![])),
        value: mini::cst("a", vec![]),
        is_unsafe: false,
        all: vec![nm("myOpaque")],
    }))
    .unwrap();

    assert_eq!(env.len(), len_before + 4);
    assert!(matches!(
        env.get(&nm("myAxiom")),
        Some(ConstantInfo::Axiom(_))
    ));
    assert!(matches!(env.get(&nm("myDef")), Some(ConstantInfo::Defn(_))));
    assert!(matches!(env.get(&nm("myThm")), Some(ConstantInfo::Thm(_))));
    assert!(matches!(
        env.get(&nm("myOpaque")),
        Some(ConstantInfo::Opaque(_))
    ));
}

#[test]
fn rejects_duplicate_name() {
    let mut env = mini::env();
    let err = env
        .add_decl(Declaration::Axiom(AxiomVal {
            val: cv("A", vec![], mini::sort0()),
            is_unsafe: false,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::AlreadyDeclared(nm("A")));
}

#[test]
fn rejects_duplicate_univ_param() {
    let mut env = mini::env();
    let p = nm("p");
    let err = env
        .add_decl(Declaration::Axiom(AxiomVal {
            val: cv(
                "dupAx",
                vec![Arc::clone(&p), Arc::clone(&p)],
                mini::sort_param("p"),
            ),
            is_unsafe: false,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::DuplicateUnivParam(p));
}

#[test]
fn rejects_mvar_in_type_or_value() {
    // In the declared type.
    let mut env = mini::env();
    let err = env
        .add_decl(Declaration::Axiom(AxiomVal {
            val: cv("mvarAx", vec![], Expr::mvar(nm("m"))),
            is_unsafe: false,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::HasMetavars(nm("mvarAx")));

    // In the value.
    let mut env2 = mini::env();
    let err2 = env2
        .add_decl(Declaration::Defn(DefinitionVal {
            val: cv("mvarDef", vec![], mini::cst("A", vec![])),
            value: Expr::mvar(nm("m")),
            hints: crate::ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("mvarDef")],
        }))
        .unwrap_err();
    assert_eq!(err2, KernelError::HasMetavars(nm("mvarDef")));
}

#[test]
fn rejects_fvar_in_type_or_value() {
    // In the declared type.
    let mut env = mini::env();
    let err = env
        .add_decl(Declaration::Axiom(AxiomVal {
            val: cv("fvarAx", vec![], Expr::fvar(nm("x"))),
            is_unsafe: false,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::HasFVars(nm("fvarAx")));

    // In the value.
    let mut env2 = mini::env();
    let err2 = env2
        .add_decl(Declaration::Defn(DefinitionVal {
            val: cv("fvarDef", vec![], mini::cst("A", vec![])),
            value: Expr::fvar(nm("x")),
            hints: crate::ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("fvarDef")],
        }))
        .unwrap_err();
    assert_eq!(err2, KernelError::HasFVars(nm("fvarDef")));
}

#[test]
fn rejects_type_that_is_not_a_sort() {
    // axiom badTy : Nat.zero -- Nat.zero's own type is `Nat`, not a Sort.
    let mut env = mini::env();
    let err = env
        .add_decl(Declaration::Axiom(AxiomVal {
            val: cv("badTy", vec![], mini::cstn(nm2("Nat", "zero"), vec![])),
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
    let err = env
        .add_decl(Declaration::Defn(DefinitionVal {
            val: cv("x", vec![], mini::cst("A", vec![])),
            value: mini::cst("bt", vec![]),
            hints: crate::ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("x")],
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::DefTypeMismatch(nm("x")));
}

#[test]
fn rejects_theorem_not_prop() {
    // thm myThmBad : B := bt -- `B : Type`, not a `Prop`.
    let mut env = mini::env();
    let err = env
        .add_decl(Declaration::Thm(TheoremVal {
            val: cv("myThmBad", vec![], mini::cst("B", vec![])),
            value: mini::cst("bt", vec![]),
            all: vec![nm("myThmBad")],
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::TheoremTypeNotProp(nm("myThmBad")));
}

#[test]
fn rejects_unknown_constant_in_value() {
    let mut env = mini::env();
    let err = env
        .add_decl(Declaration::Defn(DefinitionVal {
            val: cv("y", vec![], mini::cst("A", vec![])),
            value: mini::cst("does_not_exist", vec![]),
            hints: crate::ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("y")],
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::UnknownConstant(nm("does_not_exist")));
}

#[test]
fn rejects_unsafe_defn_at_add_decl() {
    let mut env = mini::env();
    let err = env
        .add_decl(Declaration::Defn(DefinitionVal {
            val: cv("unsafeDef", vec![], mini::cst("A", vec![])),
            value: mini::cst("a", vec![]),
            hints: crate::ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Unsafe,
            all: vec![nm("unsafeDef")],
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::UnsafeConstInSafeDecl(nm("unsafeDef")));
}

#[test]
fn env_unchanged_after_rejection() {
    let mut env = mini::env();
    let len_before = env.len();
    let a_before: *const ConstantInfo = env.get(&nm("A")).unwrap() as *const _;

    let err = env
        .add_decl(Declaration::Axiom(AxiomVal {
            val: cv("A", vec![], mini::sort0()),
            is_unsafe: false,
        }))
        .unwrap_err();
    assert_eq!(err, KernelError::AlreadyDeclared(nm("A")));

    assert_eq!(env.len(), len_before);
    let a_after: *const ConstantInfo = env.get(&nm("A")).unwrap() as *const _;
    assert_eq!(a_before, a_after);

    // A rejected Defn specifically must not partially extend the
    // environment either: `add_decl` only calls `add_core` once, after
    // every check has succeeded, so a mid-pipeline `DefTypeMismatch`
    // (the ill-typed-value case) must leave `get`/`len` just as
    // untouched as the AlreadyDeclared case above.
    let err2 = env
        .add_decl(Declaration::Defn(DefinitionVal {
            val: cv("z", vec![], mini::cst("A", vec![])),
            value: mini::cst("bt", vec![]),
            hints: crate::ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("z")],
        }))
        .unwrap_err();
    assert_eq!(err2, KernelError::DefTypeMismatch(nm("z")));
    assert_eq!(env.len(), len_before);
    assert!(env.get(&nm("z")).is_none());
}
