//! Dual-checker differential harness for `bank::env::Environment`
//! (migration Task 6) — id-twin of `crate::env::tests`. `KernelError` is
//! the SAME type on both sides of the migration (`bank::decl` imports
//! `crate::KernelError` directly, no bank-local copy), so `assert_eq!`
//! on the two `add_decl` results is an exact comparison, not an
//! approximation — a verdict split shows up as a literal `assert_eq!`
//! failure rather than a hand-rolled comparator.
//!
//! Every test below builds the SAME `crate::testenv::mini` fixture
//! (bridged into the id bank via `bank::decl::intern_constant_info`,
//! matching `bank::quot::tests`' `bridge_consts` precedent — no
//! re-running the checking pipeline a second time) and the same
//! declaration the Arc test constructs, then runs `add_decl` on both and
//! compares.

use super::*;
use crate::bank::decl::{
    intern_constant_info, AxiomVal, ConstantInfo, ConstantVal, Declaration, DefinitionVal,
    OpaqueVal, TheoremVal,
};
use crate::bank::terms::Node;
use crate::bank::used_consts::used_constants;
use crate::testenv::mini as arc_mini;
use crate::{
    AxiomVal as ArcAxiomVal, ConstantVal as ArcConstantVal, Declaration as ArcDeclaration,
    DefinitionSafety, DefinitionVal as ArcDefinitionVal, Expr, Nat, OpaqueVal as ArcOpaqueVal,
    ReducibilityHints, TheoremVal as ArcTheoremVal,
};
use std::collections::HashMap;
use std::sync::Arc;

// ---- bridging / builder helpers ---------------------------------------

/// Bridge every already-admitted constant of the Arc `mini::env()`
/// fixture (Task 11's real Quot admission included) directly into a
/// fresh persistent `Store`, matching the fixture's post-admission
/// state without re-running the checking pipeline a second time.
/// Private-field struct literal: legal here because `tests` is a child
/// module of `env`, which owns `Environment`'s fields.
fn mini_env() -> Environment {
    let arc_env = arc_mini::env();
    let mut store = Store::persistent();
    let mut constants = HashMap::new();
    for ci in arc_env.iter() {
        let idci = intern_constant_info(&mut store, None, ci).unwrap();
        constants.insert(idci.name(), idci);
    }
    Environment {
        store,
        constants,
        quot_initialized: true,
    }
}

fn nm_id(env: &mut Environment, s: &str) -> NameId {
    env.store
        .intern_name(None, &crate::testenv::nm(s))
        .unwrap()
        .unwrap()
}

fn expr_id(env: &mut Environment, e: &Arc<Expr>) -> ExprId {
    env.store.intern_expr(None, e).unwrap()
}

fn id_cv(env: &mut Environment, name: &str, level_params: Vec<&str>, ty: Arc<Expr>) -> ConstantVal {
    let level_params: Vec<NameId> = level_params.into_iter().map(|p| nm_id(env, p)).collect();
    let name_id = nm_id(env, name);
    let ty_id = expr_id(env, &ty);
    ConstantVal {
        name: name_id,
        level_params,
        ty: ty_id,
    }
}

fn arc_cv(name: &str, level_params: Vec<Arc<crate::Name>>, ty: Arc<Expr>) -> ArcConstantVal {
    ArcConstantVal {
        name: crate::testenv::nm(name),
        level_params,
        ty,
    }
}

/// Run `add_decl` with logically-equivalent declarations on a fresh Arc
/// `mini::env()` and its id-native bridge, assert the two `KernelError`
/// verdicts are exactly equal (shared error type — see module doc), and
/// on success assert the two environments' sizes stayed in lockstep.
/// Returns both post-`add_decl` environments for tests needing further
/// independent assertions.
fn assert_add_decl_matches(
    mk_arc: impl FnOnce() -> ArcDeclaration,
    mk_id: impl FnOnce(&mut Environment) -> Declaration,
) -> (crate::Environment, Environment) {
    let mut arc_env = arc_mini::env();
    let arc_result = arc_env.add_decl(mk_arc());

    let mut id_env = mini_env();
    let id_decl = mk_id(&mut id_env);
    let id_result = id_env.add_decl(id_decl);

    assert_eq!(arc_result, id_result, "verdict split");
    if arc_result.is_ok() {
        assert_eq!(arc_env.len(), id_env.len(), "env sizes diverge");
    }
    (arc_env, id_env)
}

// ---- ported admission-pipeline tests -----------------------------------

#[test]
fn admits_wellformed_axiom_def_thm_opaque() {
    let mut arc_env = arc_mini::env();
    let len_before = arc_env.len();
    let mut id_env = mini_env();
    assert_eq!(id_env.len(), len_before, "fixtures start the same size");

    arc_env
        .add_decl(ArcDeclaration::Axiom(ArcAxiomVal {
            val: arc_cv("myAxiom", vec![], arc_mini::sort0()),
            is_unsafe: false,
        }))
        .unwrap();
    let my_axiom_id = nm_id(&mut id_env, "myAxiom");
    let val = id_cv(&mut id_env, "myAxiom", vec![], arc_mini::sort0());
    id_env
        .add_decl(Declaration::Axiom(AxiomVal {
            val,
            is_unsafe: false,
        }))
        .unwrap();

    arc_env
        .add_decl(ArcDeclaration::Defn(ArcDefinitionVal {
            val: arc_cv("myDef", vec![], arc_mini::cst("A", vec![])),
            value: arc_mini::cst("a", vec![]),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![crate::testenv::nm("myDef")],
        }))
        .unwrap();
    let my_def_id = nm_id(&mut id_env, "myDef");
    {
        let val = id_cv(&mut id_env, "myDef", vec![], arc_mini::cst("A", vec![]));
        let value = expr_id(&mut id_env, &arc_mini::cst("a", vec![]));
        let all = vec![my_def_id];
        id_env
            .add_decl(Declaration::Defn(DefinitionVal {
                val,
                value,
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all,
            }))
            .unwrap();
    }

    arc_env
        .add_decl(ArcDeclaration::Thm(ArcTheoremVal {
            val: arc_cv("myThm", vec![], arc_mini::cst("A", vec![])),
            value: arc_mini::cst("a", vec![]),
            all: vec![crate::testenv::nm("myThm")],
        }))
        .unwrap();
    let my_thm_id = nm_id(&mut id_env, "myThm");
    {
        let val = id_cv(&mut id_env, "myThm", vec![], arc_mini::cst("A", vec![]));
        let value = expr_id(&mut id_env, &arc_mini::cst("a", vec![]));
        let all = vec![my_thm_id];
        id_env
            .add_decl(Declaration::Thm(TheoremVal { val, value, all }))
            .unwrap();
    }

    arc_env
        .add_decl(ArcDeclaration::Opaque(ArcOpaqueVal {
            val: arc_cv("myOpaque", vec![], arc_mini::cst("A", vec![])),
            value: arc_mini::cst("a", vec![]),
            is_unsafe: false,
            all: vec![crate::testenv::nm("myOpaque")],
        }))
        .unwrap();
    let my_opaque_id = nm_id(&mut id_env, "myOpaque");
    {
        let val = id_cv(&mut id_env, "myOpaque", vec![], arc_mini::cst("A", vec![]));
        let value = expr_id(&mut id_env, &arc_mini::cst("a", vec![]));
        let all = vec![my_opaque_id];
        id_env
            .add_decl(Declaration::Opaque(OpaqueVal {
                val,
                value,
                is_unsafe: false,
                all,
            }))
            .unwrap();
    }

    assert_eq!(arc_env.len(), len_before + 4);
    assert_eq!(id_env.len(), len_before + 4);

    assert!(matches!(
        arc_env.get(&crate::testenv::nm("myAxiom")),
        Some(crate::ConstantInfo::Axiom(_))
    ));
    assert!(matches!(
        id_env.get(my_axiom_id),
        Some(ConstantInfo::Axiom(_))
    ));
    assert!(matches!(
        arc_env.get(&crate::testenv::nm("myDef")),
        Some(crate::ConstantInfo::Defn(_))
    ));
    assert!(matches!(id_env.get(my_def_id), Some(ConstantInfo::Defn(_))));
    assert!(matches!(
        arc_env.get(&crate::testenv::nm("myThm")),
        Some(crate::ConstantInfo::Thm(_))
    ));
    assert!(matches!(id_env.get(my_thm_id), Some(ConstantInfo::Thm(_))));
    assert!(matches!(
        arc_env.get(&crate::testenv::nm("myOpaque")),
        Some(crate::ConstantInfo::Opaque(_))
    ));
    assert!(matches!(
        id_env.get(my_opaque_id),
        Some(ConstantInfo::Opaque(_))
    ));
}

#[test]
fn rejects_duplicate_name() {
    assert_add_decl_matches(
        || {
            ArcDeclaration::Axiom(ArcAxiomVal {
                val: arc_cv("A", vec![], arc_mini::sort0()),
                is_unsafe: false,
            })
        },
        |env| {
            Declaration::Axiom(AxiomVal {
                val: id_cv(env, "A", vec![], arc_mini::sort0()),
                is_unsafe: false,
            })
        },
    );
}

#[test]
fn rejects_duplicate_univ_param() {
    assert_add_decl_matches(
        || {
            ArcDeclaration::Axiom(ArcAxiomVal {
                val: arc_cv(
                    "dupAx",
                    vec![crate::testenv::nm("p"), crate::testenv::nm("p")],
                    arc_mini::sort_param("p"),
                ),
                is_unsafe: false,
            })
        },
        |env| {
            Declaration::Axiom(AxiomVal {
                val: id_cv(env, "dupAx", vec!["p", "p"], arc_mini::sort_param("p")),
                is_unsafe: false,
            })
        },
    );
}

#[test]
fn rejects_mvar_in_type_or_value() {
    // In the declared type.
    assert_add_decl_matches(
        || {
            ArcDeclaration::Axiom(ArcAxiomVal {
                val: arc_cv("mvarAx", vec![], Expr::mvar(crate::testenv::nm("m"))),
                is_unsafe: false,
            })
        },
        |env| {
            Declaration::Axiom(AxiomVal {
                val: id_cv(env, "mvarAx", vec![], Expr::mvar(crate::testenv::nm("m"))),
                is_unsafe: false,
            })
        },
    );

    // In the value.
    assert_add_decl_matches(
        || {
            ArcDeclaration::Defn(ArcDefinitionVal {
                val: arc_cv("mvarDef", vec![], arc_mini::cst("A", vec![])),
                value: Expr::mvar(crate::testenv::nm("m")),
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all: vec![crate::testenv::nm("mvarDef")],
            })
        },
        |env| {
            let val = id_cv(env, "mvarDef", vec![], arc_mini::cst("A", vec![]));
            let value = expr_id(env, &Expr::mvar(crate::testenv::nm("m")));
            let all = vec![nm_id(env, "mvarDef")];
            Declaration::Defn(DefinitionVal {
                val,
                value,
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all,
            })
        },
    );
}

#[test]
fn rejects_fvar_in_type_or_value() {
    // In the declared type.
    assert_add_decl_matches(
        || {
            ArcDeclaration::Axiom(ArcAxiomVal {
                val: arc_cv("fvarAx", vec![], Expr::fvar(crate::testenv::nm("x"))),
                is_unsafe: false,
            })
        },
        |env| {
            Declaration::Axiom(AxiomVal {
                val: id_cv(env, "fvarAx", vec![], Expr::fvar(crate::testenv::nm("x"))),
                is_unsafe: false,
            })
        },
    );

    // In the value.
    assert_add_decl_matches(
        || {
            ArcDeclaration::Defn(ArcDefinitionVal {
                val: arc_cv("fvarDef", vec![], arc_mini::cst("A", vec![])),
                value: Expr::fvar(crate::testenv::nm("x")),
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all: vec![crate::testenv::nm("fvarDef")],
            })
        },
        |env| {
            let val = id_cv(env, "fvarDef", vec![], arc_mini::cst("A", vec![]));
            let value = expr_id(env, &Expr::fvar(crate::testenv::nm("x")));
            let all = vec![nm_id(env, "fvarDef")];
            Declaration::Defn(DefinitionVal {
                val,
                value,
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all,
            })
        },
    );
}

#[test]
fn rejects_type_that_is_not_a_sort() {
    // axiom badTy : Nat.zero -- Nat.zero's own type is `Nat`, not a Sort.
    assert_add_decl_matches(
        || {
            ArcDeclaration::Axiom(ArcAxiomVal {
                val: arc_cv(
                    "badTy",
                    vec![],
                    arc_mini::cstn(crate::testenv::nm2("Nat", "zero"), vec![]),
                ),
                is_unsafe: false,
            })
        },
        |env| {
            Declaration::Axiom(AxiomVal {
                val: id_cv(
                    env,
                    "badTy",
                    vec![],
                    arc_mini::cstn(crate::testenv::nm2("Nat", "zero"), vec![]),
                ),
                is_unsafe: false,
            })
        },
    );
}

#[test]
fn rejects_ill_typed_value() {
    // def x : A := bt -- `bt : B`, and `A`/`B` are distinct opaque
    // constants (Prop vs Type respectively in `mini::env`), not defeq.
    assert_add_decl_matches(
        || {
            ArcDeclaration::Defn(ArcDefinitionVal {
                val: arc_cv("x", vec![], arc_mini::cst("A", vec![])),
                value: arc_mini::cst("bt", vec![]),
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all: vec![crate::testenv::nm("x")],
            })
        },
        |env| {
            let val = id_cv(env, "x", vec![], arc_mini::cst("A", vec![]));
            let value = expr_id(env, &arc_mini::cst("bt", vec![]));
            let all = vec![nm_id(env, "x")];
            Declaration::Defn(DefinitionVal {
                val,
                value,
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all,
            })
        },
    );
}

#[test]
fn rejects_theorem_not_prop() {
    // thm myThmBad : B := bt -- `B : Type`, not a `Prop`.
    assert_add_decl_matches(
        || {
            ArcDeclaration::Thm(ArcTheoremVal {
                val: arc_cv("myThmBad", vec![], arc_mini::cst("B", vec![])),
                value: arc_mini::cst("bt", vec![]),
                all: vec![crate::testenv::nm("myThmBad")],
            })
        },
        |env| {
            let val = id_cv(env, "myThmBad", vec![], arc_mini::cst("B", vec![]));
            let value = expr_id(env, &arc_mini::cst("bt", vec![]));
            let all = vec![nm_id(env, "myThmBad")];
            Declaration::Thm(TheoremVal { val, value, all })
        },
    );
}

#[test]
fn rejects_unknown_constant_in_value() {
    assert_add_decl_matches(
        || {
            ArcDeclaration::Defn(ArcDefinitionVal {
                val: arc_cv("y", vec![], arc_mini::cst("A", vec![])),
                value: arc_mini::cst("does_not_exist", vec![]),
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all: vec![crate::testenv::nm("y")],
            })
        },
        |env| {
            let val = id_cv(env, "y", vec![], arc_mini::cst("A", vec![]));
            let value = expr_id(env, &arc_mini::cst("does_not_exist", vec![]));
            let all = vec![nm_id(env, "y")];
            Declaration::Defn(DefinitionVal {
                val,
                value,
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all,
            })
        },
    );
}

#[test]
fn rejects_unsafe_defn_at_add_decl() {
    assert_add_decl_matches(
        || {
            ArcDeclaration::Defn(ArcDefinitionVal {
                val: arc_cv("unsafeDef", vec![], arc_mini::cst("A", vec![])),
                value: arc_mini::cst("a", vec![]),
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Unsafe,
                all: vec![crate::testenv::nm("unsafeDef")],
            })
        },
        |env| {
            let val = id_cv(env, "unsafeDef", vec![], arc_mini::cst("A", vec![]));
            let value = expr_id(env, &arc_mini::cst("a", vec![]));
            let all = vec![nm_id(env, "unsafeDef")];
            Declaration::Defn(DefinitionVal {
                val,
                value,
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Unsafe,
                all,
            })
        },
    );
}

#[test]
fn env_unchanged_after_rejection() {
    let mut arc_env = arc_mini::env();
    let mut id_env = mini_env();
    let len_before = arc_env.len();
    assert_eq!(id_env.len(), len_before);

    let a_id = nm_id(&mut id_env, "A");
    let a_before = id_env.get(a_id).unwrap().clone();

    let arc_err = arc_env
        .add_decl(ArcDeclaration::Axiom(ArcAxiomVal {
            val: arc_cv("A", vec![], arc_mini::sort0()),
            is_unsafe: false,
        }))
        .unwrap_err();
    let id_val = id_cv(&mut id_env, "A", vec![], arc_mini::sort0());
    let id_err = id_env
        .add_decl(Declaration::Axiom(AxiomVal {
            val: id_val,
            is_unsafe: false,
        }))
        .unwrap_err();
    assert_eq!(arc_err, id_err);

    assert_eq!(arc_env.len(), len_before);
    assert_eq!(id_env.len(), len_before);
    let a_after = id_env.get(a_id).unwrap();
    assert!(
        crate::bank::decl::constant_info_eq(&a_before, a_after),
        "rejected add_decl must not mutate the existing entry"
    );

    // A rejected Defn specifically must not partially extend the
    // environment either: `add_decl` only calls `add_core` once, after
    // every check has succeeded, so a mid-pipeline `DefTypeMismatch`
    // must leave `get`/`len` just as untouched as the AlreadyDeclared
    // case above.
    let arc_err2 = arc_env
        .add_decl(ArcDeclaration::Defn(ArcDefinitionVal {
            val: arc_cv("z", vec![], arc_mini::cst("A", vec![])),
            value: arc_mini::cst("bt", vec![]),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![crate::testenv::nm("z")],
        }))
        .unwrap_err();
    let z_id = nm_id(&mut id_env, "z");
    let id_err2 = {
        let val = id_cv(&mut id_env, "z", vec![], arc_mini::cst("A", vec![]));
        let value = expr_id(&mut id_env, &arc_mini::cst("bt", vec![]));
        let all = vec![z_id];
        id_env
            .add_decl(Declaration::Defn(DefinitionVal {
                val,
                value,
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all,
            }))
            .unwrap_err()
    };
    assert_eq!(arc_err2, id_err2);
    assert_eq!(arc_env.len(), len_before);
    assert_eq!(id_env.len(), len_before);
    assert!(arc_env.get(&crate::testenv::nm("z")).is_none());
    assert!(id_env.get(z_id).is_none());
}

// ---- promotion-specific region-discipline gate -------------------------

#[test]
fn admitted_inductive_has_no_scratch_ids() {
    let mut env = Environment::default();
    let foo_name = nm_id(&mut env, "Foo");
    let mk_name = nm_id(&mut env, "Foo.mk");
    let ty1 = expr_id(&mut env, &arc_mini::type1());
    let foo_const = expr_id(&mut env, &arc_mini::cstn(crate::testenv::nm("Foo"), vec![]));

    env.add_decl(Declaration::Inductive {
        lparams: vec![],
        nparams: Nat::from(0u64),
        types: vec![crate::bank::decl::InductiveType {
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
