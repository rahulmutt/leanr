//! Unit tests for oracle-faithful replay (Task 12).
//!
//! These build small `ConstantInfo` maps and replay them from a fresh
//! (or lightly pre-seeded) `Environment`. Where a test needs a real
//! inductive with a regenerated constructor/recursor, it admits `Nat`
//! once into a scratch env and reuses the KERNEL-regenerated infos as
//! the "decoded" ones (`nat_world`) — so the postponed structural check
//! compares like against like, and a deliberate tamper is the only thing
//! that makes it fail.

use std::collections::HashMap;
use std::sync::Arc;

use super::replay;
use crate::testenv::mini;
use crate::testenv::{nm, nm2};
use crate::{
    AxiomVal, ConstantInfo, ConstantVal, Declaration, DefinitionSafety, DefinitionVal, Environment,
    InductiveType, InductiveVal, KernelError, Name, Nat, OpaqueVal, TheoremVal,
};

// ---- builders -----------------------------------------------------------

fn cval(name: Arc<Name>, ty: Arc<crate::Expr>) -> ConstantVal {
    ConstantVal {
        name,
        level_params: vec![],
        ty,
    }
}

fn axiom(name: &str, ty: Arc<crate::Expr>, is_unsafe: bool) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        val: cval(nm(name), ty),
        is_unsafe,
    })
}

fn map_of(infos: Vec<ConstantInfo>) -> HashMap<Arc<Name>, ConstantInfo> {
    infos
        .into_iter()
        .map(|c| (Arc::clone(c.name()), c))
        .collect()
}

/// `inductive Nat where | zero | succ (n : Nat)` — the testenv shape.
fn nat_decl() -> Declaration {
    Declaration::Inductive {
        lparams: vec![],
        nparams: Nat::from(0u64),
        types: vec![InductiveType {
            name: nm("Nat"),
            ty: mini::type1(),
            ctors: vec![
                (nm2("Nat", "zero"), mini::nat()),
                (nm2("Nat", "succ"), mini::pi("n", mini::nat(), mini::nat())),
            ],
        }],
        is_unsafe: false,
    }
}

/// The four constants the kernel produces when it admits `Nat`, keyed by
/// name. Using the REGENERATED infos as the decoded ones guarantees the
/// postponed ctor/recursor checks pass unless a test tampers with them.
fn nat_world() -> HashMap<Arc<Name>, ConstantInfo> {
    let mut env = Environment::default();
    env.add_decl(nat_decl()).expect("Nat admits");
    let names = [
        nm("Nat"),
        nm2("Nat", "zero"),
        nm2("Nat", "succ"),
        nm2("Nat", "rec"),
    ];
    let mut m = HashMap::new();
    for n in names {
        let info = env.get(&n).expect("regenerated").clone();
        m.insert(n, info);
    }
    m
}

// ---- tests --------------------------------------------------------------

#[test]
fn replays_nat_world_from_empty_env() {
    let mut env = Environment::default();
    let stats = replay(&mut env, nat_world()).expect("Nat world replays");
    // Only the inductive block is sent to the kernel; the constructors
    // and recursor are checked structurally, not counted.
    assert_eq!(stats.checked, 1);
    assert_eq!(stats.skipped_unsafe, 0);
    assert!(env.get(&nm("Nat")).is_some());
    assert!(env.get(&nm2("Nat", "zero")).is_some());
    assert!(env.get(&nm2("Nat", "rec")).is_some());
}

#[test]
fn replays_out_of_order_deps() {
    // d : A := a ; a : A ; A : Prop. `d` depends on `a` depends on `A`;
    // the map imposes no order, so replay must discover it from
    // `used_constants`.
    let a_ty = axiom("A", mini::sort0(), false);
    let a_val = axiom("a", mini::cst("A", vec![]), false);
    let d = ConstantInfo::Defn(DefinitionVal {
        val: cval(nm("d"), mini::cst("A", vec![])),
        value: mini::cst("a", vec![]),
        hints: crate::ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Safe,
        all: vec![nm("d")],
    });
    // Insert value-first so at least one iteration order starts at a
    // dependent — the outcome must not depend on it.
    let map = map_of(vec![d, a_val, a_ty]);

    let mut env = Environment::default();
    let stats = replay(&mut env, map).expect("chain replays");
    assert_eq!(stats.checked, 3);
    assert!(env.get(&nm("A")).is_some());
    assert!(env.get(&nm("a")).is_some());
    assert!(env.get(&nm("d")).is_some());
}

#[test]
fn skips_unsafe_and_partial() {
    let safe = axiom("s", mini::sort0(), false);
    let unsafe_ax = axiom("u", mini::sort0(), true);
    // A partial def is never checked, so its (bogus) value is irrelevant.
    let partial = ConstantInfo::Defn(DefinitionVal {
        val: cval(nm("p"), mini::type1()),
        value: mini::sort0(),
        hints: crate::ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Partial,
        all: vec![nm("p")],
    });
    let map = map_of(vec![safe, unsafe_ax, partial]);

    let mut env = Environment::default();
    let stats = replay(&mut env, map).expect("safe part replays");
    assert_eq!(stats.checked, 1);
    assert_eq!(stats.skipped_unsafe, 2);
    assert!(env.get(&nm("s")).is_some());
    assert!(env.get(&nm("u")).is_none(), "unsafe never admitted");
    assert!(env.get(&nm("p")).is_none(), "partial never admitted");
}

#[test]
fn thm_duplicate_tolerated() {
    // Pre-seed an env with `A : Prop`, `a : A`, and theorem `T : A := a`.
    let mut env = Environment::default();
    env.add_decl(Declaration::Axiom(AxiomVal {
        val: cval(nm("A"), mini::sort0()),
        is_unsafe: false,
    }))
    .unwrap();
    env.add_decl(Declaration::Axiom(AxiomVal {
        val: cval(nm("a"), mini::cst("A", vec![])),
        is_unsafe: false,
    }))
    .unwrap();
    let thm = |all: Vec<Arc<Name>>| {
        ConstantInfo::Thm(TheoremVal {
            val: cval(nm("T"), mini::cst("A", vec![])),
            value: mini::cst("a", vec![]),
            all,
        })
    };
    let ConstantInfo::Thm(seed) = thm(vec![nm("T")]) else {
        unreachable!()
    };
    env.add_decl(Declaration::Thm(seed)).unwrap();

    // Replaying a STRUCTURALLY IDENTICAL theorem is tolerated: no
    // re-admission (checked stays 0), no `AlreadyDeclared`.
    let dup = map_of(vec![thm(vec![nm("T")])]);
    let stats = replay(&mut env, dup).expect("duplicate theorem tolerated");
    assert_eq!(stats.checked, 0, "duplicate not re-sent to the kernel");

    // A theorem with the same name but a different `all` is NOT tolerated:
    // it hits `add_decl`, which rejects the name clash.
    let differing = map_of(vec![thm(vec![nm("T"), nm("Other")])]);
    let err = replay(&mut env, differing).expect_err("non-identical duplicate rejected");
    assert_eq!(err.error, KernelError::AlreadyDeclared(nm("T")));
    assert_eq!(err.decl, nm("T"));
}

#[test]
fn missing_dep_is_error() {
    // An inductive whose constructor name is absent from the module set:
    // the oracle's `newConstants[n]!` panic becomes a clean
    // `MissingConstant` for us (untrusted input).
    let foo = ConstantInfo::Induct(InductiveVal {
        val: cval(nm("Foo"), mini::type1()),
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![nm("Foo")],
        ctors: vec![nm2("Foo", "mk")],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    });
    let map = map_of(vec![foo]);

    let mut env = Environment::default();
    let err = replay(&mut env, map).expect_err("missing ctor is an error");
    assert_eq!(err.error, KernelError::MissingConstant(nm2("Foo", "mk")));
    // No panic, and the env is untouched by the failed block.
    assert!(env.get(&nm("Foo")).is_none());
}

#[test]
fn postponed_ctor_mismatch_detected() {
    // Tamper the decoded `Nat.zero`'s `num_fields`. The kernel regenerates
    // the real ctor (num_fields = 0) when it admits `Nat`; the postponed
    // structural check then rejects the tampered decoded one.
    let mut map = nat_world();
    let tampered = match map.get(&nm2("Nat", "zero")).unwrap().clone() {
        ConstantInfo::Ctor(mut v) => {
            v.num_fields = Nat::from(99u64);
            ConstantInfo::Ctor(v)
        }
        _ => unreachable!(),
    };
    map.insert(nm2("Nat", "zero"), tampered);

    let mut env = Environment::default();
    let err = replay(&mut env, map).expect_err("tampered ctor rejected");
    assert_eq!(
        err.error,
        KernelError::ConstructorMismatch(nm2("Nat", "zero"))
    );
}

#[test]
fn postponed_rec_mismatch_detected() {
    // Tamper the decoded `Nat.rec`'s first rule rhs.
    let mut map = nat_world();
    let tampered = match map.get(&nm2("Nat", "rec")).unwrap().clone() {
        ConstantInfo::Rec(mut v) => {
            v.rules[0].rhs = mini::cst("bogus", vec![]);
            ConstantInfo::Rec(v)
        }
        _ => unreachable!(),
    };
    map.insert(nm2("Nat", "rec"), tampered);

    let mut env = Environment::default();
    let err = replay(&mut env, map).expect_err("tampered recursor rejected");
    assert_eq!(err.error, KernelError::RecursorMismatch(nm2("Nat", "rec")));
}

#[test]
fn opaque_replays() {
    // Sanity: the opaque arm goes through `add_decl` and is counted.
    let a_ty = axiom("A", mini::sort0(), false);
    let a_val = axiom("a", mini::cst("A", vec![]), false);
    let w = ConstantInfo::Opaque(OpaqueVal {
        val: cval(nm("w"), mini::cst("A", vec![])),
        value: mini::cst("a", vec![]),
        is_unsafe: false,
        all: vec![nm("w")],
    });
    let map = map_of(vec![a_ty, a_val, w]);
    let mut env = Environment::default();
    let stats = replay(&mut env, map).expect("opaque replays");
    assert_eq!(stats.checked, 3);
    assert!(env.get(&nm("w")).is_some());
}
