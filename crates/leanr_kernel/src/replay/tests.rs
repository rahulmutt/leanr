//! Unit tests for oracle-faithful replay (migration Task 8: ported from
//! the pre-flip `crate::replay::tests`, which dual-compared against the
//! Arc replay this migration deletes — see that file's history,
//! `git show 9b1c773:crates/leanr_kernel/src/replay/tests.rs`). Every
//! test asserts the SAME `ReplayStats`/errors that file pinned, now
//! directly against the id-native `replay`: fixtures are built as
//! `ArcConstantInfo` (the decoder-boundary shape) and bridged into id
//! form via `Environment::intern_module` — the real production bridge,
//! not a test-only shortcut.
//!
//! `nat_world` reproduces the old file's "kernel-regenerated `Nat`
//! ctors/recursor" fixture the same way the old file did: admit `Nat`
//! for real (`Environment::add_decl`), then bridge the KERNEL-REGENERATED
//! ctor/recursor `ConstantInfo`s back to `Arc` form via `to_constant_info`
//! so they can be fed back into `intern_module` as the "decoded" input —
//! guaranteeing the postponed structural check compares like against
//! like, so a deliberate tamper is the only thing that makes it fail
//! (a hand-rolled fixture, even an oracle-faithful one, is not
//! guaranteed to be byte-identical to what `add_inductive` computes —
//! e.g. `testenv::mini::nat_decls()`'s recursor rules are NOT, which is
//! why this doesn't just reuse them directly).

use super::*;
use crate::testenv::mini;
use crate::testenv::{nm, nm2};
use crate::{
    to_constant_info, ArcAxiomVal, ArcConstantInfo, ArcConstantVal, ArcDeclaration,
    ArcDefinitionVal, ArcInductiveType, ArcInductiveVal, ArcOpaqueVal, ArcTheoremVal,
    DefinitionSafety, Environment, KernelError, Name, Nat, RecGuard,
};
use std::sync::Arc;

// ---- builders (Arc-side; bridged into id form via `intern_module`) ----

fn cval(name: Arc<Name>, ty: Arc<crate::Expr>) -> ArcConstantVal {
    ArcConstantVal {
        name,
        level_params: vec![],
        ty,
    }
}

fn axiom(name: &str, ty: Arc<crate::Expr>, is_unsafe: bool) -> ArcConstantInfo {
    ArcConstantInfo::Axiom(ArcAxiomVal {
        val: cval(nm(name), ty),
        is_unsafe,
    })
}

/// `inductive Nat where | zero | succ (n : Nat)` — the testenv shape
/// (`mini::nat()`/`mini::pi`), admitted for real so the resulting
/// ctor/recursor `ConstantInfo`s are the KERNEL's own regenerated ones
/// (see this module's doc comment).
fn nat_decl_arc() -> ArcDeclaration {
    ArcDeclaration::Inductive {
        lparams: vec![],
        nparams: Nat::from(0u64),
        types: vec![ArcInductiveType {
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

/// The four constants the kernel produces when it admits `Nat`, bridged
/// back to `Arc` form (the decoder-boundary shape `intern_module`
/// expects) so they can be replayed as if freshly decoded. Using the
/// REGENERATED infos as the decoded ones guarantees the postponed ctor/
/// recursor checks pass unless a test tampers with them.
fn nat_world() -> Vec<ArcConstantInfo> {
    let mut env = Environment::default();
    let decl = env.intern_declaration(&nat_decl_arc()).unwrap();
    env.add_decl(decl).expect("Nat admits");
    let names = [
        nm("Nat"),
        nm2("Nat", "zero"),
        nm2("Nat", "succ"),
        nm2("Nat", "rec"),
    ];
    let mut g = RecGuard::new();
    names
        .iter()
        .map(|n| {
            let nid = id_name(&mut env, n);
            let ci = env.get(nid).expect("regenerated").clone();
            to_constant_info(env.view().store, None, &ci, &mut g).unwrap()
        })
        .collect()
}

fn tampered_nat_ctor_zero() -> Vec<ArcConstantInfo> {
    let mut infos = nat_world();
    for ci in infos.iter_mut() {
        if let ArcConstantInfo::Ctor(v) = ci {
            if *v.val.name == *nm2("Nat", "zero") {
                v.num_fields = Nat::from(99u64);
            }
        }
    }
    infos
}

fn tampered_nat_rec() -> Vec<ArcConstantInfo> {
    let mut infos = nat_world();
    for ci in infos.iter_mut() {
        if let ArcConstantInfo::Rec(v) = ci {
            v.rules[0].rhs = mini::cst("bogus", vec![]);
        }
    }
    infos
}

/// Look up a name already admitted into `env`'s persistent store.
/// `Environment::intern_name` is `pub(crate)` — same-crate test code may
/// call it directly; re-interning an already-present name is a no-op
/// lookup (the interning invariant), never a fresh row.
fn id_name(env: &mut Environment, n: &Arc<Name>) -> NameId {
    env.intern_name(n).unwrap().unwrap()
}

// ---- ported replay tests ------------------------------------------------

#[test]
fn replays_nat_world_from_empty_env() {
    let mut env = Environment::default();
    let map = env.intern_module(nat_world()).unwrap();
    let stats = replay(&mut env, map).expect("Nat world replays");
    // Only the inductive block is sent to the kernel; the constructors
    // and recursor are checked structurally, not counted.
    assert_eq!(stats.checked, 1);
    assert_eq!(stats.skipped_unsafe, 0);
    let nat_id = id_name(&mut env, &nm("Nat"));
    let nat_zero_id = id_name(&mut env, &nm2("Nat", "zero"));
    let nat_rec_id = id_name(&mut env, &nm2("Nat", "rec"));
    assert!(env.get(nat_id).is_some());
    assert!(env.get(nat_zero_id).is_some());
    assert!(env.get(nat_rec_id).is_some());
}

#[test]
fn replays_out_of_order_deps() {
    // d : A := a ; a : A ; A : Prop. `d` depends on `a` depends on `A`;
    // the map imposes no order, so replay must discover it from
    // `used_constants`.
    let a_ty = axiom("A", mini::sort0(), false);
    let a_val = axiom("a", mini::cst("A", vec![]), false);
    let d = ArcConstantInfo::Defn(ArcDefinitionVal {
        val: cval(nm("d"), mini::cst("A", vec![])),
        value: mini::cst("a", vec![]),
        hints: crate::ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Safe,
        all: vec![nm("d")],
    });
    // Insert value-first so at least one iteration order starts at a
    // dependent — the outcome must not depend on it.
    let module = vec![d, a_val, a_ty];

    let mut env = Environment::default();
    let map = env.intern_module(module).unwrap();
    let stats = replay(&mut env, map).expect("chain replays");
    assert_eq!(stats.checked, 3);
    for n in [nm("A"), nm("a"), nm("d")] {
        let id = id_name(&mut env, &n);
        assert!(env.get(id).is_some(), "{n} missing from env");
    }
}

#[test]
fn skips_unsafe_and_partial() {
    let safe = axiom("s", mini::sort0(), false);
    let unsafe_ax = axiom("u", mini::sort0(), true);
    // A partial def is never checked, so its (bogus) value is irrelevant.
    let partial = ArcConstantInfo::Defn(ArcDefinitionVal {
        val: cval(nm("p"), mini::type1()),
        value: mini::sort0(),
        hints: crate::ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Partial,
        all: vec![nm("p")],
    });
    let module = vec![safe, unsafe_ax, partial];

    let mut env = Environment::default();
    let map = env.intern_module(module).unwrap();
    let stats = replay(&mut env, map).expect("safe part replays");
    assert_eq!(stats.checked, 1);
    assert_eq!(stats.skipped_unsafe, 2);
    let s_id = id_name(&mut env, &nm("s"));
    let u_id = id_name(&mut env, &nm("u"));
    let p_id = id_name(&mut env, &nm("p"));
    assert!(env.get(s_id).is_some());
    assert!(env.get(u_id).is_none(), "unsafe never admitted");
    assert!(env.get(p_id).is_none(), "partial never admitted");
}

#[test]
fn thm_duplicate_tolerated() {
    // Pre-seed an env with `A : Prop`, `a : A`, and theorem `T : A := a`,
    // via `replay` itself (exercising the same public bridge/admission
    // surface the actual test payload below uses).
    fn seed_constants() -> Vec<ArcConstantInfo> {
        vec![
            axiom("A", mini::sort0(), false),
            axiom("a", mini::cst("A", vec![]), false),
            thm_ci(vec![nm("T")]),
        ]
    }
    fn thm_ci(all: Vec<Arc<Name>>) -> ArcConstantInfo {
        ArcConstantInfo::Thm(ArcTheoremVal {
            val: cval(nm("T"), mini::cst("A", vec![])),
            value: mini::cst("a", vec![]),
            all,
        })
    }

    let mut env = Environment::default();
    let seed_map = env.intern_module(seed_constants()).unwrap();
    replay(&mut env, seed_map).expect("seed replays");

    // Replaying a STRUCTURALLY IDENTICAL theorem is tolerated: no
    // re-admission (checked stays 0), no `AlreadyDeclared`.
    let dup_map = env.intern_module(vec![thm_ci(vec![nm("T")])]).unwrap();
    let stats = replay(&mut env, dup_map).expect("duplicate theorem tolerated");
    assert_eq!(stats.checked, 0, "duplicate not re-sent to the kernel");

    // A theorem with the same name but a different `all` is NOT
    // tolerated: it hits `add_decl`, which rejects the name clash.
    let differing_map = env
        .intern_module(vec![thm_ci(vec![nm("T"), nm("Other")])])
        .unwrap();
    let err = replay(&mut env, differing_map).expect_err("non-identical duplicate rejected");
    assert_eq!(err.error, KernelError::AlreadyDeclared(nm("T")));
    assert_eq!(err.decl, nm("T"));
}

#[test]
fn missing_dep_is_error() {
    // An inductive whose constructor name is absent from the module set:
    // the oracle's `newConstants[n]!` panic becomes a clean
    // `MissingConstant` for us (untrusted input).
    let module = vec![ArcConstantInfo::Induct(ArcInductiveVal {
        val: cval(nm("Foo"), mini::type1()),
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![nm("Foo")],
        ctors: vec![nm2("Foo", "mk")],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    })];

    let mut env = Environment::default();
    let map = env.intern_module(module).unwrap();
    let err = replay(&mut env, map).expect_err("missing ctor is an error");
    assert_eq!(err.error, KernelError::MissingConstant(nm2("Foo", "mk")));
    // No panic, and the env is untouched by the failed block.
    let foo_id = id_name(&mut env, &nm("Foo"));
    assert!(env.get(foo_id).is_none());
}

#[test]
fn postponed_ctor_mismatch_detected() {
    // Tamper the decoded `Nat.zero`'s `num_fields`. The kernel
    // regenerates the real ctor (num_fields = 0) when it admits `Nat`;
    // the postponed structural check then rejects the tampered decoded
    // one.
    let mut env = Environment::default();
    let map = env.intern_module(tampered_nat_ctor_zero()).unwrap();
    let err = replay(&mut env, map).expect_err("tampered ctor rejected");
    assert_eq!(
        err.error,
        KernelError::ConstructorMismatch(nm2("Nat", "zero"))
    );
}

#[test]
fn postponed_rec_mismatch_detected() {
    // Tamper the decoded `Nat.rec`'s first rule rhs.
    let mut env = Environment::default();
    let map = env.intern_module(tampered_nat_rec()).unwrap();
    let err = replay(&mut env, map).expect_err("tampered recursor rejected");
    assert_eq!(err.error, KernelError::RecursorMismatch(nm2("Nat", "rec")));
}

#[test]
fn opaque_replays() {
    // Sanity: the opaque arm goes through `add_decl` and is counted.
    let a_ty = axiom("A", mini::sort0(), false);
    let a_val = axiom("a", mini::cst("A", vec![]), false);
    let w = ArcConstantInfo::Opaque(ArcOpaqueVal {
        val: cval(nm("w"), mini::cst("A", vec![])),
        value: mini::cst("a", vec![]),
        is_unsafe: false,
        all: vec![nm("w")],
    });
    let module = vec![a_ty, a_val, w];
    let mut env = Environment::default();
    let map = env.intern_module(module).unwrap();
    let stats = replay(&mut env, map).expect("opaque replays");
    assert_eq!(stats.checked, 3);
    let w_id = id_name(&mut env, &nm("w"));
    assert!(env.get(w_id).is_some());
}
