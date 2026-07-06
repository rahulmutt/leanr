//! Dual-checker differential harness for oracle-faithful replay
//! (migration Task 6) — id-twin of `crate::replay::tests`. Builds
//! Arc-side fixtures (reusing `crate::testenv::mini` where possible),
//! runs Arc `crate::replay::replay` and the id-native `replay` (this
//! module, glob-imported via `use super::*`) on the SAME logical input —
//! the id side bridges via `Environment::intern_module` — and asserts
//! identical `ReplayStats`/verdicts. On success, `len()` must also
//! agree, and every Arc-admitted entry must bridge to something the id
//! side agrees with structurally (`bank::decl::constant_info_eq`).
//!
//! Arc types are imported UNALIASED and shadow the id-native names
//! `super::*` brings in for `ConstantInfo`/`Declaration`/`InductiveType`
//! (Rust's "explicit import shadows glob" rule — same convention
//! `bank::quot::tests` established); the id-native `Environment` is
//! always spelled out as `crate::bank::env::Environment` to keep every
//! reference to it visually unambiguous against the unqualified (Arc)
//! `crate::Environment`.

use super::*;
use crate::bank::decl::{constant_info_eq, intern_constant_info};
use crate::bank::Store;
use crate::testenv::mini;
use crate::{
    AxiomVal, ConstantInfo, ConstantVal, Declaration, DefinitionSafety, DefinitionVal,
    InductiveType, InductiveVal, KernelError, Name, Nat, OpaqueVal, TheoremVal,
};
use std::collections::HashMap;
use std::sync::Arc;

// ---- builders (Arc-side; both harness sides bridge the SAME fixture) --

fn nm(s: &str) -> Arc<Name> {
    crate::testenv::nm(s)
}

fn nm2(a: &str, b: &str) -> Arc<Name> {
    crate::testenv::nm2(a, b)
}

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

fn to_map(infos: Vec<ConstantInfo>) -> HashMap<Arc<Name>, ConstantInfo> {
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

/// The four constants the kernel produces when it admits `Nat`, as a
/// plain `Vec` (Arc-side; both harness sides bridge this same list —
/// using the REGENERATED infos as the decoded ones guarantees the
/// postponed ctor/recursor checks pass unless a test tampers with them).
fn nat_world() -> Vec<ConstantInfo> {
    let mut env = crate::Environment::default();
    env.add_decl(nat_decl()).expect("Nat admits");
    let names = [
        nm("Nat"),
        nm2("Nat", "zero"),
        nm2("Nat", "succ"),
        nm2("Nat", "rec"),
    ];
    names
        .iter()
        .map(|n| env.get(n).expect("regenerated").clone())
        .collect()
}

fn tampered_nat_ctor_zero() -> Vec<ConstantInfo> {
    let mut infos = nat_world();
    for ci in infos.iter_mut() {
        if let ConstantInfo::Ctor(v) = ci {
            if *v.val.name == *nm2("Nat", "zero") {
                v.num_fields = Nat::from(99u64);
            }
        }
    }
    infos
}

fn tampered_nat_rec() -> Vec<ConstantInfo> {
    let mut infos = nat_world();
    for ci in infos.iter_mut() {
        if let ConstantInfo::Rec(v) = ci {
            v.rules[0].rhs = mini::cst("bogus", vec![]);
        }
    }
    infos
}

fn id_name(env: &mut crate::bank::env::Environment, n: &Arc<Name>) -> NameId {
    env.intern_name(n).unwrap().unwrap()
}

// ---- dual-harness driver ------------------------------------------------

/// Run `mk()` (called once per side, so each gets its own fresh Arc
/// fixture) through Arc `crate::replay::replay` and the id-native
/// `replay`. Asserts identical `ReplayStats`/verdict; on success also
/// asserts matching `len()` and spot-checks that every Arc-admitted
/// entry bridges to something the id side agrees with structurally.
fn assert_replay_matches(
    mk: impl Fn() -> Vec<ConstantInfo>,
) -> (
    Result<crate::replay::ReplayStats, crate::replay::ReplayError>,
    Result<ReplayStats, ReplayError>,
    crate::Environment,
    crate::bank::env::Environment,
) {
    let mut arc_env = crate::Environment::default();
    let arc_result = crate::replay::replay(&mut arc_env, to_map(mk()));

    let mut id_env = crate::bank::env::Environment::default();
    let id_map = id_env.intern_module(mk()).unwrap();
    let id_result = replay(&mut id_env, id_map);

    match (&arc_result, &id_result) {
        (Ok(a), Ok(b)) => {
            assert_eq!(a.checked, b.checked, "checked count diverges");
            assert_eq!(
                a.skipped_unsafe, b.skipped_unsafe,
                "skipped_unsafe diverges"
            );
            assert_eq!(arc_env.len(), id_env.len(), "env sizes diverge");
            for arc_ci in arc_env.iter() {
                let mut scratch = Store::scratch();
                let bridged =
                    intern_constant_info(&mut scratch, Some(id_env.view().store), arc_ci).unwrap();
                let id_ci = id_env
                    .get(bridged.name())
                    .unwrap_or_else(|| panic!("missing {:?} in id env", arc_ci.name()));
                assert!(
                    constant_info_eq(&bridged, id_ci),
                    "mismatch for {:?}",
                    arc_ci.name()
                );
            }
        }
        (Err(a), Err(b)) => {
            assert_eq!(a.error, b.error, "error variant diverges");
            assert_eq!(a.decl, b.decl, "blamed decl diverges");
        }
        (a, b) => panic!("verdict split: arc={a:?} id={b:?}"),
    }
    (arc_result, id_result, arc_env, id_env)
}

// ---- ported replay tests ------------------------------------------------

#[test]
fn replays_nat_world_from_empty_env() {
    let (arc_result, id_result, arc_env, mut id_env) = assert_replay_matches(nat_world);
    let arc_stats = arc_result.expect("Nat world replays (arc)");
    let id_stats = id_result.expect("Nat world replays (id)");
    // Only the inductive block is sent to the kernel; the constructors
    // and recursor are checked structurally, not counted.
    assert_eq!(arc_stats.checked, 1);
    assert_eq!(id_stats.checked, 1);
    assert_eq!(arc_stats.skipped_unsafe, 0);
    assert_eq!(id_stats.skipped_unsafe, 0);
    assert!(arc_env.get(&nm("Nat")).is_some());
    assert!(arc_env.get(&nm2("Nat", "zero")).is_some());
    assert!(arc_env.get(&nm2("Nat", "rec")).is_some());
    let nat_id = id_name(&mut id_env, &nm("Nat"));
    let nat_zero_id = id_name(&mut id_env, &nm2("Nat", "zero"));
    let nat_rec_id = id_name(&mut id_env, &nm2("Nat", "rec"));
    assert!(id_env.get(nat_id).is_some());
    assert!(id_env.get(nat_zero_id).is_some());
    assert!(id_env.get(nat_rec_id).is_some());
}

#[test]
fn replays_out_of_order_deps() {
    // d : A := a ; a : A ; A : Prop. `d` depends on `a` depends on `A`;
    // the map imposes no order, so replay must discover it from
    // `used_constants`.
    let mk = || {
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
        vec![d, a_val, a_ty]
    };
    let (arc_result, id_result, arc_env, mut id_env) = assert_replay_matches(mk);
    let arc_stats = arc_result.expect("chain replays (arc)");
    let id_stats = id_result.expect("chain replays (id)");
    assert_eq!(arc_stats.checked, 3);
    assert_eq!(id_stats.checked, 3);
    assert!(arc_env.get(&nm("A")).is_some());
    assert!(arc_env.get(&nm("a")).is_some());
    assert!(arc_env.get(&nm("d")).is_some());
    for n in [nm("A"), nm("a"), nm("d")] {
        let id = id_name(&mut id_env, &n);
        assert!(id_env.get(id).is_some(), "{n} missing from id env");
    }
}

#[test]
fn skips_unsafe_and_partial() {
    let mk = || {
        let safe = axiom("s", mini::sort0(), false);
        let unsafe_ax = axiom("u", mini::sort0(), true);
        // A partial def is never checked, so its (bogus) value is
        // irrelevant.
        let partial = ConstantInfo::Defn(DefinitionVal {
            val: cval(nm("p"), mini::type1()),
            value: mini::sort0(),
            hints: crate::ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Partial,
            all: vec![nm("p")],
        });
        vec![safe, unsafe_ax, partial]
    };
    let (arc_result, id_result, arc_env, mut id_env) = assert_replay_matches(mk);
    let arc_stats = arc_result.expect("safe part replays (arc)");
    let id_stats = id_result.expect("safe part replays (id)");
    assert_eq!(arc_stats.checked, 1);
    assert_eq!(id_stats.checked, 1);
    assert_eq!(arc_stats.skipped_unsafe, 2);
    assert_eq!(id_stats.skipped_unsafe, 2);
    assert!(arc_env.get(&nm("s")).is_some());
    assert!(arc_env.get(&nm("u")).is_none(), "unsafe never admitted");
    assert!(arc_env.get(&nm("p")).is_none(), "partial never admitted");
    let s_id = id_name(&mut id_env, &nm("s"));
    let u_id = id_name(&mut id_env, &nm("u"));
    let p_id = id_name(&mut id_env, &nm("p"));
    assert!(id_env.get(s_id).is_some());
    assert!(id_env.get(u_id).is_none(), "unsafe never admitted (id)");
    assert!(id_env.get(p_id).is_none(), "partial never admitted (id)");
}

#[test]
fn thm_duplicate_tolerated() {
    // Pre-seed both envs with `A : Prop`, `a : A`, and theorem
    // `T : A := a`, via `replay` itself (exercising the same public
    // bridge/admission surface the actual test payload below uses).
    fn seed_constants() -> Vec<ConstantInfo> {
        vec![
            axiom("A", mini::sort0(), false),
            axiom("a", mini::cst("A", vec![]), false),
            thm_ci(vec![nm("T")]),
        ]
    }
    fn thm_ci(all: Vec<Arc<Name>>) -> ConstantInfo {
        ConstantInfo::Thm(TheoremVal {
            val: cval(nm("T"), mini::cst("A", vec![])),
            value: mini::cst("a", vec![]),
            all,
        })
    }

    let mut arc_env = crate::Environment::default();
    crate::replay::replay(&mut arc_env, to_map(seed_constants())).expect("seed replays (arc)");
    let mut id_env = crate::bank::env::Environment::default();
    let seed_map = id_env.intern_module(seed_constants()).unwrap();
    replay(&mut id_env, seed_map).expect("seed replays (id)");

    // Replaying a STRUCTURALLY IDENTICAL theorem is tolerated: no
    // re-admission (checked stays 0), no `AlreadyDeclared`.
    let arc_stats = crate::replay::replay(&mut arc_env, to_map(vec![thm_ci(vec![nm("T")])]))
        .expect("duplicate theorem tolerated (arc)");
    assert_eq!(
        arc_stats.checked, 0,
        "duplicate not re-sent to the kernel (arc)"
    );
    let id_dup = id_env.intern_module(vec![thm_ci(vec![nm("T")])]).unwrap();
    let id_stats = replay(&mut id_env, id_dup).expect("duplicate theorem tolerated (id)");
    assert_eq!(
        id_stats.checked, 0,
        "duplicate not re-sent to the kernel (id)"
    );

    // A theorem with the same name but a different `all` is NOT
    // tolerated: it hits `add_decl`, which rejects the name clash.
    let arc_err = crate::replay::replay(
        &mut arc_env,
        to_map(vec![thm_ci(vec![nm("T"), nm("Other")])]),
    )
    .expect_err("non-identical duplicate rejected (arc)");
    assert_eq!(arc_err.error, KernelError::AlreadyDeclared(nm("T")));
    assert_eq!(arc_err.decl, nm("T"));

    let id_differing = id_env
        .intern_module(vec![thm_ci(vec![nm("T"), nm("Other")])])
        .unwrap();
    let id_err =
        replay(&mut id_env, id_differing).expect_err("non-identical duplicate rejected (id)");
    assert_eq!(id_err.error, KernelError::AlreadyDeclared(nm("T")));
    assert_eq!(id_err.decl, nm("T"));
}

#[test]
fn missing_dep_is_error() {
    // An inductive whose constructor name is absent from the module set:
    // the oracle's `newConstants[n]!` panic becomes a clean
    // `MissingConstant` for us (untrusted input).
    let mk = || {
        vec![ConstantInfo::Induct(InductiveVal {
            val: cval(nm("Foo"), mini::type1()),
            num_params: Nat::from(0u64),
            num_indices: Nat::from(0u64),
            all: vec![nm("Foo")],
            ctors: vec![nm2("Foo", "mk")],
            num_nested: Nat::from(0u64),
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        })]
    };
    let (arc_result, id_result, arc_env, _id_env) = assert_replay_matches(mk);
    let arc_err = arc_result.expect_err("missing ctor is an error (arc)");
    let id_err = id_result.expect_err("missing ctor is an error (id)");
    assert_eq!(
        arc_err.error,
        KernelError::MissingConstant(nm2("Foo", "mk"))
    );
    assert_eq!(id_err.error, KernelError::MissingConstant(nm2("Foo", "mk")));
    // No panic, and the env is untouched by the failed block.
    assert!(arc_env.get(&nm("Foo")).is_none());
}

#[test]
fn postponed_ctor_mismatch_detected() {
    // Tamper the decoded `Nat.zero`'s `num_fields`. The kernel
    // regenerates the real ctor (num_fields = 0) when it admits `Nat`;
    // the postponed structural check then rejects the tampered decoded
    // one.
    let (arc_result, id_result, _, _) = assert_replay_matches(tampered_nat_ctor_zero);
    let arc_err = arc_result.expect_err("tampered ctor rejected (arc)");
    let id_err = id_result.expect_err("tampered ctor rejected (id)");
    assert_eq!(
        arc_err.error,
        KernelError::ConstructorMismatch(nm2("Nat", "zero"))
    );
    assert_eq!(
        id_err.error,
        KernelError::ConstructorMismatch(nm2("Nat", "zero"))
    );
}

#[test]
fn postponed_rec_mismatch_detected() {
    // Tamper the decoded `Nat.rec`'s first rule rhs.
    let (arc_result, id_result, _, _) = assert_replay_matches(tampered_nat_rec);
    let arc_err = arc_result.expect_err("tampered recursor rejected (arc)");
    let id_err = id_result.expect_err("tampered recursor rejected (id)");
    assert_eq!(
        arc_err.error,
        KernelError::RecursorMismatch(nm2("Nat", "rec"))
    );
    assert_eq!(
        id_err.error,
        KernelError::RecursorMismatch(nm2("Nat", "rec"))
    );
}

#[test]
fn opaque_replays() {
    // Sanity: the opaque arm goes through `add_decl` and is counted.
    let mk = || {
        let a_ty = axiom("A", mini::sort0(), false);
        let a_val = axiom("a", mini::cst("A", vec![]), false);
        let w = ConstantInfo::Opaque(OpaqueVal {
            val: cval(nm("w"), mini::cst("A", vec![])),
            value: mini::cst("a", vec![]),
            is_unsafe: false,
            all: vec![nm("w")],
        });
        vec![a_ty, a_val, w]
    };
    let (arc_result, id_result, arc_env, mut id_env) = assert_replay_matches(mk);
    let arc_stats = arc_result.expect("opaque replays (arc)");
    let id_stats = id_result.expect("opaque replays (id)");
    assert_eq!(arc_stats.checked, 3);
    assert_eq!(id_stats.checked, 3);
    assert!(arc_env.get(&nm("w")).is_some());
    let w_id = id_name(&mut id_env, &nm("w"));
    assert!(id_env.get(w_id).is_some());
}
