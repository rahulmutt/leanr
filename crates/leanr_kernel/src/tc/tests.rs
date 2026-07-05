//! Task 6 tests. A small environment is built BY HAND from hand-rolled
//! `ConstantInfo`s (no olean; fixtures arrive in Task 12). The `mini`
//! module is the shared fixture; each test transcribes one brief case.

use super::*;
use crate::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, Environment,
    Expr, KernelError, Level, Name, Nat, OpaqueVal, RecGuard, ReducibilityHints,
};
use std::sync::Arc;

/// Build a single-component `Name` (no `Name::from_str` exists — see
/// every prior task's test helpers).
fn nm(s: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: s.to_string(),
    })
}

fn g() -> RecGuard {
    RecGuard::new()
}

/// The hand-rolled kernel environment shared by the tests below.
mod mini {
    use super::*;

    pub fn u() -> Arc<Name> {
        nm("u")
    }

    /// `Sort 0` = `Prop`.
    pub fn sort0() -> Arc<Expr> {
        Expr::sort(Arc::new(Level::Zero), &mut g()).unwrap()
    }

    /// `Sort u`.
    pub fn sort_u() -> Arc<Expr> {
        Expr::sort(Arc::new(Level::Param(u())), &mut g()).unwrap()
    }

    /// `Sort 1` = `Type`.
    pub fn type1() -> Arc<Expr> {
        Expr::sort(Level::mk_succ(Arc::new(Level::Zero)), &mut g()).unwrap()
    }

    /// `Const name levels`.
    pub fn cst(name: &str, levels: Vec<Arc<Level>>) -> Arc<Expr> {
        Expr::const_(nm(name), levels, &mut g()).unwrap()
    }

    fn cval(name: &str, level_params: Vec<Arc<Name>>, ty: Arc<Expr>) -> ConstantVal {
        ConstantVal {
            name: nm(name),
            level_params,
            ty,
        }
    }

    fn axiom(name: &str, ty: Arc<Expr>) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            val: cval(name, vec![], ty),
            is_unsafe: false,
        })
    }

    /// `Π (α : Sort u), α → α` in de Bruijn form.
    pub fn id1_type() -> Arc<Expr> {
        let inner = Expr::forall_e(
            nm("a"),
            Expr::bvar(Nat::from(0u64)), // α
            Expr::bvar(Nat::from(1u64)), // α (one binder deeper)
            BinderInfo::Default,
        );
        Expr::forall_e(nm("α"), sort_u(), inner, BinderInfo::Default)
    }

    /// `λ (α : Sort u) (x : α), x`.
    pub fn id1_value() -> Arc<Expr> {
        let inner = Expr::lam(
            nm("x"),
            Expr::bvar(Nat::from(0u64)), // α
            Expr::bvar(Nat::from(0u64)), // x
            BinderInfo::Default,
        );
        Expr::lam(nm("α"), sort_u(), inner, BinderInfo::Default)
    }

    /// The shared environment:
    ///   axiom A : Prop        axiom a : A
    ///   def   id₁ : Π (α : Sort u), α → α := λ α x, x   (Regular hints)
    ///   opaque w : A := a
    ///   axiom B : Type        axiom bt : B       axiom bf : B
    pub fn env() -> Environment {
        let id1 = ConstantInfo::Defn(DefinitionVal {
            val: cval("id1", vec![u()], id1_type()),
            value: id1_value(),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("id1")],
        });
        let w = ConstantInfo::Opaque(OpaqueVal {
            val: cval("w", vec![], cst("A", vec![])),
            value: cst("a", vec![]),
            is_unsafe: false,
            all: vec![nm("w")],
        });
        let module = vec![
            axiom("A", sort0()),
            axiom("a", cst("A", vec![])),
            id1,
            w,
            axiom("B", type1()),
            axiom("bt", cst("B", vec![])),
            axiom("bf", cst("B", vec![])),
        ];
        Environment::from_modules(vec![module]).unwrap()
    }
}

fn deq(tc: &mut TypeChecker, a: &Arc<Expr>, b: &Arc<Expr>) -> bool {
    tc.is_def_eq(a, b).unwrap()
}

#[test]
fn infer_sort_of_sort() {
    // infer(Sort u) = Sort (u+1)
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let r = tc.infer_type(&mini::sort_u()).unwrap();
    let expected = Expr::sort(Level::mk_succ(Arc::new(Level::Param(mini::u()))), &mut g()).unwrap();
    assert!(deq(&mut tc, &r, &expected));
}

#[test]
fn infer_lambda_gives_pi() {
    // infer(λ (x : A), x) ≡ A → A
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let lam = Expr::lam(
        nm("x"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let r = tc.infer_type(&lam).unwrap();
    let a_to_a = Expr::forall_e(
        nm("x"),
        mini::cst("A", vec![]),
        mini::cst("A", vec![]),
        BinderInfo::Default,
    );
    assert!(deq(&mut tc, &r, &a_to_a));
}

#[test]
fn check_rejects_loose_bvar() {
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::bvar(Nat::from(0u64));
    assert_eq!(tc.infer_type(&e).unwrap_err(), KernelError::LooseBVar);
}

#[test]
fn check_rejects_mvar() {
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::mvar(nm("m"));
    assert_eq!(
        tc.infer_type(&e).unwrap_err(),
        KernelError::MetavarEncountered
    );
}

#[test]
fn check_rejects_univ_arity() {
    // Const id₁ [] — decl has 1 level param.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let e = mini::cst("id1", vec![]);
    assert_eq!(
        tc.infer_type(&e).unwrap_err(),
        KernelError::UnivParamArityMismatch { name: nm("id1") }
    );
}

#[test]
fn app_type_mismatch_rejected() {
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let id1_0 = mini::cst("id1", vec![Arc::new(Level::Zero)]);
    // id₁.{0} A a is well-typed.
    let good = Expr::app(
        Expr::app(Arc::clone(&id1_0), mini::cst("A", vec![])),
        mini::cst("a", vec![]),
    );
    assert!(tc.check(&good, &[]).is_ok());
    // id₁.{0} a a — first arg `a : A` where a `Sort 0` is expected.
    let bad = Expr::app(
        Expr::app(id1_0, mini::cst("a", vec![])),
        mini::cst("a", vec![]),
    );
    assert_eq!(
        tc.check(&bad, &[]).unwrap_err(),
        KernelError::AppTypeMismatch
    );
}

#[test]
fn beta_whnf() {
    // whnf((λ x, x) a) = a, ptr-preserved.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let a = mini::cst("a", vec![]);
    let idfun = Expr::lam(
        nm("x"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let e = Expr::app(idfun, Arc::clone(&a));
    let r = tc.whnf(&e).unwrap();
    assert!(Arc::ptr_eq(&r, &a));
}

#[test]
fn zeta_whnf() {
    // whnf(let x := a in x) = a.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let a = mini::cst("a", vec![]);
    let e = Expr::let_e(
        nm("x"),
        mini::cst("A", vec![]),
        Arc::clone(&a),
        Expr::bvar(Nat::from(0u64)),
        false,
    );
    let r = tc.whnf(&e).unwrap();
    assert!(Arc::ptr_eq(&r, &a));
}

#[test]
fn delta_whnf() {
    // whnf(id₁.{0} A a) = a via unfold + beta chain.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let a = mini::cst("a", vec![]);
    let e = Expr::app(
        Expr::app(
            mini::cst("id1", vec![Arc::new(Level::Zero)]),
            mini::cst("A", vec![]),
        ),
        Arc::clone(&a),
    );
    let r = tc.whnf(&e).unwrap();
    assert!(Expr::structural_eq(&r, &a, &mut g()).unwrap());
}

#[test]
fn defeq_alpha_binding() {
    // λ x, x ≡ λ y, y (binder names ignored).
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let lx = Expr::lam(
        nm("x"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let ly = Expr::lam(
        nm("y"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    assert!(deq(&mut tc, &lx, &ly));
}

#[test]
fn defeq_proof_irrelevance() {
    // a ≡ w (both : A : Prop).
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let a = mini::cst("a", vec![]);
    let w = mini::cst("w", vec![]);
    assert!(deq(&mut tc, &a, &w));
}

#[test]
fn defeq_pi_congruence() {
    // Π(x:A),A ≡ Π(y:A),A ; and NOT ≡ Π(x:A),Prop
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let pi_a_x = Expr::forall_e(
        nm("x"),
        mini::cst("A", vec![]),
        mini::cst("A", vec![]),
        BinderInfo::Default,
    );
    let pi_a_y = Expr::forall_e(
        nm("y"),
        mini::cst("A", vec![]),
        mini::cst("A", vec![]),
        BinderInfo::Default,
    );
    assert!(deq(&mut tc, &pi_a_x, &pi_a_y));
    let pi_a_prop = Expr::forall_e(
        nm("x"),
        mini::cst("A", vec![]),
        mini::sort0(),
        BinderInfo::Default,
    );
    assert!(!deq(&mut tc, &pi_a_x, &pi_a_prop));
}

#[test]
fn whnf_cache_and_sharing() {
    // whnf twice: the second call returns the same Arc (cache hit).
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let idfun = Expr::lam(
        nm("x"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let e = Expr::app(idfun, mini::cst("a", vec![]));
    let r1 = tc.whnf(&e).unwrap();
    let r2 = tc.whnf(&e).unwrap();
    assert!(Arc::ptr_eq(&r1, &r2));
}

#[test]
fn check_sets_lparams() {
    // check(λ (α : Sort u), α, [u]) passes; with [] the undefined param
    // `u` is a check_level error (mapped to UnivParamArityMismatch).
    //
    // Independent `TypeChecker`s per check: the `infer_type` memo
    // (`m_infer_type[infer_only]`, oracle state) is keyed by expr pointer,
    // NOT by lparams — so checking the SAME `lam` Arc twice on ONE checker
    // would hit the cache and skip re-validation (identical to the
    // oracle). Real admission (Replay) builds a fresh checker per decl,
    // which is what these two checks model.
    let env = mini::env();
    let lam = Expr::lam(
        nm("α"),
        mini::sort_u(),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let mut tc_ok = TypeChecker::new(&env);
    assert!(tc_ok.check(&lam, &[mini::u()]).is_ok());
    let mut tc_bad = TypeChecker::new(&env);
    assert_eq!(
        tc_bad.check(&lam, &[]).unwrap_err(),
        KernelError::UnivParamArityMismatch { name: mini::u() }
    );
}
