//! Task 6 tests. A small environment is built BY HAND from hand-rolled
//! `ConstantInfo`s (no olean; fixtures arrive in Task 12). The `mini`
//! module (promoted to `crate::testenv` in Task 8, shared with
//! `env.rs`'s admission tests) is the shared fixture; each test
//! transcribes one brief case.

use super::*;
use crate::testenv::{g, mini, nm, nm2};
use crate::{BinderInfo, ExprNode, KernelError, Level, Literal, Nat};
use std::sync::Arc;

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

// ===================================================================
// Task 7: special reductions
// ===================================================================

fn lit_nat(n: u64) -> Arc<Expr> {
    Expr::lit(Literal::NatVal(Nat::from(n)))
}

fn seq(a: &Arc<Expr>, b: &Arc<Expr>) -> bool {
    Expr::structural_eq(a, b, &mut g()).unwrap()
}

/// `Nat.succ arg`.
fn nat_succ(arg: Arc<Expr>) -> Arc<Expr> {
    mini::app(mini::cstn(nm2("Nat", "succ"), vec![]), arg)
}

/// `Nat.<op> a b`.
fn nat_binop(op: &str, a: Arc<Expr>, b: Arc<Expr>) -> Arc<Expr> {
    mini::appn(mini::cstn(nm2("Nat", op), vec![]), vec![a, b])
}

fn zero_lvl() -> Arc<Level> {
    Arc::new(Level::Zero)
}

fn one_lvl() -> Arc<Level> {
    Level::mk_succ(Arc::new(Level::Zero))
}

#[test]
fn iota_reduces_nat_rec_on_succ() {
    // whnf(Nat.rec.{0} C z s (Nat.succ n)) = s n (Nat.rec.{0} C z s n)
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let (cc, z, s, n) = (
        mini::cst("C", vec![]),
        mini::cst("z", vec![]),
        mini::cst("s", vec![]),
        mini::cst("n", vec![]),
    );
    let natrec = mini::cstn(nm2("Nat", "rec"), vec![zero_lvl()]);
    let e = mini::appn(
        Arc::clone(&natrec),
        vec![
            Arc::clone(&cc),
            Arc::clone(&z),
            Arc::clone(&s),
            nat_succ(Arc::clone(&n)),
        ],
    );
    let r = tc.whnf(&e).unwrap();
    let expected = mini::app(
        mini::app(Arc::clone(&s), Arc::clone(&n)),
        mini::appn(natrec, vec![cc, z, s, n]),
    );
    assert!(seq(&r, &expected), "got {:?}", r);
}

#[test]
fn iota_on_literal_major() {
    // whnf(Nat.rec.{0} C z s 2) = s 1 (Nat.rec.{0} C z s 1) — the literal
    // major `2` is converted to `Nat.succ 1` before rule selection.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let (cc, z, s) = (
        mini::cst("C", vec![]),
        mini::cst("z", vec![]),
        mini::cst("s", vec![]),
    );
    let natrec = mini::cstn(nm2("Nat", "rec"), vec![zero_lvl()]);
    let e = mini::appn(
        Arc::clone(&natrec),
        vec![Arc::clone(&cc), Arc::clone(&z), Arc::clone(&s), lit_nat(2)],
    );
    let r = tc.whnf(&e).unwrap();
    let expected = mini::app(
        mini::app(Arc::clone(&s), lit_nat(1)),
        mini::appn(natrec, vec![cc, z, s, lit_nat(1)]),
    );
    assert!(seq(&r, &expected), "got {:?}", r);
}

#[test]
fn k_like_rec_on_eq() {
    // whnf(Eq.rec.{0,1} A a0 Mot req a0 h) = req, where h : @Eq.{1} A a0 a0
    // is an opaque rfl-typed proof. The K-recursor synthesizes `Eq.refl`
    // from h's type and selects the (fields-less) refl rule.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let eqrec = mini::cstn(nm2("Eq", "rec"), vec![zero_lvl(), one_lvl()]);
    let args = vec![
        mini::cst("A", vec![]),
        mini::cst("a0", vec![]),
        mini::cst("Mot", vec![]),
        mini::cst("req", vec![]),
        mini::cst("a0", vec![]),
        mini::cst("h", vec![]),
    ];
    let e = mini::appn(eqrec, args);
    let r = tc.whnf(&e).unwrap();
    assert!(seq(&r, &mini::cst("req", vec![])), "got {:?}", r);
}

#[test]
fn quot_lift_beta() {
    // whnf(Quot.lift.{0,0} α r β f h (Quot.mk.{0} α r a)) = f a
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let (alpha, rel, beta, f, h, a) = (
        mini::cst("α", vec![]),
        mini::cst("r", vec![]),
        mini::cst("β", vec![]),
        mini::cst("f", vec![]),
        mini::cst("h", vec![]),
        mini::cst("a", vec![]),
    );
    let mk = mini::appn(
        mini::cstn(nm2("Quot", "mk"), vec![zero_lvl()]),
        vec![Arc::clone(&alpha), Arc::clone(&rel), Arc::clone(&a)],
    );
    let e = mini::appn(
        mini::cstn(nm2("Quot", "lift"), vec![zero_lvl(), zero_lvl()]),
        vec![alpha, rel, beta, Arc::clone(&f), h, mk],
    );
    let r = tc.whnf(&e).unwrap();
    assert!(seq(&r, &mini::app(f, a)), "got {:?}", r);
}

#[test]
fn quot_ind_beta() {
    // whnf(Quot.ind.{0} α r β h (Quot.mk.{0} α r a)) = h a
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let (alpha, rel, beta, h, a) = (
        mini::cst("α", vec![]),
        mini::cst("r", vec![]),
        mini::cst("β", vec![]),
        mini::cst("h", vec![]),
        mini::cst("a", vec![]),
    );
    let mk = mini::appn(
        mini::cstn(nm2("Quot", "mk"), vec![zero_lvl()]),
        vec![Arc::clone(&alpha), Arc::clone(&rel), Arc::clone(&a)],
    );
    let e = mini::appn(
        mini::cstn(nm2("Quot", "ind"), vec![zero_lvl()]),
        vec![alpha, rel, beta, Arc::clone(&h), mk],
    );
    let r = tc.whnf(&e).unwrap();
    assert!(seq(&r, &mini::app(h, a)), "got {:?}", r);
}

#[test]
fn nat_add_folds() {
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    // add 2 3 = 5
    assert!(seq(
        &tc.whnf(&nat_binop("add", lit_nat(2), lit_nat(3))).unwrap(),
        &lit_nat(5)
    ));
    // sub 2 5 = 0 (truncated)
    assert!(seq(
        &tc.whnf(&nat_binop("sub", lit_nat(2), lit_nat(5))).unwrap(),
        &lit_nat(0)
    ));
    // div 5 0 = 0
    assert!(seq(
        &tc.whnf(&nat_binop("div", lit_nat(5), lit_nat(0))).unwrap(),
        &lit_nat(0)
    ));
    // mod 5 0 = 5
    assert!(seq(
        &tc.whnf(&nat_binop("mod", lit_nat(5), lit_nat(0))).unwrap(),
        &lit_nat(5)
    ));
    // pow guard: exponent 2^25 > 1<<24 ⇒ un-reduced (still an app).
    let pow = nat_binop("pow", lit_nat(2), lit_nat(1 << 25));
    let r = tc.whnf(&pow).unwrap();
    assert!(matches!(r.node(), ExprNode::App { .. }), "got {:?}", r);
    assert!(!matches!(r.node(), ExprNode::Lit(_)));
    // pow that is allowed: 2^10 = 1024.
    assert!(seq(
        &tc.whnf(&nat_binop("pow", lit_nat(2), lit_nat(10))).unwrap(),
        &lit_nat(1024)
    ));
}

#[test]
fn nat_beq_folds_to_bool() {
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let r = tc.whnf(&nat_binop("beq", lit_nat(2), lit_nat(2))).unwrap();
    assert!(
        seq(&r, &mini::cstn(nm2("Bool", "true"), vec![])),
        "got {:?}",
        r
    );
    let r2 = tc.whnf(&nat_binop("beq", lit_nat(2), lit_nat(3))).unwrap();
    assert!(seq(&r2, &mini::cstn(nm2("Bool", "false"), vec![])));
    // ble 2 3 = true
    let r3 = tc.whnf(&nat_binop("ble", lit_nat(2), lit_nat(3))).unwrap();
    assert!(seq(&r3, &mini::cstn(nm2("Bool", "true"), vec![])));
}

#[test]
fn succ_folds() {
    // whnf(Nat.succ 4) = 5
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let r = tc.whnf(&nat_succ(lit_nat(4))).unwrap();
    assert!(seq(&r, &lit_nat(5)), "got {:?}", r);
}

#[test]
fn offset_defeq() {
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    // succ (succ n0) ≡ succ (succ n0) via offset peeling.
    let n0 = mini::cst("n0", vec![]);
    let t = nat_succ(nat_succ(Arc::clone(&n0)));
    let s = nat_succ(nat_succ(Arc::clone(&n0)));
    assert!(deq(&mut tc, &t, &s));
    // literal-vs-succ: 2 ≡ Nat.succ 1 (offset mixes literal and succ).
    assert!(deq(&mut tc, &lit_nat(2), &nat_succ(lit_nat(1))));
    // negative: succ n0 is not defeq to n0.
    assert!(!deq(&mut tc, &nat_succ(Arc::clone(&n0)), &n0));
}

#[test]
fn eta_lambda() {
    // ff ≡ λ (x : B), ff x
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let ff = mini::cst("ff", vec![]);
    let eta = Expr::lam(
        nm("x"),
        mini::cst("B", vec![]),
        mini::app(Arc::clone(&ff), Expr::bvar(Nat::from(0u64))),
        BinderInfo::Default,
    );
    assert!(deq(&mut tc, &ff, &eta));
}

#[test]
fn eta_struct() {
    // p ≡ Prod.mk A B p.0 p.1
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let p = mini::cst("p", vec![]);
    let proj0 = Expr::proj(nm("Prod"), Nat::from(0u64), Arc::clone(&p));
    let proj1 = Expr::proj(nm("Prod"), Nat::from(1u64), Arc::clone(&p));
    let mk = mini::appn(
        mini::cstn(nm2("Prod", "mk"), vec![]),
        vec![mini::cst("A", vec![]), mini::cst("B", vec![]), proj0, proj1],
    );
    assert!(deq(&mut tc, &p, &mk));
}

#[test]
fn unit_like_defeq() {
    // Any two Unit-typed terms are defeq.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let ux = mini::cst("ux", vec![]);
    let uy = mini::cst("uy", vec![]);
    assert!(deq(&mut tc, &ux, &uy));
}

#[test]
fn string_lit_expansion() {
    // "ab" ≡ String.ofList (List.cons Char (Char.ofNat 97)
    //                        (List.cons Char (Char.ofNat 98)
    //                         (List.nil Char)))
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let str_lit = Expr::lit(Literal::StrVal("ab".to_string()));
    let char_ty = mini::cstn(nm("Char"), vec![]);
    let list_nil = mini::cstn(nm2("List", "nil"), vec![zero_lvl()]);
    let list_cons = mini::cstn(nm2("List", "cons"), vec![zero_lvl()]);
    let char_of_nat = mini::cstn(nm2("Char", "ofNat"), vec![]);
    let string_of_list = mini::cstn(nm2("String", "ofList"), vec![]);
    let nil = mini::app(list_nil, Arc::clone(&char_ty));
    let cons_char = mini::app(list_cons, char_ty);
    // built tail-first: b (98) then a (97)
    let tail = mini::appn(
        Arc::clone(&cons_char),
        vec![mini::app(Arc::clone(&char_of_nat), lit_nat(98)), nil],
    );
    let list = mini::appn(cons_char, vec![mini::app(char_of_nat, lit_nat(97)), tail]);
    let expanded = mini::app(string_of_list, list);
    assert!(deq(&mut tc, &str_lit, &expanded));
}

#[test]
fn equiv_manager_memoizes_structural_equality() {
    // (1) Two pointer-distinct but structurally-equal `f a` applications
    // must compare equal: the old pointer-only cache would have said
    // `false` here, since neither the `Const`s nor the `App` node are
    // shared `Arc`s.
    let app1 = Expr::app(mini::cst("f", vec![]), mini::cst("a", vec![]));
    let app2 = Expr::app(mini::cst("f", vec![]), mini::cst("a", vec![]));
    assert!(!Arc::ptr_eq(&app1, &app2));
    let mut uf = UnionFind::default();
    assert_eq!(uf.is_equiv(&app1, &app2, false, &mut g()), Ok(true));

    // (2) A genuine structural mismatch (`f a` vs `f b`) is still `false`.
    let app3 = Expr::app(mini::cst("f", vec![]), mini::cst("b", vec![]));
    assert_eq!(uf.is_equiv(&app1, &app3, false, &mut g()), Ok(false));

    // (3) Class short-circuit: `p` and `q` are structurally unequal
    // consts, so a fresh `UnionFind` reports them unequal. Once `merge`
    // records them as equivalent, `is_equiv` reports `true` for the same
    // pair via the union-find class lookup alone — the structural compare
    // never runs again. This is the memoization the rewrite added.
    let p = mini::cst("p", vec![]);
    let q = mini::cst("q", vec![]);
    let mut uf2 = UnionFind::default();
    assert_eq!(uf2.is_equiv(&p, &q, false, &mut g()), Ok(false));
    uf2.merge(&p, &q);
    assert_eq!(uf2.is_equiv(&p, &q, false, &mut g()), Ok(true));
}
