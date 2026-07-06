//! Dual-checker differential harness for the id-based `TypeChecker`
//! (migration Task 4). Every test below builds its scenario with the
//! Arc-kernel `crate::testenv::mini` fixtures (unchanged — the SAME
//! hand-rolled environment/expressions `crate::tc::tests` already
//! exercises against the Arc checker in its own, untouched test file),
//! bridges the environment and expression(s) into the term bank, then
//! runs BOTH checkers and asserts identical results. This file adds
//! differential coverage; it does not replace or restate
//! `crate::tc::tests`, which keeps independently pinning the Arc
//! checker's expected values (a passing, unmodified oracle for these
//! same scenarios) — see this module's harness fns for why a bare
//! `assert_eq!(result, expected)` is unnecessary here.
//!
//! Two tests below (`equiv_manager_memoizes_structural_equality`,
//! `unfold_definition_memoizes_polymorphic_unfolds`) poke PRIVATE
//! internals (`UnionFind`, `unfold_definition`) directly, exactly as
//! their Arc originals do — there is no "other side" to dual-compare
//! for a single implementation's own cache-identity behavior, so they
//! assert the id-space analogue (`ExprId` equality where the Arc
//! version asserts `Arc::ptr_eq`) directly against this checker alone.
//! Every other test routes through one of the harness fns below.

use super::*;
use crate::bank::decl::intern_constant_info;
use crate::bank::NameId;
use crate::testenv::{g, mini, nm, nm2};
use crate::{Environment, Expr, Level, Literal, Name, Nat};
use std::collections::HashMap;
use std::sync::Arc;

/// Bridge an Arc-kernel test env into (persistent store, consts map).
fn bridge_env(env: &Environment) -> (Store, HashMap<NameId, ConstantInfo>) {
    let mut st = Store::persistent();
    let mut consts = HashMap::new();
    for ci in env.iter() {
        let idci = intern_constant_info(&mut st, None, ci).unwrap();
        consts.insert(idci.name(), idci);
    }
    (st, consts)
}

/// The per-test harness for `infer_type`: same input expr, both
/// checkers, same verdict.
fn assert_infer_matches(env: &Environment, e: &Arc<Expr>) {
    let arc_result = crate::TypeChecker::new(env).infer_type(e);
    let (st, consts) = bridge_env(env);
    let mut scratch = Store::scratch();
    let eid = scratch.intern_expr(Some(&st), e).unwrap();
    let view = EnvView {
        consts: &consts,
        extra: None,
        quot_initialized: env.quot_initialized(),
        store: &st,
    };
    let id_result = TypeChecker::new(view, &mut scratch).infer_type(eid);
    match (arc_result, id_result) {
        (Ok(a), Ok(b)) => {
            let b = scratch.to_expr(Some(&st), b, &mut g()).unwrap();
            assert!(Expr::structural_eq(&a, &b, &mut g()).unwrap());
        }
        (Err(a), Err(b)) => assert_eq!(a, b),
        (a, b) => panic!("verdict split: arc={a:?} id={b:?}"),
    }
}

/// The per-test harness for `check`: same input expr + level params,
/// both checkers, same verdict.
fn assert_check_matches(env: &Environment, e: &Arc<Expr>, lparams: &[Arc<Name>]) {
    let arc_result = crate::TypeChecker::new(env).check(e, lparams);
    let (st, consts) = bridge_env(env);
    let mut scratch = Store::scratch();
    let eid = scratch.intern_expr(Some(&st), e).unwrap();
    let lparam_ids: Vec<NameId> = lparams
        .iter()
        .map(|n| scratch.intern_name(Some(&st), n).unwrap().unwrap())
        .collect();
    let view = EnvView {
        consts: &consts,
        extra: None,
        quot_initialized: env.quot_initialized(),
        store: &st,
    };
    let id_result = TypeChecker::new(view, &mut scratch).check(eid, &lparam_ids);
    match (arc_result, id_result) {
        (Ok(a), Ok(b)) => {
            let b = scratch.to_expr(Some(&st), b, &mut g()).unwrap();
            assert!(Expr::structural_eq(&a, &b, &mut g()).unwrap());
        }
        (Err(a), Err(b)) => assert_eq!(a, b),
        (a, b) => panic!("verdict split: arc={a:?} id={b:?}"),
    }
}

/// The per-test harness for `whnf`: same input expr, both checkers,
/// structurally-equal (or identically-erroring) results.
fn assert_whnf_matches(env: &Environment, e: &Arc<Expr>) {
    let arc_result = crate::TypeChecker::new(env).whnf(e);
    let (st, consts) = bridge_env(env);
    let mut scratch = Store::scratch();
    let eid = scratch.intern_expr(Some(&st), e).unwrap();
    let view = EnvView {
        consts: &consts,
        extra: None,
        quot_initialized: env.quot_initialized(),
        store: &st,
    };
    let id_result = TypeChecker::new(view, &mut scratch).whnf(eid);
    match (arc_result, id_result) {
        (Ok(a), Ok(b)) => {
            let b = scratch.to_expr(Some(&st), b, &mut g()).unwrap();
            assert!(Expr::structural_eq(&a, &b, &mut g()).unwrap());
        }
        (Err(a), Err(b)) => assert_eq!(a, b),
        (a, b) => panic!("verdict split: arc={a:?} id={b:?}"),
    }
}

/// The per-test harness for `is_def_eq`: same input pair, both
/// checkers, identical bool (compared directly — no bridging needed).
fn assert_is_def_eq_matches(env: &Environment, t: &Arc<Expr>, s: &Arc<Expr>) {
    let arc_result = crate::TypeChecker::new(env).is_def_eq(t, s);
    let (st, consts) = bridge_env(env);
    let mut scratch = Store::scratch();
    let tid = scratch.intern_expr(Some(&st), t).unwrap();
    let sid = scratch.intern_expr(Some(&st), s).unwrap();
    let view = EnvView {
        consts: &consts,
        extra: None,
        quot_initialized: env.quot_initialized(),
        store: &st,
    };
    let id_result = TypeChecker::new(view, &mut scratch).is_def_eq(tid, sid);
    match (arc_result, id_result) {
        (Ok(a), Ok(b)) => assert_eq!(a, b),
        (Err(a), Err(b)) => assert_eq!(a, b),
        (a, b) => panic!("verdict split: arc={a:?} id={b:?}"),
    }
}

#[test]
fn infer_sort_of_sort() {
    let env = mini::env();
    assert_infer_matches(&env, &mini::sort_u());
}

#[test]
fn infer_lambda_gives_pi() {
    let env = mini::env();
    let lam = Expr::lam(
        nm("x"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    assert_infer_matches(&env, &lam);
}

#[test]
fn check_rejects_loose_bvar() {
    let env = mini::env();
    let e = Expr::bvar(Nat::from(0u64));
    assert_infer_matches(&env, &e);
}

#[test]
fn check_rejects_mvar() {
    let env = mini::env();
    let e = Expr::mvar(nm("m"));
    assert_infer_matches(&env, &e);
}

#[test]
fn check_rejects_univ_arity() {
    let env = mini::env();
    let e = mini::cst("id1", vec![]);
    assert_infer_matches(&env, &e);
}

/// Not a port of an Arc `tc/tests.rs` case — regression coverage for a
/// bug this task's review caught: a `Const` naming something NEVER
/// interned into the persistent store mints a fresh SCRATCH-region
/// `NameId` (the whole point of "unknown constant"), and
/// `EnvView::get_with`'s own `to_name(None, ...)` call resolves a miss
/// against `store` alone — wrong for a scratch id (see `store_for`'s
/// doc comment) and, depending on index sizes, either reports the WRONG
/// name or panics on an out-of-bounds row read. `TypeChecker::env_get_with`
/// does not delegate to `EnvView::get_with` for exactly this reason; this
/// test exercises it end-to-end through `infer_type`, referencing a name
/// that is `Anonymous`-free and provably absent from `mini::env()`.
#[test]
fn unknown_constant_from_a_fresh_scratch_name_reports_correctly() {
    let env = mini::env();
    let e = mini::cst("TotallyUnknownDeclaration", vec![]);
    assert_infer_matches(&env, &e);
}

#[test]
fn app_type_mismatch_rejected() {
    let env = mini::env();
    let id1_0 = mini::cst("id1", vec![Arc::new(Level::Zero)]);
    let good = Expr::app(
        Expr::app(Arc::clone(&id1_0), mini::cst("A", vec![])),
        mini::cst("a", vec![]),
    );
    assert_check_matches(&env, &good, &[]);
    let bad = Expr::app(
        Expr::app(id1_0, mini::cst("a", vec![])),
        mini::cst("a", vec![]),
    );
    assert_check_matches(&env, &bad, &[]);
}

#[test]
fn beta_whnf() {
    let env = mini::env();
    let a = mini::cst("a", vec![]);
    let idfun = Expr::lam(
        nm("x"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let e = Expr::app(idfun, a);
    assert_whnf_matches(&env, &e);
}

#[test]
fn zeta_whnf() {
    let env = mini::env();
    let a = mini::cst("a", vec![]);
    let e = Expr::let_e(
        nm("x"),
        mini::cst("A", vec![]),
        a,
        Expr::bvar(Nat::from(0u64)),
        false,
    );
    assert_whnf_matches(&env, &e);
}

#[test]
fn delta_whnf() {
    let env = mini::env();
    let a = mini::cst("a", vec![]);
    let e = Expr::app(
        Expr::app(
            mini::cst("id1", vec![Arc::new(Level::Zero)]),
            mini::cst("A", vec![]),
        ),
        a,
    );
    assert_whnf_matches(&env, &e);
}

#[test]
fn defeq_alpha_binding() {
    let env = mini::env();
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
    assert_is_def_eq_matches(&env, &lx, &ly);
}

#[test]
fn defeq_proof_irrelevance() {
    let env = mini::env();
    let a = mini::cst("a", vec![]);
    let w = mini::cst("w", vec![]);
    assert_is_def_eq_matches(&env, &a, &w);
}

#[test]
fn defeq_pi_congruence() {
    let env = mini::env();
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
    assert_is_def_eq_matches(&env, &pi_a_x, &pi_a_y);
    let pi_a_prop = Expr::forall_e(
        nm("x"),
        mini::cst("A", vec![]),
        mini::sort0(),
        BinderInfo::Default,
    );
    assert_is_def_eq_matches(&env, &pi_a_x, &pi_a_prop);
}

#[test]
fn whnf_cache_and_sharing() {
    // Arc-side pins pointer-identity cache reuse (`crate::tc::tests`,
    // unchanged); here we only need the dual-checker parity property,
    // which the harness already gives us — call it twice, matching the
    // original's two `tc.whnf(&e)` calls.
    let env = mini::env();
    let idfun = Expr::lam(
        nm("x"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let e = Expr::app(idfun, mini::cst("a", vec![]));
    assert_whnf_matches(&env, &e);
    assert_whnf_matches(&env, &e);
}

#[test]
fn check_sets_lparams() {
    let env = mini::env();
    let lam = Expr::lam(
        nm("α"),
        mini::sort_u(),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    assert_check_matches(&env, &lam, &[mini::u()]);
    assert_check_matches(&env, &lam, &[]);
}

// ===================================================================
// Task 7: special reductions
// ===================================================================

fn lit_nat(n: u64) -> Arc<Expr> {
    Expr::lit(Literal::NatVal(Nat::from(n)))
}

fn nat_succ(arg: Arc<Expr>) -> Arc<Expr> {
    mini::app(mini::cstn(nm2("Nat", "succ"), vec![]), arg)
}

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
    let env = mini::env();
    let (cc, z, s, n) = (
        mini::cst("C", vec![]),
        mini::cst("z", vec![]),
        mini::cst("s", vec![]),
        mini::cst("n", vec![]),
    );
    let natrec = mini::cstn(nm2("Nat", "rec"), vec![zero_lvl()]);
    let e = mini::appn(natrec, vec![cc, z, s, nat_succ(n)]);
    assert_whnf_matches(&env, &e);
}

#[test]
fn iota_on_literal_major() {
    let env = mini::env();
    let (cc, z, s) = (
        mini::cst("C", vec![]),
        mini::cst("z", vec![]),
        mini::cst("s", vec![]),
    );
    let natrec = mini::cstn(nm2("Nat", "rec"), vec![zero_lvl()]);
    let e = mini::appn(natrec, vec![cc, z, s, lit_nat(2)]);
    assert_whnf_matches(&env, &e);
}

#[test]
fn k_like_rec_on_eq() {
    let env = mini::env();
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
    assert_whnf_matches(&env, &e);
}

#[test]
fn quot_lift_beta() {
    let env = mini::env();
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
        vec![alpha.clone(), rel.clone(), a],
    );
    let e = mini::appn(
        mini::cstn(nm2("Quot", "lift"), vec![zero_lvl(), zero_lvl()]),
        vec![alpha, rel, beta, f, h, mk],
    );
    assert_whnf_matches(&env, &e);
}

#[test]
fn quot_ind_beta() {
    let env = mini::env();
    let (alpha, rel, beta, h, a) = (
        mini::cst("α", vec![]),
        mini::cst("r", vec![]),
        mini::cst("β", vec![]),
        mini::cst("h", vec![]),
        mini::cst("a", vec![]),
    );
    let mk = mini::appn(
        mini::cstn(nm2("Quot", "mk"), vec![zero_lvl()]),
        vec![alpha.clone(), rel.clone(), a],
    );
    let e = mini::appn(
        mini::cstn(nm2("Quot", "ind"), vec![zero_lvl()]),
        vec![alpha, rel, beta, h, mk],
    );
    assert_whnf_matches(&env, &e);
}

#[test]
fn nat_add_folds() {
    let env = mini::env();
    assert_whnf_matches(&env, &nat_binop("add", lit_nat(2), lit_nat(3)));
    assert_whnf_matches(&env, &nat_binop("sub", lit_nat(2), lit_nat(5)));
    assert_whnf_matches(&env, &nat_binop("div", lit_nat(5), lit_nat(0)));
    assert_whnf_matches(&env, &nat_binop("mod", lit_nat(5), lit_nat(0)));
    // pow guard: exponent 2^25 > 1<<24 ⇒ un-reduced.
    assert_whnf_matches(&env, &nat_binop("pow", lit_nat(2), lit_nat(1 << 25)));
    // pow that is allowed: 2^10 = 1024.
    assert_whnf_matches(&env, &nat_binop("pow", lit_nat(2), lit_nat(10)));
}

#[test]
fn nat_beq_folds_to_bool() {
    let env = mini::env();
    assert_whnf_matches(&env, &nat_binop("beq", lit_nat(2), lit_nat(2)));
    assert_whnf_matches(&env, &nat_binop("beq", lit_nat(2), lit_nat(3)));
    assert_whnf_matches(&env, &nat_binop("ble", lit_nat(2), lit_nat(3)));
}

#[test]
fn succ_folds() {
    let env = mini::env();
    assert_whnf_matches(&env, &nat_succ(lit_nat(4)));
}

#[test]
fn offset_defeq() {
    let env = mini::env();
    let n0 = mini::cst("n0", vec![]);
    let t = nat_succ(nat_succ(Arc::clone(&n0)));
    let s = nat_succ(nat_succ(Arc::clone(&n0)));
    assert_is_def_eq_matches(&env, &t, &s);
    assert_is_def_eq_matches(&env, &lit_nat(2), &nat_succ(lit_nat(1)));
    assert_is_def_eq_matches(&env, &nat_succ(Arc::clone(&n0)), &n0);
}

#[test]
fn eta_lambda() {
    let env = mini::env();
    let ff = mini::cst("ff", vec![]);
    let eta = Expr::lam(
        nm("x"),
        mini::cst("B", vec![]),
        mini::app(Arc::clone(&ff), Expr::bvar(Nat::from(0u64))),
        BinderInfo::Default,
    );
    assert_is_def_eq_matches(&env, &ff, &eta);
}

#[test]
fn eta_struct() {
    let env = mini::env();
    let p = mini::cst("p", vec![]);
    let proj0 = Expr::proj(nm("Prod"), Nat::from(0u64), Arc::clone(&p));
    let proj1 = Expr::proj(nm("Prod"), Nat::from(1u64), Arc::clone(&p));
    let mk = mini::appn(
        mini::cstn(nm2("Prod", "mk"), vec![]),
        vec![mini::cst("A", vec![]), mini::cst("B", vec![]), proj0, proj1],
    );
    assert_is_def_eq_matches(&env, &p, &mk);
}

#[test]
fn unit_like_defeq() {
    let env = mini::env();
    let ux = mini::cst("ux", vec![]);
    let uy = mini::cst("uy", vec![]);
    assert_is_def_eq_matches(&env, &ux, &uy);
}

#[test]
fn string_lit_expansion() {
    let env = mini::env();
    let str_lit = Expr::lit(Literal::StrVal("ab".to_string()));
    let char_ty = mini::cstn(nm("Char"), vec![]);
    let list_nil = mini::cstn(nm2("List", "nil"), vec![zero_lvl()]);
    let list_cons = mini::cstn(nm2("List", "cons"), vec![zero_lvl()]);
    let char_of_nat = mini::cstn(nm2("Char", "ofNat"), vec![]);
    let string_of_list = mini::cstn(nm2("String", "ofList"), vec![]);
    let nil = mini::app(list_nil, Arc::clone(&char_ty));
    let cons_char = mini::app(list_cons, char_ty);
    let tail = mini::appn(
        Arc::clone(&cons_char),
        vec![mini::app(Arc::clone(&char_of_nat), lit_nat(98)), nil],
    );
    let list = mini::appn(cons_char, vec![mini::app(char_of_nat, lit_nat(97)), tail]);
    let expanded = mini::app(string_of_list, list);
    assert_is_def_eq_matches(&env, &str_lit, &expanded);
}

// -------------------------------------------------------------------
// Private-internals tests: no Arc-side counterpart to dual-compare
// against, so these assert the id-space analogue of the Arc test's
// pointer-identity claim directly against this checker.
// -------------------------------------------------------------------

#[test]
fn equiv_manager_memoizes_structural_equality() {
    let mut st = Store::persistent();
    let f = st.intern_name(None, &nm("f")).unwrap();
    let a_ = st.intern_name(None, &nm("a")).unwrap();
    let b_ = st.intern_name(None, &nm("b")).unwrap();
    let p_ = st.intern_name(None, &nm("p")).unwrap();
    let q_ = st.intern_name(None, &nm("q")).unwrap();
    let no_lv = st.intern_level_list(None, &[]).unwrap();
    let cst = |st: &mut Store, n| st.expr_const(None, n, no_lv).unwrap();

    // (1) Two id-distinct but structurally-equal `f a` applications must
    // compare equal via the union-find's structural fallback.
    let f1 = cst(&mut st, f);
    let a1 = cst(&mut st, a_);
    let app1 = st.expr_app(None, f1, a1).unwrap();
    let f2 = cst(&mut st, f);
    let a2 = cst(&mut st, a_);
    let app2 = st.expr_app(None, f2, a2).unwrap();
    // The interning invariant already makes these the SAME id (a
    // strictly stronger property than the Arc port's `!Arc::ptr_eq`
    // pre-condition — see the porting table: `==` now hits more, never
    // fewer, than `Arc::ptr_eq`), so `is_equiv` is trivially true here
    // via the `a == b` fast path, not the structural fallback below.
    assert_eq!(app1, app2);
    let mut uf = UnionFind::default();
    assert_eq!(
        uf.is_equiv(&st, None, app1, app2, false, &mut g()),
        Ok(true)
    );

    // (2) A genuine structural mismatch (`f a` vs `f b`) is still `false`.
    let f3 = cst(&mut st, f);
    let b1 = cst(&mut st, b_);
    let app3 = st.expr_app(None, f3, b1).unwrap();
    assert_eq!(
        uf.is_equiv(&st, None, app1, app3, false, &mut g()),
        Ok(false)
    );

    // (3) Class short-circuit: `p` and `q` are structurally unequal
    // consts, so a fresh `UnionFind` reports them unequal; once `merge`
    // records them as equivalent, `is_equiv` reports `true` via the
    // union-find class lookup alone.
    let p = cst(&mut st, p_);
    let q = cst(&mut st, q_);
    let mut uf2 = UnionFind::default();
    assert_eq!(uf2.is_equiv(&st, None, p, q, false, &mut g()), Ok(false));
    uf2.merge(p, q);
    assert_eq!(uf2.is_equiv(&st, None, p, q, false, &mut g()), Ok(true));
}

#[test]
fn unfold_definition_memoizes_polymorphic_unfolds() {
    let env = mini::env();
    let c = mini::cst("id1", vec![Arc::new(Level::Zero)]);
    let (st, consts) = bridge_env(&env);
    let mut scratch = Store::scratch();
    let cid = scratch.intern_expr(Some(&st), &c).unwrap();
    let view = EnvView {
        consts: &consts,
        extra: None,
        quot_initialized: env.quot_initialized(),
        store: &st,
    };
    let mut tc = TypeChecker::new(view, &mut scratch);
    let u1 = tc.unfold_definition(cid).unwrap().unwrap();
    let u2 = tc.unfold_definition(cid).unwrap().unwrap();
    assert_eq!(
        u1, u2,
        "repeated unfold of one Const must be memoized (oracle m_unfold)"
    );
}
