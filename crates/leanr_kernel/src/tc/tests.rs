//! Unit tests for the id-native `TypeChecker` (migration Task 8: ported
//! from the pre-flip `crate::tc::tests`, which dual-compared against
//! the Arc checker this migration deletes — see that file's history,
//! `git show 9b1c773:crates/leanr_kernel/src/tc/tests.rs`). Every test
//! below asserts the SAME expected values that file pinned, now
//! directly against the id checker: the interning invariant makes id
//! equality the exact id-space analogue of the Arc tests'
//! `Arc::ptr_eq`/`Expr::structural_eq` checks, so no bridging or
//! cross-kernel comparison is needed any more.
//!
//! Two tests (`equiv_manager_memoizes_structural_equality`,
//! `unfold_definition_memoizes_polymorphic_unfolds`) poke PRIVATE
//! internals (`UnionFind`, `unfold_definition`) directly, exactly as
//! their Arc originals did — there is no "other side" to compare for a
//! single implementation's own cache-identity behavior.

use super::*;
use crate::testenv::{g, mini, nm, nm2};
use crate::{BinderInfo, Environment, Expr, KernelError, Level, Literal, Nat};
use std::sync::Arc;

/// Intern an `Arc<Expr>` fixture into `scratch`, based on `env`'s
/// persistent store.
fn xid(scratch: &mut Store, base: &Store, e: &Arc<Expr>) -> ExprId {
    scratch.intern_expr(Some(base), e).unwrap()
}

/// `infer_type`, id-native: intern `e` into a fresh scratch checker over
/// `env`, run `infer_type`.
fn infer(env: &Environment, scratch: &mut Store, e: &Arc<Expr>) -> Result<ExprId, KernelError> {
    let base = env.view().store;
    let eid = xid(scratch, base, e);
    TypeChecker::new(env.view(), scratch).infer_type(eid)
}

/// `check`, id-native.
fn check(
    env: &Environment,
    scratch: &mut Store,
    e: &Arc<Expr>,
    lparams: &[Arc<crate::Name>],
) -> Result<ExprId, KernelError> {
    let base = env.view().store;
    let eid = xid(scratch, base, e);
    let lparam_ids: Vec<NameId> = lparams
        .iter()
        .map(|n| scratch.intern_name(Some(base), n).unwrap().unwrap())
        .collect();
    TypeChecker::new(env.view(), scratch).check(eid, &lparam_ids)
}

/// `whnf`, id-native.
fn whnf(env: &Environment, scratch: &mut Store, e: &Arc<Expr>) -> Result<ExprId, KernelError> {
    let base = env.view().store;
    let eid = xid(scratch, base, e);
    TypeChecker::new(env.view(), scratch).whnf(eid)
}

/// `is_def_eq`, id-native.
fn deq(env: &Environment, scratch: &mut Store, a: &Arc<Expr>, b: &Arc<Expr>) -> bool {
    let base = env.view().store;
    let aid = xid(scratch, base, a);
    let bid = xid(scratch, base, b);
    TypeChecker::new(env.view(), scratch)
        .is_def_eq(aid, bid)
        .unwrap()
}

#[test]
fn infer_sort_of_sort() {
    // infer(Sort u) = Sort (u+1)
    let env = mini::env();
    let mut scratch = Store::scratch();
    let r = infer(&env, &mut scratch, &mini::sort_u()).unwrap();
    let expected = Expr::sort(Level::mk_succ(Arc::new(Level::Param(mini::u()))), &mut g()).unwrap();
    let base = env.view().store;
    assert_eq!(r, xid(&mut scratch, base, &expected));
}

#[test]
fn infer_lambda_gives_pi() {
    // infer(λ (x : A), x) ≡ A → A
    let env = mini::env();
    let mut scratch = Store::scratch();
    let lam = Expr::lam(
        nm("x"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let r = infer(&env, &mut scratch, &lam).unwrap();
    let a_to_a = Expr::forall_e(
        nm("x"),
        mini::cst("A", vec![]),
        mini::cst("A", vec![]),
        BinderInfo::Default,
    );
    let base = env.view().store;
    assert_eq!(r, xid(&mut scratch, base, &a_to_a));
}

#[test]
fn check_rejects_loose_bvar() {
    let env = mini::env();
    let mut scratch = Store::scratch();
    let e = Expr::bvar(Nat::from(0u64));
    assert_eq!(
        infer(&env, &mut scratch, &e).unwrap_err(),
        KernelError::LooseBVar
    );
}

#[test]
fn check_rejects_mvar() {
    let env = mini::env();
    let mut scratch = Store::scratch();
    let e = Expr::mvar(nm("m"));
    assert_eq!(
        infer(&env, &mut scratch, &e).unwrap_err(),
        KernelError::MetavarEncountered
    );
}

#[test]
fn check_rejects_univ_arity() {
    // Const id₁ [] — decl has 1 level param.
    let env = mini::env();
    let mut scratch = Store::scratch();
    let e = mini::cst("id1", vec![]);
    assert_eq!(
        infer(&env, &mut scratch, &e).unwrap_err(),
        KernelError::UnivParamArityMismatch { name: nm("id1") }
    );
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
    let mut scratch = Store::scratch();
    let e = mini::cst("TotallyUnknownDeclaration", vec![]);
    assert_eq!(
        infer(&env, &mut scratch, &e).unwrap_err(),
        KernelError::UnknownConstant(nm("TotallyUnknownDeclaration"))
    );
}

#[test]
fn app_type_mismatch_rejected() {
    let env = mini::env();
    let mut scratch = Store::scratch();
    let id1_0 = mini::cst("id1", vec![Arc::new(Level::Zero)]);
    // id₁.{0} A a is well-typed.
    let good = Expr::app(
        Expr::app(Arc::clone(&id1_0), mini::cst("A", vec![])),
        mini::cst("a", vec![]),
    );
    assert!(check(&env, &mut scratch, &good, &[]).is_ok());
    // id₁.{0} a a — first arg `a : A` where a `Sort 0` is expected.
    let bad = Expr::app(
        Expr::app(id1_0, mini::cst("a", vec![])),
        mini::cst("a", vec![]),
    );
    assert_eq!(
        check(&env, &mut scratch, &bad, &[]).unwrap_err(),
        KernelError::AppTypeMismatch
    );
}

#[test]
fn beta_whnf() {
    // whnf((λ x, x) a) = a
    let env = mini::env();
    let mut scratch = Store::scratch();
    let a = mini::cst("a", vec![]);
    let idfun = Expr::lam(
        nm("x"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let e = Expr::app(idfun, Arc::clone(&a));
    let r = whnf(&env, &mut scratch, &e).unwrap();
    let base = env.view().store;
    assert_eq!(r, xid(&mut scratch, base, &a));
}

#[test]
fn zeta_whnf() {
    // whnf(let x := a in x) = a.
    let env = mini::env();
    let mut scratch = Store::scratch();
    let a = mini::cst("a", vec![]);
    let e = Expr::let_e(
        nm("x"),
        mini::cst("A", vec![]),
        Arc::clone(&a),
        Expr::bvar(Nat::from(0u64)),
        false,
    );
    let r = whnf(&env, &mut scratch, &e).unwrap();
    let base = env.view().store;
    assert_eq!(r, xid(&mut scratch, base, &a));
}

#[test]
fn delta_whnf() {
    // whnf(id₁.{0} A a) = a via unfold + beta chain.
    let env = mini::env();
    let mut scratch = Store::scratch();
    let a = mini::cst("a", vec![]);
    let e = Expr::app(
        Expr::app(
            mini::cst("id1", vec![Arc::new(Level::Zero)]),
            mini::cst("A", vec![]),
        ),
        Arc::clone(&a),
    );
    let r = whnf(&env, &mut scratch, &e).unwrap();
    let base = env.view().store;
    assert_eq!(r, xid(&mut scratch, base, &a));
}

#[test]
fn defeq_alpha_binding() {
    // λ x, x ≡ λ y, y (binder names ignored).
    let env = mini::env();
    let mut scratch = Store::scratch();
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
    assert!(deq(&env, &mut scratch, &lx, &ly));
}

#[test]
fn defeq_proof_irrelevance() {
    // a ≡ w (both : A : Prop).
    let env = mini::env();
    let mut scratch = Store::scratch();
    let a = mini::cst("a", vec![]);
    let w = mini::cst("w", vec![]);
    assert!(deq(&env, &mut scratch, &a, &w));
}

#[test]
fn defeq_pi_congruence() {
    // Π(x:A),A ≡ Π(y:A),A ; and NOT ≡ Π(x:A),Prop
    let env = mini::env();
    let mut scratch = Store::scratch();
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
    assert!(deq(&env, &mut scratch, &pi_a_x, &pi_a_y));
    let pi_a_prop = Expr::forall_e(
        nm("x"),
        mini::cst("A", vec![]),
        mini::sort0(),
        BinderInfo::Default,
    );
    assert!(!deq(&env, &mut scratch, &pi_a_x, &pi_a_prop));
}

#[test]
fn whnf_cache_and_sharing() {
    // whnf twice: the second call returns the same id (cache hit — the
    // Arc original asserted `Arc::ptr_eq`; the interning invariant makes
    // id equality the exact id-space analogue).
    let env = mini::env();
    let mut scratch = Store::scratch();
    let idfun = Expr::lam(
        nm("x"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let e = Expr::app(idfun, mini::cst("a", vec![]));
    let r1 = whnf(&env, &mut scratch, &e).unwrap();
    let r2 = whnf(&env, &mut scratch, &e).unwrap();
    assert_eq!(r1, r2);
}

#[test]
fn check_sets_lparams() {
    // check(λ (α : Sort u), α, [u]) passes; with [] the undefined param
    // `u` is a check_level error (mapped to UnivParamArityMismatch).
    //
    // Independent checkers per check (fresh `scratch`/`TypeChecker` per
    // call, exactly like `infer`/`check`/`whnf`/`deq` above): the
    // `infer_type` memo is keyed by `ExprId`, NOT by lparams, so
    // checking the SAME id twice on ONE checker would hit the cache and
    // skip re-validation (identical to the oracle). Real admission
    // (Replay) builds a fresh checker per decl, which is what these two
    // checks model.
    let env = mini::env();
    let lam = Expr::lam(
        nm("α"),
        mini::sort_u(),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let mut scratch_ok = Store::scratch();
    assert!(check(&env, &mut scratch_ok, &lam, &[mini::u()]).is_ok());
    let mut scratch_bad = Store::scratch();
    assert_eq!(
        check(&env, &mut scratch_bad, &lam, &[]).unwrap_err(),
        KernelError::UnivParamArityMismatch { name: mini::u() }
    );
}

// ===================================================================
// Task 7: special reductions
// ===================================================================

fn lit_nat(n: u64) -> Arc<Expr> {
    Expr::lit(Literal::NatVal(Nat::from(n)))
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
    let mut scratch = Store::scratch();
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
    let r = whnf(&env, &mut scratch, &e).unwrap();
    let expected = mini::app(
        mini::app(Arc::clone(&s), Arc::clone(&n)),
        mini::appn(natrec, vec![cc, z, s, n]),
    );
    let base = env.view().store;
    assert_eq!(r, xid(&mut scratch, base, &expected));
}

#[test]
fn iota_on_literal_major() {
    // whnf(Nat.rec.{0} C z s 2) = s 1 (Nat.rec.{0} C z s 1) — the literal
    // major `2` is converted to `Nat.succ 1` before rule selection.
    let env = mini::env();
    let mut scratch = Store::scratch();
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
    let r = whnf(&env, &mut scratch, &e).unwrap();
    let expected = mini::app(
        mini::app(Arc::clone(&s), lit_nat(1)),
        mini::appn(natrec, vec![cc, z, s, lit_nat(1)]),
    );
    let base = env.view().store;
    assert_eq!(r, xid(&mut scratch, base, &expected));
}

#[cfg(feature = "trace-reductions")]
#[test]
fn trace_counts_nat_rec_reductions() {
    use crate::tc::trace;
    trace::reset();
    let env = mini::env();
    let mut scratch = Store::scratch();
    let base = env.view().store;
    let (cc, z, s) = (
        mini::cst("C", vec![]),
        mini::cst("z", vec![]),
        mini::cst("s", vec![]),
    );
    let natrec = mini::cstn(nm2("Nat", "rec"), vec![zero_lvl()]);
    let e = mini::appn(natrec, vec![cc, z, s, lit_nat(3)]);
    let mut cur = xid(&mut scratch, base, &e);
    let mut checker = TypeChecker::new(env.view(), &mut scratch);
    // `whnf` fires the recursor exactly once per call (weak head normal
    // form does not recurse into the minor premise's arguments; see
    // `iota_on_literal_major` above, which pins `whnf(rec ... 2) = s 1
    // (rec ... 1)` — the nested `rec` stays unreduced). Walking literal
    // 3 down through 2, 1, 0 by re-`whnf`-ing the nested `Nat.rec`
    // argument three times gives 3 real recursor firings.
    for _ in 0..3 {
        let r = checker.whnf(cur).unwrap();
        let args = checker.get_app_args(r);
        cur = *args.last().expect("succ minor applied to (n, ih)");
    }
    assert!(trace::total() >= 3, "snapshot: {:?}", trace::snapshot());
}

#[test]
fn k_like_rec_on_eq() {
    // whnf(Eq.rec.{0,1} A a0 Mot req a0 h) = req, where h : @Eq.{1} A a0 a0
    // is an opaque rfl-typed proof. The K-recursor synthesizes `Eq.refl`
    // from h's type and selects the (fields-less) refl rule.
    let env = mini::env();
    let mut scratch = Store::scratch();
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
    let r = whnf(&env, &mut scratch, &e).unwrap();
    let base = env.view().store;
    assert_eq!(r, xid(&mut scratch, base, &mini::cst("req", vec![])));
}

#[test]
fn quot_lift_beta() {
    // whnf(Quot.lift.{0,0} α r β f h (Quot.mk.{0} α r a)) = f a
    let env = mini::env();
    let mut scratch = Store::scratch();
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
    let r = whnf(&env, &mut scratch, &e).unwrap();
    let base = env.view().store;
    assert_eq!(r, xid(&mut scratch, base, &mini::app(f, a)));
}

#[test]
fn quot_ind_beta() {
    // whnf(Quot.ind.{0} α r β h (Quot.mk.{0} α r a)) = h a
    let env = mini::env();
    let mut scratch = Store::scratch();
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
    let r = whnf(&env, &mut scratch, &e).unwrap();
    let base = env.view().store;
    assert_eq!(r, xid(&mut scratch, base, &mini::app(h, a)));
}

#[test]
fn nat_add_folds() {
    let env = mini::env();
    let mut scratch = Store::scratch();
    let base = env.view().store;
    // add 2 3 = 5
    let r = whnf(
        &env,
        &mut scratch,
        &nat_binop("add", lit_nat(2), lit_nat(3)),
    )
    .unwrap();
    assert_eq!(r, xid(&mut scratch, base, &lit_nat(5)));
    // sub 2 5 = 0 (truncated)
    let r = whnf(
        &env,
        &mut scratch,
        &nat_binop("sub", lit_nat(2), lit_nat(5)),
    )
    .unwrap();
    assert_eq!(r, xid(&mut scratch, base, &lit_nat(0)));
    // div 5 0 = 0
    let r = whnf(
        &env,
        &mut scratch,
        &nat_binop("div", lit_nat(5), lit_nat(0)),
    )
    .unwrap();
    assert_eq!(r, xid(&mut scratch, base, &lit_nat(0)));
    // mod 5 0 = 5
    let r = whnf(
        &env,
        &mut scratch,
        &nat_binop("mod", lit_nat(5), lit_nat(0)),
    )
    .unwrap();
    assert_eq!(r, xid(&mut scratch, base, &lit_nat(5)));
    // pow guard: exponent 2^25 > 1<<24 ⇒ un-reduced (still an App node).
    let pow = nat_binop("pow", lit_nat(2), lit_nat(1 << 25));
    let r = whnf(&env, &mut scratch, &pow).unwrap();
    assert!(
        matches!(scratch.expr_node(Some(base), r), Node::App { .. }),
        "got {r:?}"
    );
    // pow that is allowed: 2^10 = 1024.
    let r = whnf(
        &env,
        &mut scratch,
        &nat_binop("pow", lit_nat(2), lit_nat(10)),
    )
    .unwrap();
    assert_eq!(r, xid(&mut scratch, base, &lit_nat(1024)));
}

#[test]
fn nat_beq_folds_to_bool() {
    let env = mini::env();
    let mut scratch = Store::scratch();
    let base = env.view().store;
    let r = whnf(
        &env,
        &mut scratch,
        &nat_binop("beq", lit_nat(2), lit_nat(2)),
    )
    .unwrap();
    assert_eq!(
        r,
        xid(&mut scratch, base, &mini::cstn(nm2("Bool", "true"), vec![]))
    );
    let r2 = whnf(
        &env,
        &mut scratch,
        &nat_binop("beq", lit_nat(2), lit_nat(3)),
    )
    .unwrap();
    assert_eq!(
        r2,
        xid(
            &mut scratch,
            base,
            &mini::cstn(nm2("Bool", "false"), vec![])
        )
    );
    // ble 2 3 = true
    let r3 = whnf(
        &env,
        &mut scratch,
        &nat_binop("ble", lit_nat(2), lit_nat(3)),
    )
    .unwrap();
    assert_eq!(
        r3,
        xid(&mut scratch, base, &mini::cstn(nm2("Bool", "true"), vec![]))
    );
}

/// Result-B regression (fix: `unfold_and_whnf` consults `reduce_nat`
/// before delta-unfolding — tc.rs, `Nat.brecOn`/`Nat.below` divergence).
///
/// Drives the kernel into deciding `P Bool.true =?= P (Nat.beq 4 x)`
/// where `x` is a LET-BOUND fvar whose value is a literal: `Nat.beq 4 x`
/// then has `has_fvar == true`, so BOTH pre-existing `reduce_nat` guards
/// miss it — the top-level `whnf` loop is never consulted on this
/// `is_def_eq` route, and `lazy_delta_reduction`'s joint
/// `!has_fvar(t) && !has_fvar(s)` fast-path guard skips it — leaving the
/// `lazy_delta_reduction_step` unfold as the only route to an answer
/// (exactly how `Char.ofOrdinal._proof_3` escaped into the `Nat.below`
/// tower walk). The fixture `Nat.beq` body is an opaque stub, so
/// delta-unfolding CANNOT decide the pair: the check succeeds iff the
/// native reduction fired on the unfold step, matching the oracle's
/// native behavior (real `Kernel.whnf` reduces `Nat.beq big (Nat.sub x
/// 5)` with a let-bound `x` straight to `Bool.true`).
#[test]
fn nat_beq_native_reduction_fires_on_is_def_eq_path_with_let_fvar() {
    let env = mini::env_with(mini::nat_beq_regression_decls());
    let mut scratch = Store::scratch();
    // let x : Nat := 4; useP x hPtrue
    //   useP x : P (Nat.beq 4 x) → B,  hPtrue : P Bool.true
    let body = mini::appn(
        mini::cst("useP", vec![]),
        vec![mini::bvar(0), mini::cst("hPtrue", vec![])],
    );
    let e = Expr::let_e(nm("x"), mini::nat(), lit_nat(4), body, false);
    // Pre-fix: Err(AppTypeMismatch) — the stub unfold sticks at
    // `Nat.beqAux 4 x` and the pair is (wrongly) undecidable. Post-fix:
    // the unfold step natively collapses `Nat.beq 4 x` to `Bool.true`.
    check(&env, &mut scratch, &e, &[]).unwrap();
}

#[test]
fn succ_folds() {
    // whnf(Nat.succ 4) = 5
    let env = mini::env();
    let mut scratch = Store::scratch();
    let r = whnf(&env, &mut scratch, &nat_succ(lit_nat(4))).unwrap();
    let base = env.view().store;
    assert_eq!(r, xid(&mut scratch, base, &lit_nat(5)));
}

#[test]
fn offset_defeq() {
    let env = mini::env();
    let mut scratch = Store::scratch();
    // succ (succ n0) ≡ succ (succ n0) via offset peeling.
    let n0 = mini::cst("n0", vec![]);
    let t = nat_succ(nat_succ(Arc::clone(&n0)));
    let s = nat_succ(nat_succ(Arc::clone(&n0)));
    assert!(deq(&env, &mut scratch, &t, &s));
    // literal-vs-succ: 2 ≡ Nat.succ 1 (offset mixes literal and succ).
    assert!(deq(&env, &mut scratch, &lit_nat(2), &nat_succ(lit_nat(1))));
    // negative: succ n0 is not defeq to n0.
    assert!(!deq(&env, &mut scratch, &nat_succ(Arc::clone(&n0)), &n0));
}

#[test]
fn eta_lambda() {
    // ff ≡ λ (x : B), ff x
    let env = mini::env();
    let mut scratch = Store::scratch();
    let ff = mini::cst("ff", vec![]);
    let eta = Expr::lam(
        nm("x"),
        mini::cst("B", vec![]),
        mini::app(Arc::clone(&ff), Expr::bvar(Nat::from(0u64))),
        BinderInfo::Default,
    );
    assert!(deq(&env, &mut scratch, &ff, &eta));
}

#[test]
fn eta_struct() {
    // p ≡ Prod.mk A B p.0 p.1
    let env = mini::env();
    let mut scratch = Store::scratch();
    let p = mini::cst("p", vec![]);
    let proj0 = Expr::proj(nm("Prod"), Nat::from(0u64), Arc::clone(&p));
    let proj1 = Expr::proj(nm("Prod"), Nat::from(1u64), Arc::clone(&p));
    let mk = mini::appn(
        mini::cstn(nm2("Prod", "mk"), vec![]),
        vec![mini::cst("A", vec![]), mini::cst("B", vec![]), proj0, proj1],
    );
    assert!(deq(&env, &mut scratch, &p, &mk));
}

#[test]
fn unit_like_defeq() {
    // Any two Unit-typed terms are defeq.
    let env = mini::env();
    let mut scratch = Store::scratch();
    let ux = mini::cst("ux", vec![]);
    let uy = mini::cst("uy", vec![]);
    assert!(deq(&env, &mut scratch, &ux, &uy));
}

#[test]
fn string_lit_expansion() {
    // "ab" ≡ String.ofList (List.cons Char (Char.ofNat 97)
    //                        (List.cons Char (Char.ofNat 98)
    //                         (List.nil Char)))
    let env = mini::env();
    let mut scratch = Store::scratch();
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
    assert!(deq(&env, &mut scratch, &str_lit, &expanded));
}

// -------------------------------------------------------------------
// Private-internals tests: no cross-kernel comparison to make (never
// had one — even before migration Task 8, these asserted the id-space
// analogue of the Arc test's pointer-identity claim directly).
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
    // oracle: type_checker.cpp:497-518 — `m_unfold` returns the SAME
    // expr for a repeated unfold of one `Const` (levels non-empty), so
    // downstream id-keyed caches (whnf/infer/failure) hit instead of
    // re-reducing a fresh copy of the definition's value each time.
    let env = mini::env();
    let c = mini::cst("id1", vec![Arc::new(Level::Zero)]);
    let mut scratch = Store::scratch();
    let base = env.view().store;
    let cid = xid(&mut scratch, base, &c);
    let mut tc = TypeChecker::new(env.view(), &mut scratch);
    let u1 = tc.unfold_definition(cid).unwrap().unwrap();
    let u2 = tc.unfold_definition(cid).unwrap().unwrap();
    assert_eq!(
        u1, u2,
        "repeated unfold of one Const must be memoized (oracle m_unfold)"
    );
}
