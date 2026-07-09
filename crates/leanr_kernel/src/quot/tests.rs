//! Unit tests for the id-native `quot::add_quot` (migration Task 8:
//! ported from the pre-flip `crate::quot::tests`, which dual-compared
//! against the Arc `quot`/`add_quot` this migration deletes — see
//! `git show 9b1c773:crates/leanr_kernel/src/quot/tests.rs`). Every test
//! below asserts the SAME expected values that file pinned, now
//! directly against the id-native admission path
//! (`Environment::from_modules` + `Environment::add_decl(Declaration::Quot)`,
//! which is the real production entry point `add_quot` is dispatched
//! from): the interning invariant makes id equality the exact id-space
//! analogue of the Arc test's `Expr::structural_eq`/`Expr::alpha_eq`
//! checks.
//!
//! NOTE: these tests build their own tiny environments rather than
//! reusing `crate::testenv::mini::env()` — that fixture already runs
//! `add_decl(Declaration::Quot)` itself, so a pre-initialized env would
//! mask exactly what these tests must observe: the
//! uninitialized-before/initialized-after transition and the failure
//! paths of `check_eq_type`.

use super::*;
use crate::bank::LevelId;
use crate::{
    ArcConstantInfo, ArcConstantVal, ArcConstructorVal, ArcInductiveVal, ArcQuotVal, Declaration,
    Environment, Level, Name, Nat, QuotKind, TypeChecker,
};
use std::sync::Arc;

fn nm(s: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: s.to_string(),
    })
}

fn nm2(a: &str, b: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: nm(a),
        part: b.to_string(),
    })
}

fn cval(name: Arc<Name>, level_params: Vec<Arc<Name>>, ty: Arc<Expr>) -> ArcConstantVal {
    ArcConstantVal {
        name,
        level_params,
        ty,
    }
}

fn bvar(i: u64) -> Arc<Expr> {
    Expr::bvar(Nat::from(i))
}

/// Arc-side `mk_arrow` (shadows `quot`'s private id-native `arrow`,
/// glob-imported via `super::*`) — matches `crate::quot`'s own private
/// helper of the same name, used only to build these Arc fixtures.
fn arrow(dom: Arc<Expr>, body: Arc<Expr>) -> Arc<Expr> {
    Expr::forall_e(nm("a"), dom, body, BinderInfo::Default)
}

/// `Π {<alpha_name> : Sort u_1}, <alpha_name> → <alpha_name> → Prop`,
/// built directly via de Bruijn indices (no `LocalContext` needed for a
/// shape this shallow — matches `testenv::mini::eq_ty`'s established
/// technique for the SAME fixture shape).
fn eq_ty(u1: &Arc<Name>, alpha_name: &str) -> Arc<Expr> {
    let mut g = RecGuard::new();
    let sort_u1 = Expr::sort(Arc::new(Level::Param(Arc::clone(u1))), &mut g).unwrap();
    let prop = Expr::sort(Arc::new(Level::Zero), &mut g).unwrap();
    Expr::forall_e(
        nm(alpha_name),
        sort_u1,
        arrow(bvar(0), arrow(bvar(1), prop)),
        BinderInfo::Implicit,
    )
}

/// `Π {<alpha_name> : Sort u_1} (<a_name> : <alpha_name>), @Eq.{u_1}
/// <alpha_name> <a_name> <a_name>` — same technique as `eq_ty`.
fn eq_refl_ty(u1: &Arc<Name>, alpha_name: &str, a_name: &str, a_info: BinderInfo) -> Arc<Expr> {
    let mut g = RecGuard::new();
    let sort_u1 = Expr::sort(Arc::new(Level::Param(Arc::clone(u1))), &mut g).unwrap();
    let eq_const = Expr::const_(
        nm("Eq"),
        vec![Arc::new(Level::Param(Arc::clone(u1)))],
        &mut g,
    )
    .unwrap();
    Expr::forall_e(
        nm(alpha_name),
        sort_u1,
        Expr::forall_e(
            nm(a_name),
            bvar(0),
            Expr::mk_app_spine(eq_const, &[bvar(1), bvar(0), bvar(0)]),
            a_info,
        ),
        BinderInfo::Implicit,
    )
}

/// A minimal `Eq`/`Eq.refl` pair that DOES satisfy `check_eq_type`:
/// `Eq.{u_1} : {α : Sort u_1} → α → α → Prop`, one constructor
/// `Eq.refl.{u_1} : {α : Sort u_1} → (a : α) → @Eq.{u_1} α a a`.
fn well_shaped_eq() -> Vec<ArcConstantInfo> {
    let u1 = nm("u_1");
    let eq_ind = ArcConstantInfo::Induct(ArcInductiveVal {
        val: cval(nm("Eq"), vec![Arc::clone(&u1)], eq_ty(&u1, "α")),
        num_params: Nat::from(2u64),
        num_indices: Nat::from(1u64),
        all: vec![nm("Eq")],
        ctors: vec![nm2("Eq", "refl")],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    });
    let refl = ArcConstantInfo::Ctor(ArcConstructorVal {
        val: cval(
            nm2("Eq", "refl"),
            vec![Arc::clone(&u1)],
            eq_refl_ty(&u1, "α", "a", BinderInfo::Default),
        ),
        induct: nm("Eq"),
        cidx: Nat::from(0u64),
        num_params: Nat::from(2u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
    });
    vec![eq_ind, refl]
}

/// Same shape as `well_shaped_eq`, but every binder is spelled and
/// annotated differently from `check_eq_type`'s hard-coded expectation
/// (`"α"`/`"a"`, both `BinderInfo::Implicit`/`Default`): `Eq`'s Sort
/// binder is named `"x"` (a real Lean-produced `Eq` need not match our
/// literal choice of name), and `Eq.refl`'s value binder is named `"z"`
/// AND given `BinderInfo::StrictImplicit` instead of `Default` (a
/// binder-info difference, independent of the name difference). This
/// mirrors a real-Lean-produced `Eq`/`Eq.refl` whose source names differ
/// from ours — exactly the closure-replay failure the Arc-era fix this
/// pins resolves (see `check_eq_type`'s doc comment in `quot.rs`).
/// Regressed against plain structural equality, `add_quot` would reject
/// this env; with `alpha_eq` it must be accepted.
fn alpha_equivalent_eq() -> Vec<ArcConstantInfo> {
    let u1 = nm("u_1");
    let eq_ind = ArcConstantInfo::Induct(ArcInductiveVal {
        val: cval(nm("Eq"), vec![Arc::clone(&u1)], eq_ty(&u1, "x")),
        num_params: Nat::from(2u64),
        num_indices: Nat::from(1u64),
        all: vec![nm("Eq")],
        ctors: vec![nm2("Eq", "refl")],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    });
    let refl = ArcConstantInfo::Ctor(ArcConstructorVal {
        val: cval(
            nm2("Eq", "refl"),
            vec![Arc::clone(&u1)],
            eq_refl_ty(&u1, "x", "z", BinderInfo::StrictImplicit),
        ),
        induct: nm("Eq"),
        cidx: Nat::from(0u64),
        num_params: Nat::from(2u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
    });
    vec![eq_ind, refl]
}

fn xid(scratch: &mut Store, base: &Store, e: &Arc<Expr>) -> ExprId {
    scratch.intern_expr(Some(base), e).unwrap()
}

fn xname(scratch: &mut Store, base: &Store, n: &Arc<Name>) -> NameId {
    scratch.intern_name(Some(base), n).unwrap().unwrap()
}

/// Look up an already-admitted constant by its Arc-side name.
fn get<'e>(env: &'e Environment, scratch: &mut Store, n: &Arc<Name>) -> &'e ConstantInfo {
    let base = env.view().store;
    let nid = xname(scratch, base, n);
    env.get(nid)
        .unwrap_or_else(|| panic!("missing constant {n}"))
}

/// `lctx.mk_local_decl` plus name interning, id-native.
fn declare(
    scratch: &mut Store,
    base: &Store,
    lctx: &mut LocalContext,
    gen: &mut FVarIdGen,
    name: &str,
    ty: ExprId,
    info: BinderInfo,
) -> ExprId {
    let n = xname(scratch, base, &nm(name));
    lctx.mk_local_decl(scratch, Some(base), gen, Some(n), ty, info)
        .unwrap()
}

fn pi_id(
    scratch: &mut Store,
    base: &Store,
    lctx: &LocalContext,
    fvars: &[ExprId],
    body: ExprId,
) -> ExprId {
    crate::subst::mk_pi(scratch, Some(base), lctx, fvars, body, &mut RecGuard::new()).unwrap()
}

fn arrow_id(scratch: &mut Store, base: &Store, dom: ExprId, body: ExprId) -> ExprId {
    super::arrow(scratch, Some(base), dom, body).unwrap()
}

fn app_id(scratch: &mut Store, base: &Store, f: ExprId, arg: ExprId) -> ExprId {
    scratch.expr_app(Some(base), f, arg).unwrap()
}

fn appn_id(scratch: &mut Store, base: &Store, f: ExprId, args: &[ExprId]) -> ExprId {
    args.iter().fold(f, |acc, &a| app_id(scratch, base, acc, a))
}

fn const_id(scratch: &mut Store, base: &Store, name: NameId, levels: &[LevelId]) -> ExprId {
    let ls = scratch.intern_level_list(Some(base), levels).unwrap();
    scratch.expr_const(Some(base), Some(name), ls).unwrap()
}

/// Independently transcribe the hard-coded types `add_quot` produces
/// (oracle: quot.cpp:53-96, ported from `crate::quot::tests`'
/// `add_quot_after_eq_succeeds`), returning `(quot_ty, mk_ty, lift_ty,
/// ind_ty, u_name, v_name)` as ids already resolved against `base` (so
/// they compare equal — not just structurally, ID-equal — to the
/// persistent ids `add_quot`'s own output promotes into `base`, PROVIDED
/// this transcription matches: base-lookup dedup means identical content
/// interns to the identical existing id).
#[allow(clippy::type_complexity)]
fn expected_quot_types(
    scratch: &mut Store,
    base: &Store,
) -> (ExprId, ExprId, ExprId, ExprId, NameId, NameId) {
    let u_name = xname(scratch, base, &nm("u"));
    let u = scratch.level_param(Some(base), Some(u_name)).unwrap();
    let sort_u = scratch.expr_sort(Some(base), u).unwrap();
    let zero = scratch.level_zero(Some(base)).unwrap();
    let prop = scratch.expr_sort(Some(base), zero).unwrap();
    let mut gen = FVarIdGen::default();

    // constant {u} Quot {α : Sort u} (r : α → α → Prop) : Sort u
    let mut lctx = LocalContext::default();
    let alpha = declare(
        scratch,
        base,
        &mut lctx,
        &mut gen,
        "α",
        sort_u,
        BinderInfo::Implicit,
    );
    let r_dom = {
        let a2 = arrow_id(scratch, base, alpha, prop);
        arrow_id(scratch, base, alpha, a2)
    };
    let r = declare(
        scratch,
        base,
        &mut lctx,
        &mut gen,
        "r",
        r_dom,
        BinderInfo::Default,
    );
    let quot_ty = pi_id(scratch, base, &lctx, &[alpha, r], sort_u);

    let quot_name = xname(scratch, base, &nm("Quot"));
    let quot_const_u = const_id(scratch, base, quot_name, &[u]);
    let quot_r = appn_id(scratch, base, quot_const_u, &[alpha, r]);
    let a = declare(
        scratch,
        base,
        &mut lctx,
        &mut gen,
        "a",
        alpha,
        BinderInfo::Default,
    );
    // constant {u} Quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : @Quot.{u} α r
    let mk_ty = pi_id(scratch, base, &lctx, &[alpha, r, a], quot_r);

    // ---- Quot.lift, Quot.ind: fresh local context; r/α re-declared ----
    let mut lctx = LocalContext::default();
    let alpha = declare(
        scratch,
        base,
        &mut lctx,
        &mut gen,
        "α",
        sort_u,
        BinderInfo::Implicit,
    );
    let r_dom = {
        let a2 = arrow_id(scratch, base, alpha, prop);
        arrow_id(scratch, base, alpha, a2)
    };
    let r = declare(
        scratch,
        base,
        &mut lctx,
        &mut gen,
        "r",
        r_dom,
        BinderInfo::Implicit,
    );
    let quot_r = appn_id(scratch, base, quot_const_u, &[alpha, r]);
    let a = declare(
        scratch,
        base,
        &mut lctx,
        &mut gen,
        "a",
        alpha,
        BinderInfo::Default,
    );

    let v_name = xname(scratch, base, &nm("v"));
    let v = scratch.level_param(Some(base), Some(v_name)).unwrap();
    let sort_v = scratch.expr_sort(Some(base), v).unwrap();
    let beta = declare(
        scratch,
        base,
        &mut lctx,
        &mut gen,
        "β",
        sort_v,
        BinderInfo::Implicit,
    );
    let f_dom = arrow_id(scratch, base, alpha, beta);
    let f = declare(
        scratch,
        base,
        &mut lctx,
        &mut gen,
        "f",
        f_dom,
        BinderInfo::Default,
    );
    let b = declare(
        scratch,
        base,
        &mut lctx,
        &mut gen,
        "b",
        alpha,
        BinderInfo::Default,
    );

    let r_a_b = appn_id(scratch, base, r, &[a, b]);
    let eq_name = xname(scratch, base, &nm("Eq"));
    let eq_v = const_id(scratch, base, eq_name, &[v]);
    let f_a = app_id(scratch, base, f, a);
    let f_b = app_id(scratch, base, f, b);
    let f_a_eq_f_b = appn_id(scratch, base, eq_v, &[beta, f_a, f_b]);
    // (∀ a b : α, r a b → f a = f b)
    let sanity = {
        let body = arrow_id(scratch, base, r_a_b, f_a_eq_f_b);
        pi_id(scratch, base, &lctx, &[a, b], body)
    };
    // constant {u v} Quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β)
    //                          : (∀ a b : α, r a b → f a = f b) → @Quot.{u} α r → β
    let lift_body = {
        let t1 = arrow_id(scratch, base, quot_r, beta);
        arrow_id(scratch, base, sanity, t1)
    };
    let lift_ty = pi_id(scratch, base, &lctx, &[alpha, r, beta, f], lift_body);

    // { β : @Quot.{u} α r → Prop } — Quot.ind's own β (re-declared).
    let beta_ind_dom = arrow_id(scratch, base, quot_r, prop);
    let beta = declare(
        scratch,
        base,
        &mut lctx,
        &mut gen,
        "β",
        beta_ind_dom,
        BinderInfo::Implicit,
    );
    let quot_mk_name = xname(scratch, base, &nm2("Quot", "mk"));
    let quot_mk_const_u = const_id(scratch, base, quot_mk_name, &[u]);
    let quot_mk_a = appn_id(scratch, base, quot_mk_const_u, &[alpha, r, a]);
    // (∀ a : α, β (@Quot.mk.{u} α r a))
    let all_quot = {
        let body = app_id(scratch, base, beta, quot_mk_a);
        pi_id(scratch, base, &lctx, &[a], body)
    };
    let q = declare(
        scratch,
        base,
        &mut lctx,
        &mut gen,
        "q",
        quot_r,
        BinderInfo::Default,
    );
    let q_pi = {
        let body = app_id(scratch, base, beta, q);
        pi_id(scratch, base, &lctx, &[q], body)
    };
    let mk_name = xname(scratch, base, &nm("mk"));
    let ind_body = scratch
        .expr_forall(
            Some(base),
            Some(mk_name),
            all_quot,
            q_pi,
            BinderInfo::Default,
        )
        .unwrap();
    let ind_ty = pi_id(scratch, base, &lctx, &[alpha, r, beta], ind_body);

    (quot_ty, mk_ty, lift_ty, ind_ty, u_name, v_name)
}

#[test]
fn add_quot_accepts_alpha_equivalent_eq_shape() {
    // RED without the fix: plain structural equality's `na != nb || ia
    // != ib` guard (expr.rs, Lam/ForallE arm) would reject this env
    // since both an `Eq` binder name AND an `Eq.refl` binder's
    // `BinderInfo` differ from `check_eq_type`'s hard-coded expectation.
    // GREEN with the fix: `check_eq_type` uses alpha-equivalence
    // (`quot::alpha_eq`), which is insensitive to both, so `add_quot`
    // succeeds.
    let mut env = Environment::from_modules(vec![alpha_equivalent_eq()]).unwrap();
    env.add_decl(Declaration::Quot).unwrap();
    assert!(env.quot_initialized());
}

#[test]
fn add_quot_without_eq_fails() {
    let mut env = Environment::default();
    let err = env.add_decl(Declaration::Quot).unwrap_err();
    assert_eq!(err, KernelError::InvalidQuot { what: "Eq" });
    assert!(!env.quot_initialized());
}

#[test]
fn add_quot_wrong_eq_shape_fails() {
    let mut consts = well_shaped_eq();
    match &mut consts[0] {
        ArcConstantInfo::Induct(v) => v.ctors.push(nm2("Eq", "other")),
        _ => unreachable!(),
    }
    let mut env = Environment::from_modules(vec![consts]).unwrap();
    let err = env.add_decl(Declaration::Quot).unwrap_err();
    assert!(matches!(err, KernelError::InvalidQuot { .. }));
    assert!(!env.quot_initialized());
}

#[test]
fn add_quot_after_eq_succeeds() {
    let mut env = Environment::from_modules(vec![well_shaped_eq()]).unwrap();
    env.add_decl(Declaration::Quot).unwrap();
    assert!(env.quot_initialized());
    // Idempotent: a second call is a documented no-op success
    // (quot.cpp:48-49).
    env.add_decl(Declaration::Quot).unwrap();

    let mut scratch = Store::scratch();
    let base = env.view().store;
    let (expected_quot_ty, expected_mk_ty, expected_lift_ty, expected_ind_ty, u_name, v_name) =
        expected_quot_types(&mut scratch, base);

    match get(&env, &mut scratch, &nm("Quot")) {
        ConstantInfo::Quot(v) => {
            assert_eq!(v.kind, QuotKind::Type);
            assert_eq!(v.val.level_params, vec![u_name]);
            assert_eq!(v.val.ty, expected_quot_ty);
        }
        other => panic!("expected Quot, got {other:?}"),
    }
    match get(&env, &mut scratch, &nm2("Quot", "mk")) {
        ConstantInfo::Quot(v) => {
            assert_eq!(v.kind, QuotKind::Ctor);
            assert_eq!(v.val.level_params, vec![u_name]);
            assert_eq!(v.val.ty, expected_mk_ty);
        }
        other => panic!("expected Quot, got {other:?}"),
    }
    match get(&env, &mut scratch, &nm2("Quot", "lift")) {
        ConstantInfo::Quot(v) => {
            assert_eq!(v.kind, QuotKind::Lift);
            assert_eq!(v.val.level_params, vec![u_name, v_name]);
            assert_eq!(v.val.ty, expected_lift_ty);
        }
        other => panic!("expected Quot, got {other:?}"),
    }
    match get(&env, &mut scratch, &nm2("Quot", "ind")) {
        ConstantInfo::Quot(v) => {
            assert_eq!(v.kind, QuotKind::Ind);
            assert_eq!(v.val.level_params, vec![u_name]);
            assert_eq!(v.val.ty, expected_ind_ty);
        }
        other => panic!("expected Quot, got {other:?}"),
    }
}

#[test]
fn quot_iota_gated_on_initialized() {
    // Build an env with a well-shaped `Eq` AND the four `Quot`
    // constants already present under their real names (placeholder
    // types — reduction never inspects them, only the head name and
    // `quot_initialized`), but WITHOUT calling `add_quot`: the flag
    // defaults to false. This is exactly the shape the old Task-7
    // name-presence proxy would have accepted as "initialized"; proving
    // the reduction does NOT fire here is what proves that proxy is
    // gone (reintroducing it would make this assertion fail, since the
    // proxy only checked presence, which holds below).
    let mut consts = well_shaped_eq();
    let placeholder_ty = Expr::sort(Arc::new(Level::Zero), &mut RecGuard::new()).unwrap();
    let mk_quot_const = |name: Arc<Name>, kind: QuotKind, lparams: Vec<Arc<Name>>| {
        ArcConstantInfo::Quot(ArcQuotVal {
            val: cval(name, lparams, Arc::clone(&placeholder_ty)),
            kind,
        })
    };
    consts.push(mk_quot_const(nm("Quot"), QuotKind::Type, vec![nm("u")]));
    consts.push(mk_quot_const(
        nm2("Quot", "mk"),
        QuotKind::Ctor,
        vec![nm("u")],
    ));
    consts.push(mk_quot_const(
        nm2("Quot", "lift"),
        QuotKind::Lift,
        vec![nm("u"), nm("v")],
    ));
    consts.push(mk_quot_const(
        nm2("Quot", "ind"),
        QuotKind::Ind,
        vec![nm("u")],
    ));
    let mut env = Environment::from_modules(vec![consts]).unwrap();
    assert!(!env.quot_initialized());

    // Quot.lift.{0,0} α r β f h (Quot.mk.{0} α r a)
    let zero = Arc::new(Level::Zero);
    let alpha = Expr::const_(nm("α"), vec![], &mut RecGuard::new()).unwrap();
    let rel = Expr::const_(nm("r"), vec![], &mut RecGuard::new()).unwrap();
    let beta = Expr::const_(nm("β"), vec![], &mut RecGuard::new()).unwrap();
    let f = Expr::const_(nm("f"), vec![], &mut RecGuard::new()).unwrap();
    let h = Expr::const_(nm("h"), vec![], &mut RecGuard::new()).unwrap();
    let a = Expr::const_(nm("a"), vec![], &mut RecGuard::new()).unwrap();
    let mk = Expr::mk_app_spine(
        Expr::const_(
            nm2("Quot", "mk"),
            vec![Arc::clone(&zero)],
            &mut RecGuard::new(),
        )
        .unwrap(),
        &[Arc::clone(&alpha), Arc::clone(&rel), Arc::clone(&a)],
    );
    let e = Expr::mk_app_spine(
        Expr::const_(
            nm2("Quot", "lift"),
            vec![Arc::clone(&zero), Arc::clone(&zero)],
            &mut RecGuard::new(),
        )
        .unwrap(),
        &[alpha, rel, beta, Arc::clone(&f), h, mk],
    );

    let mut scratch = Store::scratch();

    // BEFORE add_quot: does not reduce (whnf leaves `e` unchanged).
    let eid_before = xid(&mut scratch, env.view().store, &e);
    let before = TypeChecker::new(env.view(), &mut scratch)
        .whnf(eid_before)
        .unwrap();
    assert_eq!(before, eid_before);

    // AFTER add_quot: the SAME expression now reduces to `f a`.
    env.add_decl(Declaration::Quot).unwrap();
    assert!(env.quot_initialized());
    let eid_after = xid(&mut scratch, env.view().store, &e);
    let after = TypeChecker::new(env.view(), &mut scratch)
        .whnf(eid_after)
        .unwrap();
    let expected = xid(&mut scratch, env.view().store, &Expr::app(f, a));
    assert_eq!(after, expected);
}
