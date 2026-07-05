//! Task 11 tests: `add_quot` admission (success / missing-`Eq` /
//! wrong-`Eq`-shape / the `quot_initialized` gating it fixes).
//! `constant_info_eq`'s own test lives in `decl.rs` (it isn't
//! quot-specific).
//!
//! NOTE: these tests build their own tiny environments rather than
//! reusing `crate::testenv::mini::env()` — that fixture already runs
//! `add_decl(Declaration::Quot)` (i.e. `add_quot`) itself, so a
//! pre-initialized env would mask exactly what these tests must
//! observe: the uninitialized-before / initialized-after transition
//! and the failure paths of `check_eq_type`.

use super::*;
use crate::{ConstructorVal, InductiveVal, Nat, TypeChecker};

/// A minimal `Eq`/`Eq.refl` pair that DOES satisfy `check_eq_type`:
/// `Eq.{u_1} : {α : Sort u_1} → α → α → Prop`, one constructor
/// `Eq.refl.{u_1} : {α : Sort u_1} → (a : α) → @Eq.{u_1} α a a`.
fn well_shaped_eq() -> Vec<ConstantInfo> {
    let mut g = RecGuard::new();
    let u1 = nm("u_1");
    let prop = Expr::sort(Arc::new(Level::Zero), &mut g).unwrap();

    let mut lctx = LocalContext::default();
    let mut gen = FVarIdGen::default();
    let sort_u1 = Expr::sort(Arc::new(Level::Param(Arc::clone(&u1))), &mut g).unwrap();
    let alpha = lctx.mk_local_decl(&mut gen, &nm("α"), sort_u1, BinderInfo::Implicit);
    let eq_ty = lctx
        .mk_pi(
            &[Arc::clone(&alpha)],
            &arrow(
                Arc::clone(&alpha),
                arrow(Arc::clone(&alpha), Arc::clone(&prop)),
            ),
            &mut g,
        )
        .unwrap();
    let eq_ind = ConstantInfo::Induct(InductiveVal {
        val: cval(nm("Eq"), vec![Arc::clone(&u1)], eq_ty),
        num_params: Nat::from(2u64),
        num_indices: Nat::from(1u64),
        all: vec![nm("Eq")],
        ctors: vec![nm2("Eq", "refl")],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    });

    let mut lctx2 = LocalContext::default();
    let mut gen2 = FVarIdGen::default();
    let sort_u1_2 = Expr::sort(Arc::new(Level::Param(Arc::clone(&u1))), &mut g).unwrap();
    let alpha2 = lctx2.mk_local_decl(&mut gen2, &nm("α"), sort_u1_2, BinderInfo::Implicit);
    let a2 = lctx2.mk_local_decl(
        &mut gen2,
        &nm("a"),
        Arc::clone(&alpha2),
        BinderInfo::Default,
    );
    let eq_const = Expr::const_(
        nm("Eq"),
        vec![Arc::new(Level::Param(Arc::clone(&u1)))],
        &mut g,
    )
    .unwrap();
    let eq_app = Expr::mk_app_spine(
        eq_const,
        &[Arc::clone(&alpha2), Arc::clone(&a2), Arc::clone(&a2)],
    );
    let refl_ty = lctx2
        .mk_pi(&[Arc::clone(&alpha2), Arc::clone(&a2)], &eq_app, &mut g)
        .unwrap();
    let refl = ConstantInfo::Ctor(ConstructorVal {
        val: cval(nm2("Eq", "refl"), vec![u1], refl_ty),
        induct: nm("Eq"),
        cidx: Nat::from(0u64),
        num_params: Nat::from(2u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
    });

    vec![eq_ind, refl]
}

#[test]
fn add_quot_without_eq_fails() {
    let mut env = Environment::default();
    let err = add_quot(&mut env).unwrap_err();
    assert_eq!(err, KernelError::InvalidQuot { what: "Eq" });
    assert!(!env.quot_initialized());
}

#[test]
fn add_quot_wrong_eq_shape_fails() {
    let mut consts = well_shaped_eq();
    match &mut consts[0] {
        ConstantInfo::Induct(v) => v.ctors.push(nm2("Eq", "other")),
        _ => unreachable!(),
    }
    let mut env = Environment::from_modules(vec![consts]).unwrap();
    let err = add_quot(&mut env).unwrap_err();
    assert!(matches!(err, KernelError::InvalidQuot { .. }));
    assert!(!env.quot_initialized());
}

#[test]
fn add_quot_after_eq_succeeds() {
    let mut env = Environment::from_modules(vec![well_shaped_eq()]).unwrap();
    add_quot(&mut env).unwrap();
    assert!(env.quot_initialized());
    // Idempotent: a second call is a documented no-op success
    // (quot.cpp:48-49).
    add_quot(&mut env).unwrap();

    let mut g = RecGuard::new();
    let u_name = nm("u");
    let u = Arc::new(Level::Param(Arc::clone(&u_name)));
    let sort_u = Expr::sort(Arc::clone(&u), &mut g).unwrap();
    let prop = Expr::sort(Arc::new(Level::Zero), &mut g).unwrap();

    // constant {u} Quot {α : Sort u} (r : α → α → Prop) : Sort u
    let mut lctx = LocalContext::default();
    let mut gen = FVarIdGen::default();
    let alpha = lctx.mk_local_decl(
        &mut gen,
        &nm("α"),
        Arc::clone(&sort_u),
        BinderInfo::Implicit,
    );
    let r = lctx.mk_local_decl(
        &mut gen,
        &nm("r"),
        arrow(
            Arc::clone(&alpha),
            arrow(Arc::clone(&alpha), Arc::clone(&prop)),
        ),
        BinderInfo::Default,
    );
    let expected_quot_type = lctx
        .mk_pi(&[Arc::clone(&alpha), Arc::clone(&r)], &sort_u, &mut g)
        .unwrap();

    let quot_u = Expr::const_(nm("Quot"), vec![Arc::clone(&u)], &mut g).unwrap();
    let quot_r = Expr::mk_app_spine(Arc::clone(&quot_u), &[Arc::clone(&alpha), Arc::clone(&r)]);
    let a = lctx.mk_local_decl(&mut gen, &nm("a"), Arc::clone(&alpha), BinderInfo::Default);
    // constant {u} Quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : @Quot.{u} α r
    let expected_mk_type = lctx
        .mk_pi(
            &[Arc::clone(&alpha), Arc::clone(&r), Arc::clone(&a)],
            &quot_r,
            &mut g,
        )
        .unwrap();

    // constant {u v} Quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β)
    //                          : (∀ a b : α, r a b → f a = f b) → @Quot.{u} α r → β
    let mut lctx2 = LocalContext::default();
    let mut gen2 = FVarIdGen::default();
    let alpha2 = lctx2.mk_local_decl(
        &mut gen2,
        &nm("α"),
        Arc::clone(&sort_u),
        BinderInfo::Implicit,
    );
    let r2 = lctx2.mk_local_decl(
        &mut gen2,
        &nm("r"),
        arrow(
            Arc::clone(&alpha2),
            arrow(Arc::clone(&alpha2), Arc::clone(&prop)),
        ),
        BinderInfo::Implicit,
    );
    let quot_r2 = Expr::mk_app_spine(Arc::clone(&quot_u), &[Arc::clone(&alpha2), Arc::clone(&r2)]);
    let v_name = nm("v");
    let v = Arc::new(Level::Param(Arc::clone(&v_name)));
    let sort_v = Expr::sort(Arc::clone(&v), &mut g).unwrap();
    let beta2 = lctx2.mk_local_decl(&mut gen2, &nm("β"), sort_v, BinderInfo::Implicit);
    let f2 = lctx2.mk_local_decl(
        &mut gen2,
        &nm("f"),
        arrow(Arc::clone(&alpha2), Arc::clone(&beta2)),
        BinderInfo::Default,
    );
    let a2 = lctx2.mk_local_decl(
        &mut gen2,
        &nm("a"),
        Arc::clone(&alpha2),
        BinderInfo::Default,
    );
    let b2 = lctx2.mk_local_decl(
        &mut gen2,
        &nm("b"),
        Arc::clone(&alpha2),
        BinderInfo::Default,
    );
    let r_a_b2 = Expr::mk_app_spine(Arc::clone(&r2), &[Arc::clone(&a2), Arc::clone(&b2)]);
    let eq_v2 = Expr::const_(nm("Eq"), vec![Arc::clone(&v)], &mut g).unwrap();
    let f_a2 = Expr::app(Arc::clone(&f2), Arc::clone(&a2));
    let f_b2 = Expr::app(Arc::clone(&f2), Arc::clone(&b2));
    let f_a_eq_f_b2 = Expr::mk_app_spine(eq_v2, &[Arc::clone(&beta2), f_a2, f_b2]);
    let sanity2 = lctx2
        .mk_pi(
            &[Arc::clone(&a2), Arc::clone(&b2)],
            &arrow(r_a_b2, f_a_eq_f_b2),
            &mut g,
        )
        .unwrap();
    let expected_lift_type = lctx2
        .mk_pi(
            &[
                Arc::clone(&alpha2),
                Arc::clone(&r2),
                Arc::clone(&beta2),
                Arc::clone(&f2),
            ],
            &arrow(sanity2, arrow(Arc::clone(&quot_r2), Arc::clone(&beta2))),
            &mut g,
        )
        .unwrap();

    // constant {u} Quot.ind {α : Sort u} {r : α → α → Prop} {β : @Quot.{u} α r → Prop}
    //               : (∀ a : α, β (@Quot.mk.{u} α r a)) → ∀ q : @Quot.{u} α r, β q
    let beta_ind2 = lctx2.mk_local_decl(
        &mut gen2,
        &nm("β"),
        arrow(Arc::clone(&quot_r2), Arc::clone(&prop)),
        BinderInfo::Implicit,
    );
    let quot_mk_u = Expr::const_(nm2("Quot", "mk"), vec![Arc::clone(&u)], &mut g).unwrap();
    let quot_mk_a2 = Expr::mk_app_spine(
        quot_mk_u,
        &[Arc::clone(&alpha2), Arc::clone(&r2), Arc::clone(&a2)],
    );
    let all_quot2 = lctx2
        .mk_pi(
            &[Arc::clone(&a2)],
            &Expr::app(Arc::clone(&beta_ind2), quot_mk_a2),
            &mut g,
        )
        .unwrap();
    let q2 = lctx2.mk_local_decl(
        &mut gen2,
        &nm("q"),
        Arc::clone(&quot_r2),
        BinderInfo::Default,
    );
    let q_pi2 = lctx2
        .mk_pi(
            &[Arc::clone(&q2)],
            &Expr::app(Arc::clone(&beta_ind2), Arc::clone(&q2)),
            &mut g,
        )
        .unwrap();
    let mk_node2 = Expr::forall_e(nm("mk"), all_quot2, q_pi2, BinderInfo::Default);
    let expected_ind_type = lctx2
        .mk_pi(
            &[Arc::clone(&alpha2), Arc::clone(&r2), Arc::clone(&beta_ind2)],
            &mk_node2,
            &mut g,
        )
        .unwrap();

    match env.get(&nm("Quot")).unwrap() {
        ConstantInfo::Quot(v) => {
            assert_eq!(v.kind, QuotKind::Type);
            assert_eq!(v.val.level_params, vec![Arc::clone(&u_name)]);
            assert!(Expr::structural_eq(&v.val.ty, &expected_quot_type, &mut g).unwrap());
        }
        other => panic!("expected Quot, got {other:?}"),
    }
    match env.get(&nm2("Quot", "mk")).unwrap() {
        ConstantInfo::Quot(v) => {
            assert_eq!(v.kind, QuotKind::Ctor);
            assert_eq!(v.val.level_params, vec![Arc::clone(&u_name)]);
            assert!(Expr::structural_eq(&v.val.ty, &expected_mk_type, &mut g).unwrap());
        }
        other => panic!("expected Quot, got {other:?}"),
    }
    match env.get(&nm2("Quot", "lift")).unwrap() {
        ConstantInfo::Quot(v) => {
            assert_eq!(v.kind, QuotKind::Lift);
            assert_eq!(v.val.level_params, vec![Arc::clone(&u_name), v_name]);
            assert!(Expr::structural_eq(&v.val.ty, &expected_lift_type, &mut g).unwrap());
        }
        other => panic!("expected Quot, got {other:?}"),
    }
    match env.get(&nm2("Quot", "ind")).unwrap() {
        ConstantInfo::Quot(v) => {
            assert_eq!(v.kind, QuotKind::Ind);
            assert_eq!(v.val.level_params, vec![u_name]);
            assert!(Expr::structural_eq(&v.val.ty, &expected_ind_type, &mut g).unwrap());
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
        ConstantInfo::Quot(QuotVal {
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

    // BEFORE add_quot: does not reduce (whnf leaves `e` unchanged).
    let mut g = RecGuard::new();
    {
        let mut tc = TypeChecker::new(&env);
        let before = tc.whnf(&e).unwrap();
        assert!(Expr::structural_eq(&before, &e, &mut g).unwrap());
    }

    // AFTER add_quot: the SAME expression now reduces to `f a`.
    add_quot(&mut env).unwrap();
    assert!(env.quot_initialized());
    let mut tc = TypeChecker::new(&env);
    let after = tc.whnf(&e).unwrap();
    assert!(Expr::structural_eq(&after, &Expr::app(f, a), &mut g).unwrap());
}
