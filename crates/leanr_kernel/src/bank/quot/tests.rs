//! Dual-checker differential harness for `bank::quot::add_quot`
//! (migration Task 5) — id-twin of `crate::quot::tests` (Task 11). Every
//! test below builds the SAME Arc-kernel fixtures the Arc test file
//! uses, then asserts the Arc and id-native `add_quot` produce identical
//! verdicts (see `assert_add_quot_matches`), following the dual-harness
//! pattern established by `bank::tc::tests`.

use super::*;
use crate::bank::decl::{constant_info_eq, intern_constant_info};
use crate::bank::tc::TypeChecker;
use crate::bank::NameId;
use crate::testenv::g;
use crate::{
    ConstantInfo, ConstantVal, ConstructorVal, Environment, FVarIdGen, InductiveVal, Level,
    LocalContext, Name, Nat, QuotVal,
};
use std::collections::HashMap;
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

fn cval(name: Arc<Name>, level_params: Vec<Arc<Name>>, ty: Arc<Expr>) -> ConstantVal {
    ConstantVal {
        name,
        level_params,
        ty,
    }
}

/// Arc-side `mk_arrow` (shadows `bank::quot`'s id-native `arrow`, glob-
/// imported via `super::*`) — matches `crate::quot`'s own private helper
/// of the same name, used only to build these Arc fixtures.
fn arrow(dom: Arc<Expr>, body: Arc<Expr>) -> Arc<Expr> {
    Expr::forall_e(nm("a"), dom, body, BinderInfo::Default)
}

/// A minimal `Eq`/`Eq.refl` pair that DOES satisfy `check_eq_type`
/// (verbatim fixture from `crate::quot::tests::well_shaped_eq`).
fn well_shaped_eq() -> Vec<ConstantInfo> {
    let mut rg = RecGuard::new();
    let u1 = nm("u_1");
    let prop = Expr::sort(Arc::new(Level::Zero), &mut rg).unwrap();

    let mut lctx = LocalContext::default();
    let mut gen = FVarIdGen::default();
    let sort_u1 = Expr::sort(Arc::new(Level::Param(Arc::clone(&u1))), &mut rg).unwrap();
    let alpha = lctx.mk_local_decl(&mut gen, &nm("α"), sort_u1, BinderInfo::Implicit);
    let eq_ty = lctx
        .mk_pi(
            &[Arc::clone(&alpha)],
            &arrow(
                Arc::clone(&alpha),
                arrow(Arc::clone(&alpha), Arc::clone(&prop)),
            ),
            &mut rg,
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
    let sort_u1_2 = Expr::sort(Arc::new(Level::Param(Arc::clone(&u1))), &mut rg).unwrap();
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
        &mut rg,
    )
    .unwrap();
    let eq_app = Expr::mk_app_spine(
        eq_const,
        &[Arc::clone(&alpha2), Arc::clone(&a2), Arc::clone(&a2)],
    );
    let refl_ty = lctx2
        .mk_pi(&[Arc::clone(&alpha2), Arc::clone(&a2)], &eq_app, &mut rg)
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

/// Same shape as `well_shaped_eq`, but every binder is spelled/annotated
/// differently from `check_eq_type`'s hard-coded expectation (verbatim
/// fixture from `crate::quot::tests::alpha_equivalent_eq`) — pins that
/// the id-native `check_eq_type` also uses `alpha_eq`, not structural
/// equality.
fn alpha_equivalent_eq() -> Vec<ConstantInfo> {
    let mut rg = RecGuard::new();
    let u1 = nm("u_1");
    let prop = Expr::sort(Arc::new(Level::Zero), &mut rg).unwrap();

    let mut lctx = LocalContext::default();
    let mut gen = FVarIdGen::default();
    let sort_u1 = Expr::sort(Arc::new(Level::Param(Arc::clone(&u1))), &mut rg).unwrap();
    let alpha = lctx.mk_local_decl(&mut gen, &nm("x"), sort_u1, BinderInfo::Implicit);
    let eq_ty = lctx
        .mk_pi(
            &[Arc::clone(&alpha)],
            &arrow(
                Arc::clone(&alpha),
                arrow(Arc::clone(&alpha), Arc::clone(&prop)),
            ),
            &mut rg,
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
    let sort_u1_2 = Expr::sort(Arc::new(Level::Param(Arc::clone(&u1))), &mut rg).unwrap();
    let alpha2 = lctx2.mk_local_decl(&mut gen2, &nm("x"), sort_u1_2, BinderInfo::Implicit);
    let a2 = lctx2.mk_local_decl(
        &mut gen2,
        &nm("z"),
        Arc::clone(&alpha2),
        BinderInfo::StrictImplicit,
    );
    let eq_const = Expr::const_(
        nm("Eq"),
        vec![Arc::new(Level::Param(Arc::clone(&u1)))],
        &mut rg,
    )
    .unwrap();
    let eq_app = Expr::mk_app_spine(
        eq_const,
        &[Arc::clone(&alpha2), Arc::clone(&a2), Arc::clone(&a2)],
    );
    let refl_ty = lctx2
        .mk_pi(&[Arc::clone(&alpha2), Arc::clone(&a2)], &eq_app, &mut rg)
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

fn bridge_consts(
    consts: &[ConstantInfo],
) -> (Store, HashMap<NameId, crate::bank::decl::ConstantInfo>) {
    let mut st = Store::persistent();
    let mut map = HashMap::new();
    for ci in consts {
        let idci = intern_constant_info(&mut st, None, ci).unwrap();
        map.insert(idci.name(), idci);
    }
    (st, map)
}

/// Everything a test needs after a dual `add_quot` run: the ARC env
/// (post-admission, for the ported test's own Arc-only assertions), plus
/// the raw id-side verdict (`id_result`) and the bridging stores
/// (`scratch`/`persistent`) so rejection/acceptance tests can assert
/// their own independent checks on top of the harness's already-pinned
/// arc==id agreement.
struct DualQuot {
    arc_env: Environment,
    id_result: Result<Vec<crate::bank::decl::ConstantInfo>, crate::KernelError>,
    scratch: Store,
    persistent: Store,
}

/// Run both kernels' `add_quot` against the same starting `consts`,
/// assert identical verdicts: both-Err ⇒ the exact same `KernelError`;
/// both-Ok ⇒ the four returned id `ConstantInfo`s bridge-match the Arc
/// env's post-admission constants (same intern-both-sides-into-one-store
/// technique `bank::decl`'s own `assert_eq_ci` uses). Returns the ARC env
/// (post-admission) plus the id-side verdict for tests that need further
/// independent assertions.
fn assert_add_quot_matches(consts: Vec<ConstantInfo>) -> DualQuot {
    let mut arc_env = Environment::from_modules(vec![consts.clone()]).unwrap();
    let arc_result = crate::quot::add_quot(&mut arc_env);

    let (persistent, map) = bridge_consts(&consts);
    let mut scratch = Store::scratch();
    let view = EnvView {
        consts: &map,
        extra: None,
        quot_initialized: false,
        store: &persistent,
    };
    let id_result = add_quot(&mut scratch, &view);

    match (&arc_result, &id_result) {
        (Ok(()), Ok(added)) => {
            assert_eq!(added.len(), 4, "add_quot admits exactly 4 constants");
            for ci in added {
                let arc_name = scratch.to_name(Some(&persistent), Some(ci.name()));
                let arc_ci = arc_env
                    .get(&arc_name)
                    .unwrap_or_else(|| panic!("missing {arc_name} in arc env"));
                let bridged =
                    intern_constant_info(&mut scratch, Some(&persistent), arc_ci).unwrap();
                assert!(constant_info_eq(ci, &bridged), "mismatch for {arc_name}");
            }
        }
        (Err(a), Err(b)) => assert_eq!(a, b),
        (a, b) => panic!("verdict split: arc={a:?} id={b:?}"),
    }
    DualQuot {
        arc_env,
        id_result,
        scratch,
        persistent,
    }
}

#[test]
fn add_quot_accepts_alpha_equivalent_eq_shape() {
    let res = assert_add_quot_matches(alpha_equivalent_eq());
    assert!(res.arc_env.quot_initialized());
}

#[test]
fn add_quot_without_eq_fails() {
    let res = assert_add_quot_matches(vec![]);
    assert!(!res.arc_env.quot_initialized());
    match res.id_result {
        Err(crate::KernelError::InvalidQuot { what }) => assert_eq!(what, "Eq"),
        other => panic!("expected InvalidQuot{{what: \"Eq\"}}, got {other:?}"),
    }
}

#[test]
fn add_quot_wrong_eq_shape_fails() {
    let mut consts = well_shaped_eq();
    match &mut consts[0] {
        ConstantInfo::Induct(v) => v.ctors.push(nm2("Eq", "other")),
        _ => unreachable!(),
    }
    let res = assert_add_quot_matches(consts);
    assert!(!res.arc_env.quot_initialized());
    assert!(matches!(
        res.id_result,
        Err(crate::KernelError::InvalidQuot { .. })
    ));
}

#[test]
fn add_quot_after_eq_succeeds() {
    let res = assert_add_quot_matches(well_shaped_eq());
    assert!(res.arc_env.quot_initialized());
    let DualQuot {
        scratch,
        persistent,
        id_result,
        ..
    } = res;
    let added = id_result.expect("add_quot succeeds on well-shaped Eq");

    // Idempotent: a second (id-native) call on an already-initialized
    // view is a documented no-op success (quot.cpp:48-49) — nothing left
    // to admit.
    let (persistent2, map2) = bridge_consts(&well_shaped_eq());
    let mut scratch2 = Store::scratch();
    let view = EnvView {
        consts: &map2,
        extra: None,
        quot_initialized: true,
        store: &persistent2,
    };
    let added_again = add_quot(&mut scratch2, &view).unwrap();
    assert!(
        added_again.is_empty(),
        "already-initialized add_quot is a no-op"
    );

    // Independent structural checks on the four returned constants
    // (ported from `crate::quot::tests::add_quot_after_eq_succeeds`):
    // kind, level-params, and the expected hard-coded type for each of
    // `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind`, bridged out to `Arc<Expr>`
    // and compared structurally against the same expected shapes the
    // Arc test builds.
    let mut rg = RecGuard::new();
    let u_name = nm("u");
    let u = Arc::new(Level::Param(Arc::clone(&u_name)));
    let sort_u = Expr::sort(Arc::clone(&u), &mut rg).unwrap();
    let prop = Expr::sort(Arc::new(Level::Zero), &mut rg).unwrap();

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
        .mk_pi(&[Arc::clone(&alpha), Arc::clone(&r)], &sort_u, &mut rg)
        .unwrap();

    let quot_u = Expr::const_(nm("Quot"), vec![Arc::clone(&u)], &mut rg).unwrap();
    let quot_r = Expr::mk_app_spine(Arc::clone(&quot_u), &[Arc::clone(&alpha), Arc::clone(&r)]);
    let a = lctx.mk_local_decl(&mut gen, &nm("a"), Arc::clone(&alpha), BinderInfo::Default);
    // constant {u} Quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : @Quot.{u} α r
    let expected_mk_type = lctx
        .mk_pi(
            &[Arc::clone(&alpha), Arc::clone(&r), Arc::clone(&a)],
            &quot_r,
            &mut rg,
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
    let sort_v = Expr::sort(Arc::clone(&v), &mut rg).unwrap();
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
    let eq_v2 = Expr::const_(nm("Eq"), vec![Arc::clone(&v)], &mut rg).unwrap();
    let f_a2 = Expr::app(Arc::clone(&f2), Arc::clone(&a2));
    let f_b2 = Expr::app(Arc::clone(&f2), Arc::clone(&b2));
    let f_a_eq_f_b2 = Expr::mk_app_spine(eq_v2, &[Arc::clone(&beta2), f_a2, f_b2]);
    let sanity2 = lctx2
        .mk_pi(
            &[Arc::clone(&a2), Arc::clone(&b2)],
            &arrow(r_a_b2, f_a_eq_f_b2),
            &mut rg,
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
            &mut rg,
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
    let quot_mk_u = Expr::const_(nm2("Quot", "mk"), vec![Arc::clone(&u)], &mut rg).unwrap();
    let quot_mk_a2 = Expr::mk_app_spine(
        quot_mk_u,
        &[Arc::clone(&alpha2), Arc::clone(&r2), Arc::clone(&a2)],
    );
    let all_quot2 = lctx2
        .mk_pi(
            &[Arc::clone(&a2)],
            &Expr::app(Arc::clone(&beta_ind2), quot_mk_a2),
            &mut rg,
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
            &mut rg,
        )
        .unwrap();
    let mk_node2 = Expr::forall_e(nm("mk"), all_quot2, q_pi2, BinderInfo::Default);
    let expected_ind_type = lctx2
        .mk_pi(
            &[Arc::clone(&alpha2), Arc::clone(&r2), Arc::clone(&beta_ind2)],
            &mk_node2,
            &mut rg,
        )
        .unwrap();

    for ci in &added {
        let name = scratch.to_name(Some(&persistent), Some(ci.name()));
        let (kind, level_params, ty) = match ci {
            crate::bank::decl::ConstantInfo::Quot(v) => (
                v.kind,
                v.val
                    .level_params
                    .iter()
                    .map(|lp| scratch.to_name(Some(&persistent), Some(*lp)))
                    .collect::<Vec<_>>(),
                scratch
                    .to_expr(Some(&persistent), v.val.ty, &mut g())
                    .unwrap(),
            ),
            other => panic!("expected Quot, got {other:?}"),
        };
        if name.as_ref() == nm("Quot").as_ref() {
            assert_eq!(kind, QuotKind::Type);
            assert_eq!(level_params, vec![Arc::clone(&u_name)]);
            assert!(Expr::structural_eq(&ty, &expected_quot_type, &mut rg).unwrap());
        } else if name.as_ref() == nm2("Quot", "mk").as_ref() {
            assert_eq!(kind, QuotKind::Ctor);
            assert_eq!(level_params, vec![Arc::clone(&u_name)]);
            assert!(Expr::structural_eq(&ty, &expected_mk_type, &mut rg).unwrap());
        } else if name.as_ref() == nm2("Quot", "lift").as_ref() {
            assert_eq!(kind, QuotKind::Lift);
            assert_eq!(level_params, vec![Arc::clone(&u_name), Arc::clone(&v_name)]);
            assert!(Expr::structural_eq(&ty, &expected_lift_type, &mut rg).unwrap());
        } else if name.as_ref() == nm2("Quot", "ind").as_ref() {
            assert_eq!(kind, QuotKind::Ind);
            assert_eq!(level_params, vec![Arc::clone(&u_name)]);
            assert!(Expr::structural_eq(&ty, &expected_ind_type, &mut rg).unwrap());
        } else {
            panic!("unexpected admitted constant {name}");
        }
    }
}

#[test]
fn quot_iota_gated_on_initialized() {
    // Build an env with a well-shaped `Eq` AND the four `Quot` constants
    // already present under their real names (placeholder types —
    // reduction never inspects them, only the head name and
    // `quot_initialized`), but WITHOUT having run `add_quot` (flag false
    // on both sides at first).
    let mut consts = well_shaped_eq();
    let placeholder_ty = Expr::sort(Arc::new(Level::Zero), &mut RecGuard::new()).unwrap();
    let mk_quot_const = |name: Arc<Name>, kind: crate::QuotKind, lparams: Vec<Arc<Name>>| {
        ConstantInfo::Quot(QuotVal {
            val: cval(name, lparams, Arc::clone(&placeholder_ty)),
            kind,
        })
    };
    consts.push(mk_quot_const(
        nm("Quot"),
        crate::QuotKind::Type,
        vec![nm("u")],
    ));
    consts.push(mk_quot_const(
        nm2("Quot", "mk"),
        crate::QuotKind::Ctor,
        vec![nm("u")],
    ));
    consts.push(mk_quot_const(
        nm2("Quot", "lift"),
        crate::QuotKind::Lift,
        vec![nm("u"), nm("v")],
    ));
    consts.push(mk_quot_const(
        nm2("Quot", "ind"),
        crate::QuotKind::Ind,
        vec![nm("u")],
    ));

    let mut arc_env = Environment::from_modules(vec![consts.clone()]).unwrap();
    assert!(!arc_env.quot_initialized());

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

    let (persistent, map0) = bridge_consts(&consts);
    let mut scratch = Store::scratch();
    let eid = scratch.intern_expr(Some(&persistent), &e).unwrap();

    // BEFORE add_quot: does not reduce, on either kernel.
    {
        let view = EnvView {
            consts: &map0,
            extra: None,
            quot_initialized: false,
            store: &persistent,
        };
        let mut tc = TypeChecker::new(view, &mut scratch);
        let before_id = tc.whnf(eid).unwrap();
        assert_eq!(before_id, eid);
    }
    let mut arc_tc = crate::TypeChecker::new(&arc_env);
    let before_arc = arc_tc.whnf(&e).unwrap();
    assert!(Expr::structural_eq(&before_arc, &e, &mut g()).unwrap());

    // AFTER add_quot: the SAME expression now reduces to `f a`, on both
    // kernels.
    crate::quot::add_quot(&mut arc_env).unwrap();
    assert!(arc_env.quot_initialized());

    let view0 = EnvView {
        consts: &map0,
        extra: None,
        quot_initialized: false,
        store: &persistent,
    };
    let added = add_quot(&mut scratch, &view0).unwrap();
    let mut map1 = map0.clone();
    for ci in added {
        map1.insert(ci.name(), ci);
    }
    let expected = Expr::app(f, a);
    {
        let view = EnvView {
            consts: &map1,
            extra: None,
            quot_initialized: true,
            store: &persistent,
        };
        let mut tc = TypeChecker::new(view, &mut scratch);
        let after_id = tc.whnf(eid).unwrap();
        let after_id_arc = scratch
            .to_expr(Some(&persistent), after_id, &mut g())
            .unwrap();
        assert!(Expr::structural_eq(&after_id_arc, &expected, &mut g()).unwrap());
    }
    let mut arc_tc2 = crate::TypeChecker::new(&arc_env);
    let after_arc = arc_tc2.whnf(&e).unwrap();
    assert!(Expr::structural_eq(&after_arc, &expected, &mut g()).unwrap());
}
