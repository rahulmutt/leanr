//! M4c-1 P1 gate: abstract + commit aux and main declarations over Meta0
//! (plan `docs/superpowers/plans/2026-10-03-m4c1-p1-decl-substrate.md`
//! Task 8). Mirrors the oracle probe `foo2` (plan § Oracle probe facts).

mod support;

use leanr_kernel::bank::{ExprId, LevelId, NameId, Store};
use leanr_kernel::Environment;
use leanr_kernel::{
    BinderInfo, ConstantInfo, ConstantVal, Declaration, DefinitionSafety, DefinitionVal,
    ReducibilityHints,
};
use leanr_meta::{
    sort_decl_level_params, AuxLemmas, CollectLevelParams, Config, EnvExtensions, MetaCtx,
};

struct Built {
    decls: Vec<Declaration>,
}

fn nm(ctx: &mut MetaCtx, base: Option<&Store>, s: &str) -> NameId {
    let st = ctx.store_mut();
    let mut n = None;
    for part in s.split('.') {
        let id = st.intern_str(base, part).unwrap();
        n = Some(st.name_str(base, n, id).unwrap());
    }
    n.unwrap()
}

fn cu(ctx: &mut MetaCtx, base: Option<&Store>, s: &str, levels: &[LevelId]) -> ExprId {
    let n = nm(ctx, base, s);
    let st = ctx.store_mut();
    let ls = st.intern_level_list(base, levels).unwrap();
    st.expr_const(base, Some(n), ls).unwrap()
}

/// Build `foo2` (with its aux) inside a `MetaCtx` over `env`; return the
/// declarations in commit order (aux first).
fn build_foo2(env: &Environment, exts: EnvExtensions<'_>, scratch: &mut Store) -> Built {
    let view = env.view();
    let mut ctx = MetaCtx::new(view, scratch, Config::default(), exts);
    let base = Some(view.store);
    let u_name = nm(&mut ctx, base, "u");
    let u = ctx.store_mut().level_param(base, Some(u_name)).unwrap();
    let zero = ctx.store_mut().level_zero(base).unwrap();
    let sort_u = ctx.store_mut().expr_sort(base, u).unwrap();
    let alpha_n = nm(&mut ctx, base, "α");
    let a_n = nm(&mut ctx, base, "a");
    let alpha = ctx
        .push_local_decl(Some(alpha_n), sort_u, BinderInfo::Default)
        .unwrap();
    let a = ctx
        .push_local_decl(Some(a_n), alpha, BinderInfo::Default)
        .unwrap();
    let id_u = cu(&mut ctx, base, "id", &[u]);
    let ida = ctx.store_mut().expr_app(base, id_u, alpha).unwrap();
    let ida = ctx.store_mut().expr_app(base, ida, a).unwrap();
    let eq_u = cu(&mut ctx, base, "Eq", &[u]);
    let rfl_u = cu(&mut ctx, base, "rfl", &[u]);
    let mut eq_ty = eq_u;
    for x in [alpha, ida, ida] {
        eq_ty = ctx.store_mut().expr_app(base, eq_ty, x).unwrap();
    }
    let mut pf = rfl_u;
    for x in [alpha, ida] {
        pf = ctx.store_mut().expr_app(base, pf, x).unwrap();
    }
    let pprod = cu(&mut ctx, base, "PProd", &[u, zero]);
    let mut ty_body = pprod;
    for x in [alpha, eq_ty] {
        ty_body = ctx.store_mut().expr_app(base, ty_body, x).unwrap();
    }
    let mk = cu(&mut ctx, base, "PProd.mk", &[u, zero]);
    let mut val_body = mk;
    for x in [alpha, eq_ty, a, pf] {
        val_body = ctx.store_mut().expr_app(base, val_body, x).unwrap();
    }
    let ty = ctx.mk_forall(&[alpha, a], ty_body).unwrap();
    let value = ctx.mk_lambda(&[alpha, a], val_body).unwrap();

    let foo2 = nm(&mut ctx, base, "foo2");
    let mut aux = AuxLemmas::new(foo2);
    let value = ctx.abstract_nested_proofs(&mut aux, value).unwrap();

    let mut s = CollectLevelParams::default();
    ctx.collect_level_params(&mut s, ty).unwrap();
    ctx.collect_level_params(&mut s, value).unwrap();
    let lps = sort_decl_level_params(ctx.store(), base, &[], &[u_name], &s.params).unwrap();
    assert_eq!(lps, vec![u_name]);
    let h = ctx.get_max_height(value).unwrap();

    let mut decls = aux.into_pending();
    decls.push(Declaration::Defn(DefinitionVal {
        val: ConstantVal {
            name: foo2,
            level_params: lps,
            ty,
        },
        value,
        hints: ReducibilityHints::Regular(h + 1),
        safety: DefinitionSafety::Safe,
        all: vec![foo2],
    }));
    Built { decls }
}

fn persistent(env: &mut Environment, s: &str) -> NameId {
    let st = env.store_mut();
    let mut n = None;
    for part in s.split('.') {
        let id = st.intern_str(None, part).unwrap();
        n = Some(st.name_str(None, n, id).unwrap());
    }
    n.unwrap()
}

#[test]
fn foo2_commits_its_aux_theorem_then_itself() {
    let r = support::replay_fixture_in("meta", "Meta0.olean");
    let mut env = r.env;
    let exts = EnvExtensions {
        reducibility: &r.reducibility,
        matchers: &r.matchers,
        instances: &r.instances,
        default_instances: &r.default_instances,
        projection_fns: &r.projection_fns,
        classes: &r.classes,
        coe_decls: &r.coe_decls,
        aux_recs: &r.aux_recs,
        elab_as_elim: &r.elab_as_elim,
        structures: &[],
    };
    let mut scratch = Store::scratch();
    let Built { decls } = build_foo2(&env, exts, &mut scratch);
    assert_eq!(decls.len(), 2, "one aux + the main decl");
    for d in decls {
        env.add_decl_in(&mut scratch, d).expect("kernel admits");
    }
    let aux = persistent(&mut env, "foo2._proof_1");
    let main = persistent(&mut env, "foo2");
    let u_1 = persistent(&mut env, "u_1");
    match env.get(aux) {
        Some(ConstantInfo::Thm(t)) => assert_eq!(t.val.level_params, vec![u_1]),
        other => panic!("foo2._proof_1: {other:?}"),
    }
    match env.get(main) {
        Some(ConstantInfo::Defn(d)) => assert_eq!(d.hints, ReducibilityHints::Regular(2)),
        other => panic!("foo2: {other:?}"),
    }
}

#[test]
fn the_main_decl_is_rejected_without_its_aux() {
    let r = support::replay_fixture_in("meta", "Meta0.olean");
    let mut env = r.env;
    let exts = EnvExtensions {
        reducibility: &r.reducibility,
        matchers: &r.matchers,
        instances: &r.instances,
        default_instances: &r.default_instances,
        projection_fns: &r.projection_fns,
        classes: &r.classes,
        coe_decls: &r.coe_decls,
        aux_recs: &r.aux_recs,
        elab_as_elim: &r.elab_as_elim,
        structures: &[],
    };
    let mut scratch = Store::scratch();
    let Built { decls } = build_foo2(&env, exts, &mut scratch);
    let main = decls.into_iter().last().unwrap();
    let err = env.add_decl_in(&mut scratch, main).unwrap_err();
    assert!(
        matches!(err, leanr_kernel::KernelError::UnknownConstant(_)),
        "{err:?}"
    );
}
