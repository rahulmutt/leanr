//! White-box tests of the `binop%` elaborator's helpers (macro/binop% P3),
//! over ElabOp's test-support types. The corpus pins whole terms; these pin
//! the predicates the corpus cannot isolate.

mod support;

use leanr_elab::builtin::op::{analyze, mk_const_named, to_expr};

fn with_elab<R>(k: impl FnOnce(&mut leanr_elab::TermElabM) -> R) -> R {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = support::elab_op_grammar();
    support::with_record_elab(&r, "Nat", &snap, |elab, _, _| k(elab))
}

#[test]
fn has_coe_follows_the_coercion_direction() {
    with_elab(|elab| {
        let nat = mk_const_named(elab, "Nat").unwrap();
        let z = mk_const_named(elab, "Z").unwrap();
        let u = mk_const_named(elab, "U").unwrap();
        assert!(analyze::has_coe(elab, nat, z).unwrap());
        assert!(!analyze::has_coe(elab, z, nat).unwrap());
        assert!(!analyze::has_coe(elab, nat, u).unwrap());
        assert!(!analyze::has_coe(elab, u, nat).unwrap());
    })
}

#[test]
fn has_coe_restores_the_local_context() {
    with_elab(|elab| {
        let nat = mk_const_named(elab, "Nat").unwrap();
        let z = mk_const_named(elab, "Z").unwrap();
        let before = elab.mctx.lctx_checkpoint();
        analyze::has_coe(elab, nat, z).unwrap();
        assert_eq!(elab.mctx.lctx_checkpoint(), before);
        // … on the `false` path too.
        let u = mk_const_named(elab, "U").unwrap();
        analyze::has_coe(elab, nat, u).unwrap();
        assert_eq!(elab.mctx.lctx_checkpoint(), before);
    })
}

#[test]
fn homogeneous_instance_needs_cls_max_max_max() {
    with_elab(|elab| {
        let hadd = mk_const_named(elab, "HAdd.hAdd").unwrap();
        let hpow = mk_const_named(elab, "HPow.hPow").unwrap();
        let z = mk_const_named(elab, "Z").unwrap();
        let u = mk_const_named(elab, "U").unwrap();
        assert!(to_expr::has_homogeneous_instance(elab, hadd, z).unwrap());
        // `HPow Z Nat Z` exists, `HPow Z Z Z` does not.
        assert!(!to_expr::has_homogeneous_instance(elab, hpow, z).unwrap());
        // `Add U` exists, so `HAdd U U U` via `instHAdd`.
        assert!(to_expr::has_homogeneous_instance(elab, hadd, u).unwrap());
        // A non-constant head is `false` (Extra.lean:388).
        let m = support::fresh_type_mvar(elab);
        assert!(!to_expr::has_homogeneous_instance(elab, m, z).unwrap());
        // `Nat`'s prefix is the anonymous name: no class, `false`.
        let nat = mk_const_named(elab, "Nat").unwrap();
        assert!(!to_expr::has_homogeneous_instance(elab, nat, z).unwrap());
    })
}

#[test]
fn heterogeneous_default_instances_need_two_and_the_right_side() {
    with_elab(|elab| {
        let hmul = mk_const_named(elab, "HMul.hMul").unwrap();
        let hadd = mk_const_named(elab, "HAdd.hAdd").unwrap();
        let arr = mk_const_named(elab, "Arr").unwrap();
        let nat = mk_const_named(elab, "Nat").unwrap();
        let arr_nat = support::mk_app(elab, arr, nat);
        // `HMul α (Arr α) (Arr α)`: Arr is the RHS type, so lhs = true.
        assert!(to_expr::has_heterogeneous_default_instances(elab, hmul, arr_nat, true).unwrap());
        assert!(!to_expr::has_heterogeneous_default_instances(elab, hmul, arr_nat, false).unwrap());
        // `HAdd` has one default instance (`instHAdd`): never.
        assert!(!to_expr::has_heterogeneous_default_instances(elab, hadd, arr_nat, true).unwrap());
    })
}

#[test]
fn mk_app_m_fails_on_a_type_mismatch_and_leaves_no_assignment() {
    with_elab(|elab| {
        let z = mk_const_named(elab, "Z").unwrap();
        let hadd = mk_const_named(elab, "HAdd").unwrap();
        let zero = mk_const_named(elab, "Nat.zero").unwrap(); // a term, not a type
        let hadd_name = support::const_name(elab, hadd);
        let ok = to_expr::mk_app_m(elab, hadd_name, &[z, z, z]).unwrap();
        let ok = ok.expect("HAdd Z Z Z builds");
        // The level mvars minted inside the scope were assigned and
        // instantiated there: the result carries none.
        let data = elab.mctx.store().expr_data(Some(elab.view.store), ok);
        assert!(!data.has_level_mvar());
        assert!(to_expr::mk_app_m(elab, hadd_name, &[zero, z, z])
            .unwrap()
            .is_none());
    })
}

#[test]
fn is_unknown_is_an_mvar_head() {
    with_elab(|elab| {
        let nat = mk_const_named(elab, "Nat").unwrap();
        assert!(!analyze::is_unknown(elab, nat));
        let m = support::fresh_type_mvar(elab);
        assert!(analyze::is_unknown(elab, m));
        let app = support::mk_app(elab, m, nat);
        assert!(analyze::is_unknown(elab, app));
        let app2 = support::mk_app(elab, nat, m);
        assert!(!analyze::is_unknown(elab, app2));
    })
}

#[test]
fn mk_fun_unit_is_a_unit_lambda() {
    with_elab(|elab| {
        let z = mk_const_named(elab, "Nat.zero").unwrap();
        let f = to_expr::mk_fun_unit(elab, z).unwrap();
        let ty = elab.mctx.infer_type(f).unwrap();
        let want = support::parse_type(elab, "Unit → Nat");
        assert!(elab.mctx.is_def_eq(ty, want).unwrap());
    })
}
