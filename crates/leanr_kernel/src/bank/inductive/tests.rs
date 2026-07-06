//! Dual-checker differential harness for `bank::inductive::add_inductive`
//! (migration Task 5) — id-twin of `crate::inductive::tests` (Tasks 9-10).
//! Every test below builds the SAME Arc-kernel fixtures the Arc test
//! file uses (several helpers are copied verbatim so `Declaration`
//! fixtures round-trip unchanged), then asserts the Arc and id-native
//! `add_inductive` produce identical verdicts via
//! `assert_inductive_admission_matches`, following the dual-harness
//! pattern established by `bank::tc::tests`/`bank::quot::tests`. Each
//! ported test then keeps its ORIGINAL Arc-only assertions (on `arc_env`
//! alone) verbatim — agreement between the two kernels is already pinned
//! by the harness call itself.

use super::*;
use crate::bank::decl::{constant_info_eq, intern_constant_info};
use crate::bank::NameId;
use crate::testenv::{g, mini, nm, nm2};
use crate::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, Declaration, Environment,
    Expr, ExprNode, InductiveType, InductiveVal, Level, Name, Nat, RecGuard, RecursorVal,
};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

// ---- Arc-side expr/fixture helpers (verbatim from `crate::inductive::tests`) ----

fn level_eq(a: &Arc<Level>, b: &Arc<Level>) -> bool {
    Level::structural_eq(a, b, &mut RecGuard::new()).unwrap()
}

/// Structural (de-Bruijn) equality ignoring binder *names* and
/// binder_info — verbatim from the Arc test file (see its own doc
/// comment for why a byte-exact compare isn't the right bar here).
fn eq_structural(a: &Arc<Expr>, b: &Arc<Expr>) -> bool {
    match (a.node(), b.node()) {
        (ExprNode::BVar { idx: x }, ExprNode::BVar { idx: y }) => x == y,
        (ExprNode::FVar { id: x }, ExprNode::FVar { id: y }) => x == y,
        (ExprNode::Sort { level: x }, ExprNode::Sort { level: y }) => level_eq(x, y),
        (
            ExprNode::Const {
                name: n1,
                levels: l1,
            },
            ExprNode::Const {
                name: n2,
                levels: l2,
            },
        ) => n1 == n2 && l1.len() == l2.len() && l1.iter().zip(l2).all(|(a, b)| level_eq(a, b)),
        (ExprNode::App { f: f1, arg: a1 }, ExprNode::App { f: f2, arg: a2 }) => {
            eq_structural(f1, f2) && eq_structural(a1, a2)
        }
        (
            ExprNode::Lam {
                binder_type: t1,
                body: b1,
                ..
            },
            ExprNode::Lam {
                binder_type: t2,
                body: b2,
                ..
            },
        )
        | (
            ExprNode::ForallE {
                binder_type: t1,
                body: b1,
                ..
            },
            ExprNode::ForallE {
                binder_type: t2,
                body: b2,
                ..
            },
        ) => eq_structural(t1, t2) && eq_structural(b1, b2),
        (ExprNode::Lit(x), ExprNode::Lit(y)) => x == y,
        _ => false,
    }
}

fn binder_names(e: &Arc<Expr>) -> Vec<String> {
    let mut out = Vec::new();
    fn go(e: &Arc<Expr>, out: &mut Vec<String>) {
        match e.node() {
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                ..
            }
            | ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                ..
            } => {
                out.push(binder_name.to_string());
                go(binder_type, out);
                go(body, out);
            }
            ExprNode::App { f, arg } => {
                go(f, out);
                go(arg, out);
            }
            _ => {}
        }
    }
    go(e, &mut out);
    out
}

fn sort_n(n: u64) -> Arc<Expr> {
    let mut l = Arc::new(Level::Zero);
    for _ in 0..n {
        l = Level::mk_succ(l);
    }
    Expr::sort(l, &mut RecGuard::new()).unwrap()
}

fn ind(name: &str, ty: Arc<Expr>, ctors: Vec<(Arc<Name>, Arc<Expr>)>) -> InductiveType {
    InductiveType {
        name: nm(name),
        ty,
        ctors,
    }
}

fn decl(lparams: Vec<Arc<Name>>, nparams: u64, types: Vec<InductiveType>) -> Declaration {
    Declaration::Inductive {
        lparams,
        nparams: Nat::from(nparams),
        types,
        is_unsafe: false,
    }
}

fn axiom(name: &str, ty: Arc<Expr>) -> Declaration {
    Declaration::Axiom(AxiomVal {
        val: ConstantVal {
            name: nm(name),
            level_params: vec![],
            ty,
        },
        is_unsafe: false,
    })
}

fn induct(env: &Environment, name: &Arc<Name>) -> InductiveVal {
    match env.get(name) {
        Some(ConstantInfo::Induct(v)) => v.clone(),
        other => panic!("expected inductive {name}, got {other:?}"),
    }
}

fn ctor(env: &Environment, name: &Arc<Name>) -> ConstructorVal {
    match env.get(name) {
        Some(ConstantInfo::Ctor(v)) => v.clone(),
        other => panic!("expected ctor {name}, got {other:?}"),
    }
}

fn recursor(env: &Environment, name: &Arc<Name>) -> RecursorVal {
    match env.get(name) {
        Some(ConstantInfo::Rec(v)) => v.clone(),
        other => panic!("expected recursor {name}, got {other:?}"),
    }
}

/// Nat: `inductive Nat where | zero | succ (n : Nat)`.
fn nat_decl() -> Declaration {
    decl(
        vec![],
        0,
        vec![ind(
            "Nat",
            mini::type1(),
            vec![
                (nm2("Nat", "zero"), mini::nat()),
                (nm2("Nat", "succ"), mini::pi("n", mini::nat(), mini::nat())),
            ],
        )],
    )
}

/// `Type u` = `Sort (u+1)`.
fn type_u() -> Arc<Expr> {
    Expr::sort(
        Level::mk_succ(Arc::new(Level::Param(nm("u")))),
        &mut RecGuard::new(),
    )
    .unwrap()
}

fn name_has_component(n: &Arc<Name>, s: &str) -> bool {
    let mut cur = Arc::clone(n);
    loop {
        match cur.as_ref() {
            Name::Anonymous => return false,
            Name::Str { parent, part } => {
                if part == s {
                    return true;
                }
                cur = Arc::clone(parent);
            }
            Name::Num { parent, .. } => cur = Arc::clone(parent),
        }
    }
}

fn assert_no_nested_leak(env: &Environment) {
    for n in env.constant_names() {
        assert!(
            !name_has_component(&n, "_nested"),
            "aux `_nested` name leaked into final env: {n}"
        );
    }
}

/// `inductive Tree where | node : List Tree → Tree`.
fn tree_decl() -> Declaration {
    let list0_tree = mini::app(
        mini::cstn(nm("List"), vec![Arc::new(Level::Zero)]),
        mini::cstn(nm("Tree"), vec![]),
    );
    let node_ty = mini::pi("a", list0_tree, mini::cstn(nm("Tree"), vec![]));
    decl(
        vec![],
        0,
        vec![ind(
            "Tree",
            mini::type1(),
            vec![(nm2("Tree", "node"), node_ty)],
        )],
    )
}

/// `structure Array.{u} (α : Type u) where mk :: (toList : List.{u} α)`.
fn array_decl() -> Declaration {
    let array_ty = mini::pi("α", type_u(), type_u());
    let listu = mini::cstn(nm("List"), vec![Arc::new(Level::Param(nm("u")))]);
    let arrayu = mini::cstn(nm("Array"), vec![Arc::new(Level::Param(nm("u")))]);
    let mk_ty = mini::pi(
        "α",
        type_u(),
        mini::pi(
            "toList",
            mini::app(listu, mini::bvar(0)),
            mini::app(arrayu, mini::bvar(1)),
        ),
    );
    decl(
        vec![nm("u")],
        1,
        vec![ind("Array", array_ty, vec![(nm2("Array", "mk"), mk_ty)])],
    )
}

// ---------------------------------------------------------------------
// Dual-checker harness.
// ---------------------------------------------------------------------

/// Everything a test needs after a dual-admission run: the ARC env
/// (post-admission, for the ported test's own Arc-only assertions), plus
/// the id-side ingredients (`scratch` — holds the admitted `ExprId`s;
/// `persistent`/`consts` — the full bridged base+admitted map) for tests
/// that additionally need a dual `whnf` check, plus the raw id-side
/// verdict (`id_result`) so rejection tests can assert their own
/// independent `KernelError` variant/`what`-string check on top of the
/// harness's already-pinned arc==id agreement.
struct DualAdmit {
    arc_env: Environment,
    scratch: Store,
    persistent: Store,
    consts: HashMap<NameId, crate::bank::decl::ConstantInfo>,
    id_result: Result<Vec<crate::bank::decl::ConstantInfo>, crate::KernelError>,
}

/// Bridge an Arc-kernel test env into (persistent store, consts map) —
/// same pattern as `bank::tc::tests::bridge_env`.
fn bridge_env(env: &Environment) -> (Store, HashMap<NameId, crate::bank::decl::ConstantInfo>) {
    let mut st = Store::persistent();
    let mut consts = HashMap::new();
    for ci in env.iter() {
        let idci = intern_constant_info(&mut st, None, ci).unwrap();
        consts.insert(idci.name(), idci);
    }
    (st, consts)
}

/// Run both kernels' inductive admission against independently-built
/// (but content-identical) starting environments and the SAME
/// `Declaration::Inductive`; assert identical verdicts: both-Err ⇒ the
/// exact same `KernelError`; both-Ok ⇒ every newly-admitted Arc constant
/// bridge-matches its id counterpart (same intern-both-sides-into-one-
/// store technique `bank::decl`'s own `assert_eq_ci` uses), 1:1 (no
/// extras on either side).
fn assert_inductive_admission_matches(
    mk_env: impl Fn() -> Environment,
    d: Declaration,
) -> DualAdmit {
    let (lparams, nparams, types, is_unsafe) = match &d {
        Declaration::Inductive {
            lparams,
            nparams,
            types,
            is_unsafe,
        } => (lparams.clone(), nparams.clone(), types.clone(), *is_unsafe),
        _ => panic!("harness expects Declaration::Inductive"),
    };

    let mut arc_env = mk_env();
    let before_names: HashSet<Arc<Name>> = arc_env.constant_names().into_iter().collect();
    let arc_result = arc_env.add_decl(d);

    let base_env = mk_env();
    let (persistent, consts) = bridge_env(&base_env);
    let mut scratch = Store::scratch();
    let lparam_ids: Vec<NameId> = lparams
        .iter()
        .map(|p| scratch.intern_name(Some(&persistent), p).unwrap().unwrap())
        .collect();
    let id_types: Vec<crate::bank::decl::InductiveType> = types
        .iter()
        .map(|t| {
            let name = scratch
                .intern_name(Some(&persistent), &t.name)
                .unwrap()
                .unwrap();
            let ty = scratch.intern_expr(Some(&persistent), &t.ty).unwrap();
            let ctors = t
                .ctors
                .iter()
                .map(|(cn, ct)| {
                    (
                        scratch.intern_name(Some(&persistent), cn).unwrap().unwrap(),
                        scratch.intern_expr(Some(&persistent), ct).unwrap(),
                    )
                })
                .collect();
            crate::bank::decl::InductiveType { name, ty, ctors }
        })
        .collect();
    let view = EnvView {
        consts: &consts,
        extra: None,
        quot_initialized: base_env.quot_initialized(),
        store: &persistent,
    };
    let id_result = add_inductive(
        &mut scratch,
        &view,
        lparam_ids,
        nparams,
        id_types,
        is_unsafe,
    );

    let mut full_consts = consts.clone();
    match (&arc_result, &id_result) {
        (Ok(()), Ok(added)) => {
            let after_names: Vec<Arc<Name>> = arc_env.constant_names();
            let new_names: Vec<Arc<Name>> = after_names
                .into_iter()
                .filter(|n| !before_names.contains(n))
                .collect();
            assert_eq!(
                new_names.len(),
                added.len(),
                "same number of newly-admitted constants"
            );
            for n in &new_names {
                let arc_ci = arc_env.get(n).unwrap();
                let bridged =
                    intern_constant_info(&mut scratch, Some(&persistent), arc_ci).unwrap();
                let id_name = scratch.intern_name(Some(&persistent), n).unwrap().unwrap();
                let id_ci = added
                    .iter()
                    .find(|ci| ci.name() == id_name)
                    .unwrap_or_else(|| panic!("id side missing {n}"));
                assert!(constant_info_eq(id_ci, &bridged), "mismatch for {n}");
            }
            for ci in added {
                full_consts.insert(ci.name(), ci.clone());
            }
        }
        (Err(a), Err(b)) => assert_eq!(a, b),
        (a, b) => panic!("verdict split: arc={a:?} id={b:?}"),
    }
    DualAdmit {
        arc_env,
        scratch,
        persistent,
        consts: full_consts,
        id_result,
    }
}

#[test]
fn admits_nat_and_regenerates_m1a_shapes() {
    let res = assert_inductive_admission_matches(Environment::default, nat_decl());
    let env = &res.arc_env;

    let nat = induct(env, &nm("Nat"));
    assert!(nat.is_rec, "Nat is recursive");
    assert!(!nat.is_reflexive);
    assert_eq!(nat.num_params, Nat::from(0));
    assert_eq!(nat.num_indices, Nat::from(0));
    assert_eq!(nat.num_nested, Nat::from(0));
    assert_eq!(nat.all, vec![nm("Nat")]);
    assert_eq!(nat.ctors, vec![nm2("Nat", "zero"), nm2("Nat", "succ")]);

    let zero = ctor(env, &nm2("Nat", "zero"));
    assert_eq!(zero.cidx, Nat::from(0));
    assert_eq!(zero.num_fields, Nat::from(0));
    let succ = ctor(env, &nm2("Nat", "succ"));
    assert_eq!(succ.cidx, Nat::from(1));
    assert_eq!(succ.num_fields, Nat::from(1));

    let got = recursor(env, &nm2("Nat", "rec"));
    let expected = recursor(&mini::env(), &nm2("Nat", "rec"));
    assert!(!got.k, "Nat.rec is not K-like");
    assert_eq!(got.num_params, Nat::from(0));
    assert_eq!(got.num_indices, Nat::from(0));
    assert_eq!(got.num_motives, Nat::from(1));
    assert_eq!(got.num_minors, Nat::from(2));
    assert_eq!(got.val.level_params, vec![nm("u")]);
    assert_eq!(got.all, vec![nm("Nat")]);
    assert_eq!(got.rules.len(), 2);
    for (g, e) in got.rules.iter().zip(expected.rules.iter()) {
        assert_eq!(g.ctor, e.ctor);
        assert_eq!(g.nfields, e.nfields);
        assert!(
            eq_structural(&g.rhs, &e.rhs),
            "rule rhs for {} matches",
            g.ctor
        );
    }
    assert!(
        eq_structural(&got.val.ty, &expected.val.ty),
        "Nat.rec type matches structurally"
    );
    let ExprNode::ForallE { binder_info, .. } = got.val.ty.node() else {
        panic!("recursor type is a Pi");
    };
    assert_eq!(*binder_info, BinderInfo::Implicit);
    let succ_rhs_binders = binder_names(&got.rules[1].rhs);
    assert!(
        succ_rhs_binders.iter().any(|n| n == "n_ih"),
        "IH binder is `n_ih`, got {succ_rhs_binders:?}"
    );
}

#[test]
fn admits_prod_structure_like() {
    let prod_ty = mini::pi(
        "α",
        mini::type1(),
        mini::pi("β", mini::type1(), mini::type1()),
    );
    let mk_ty = mini::pi(
        "α",
        mini::type1(),
        mini::pi(
            "β",
            mini::type1(),
            mini::pi(
                "fst",
                mini::bvar(1),
                mini::pi(
                    "snd",
                    mini::bvar(1),
                    mini::appn(
                        mini::cstn(nm("Prod"), vec![]),
                        vec![mini::bvar(3), mini::bvar(2)],
                    ),
                ),
            ),
        ),
    );
    let d = decl(
        vec![],
        2,
        vec![ind("Prod", prod_ty, vec![(nm2("Prod", "mk"), mk_ty)])],
    );
    let res = assert_inductive_admission_matches(Environment::default, d);
    let env = &res.arc_env;

    let prod = induct(env, &nm("Prod"));
    assert_eq!(prod.num_params, Nat::from(2));
    assert_eq!(prod.num_indices, Nat::from(0));
    assert_eq!(prod.ctors.len(), 1);
    assert!(!prod.is_rec);

    let mk = ctor(env, &nm2("Prod", "mk"));
    assert_eq!(mk.num_params, Nat::from(2));
    assert_eq!(mk.num_fields, Nat::from(2));

    let rec = recursor(env, &nm2("Prod", "rec"));
    assert_eq!(rec.num_minors, Nat::from(1));
    assert_eq!(rec.num_motives, Nat::from(1));
    assert_eq!(rec.num_params, Nat::from(2));
    assert_eq!(rec.num_indices, Nat::from(0));
    assert!(!rec.k);
}

/// Eq: `inductive Eq {α : Sort u_1} (a : α) : α → Prop | refl : Eq a a`.
fn eq_decl() -> Declaration {
    let eq_ty = mini::pi(
        "α",
        mini::sort_param("u_1"),
        mini::pi(
            "a",
            mini::bvar(0),
            mini::pi("b", mini::bvar(1), mini::sort0()),
        ),
    );
    let eq = mini::cstn(nm("Eq"), vec![Arc::new(Level::Param(nm("u_1")))]);
    let refl_ty = mini::pi(
        "α",
        mini::sort_param("u_1"),
        mini::pi(
            "a",
            mini::bvar(0),
            mini::appn(eq, vec![mini::bvar(1), mini::bvar(0), mini::bvar(0)]),
        ),
    );
    decl(
        vec![nm("u_1")],
        2,
        vec![ind("Eq", eq_ty, vec![(nm2("Eq", "refl"), refl_ty)])],
    )
}

#[test]
fn admits_eq_with_k() {
    let res = assert_inductive_admission_matches(Environment::default, eq_decl());
    let env = &res.arc_env;

    let eq = induct(env, &nm("Eq"));
    assert_eq!(eq.num_params, Nat::from(2));
    assert_eq!(eq.num_indices, Nat::from(1));

    let rec = recursor(env, &nm2("Eq", "rec"));
    assert!(rec.k, "Eq.rec is K-like");
    assert_eq!(rec.num_minors, Nat::from(1));
    assert_eq!(rec.num_motives, Nat::from(1));
    assert_eq!(rec.num_params, Nat::from(2));
    assert_eq!(rec.num_indices, Nat::from(1));
}

#[test]
fn large_elim_singleton() {
    let res = assert_inductive_admission_matches(Environment::default, eq_decl());
    let rec = recursor(&res.arc_env, &nm2("Eq", "rec"));
    assert_eq!(rec.val.level_params, vec![nm("u"), nm("u_1")]);
}

#[test]
fn prop_only_elim_small() {
    let or = mini::cstn(nm("Or"), vec![]);
    let or_ty = mini::pi(
        "a",
        mini::sort0(),
        mini::pi("b", mini::sort0(), mini::sort0()),
    );
    let inl_ty = mini::pi(
        "a",
        mini::sort0(),
        mini::pi(
            "b",
            mini::sort0(),
            mini::pi(
                "h",
                mini::bvar(1),
                mini::appn(Arc::clone(&or), vec![mini::bvar(2), mini::bvar(1)]),
            ),
        ),
    );
    let inr_ty = mini::pi(
        "a",
        mini::sort0(),
        mini::pi(
            "b",
            mini::sort0(),
            mini::pi(
                "h",
                mini::bvar(0),
                mini::appn(or, vec![mini::bvar(2), mini::bvar(1)]),
            ),
        ),
    );
    let d = decl(
        vec![],
        2,
        vec![ind(
            "Or",
            or_ty,
            vec![(nm2("Or", "inl"), inl_ty), (nm2("Or", "inr"), inr_ty)],
        )],
    );
    let res = assert_inductive_admission_matches(Environment::default, d);
    let env = &res.arc_env;

    let or_ind = induct(env, &nm("Or"));
    assert!(!or_ind.is_rec);
    let rec = recursor(env, &nm2("Or", "rec"));
    assert!(rec.val.level_params.is_empty(), "Or.rec small-eliminates");
    assert_eq!(rec.num_minors, Nat::from(2));
    assert_eq!(rec.num_motives, Nat::from(1));
    assert!(!rec.k);
}

#[test]
fn admits_mutual_pair() {
    let ca = mini::cstn(nm("A"), vec![]);
    let cb = mini::cstn(nm("B"), vec![]);
    let a_mk = mini::pi("b", Arc::clone(&cb), Arc::clone(&ca));
    let b_mk = mini::pi("a", Arc::clone(&ca), Arc::clone(&cb));
    let d = decl(
        vec![],
        0,
        vec![
            ind("A", mini::type1(), vec![(nm2("A", "mk"), a_mk)]),
            ind("B", mini::type1(), vec![(nm2("B", "mk"), b_mk)]),
        ],
    );
    let res = assert_inductive_admission_matches(Environment::default, d);
    let env = &res.arc_env;

    let a = induct(env, &nm("A"));
    let b = induct(env, &nm("B"));
    assert_eq!(a.all, vec![nm("A"), nm("B")]);
    assert_eq!(b.all, vec![nm("A"), nm("B")]);
    assert!(a.is_rec && b.is_rec, "mutual block is recursive");

    let a_rec = recursor(env, &nm2("A", "rec"));
    let b_rec = recursor(env, &nm2("B", "rec"));
    assert_eq!(a_rec.num_motives, Nat::from(2));
    assert_eq!(b_rec.num_motives, Nat::from(2));
    assert_eq!(a_rec.num_minors, Nat::from(2));
    assert_eq!(b_rec.num_minors, Nat::from(2));
    assert_eq!(a_rec.all, vec![nm("A"), nm("B")]);
}

#[test]
fn rejects_positivity_violation() {
    let ct = mini::cstn(nm("T"), vec![]);
    let t_to_t = mini::pi("x", Arc::clone(&ct), Arc::clone(&ct));
    let field = mini::pi("h", t_to_t, Arc::clone(&ct));
    let mk_ty = mini::pi("f", field, ct);
    let d = decl(
        vec![],
        0,
        vec![ind("T", mini::type1(), vec![(nm2("T", "mk"), mk_ty)])],
    );
    let res = assert_inductive_admission_matches(Environment::default, d);
    let err = res.arc_env.get(&nm("T"));
    assert!(err.is_none());
    // Verdict (including the exact `InvalidInductive{what:"positivity"}`
    // payload) was already pinned by the harness; re-check the specific
    // reason for readability.
    let mut env2 = Environment::default();
    let e = env2
        .add_decl(decl(
            vec![],
            0,
            vec![ind(
                "T",
                mini::type1(),
                vec![(
                    nm2("T", "mk"),
                    mini::pi(
                        "f",
                        mini::pi(
                            "h",
                            mini::pi(
                                "x",
                                mini::cstn(nm("T"), vec![]),
                                mini::cstn(nm("T"), vec![]),
                            ),
                            mini::cstn(nm("T"), vec![]),
                        ),
                        mini::cstn(nm("T"), vec![]),
                    ),
                )],
            )],
        ))
        .unwrap_err();
    match e {
        crate::KernelError::InvalidInductive { what, .. } => assert_eq!(what, "positivity"),
        other => panic!("expected positivity error, got {other:?}"),
    }
    assert!(env2.get(&nm("T")).is_none());
    assert!(env2.get(&nm2("T", "mk")).is_none());
}

#[test]
fn rejects_wrong_codomain() {
    let mk_ty = sort_n(1);
    let d = decl(
        vec![],
        0,
        vec![ind("T", mini::type1(), vec![(nm2("T", "mk"), mk_ty)])],
    );
    let res = assert_inductive_admission_matches(Environment::default, d);
    assert!(res.arc_env.get(&nm("T")).is_none());
    // Verdict (including exact-`KernelError` agreement) was already
    // pinned by the harness; re-check the specific reason for
    // readability, on the id-side error (harness proved arc==id).
    match res.id_result {
        Err(crate::KernelError::InvalidInductive { what, .. }) => {
            assert_eq!(what, "invalid return type")
        }
        other => panic!("expected invalid-return-type error, got {other:?}"),
    }
}

#[test]
fn rejects_universe_too_small() {
    let field_ty = sort_n(2);
    let mk_ty = mini::pi("α", field_ty, mini::cstn(nm("T"), vec![]));
    let d = decl(
        vec![],
        0,
        vec![ind("T", mini::type1(), vec![(nm2("T", "mk"), mk_ty)])],
    );
    let res = assert_inductive_admission_matches(Environment::default, d);
    match res.id_result {
        Err(crate::KernelError::InvalidInductive { what, .. }) => {
            assert_eq!(what, "universe too small")
        }
        other => panic!("expected universe-too-small error, got {other:?}"),
    }
}

#[test]
fn rejects_param_mismatch_across_block() {
    let a_ty = mini::pi("α", mini::type1(), mini::type1());
    let b_ty = mini::pi("α", mini::sort0(), mini::type1());
    let a_mk = mini::pi(
        "α",
        mini::type1(),
        mini::appn(mini::cstn(nm("A"), vec![]), vec![mini::bvar(0)]),
    );
    let b_mk = mini::pi(
        "α",
        mini::sort0(),
        mini::appn(mini::cstn(nm("B"), vec![]), vec![mini::bvar(0)]),
    );
    let d = decl(
        vec![],
        1,
        vec![
            ind("A", a_ty, vec![(nm2("A", "mk"), a_mk)]),
            ind("B", b_ty, vec![(nm2("B", "mk"), b_mk)]),
        ],
    );
    let res = assert_inductive_admission_matches(Environment::default, d);
    assert!(res.arc_env.get(&nm("A")).is_none());
    match res.id_result {
        Err(crate::KernelError::InvalidInductive { what, .. }) => {
            assert_eq!(what, "parameters must match")
        }
        other => panic!("expected parameter-mismatch error, got {other:?}"),
    }
}

#[test]
fn rejects_empty_inductive_block() {
    let mk_env = || {
        let mut e = Environment::default();
        e.add_decl(axiom("marker", sort_n(1))).unwrap();
        e
    };
    let before = mk_env().len();
    let res = assert_inductive_admission_matches(mk_env, decl(vec![], 0, vec![]));
    match res.arc_env.get(&nm("marker")) {
        Some(_) => {}
        None => panic!("marker constant should remain"),
    }
    assert_eq!(
        res.arc_env.len(),
        before,
        "environment unchanged on rejection"
    );
    match res.id_result {
        Err(crate::KernelError::InvalidInductive { name, what }) => {
            assert_eq!(what, "empty inductive block");
            assert!(matches!(name.as_ref(), Name::Anonymous));
        }
        other => panic!("expected empty-inductive-block error, got {other:?}"),
    }
}

#[test]
fn iota_now_reduces_declared_recursor() {
    // Admit `Nat` under the dual harness first (agreement already
    // pinned by `admits_nat_and_regenerates_m1a_shapes`; re-run here so
    // this test owns its own `DualAdmit` to extend). The `z`/`s`/`k`
    // axioms reference `Nat` and so must be added AFTER admission, on
    // both sides — matching the Arc test's own ordering (`nat_decl()`
    // first, then the axioms).
    let mut res = assert_inductive_admission_matches(Environment::default, nat_decl());
    res.arc_env.add_decl(axiom("z", mini::nat())).unwrap();
    res.arc_env
        .add_decl(axiom(
            "s",
            mini::pi("n", mini::nat(), mini::pi("ih", mini::nat(), mini::nat())),
        ))
        .unwrap();
    res.arc_env.add_decl(axiom("k", mini::nat())).unwrap();
    // Mirror the same three axioms into the id-side `consts` map
    // directly (bridging, not re-running admission — this test's
    // subject is the recursor's iota reduction, not axiom checking).
    for arc_ci in [
        match axiom("z", mini::nat()) {
            Declaration::Axiom(v) => ConstantInfo::Axiom(v),
            _ => unreachable!(),
        },
        match axiom(
            "s",
            mini::pi("n", mini::nat(), mini::pi("ih", mini::nat(), mini::nat())),
        ) {
            Declaration::Axiom(v) => ConstantInfo::Axiom(v),
            _ => unreachable!(),
        },
        match axiom("k", mini::nat()) {
            Declaration::Axiom(v) => ConstantInfo::Axiom(v),
            _ => unreachable!(),
        },
    ] {
        let idci = intern_constant_info(&mut res.scratch, Some(&res.persistent), &arc_ci).unwrap();
        res.consts.insert(idci.name(), idci);
    }

    let motive = mini::lam("x", mini::nat(), mini::nat());
    let one = Level::mk_succ(Arc::new(Level::Zero));
    let natrec = mini::cstn(nm2("Nat", "rec"), vec![one]);
    let succ_k = mini::app(
        mini::cstn(nm2("Nat", "succ"), vec![]),
        mini::cst("k", vec![]),
    );
    let major = mini::appn(
        natrec,
        vec![
            motive,
            mini::cst("z", vec![]),
            mini::cst("s", vec![]),
            succ_k,
        ],
    );

    let mut arc_tc = crate::TypeChecker::new(&res.arc_env);
    let reduced_arc = arc_tc.whnf(&major).expect("iota reduces");
    let head = Expr::get_app_fn(&reduced_arc);
    assert!(
        matches!(head.node(), ExprNode::Const { name, .. } if name.as_ref() == nm("s").as_ref()),
        "reduced head is the succ minor `s`, got {:?}",
        head.node()
    );
    assert_eq!(Expr::get_app_num_args(&reduced_arc), 2);

    // Same reduction, id-native side, using the SAME scratch the
    // admission populated (holds `Nat.rec`'s regenerated `ExprId`s).
    let DualAdmit {
        mut scratch,
        persistent,
        consts,
        ..
    } = res;
    let major_id = scratch.intern_expr(Some(&persistent), &major).unwrap();
    let view = EnvView {
        consts: &consts,
        extra: None,
        quot_initialized: false,
        store: &persistent,
    };
    let mut tc = TypeChecker::new(view, &mut scratch);
    let reduced_id = tc.whnf(major_id).unwrap();
    let reduced_id_arc = scratch
        .to_expr(Some(&persistent), reduced_id, &mut g())
        .unwrap();
    assert!(
        Expr::structural_eq(&reduced_id_arc, &reduced_arc, &mut g()).unwrap(),
        "id-native iota reduction matches the Arc kernel's"
    );
}

// ---- Task 10: nested inductives -----------------------------------------

#[test]
fn admits_nested_via_list() {
    let res = assert_inductive_admission_matches(mini::env, tree_decl());
    let env = &res.arc_env;

    let tree = induct(env, &nm("Tree"));
    assert_eq!(tree.num_nested, Nat::from(1), "one aux nested type (List)");
    assert_eq!(tree.all, vec![nm("Tree")], "all restored to the real block");
    assert_eq!(tree.ctors, vec![nm2("Tree", "node")]);
    assert!(tree.is_rec, "Tree is recursive");

    let node = ctor(env, &nm2("Tree", "node"));
    assert_eq!(node.num_params, Nat::from(0));
    assert_eq!(node.num_fields, Nat::from(1));
    let list0_tree = mini::app(
        mini::cstn(nm("List"), vec![Arc::new(Level::Zero)]),
        mini::cstn(nm("Tree"), vec![]),
    );
    let expected_node_ty = mini::pi("a", list0_tree, mini::cstn(nm("Tree"), vec![]));
    assert!(
        eq_structural(&node.val.ty, &expected_node_ty),
        "Tree.node type restored to `List.{{0}} Tree → Tree`, got {:?}",
        node.val.ty
    );

    let rec = recursor(env, &nm2("Tree", "rec"));
    assert_eq!(rec.num_motives, Nat::from(2), "motive for Tree + aux List");
    assert_eq!(rec.num_minors, Nat::from(3), "node + nil + cons minors");
    assert_eq!(rec.num_params, Nat::from(0));
    assert_eq!(rec.num_indices, Nat::from(0));
    assert_eq!(rec.all, vec![nm("Tree")], "recursor all = real block");
    assert_eq!(rec.val.level_params, vec![nm("u")]);
    assert_eq!(rec.rules.len(), 1);
    assert_eq!(rec.rules[0].ctor, nm2("Tree", "node"));
    assert_eq!(rec.rules[0].nfields, Nat::from(1));

    let rec1 = recursor(env, &nm2("Tree", "rec_1"));
    assert_eq!(rec1.num_motives, Nat::from(2));
    assert_eq!(rec1.all, vec![nm("Tree")]);
    assert_eq!(rec1.rules.len(), 2);
    assert_eq!(rec1.rules[0].ctor, nm2("List", "nil"));
    assert_eq!(rec1.rules[0].nfields, Nat::from(0));
    assert_eq!(rec1.rules[1].ctor, nm2("List", "cons"));
    assert_eq!(rec1.rules[1].nfields, Nat::from(2));

    assert_no_nested_leak(env);
}

#[test]
fn nested_iota_reduces() {
    let mk_env = || {
        let mut e = mini::env();
        e.add_decl(tree_decl()).expect("Tree admits");
        let list0_tree = mini::app(
            mini::cstn(nm("List"), vec![Arc::new(Level::Zero)]),
            mini::cstn(nm("Tree"), vec![]),
        );
        for (n, ty) in [
            ("m1", mini::type1()),
            ("m2", mini::type1()),
            ("node_min", mini::type1()),
            ("nil_min", mini::type1()),
            ("cons_min", mini::type1()),
        ] {
            e.add_decl(axiom(n, ty)).unwrap();
        }
        e.add_decl(axiom("lst", list0_tree)).unwrap();
        e
    };
    let env = mk_env();

    let one = Level::mk_succ(Arc::new(Level::Zero));
    let tree_rec = mini::cstn(nm2("Tree", "rec"), vec![one]);
    let node_app = mini::app(
        mini::cstn(nm2("Tree", "node"), vec![]),
        mini::cst("lst", vec![]),
    );
    let major = mini::appn(
        tree_rec,
        vec![
            mini::cst("m1", vec![]),
            mini::cst("m2", vec![]),
            mini::cst("node_min", vec![]),
            mini::cst("nil_min", vec![]),
            mini::cst("cons_min", vec![]),
            node_app,
        ],
    );

    let mut tc = crate::TypeChecker::new(&env);
    let reduced = tc.whnf(&major).expect("nested iota reduces");
    let head = Expr::get_app_fn(&reduced);
    assert!(
        matches!(head.node(), ExprNode::Const { name, .. } if name.as_ref() == nm("node_min").as_ref()),
        "reduced head is the node minor, got {:?}",
        head.node()
    );
    assert_eq!(Expr::get_app_num_args(&reduced), 2);

    // Dual-check the SAME reduction id-natively, bridging the already-
    // proven-agreeing `Tree` admission (via the harness) plus this
    // test's own extra axioms into one id-space environment.
    let (persistent, consts) = bridge_env(&env);
    let mut scratch = Store::scratch();
    let major_id = scratch.intern_expr(Some(&persistent), &major).unwrap();
    let view = EnvView {
        consts: &consts,
        extra: None,
        quot_initialized: env.quot_initialized(),
        store: &persistent,
    };
    let mut id_tc = TypeChecker::new(view, &mut scratch);
    let reduced_id = id_tc.whnf(major_id).unwrap();
    let reduced_id_arc = scratch
        .to_expr(Some(&persistent), reduced_id, &mut g())
        .unwrap();
    assert!(
        Expr::structural_eq(&reduced_id_arc, &reduced, &mut g()).unwrap(),
        "id-native nested iota reduction matches the Arc kernel's"
    );
}

#[test]
fn rejects_nested_positivity_violation() {
    let t = mini::cstn(nm("T"), vec![]);
    let t_to_t = mini::pi("x", Arc::clone(&t), Arc::clone(&t));
    let list_tt = mini::app(mini::cstn(nm("List"), vec![Arc::new(Level::Zero)]), t_to_t);
    let mk_ty = mini::pi("a", list_tt, t);
    let d = decl(
        vec![],
        0,
        vec![ind("T", mini::type1(), vec![(nm2("T", "mk"), mk_ty)])],
    );
    let res = assert_inductive_admission_matches(mini::env, d);
    assert!(res.arc_env.get(&nm("T")).is_none());
    assert!(res.arc_env.get(&nm2("T", "mk")).is_none());
    assert_no_nested_leak(&res.arc_env);
    match res.id_result {
        Err(crate::KernelError::InvalidInductive { what, .. }) => assert_eq!(what, "positivity"),
        other => panic!("expected positivity error, got {other:?}"),
    }
}

#[test]
fn stdlib_shape_smoke() {
    let mk_env = || {
        let mut e = mini::env();
        e.add_decl(array_decl()).expect("Array admits");
        e
    };
    let array0_stx = mini::app(
        mini::cstn(nm("Array"), vec![Arc::new(Level::Zero)]),
        mini::cstn(nm("Stx"), vec![]),
    );
    let node_ty = mini::pi("a", array0_stx, mini::cstn(nm("Stx"), vec![]));
    let leaf_ty = mini::cstn(nm("Stx"), vec![]);
    let d = decl(
        vec![],
        0,
        vec![ind(
            "Stx",
            mini::type1(),
            vec![(nm2("Stx", "node"), node_ty), (nm2("Stx", "leaf"), leaf_ty)],
        )],
    );
    let res = assert_inductive_admission_matches(mk_env, d);
    let env = &res.arc_env;

    let stx = induct(env, &nm("Stx"));
    assert_eq!(stx.num_nested, Nat::from(2));
    assert_eq!(stx.all, vec![nm("Stx")]);
    assert_eq!(stx.ctors, vec![nm2("Stx", "node"), nm2("Stx", "leaf")]);

    let rec = recursor(env, &nm2("Stx", "rec"));
    assert_eq!(rec.num_motives, Nat::from(3), "Stx + Array-aux + List-aux");
    assert_eq!(rec.num_minors, Nat::from(5), "node+leaf + mk + nil+cons");
    assert_eq!(rec.all, vec![nm("Stx")]);

    assert!(env.get(&nm2("Stx", "rec_1")).is_some());
    assert!(env.get(&nm2("Stx", "rec_2")).is_some());
    assert_no_nested_leak(env);
}
