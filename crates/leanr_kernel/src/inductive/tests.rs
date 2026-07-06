//! Unit tests for the id-native `inductive::add_inductive` (migration
//! Task 8: ported from the pre-flip `crate::inductive::tests`, which
//! hand-built a `Declaration::Inductive`, admitted it via the Arc
//! `Environment::add_decl`, and compared the resulting `ConstantInfo`s
//! against hand-transcribed oracle output — see that file's history,
//! `git show 9b1c773:crates/leanr_kernel/src/inductive/tests.rs`). The
//! Arc checker (old `env.rs`/`inductive.rs`) this migration deletes is
//! gone, so every test below drives the id-native entry point directly
//! (`inductive::add_inductive(scratch, view, ...)`, exactly the
//! low-level call the pre-migration dual-harness file already used for
//! its "id side") instead of going through `Environment::add_decl` —
//! `add_decl` requires every id in its input already interned into the
//! `Environment`'s own PRIVATE persistent store (see its doc comment),
//! which is unreachable from outside `env.rs`; `add_inductive` has no
//! such requirement; it takes a caller-supplied scratch `Store` plus an
//! `EnvView` borrowing the real environment's store read-only, and folds
//! its results into an `extra` overlay (the exact "not yet in a real
//! `Environment`, but visible to this run's checker" pattern
//! `inductive.rs`'s own nested-admission code uses internally — see its
//! module doc point 3). Every expected value below is the SAME concrete
//! value the pre-flip file pinned.

use super::*;
use crate::bank::NameId;
use crate::decl::intern_constant_info;
use crate::testenv::{mini, nm, nm2};
use crate::{
    ArcAxiomVal, ArcConstantInfo, ArcConstantVal, ArcDeclaration, ArcInductiveType, BinderInfo,
    Environment, Expr, Level, Name, Nat, RecGuard,
};
use std::collections::HashMap;
use std::sync::Arc;

// ---- Arc-side fixture helpers (verbatim from `crate::inductive::tests`,
// only the declaration DTOs renamed `Arc*` — see `decl.rs`'s module doc) ----

fn sort_n(n: u64) -> Arc<Expr> {
    let mut l = Arc::new(Level::Zero);
    for _ in 0..n {
        l = Level::mk_succ(l);
    }
    Expr::sort(l, &mut RecGuard::new()).unwrap()
}

fn ind(name: &str, ty: Arc<Expr>, ctors: Vec<(Arc<Name>, Arc<Expr>)>) -> ArcInductiveType {
    ArcInductiveType {
        name: nm(name),
        ty,
        ctors,
    }
}

fn decl(lparams: Vec<Arc<Name>>, nparams: u64, types: Vec<ArcInductiveType>) -> ArcDeclaration {
    ArcDeclaration::Inductive {
        lparams,
        nparams: Nat::from(nparams),
        types,
        is_unsafe: false,
    }
}

fn axiom(name: &str, ty: Arc<Expr>) -> ArcConstantInfo {
    ArcConstantInfo::Axiom(ArcAxiomVal {
        val: ArcConstantVal {
            name: nm(name),
            level_params: vec![],
            ty,
        },
        is_unsafe: false,
    })
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

/// `inductive Nat where | zero | succ (n : Nat)` — exactly the testenv
/// shape.
fn nat_decl() -> ArcDeclaration {
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

/// `inductive Tree where | node : List Tree → Tree`.
fn tree_decl() -> ArcDeclaration {
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
fn array_decl() -> ArcDeclaration {
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

/// Eq: `inductive Eq {α : Sort u_1} (a : α) : α → Prop | refl : Eq a a`
/// — the canonical K-like, large-eliminating singleton in Prop.
fn eq_decl() -> ArcDeclaration {
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

// ---------------------------------------------------------------------
// Id-native admission harness. `extra` plays the role `inductive.rs`'s
// own nested-admission code gives it: constants admitted by an earlier
// `admit` call in the SAME test but not (and never, in these tests)
// promoted into a real `Environment` — visible to a later `admit`/
// `TypeChecker` call via `EnvView::extra`.
// ---------------------------------------------------------------------

fn intern_lparams(scratch: &mut Store, base: &Store, lparams: &[Arc<Name>]) -> Vec<NameId> {
    lparams
        .iter()
        .map(|p| scratch.intern_name(Some(base), p).unwrap().unwrap())
        .collect()
}

fn intern_types(
    scratch: &mut Store,
    base: &Store,
    types: &[ArcInductiveType],
) -> Vec<InductiveType> {
    types
        .iter()
        .map(|t| {
            let name = scratch.intern_name(Some(base), &t.name).unwrap().unwrap();
            let ty = scratch.intern_expr(Some(base), &t.ty).unwrap();
            let ctors = t
                .ctors
                .iter()
                .map(|(cn, ct)| {
                    (
                        scratch.intern_name(Some(base), cn).unwrap().unwrap(),
                        scratch.intern_expr(Some(base), ct).unwrap(),
                    )
                })
                .collect();
            InductiveType { name, ty, ctors }
        })
        .collect()
}

/// Run `add_inductive` against `env`'s real persistent store, with
/// `extra` as the not-yet-admitted overlay.
fn admit(
    scratch: &mut Store,
    env: &Environment,
    extra: &HashMap<NameId, ConstantInfo>,
    d: ArcDeclaration,
) -> Result<Vec<ConstantInfo>, KernelError> {
    let (lparams, nparams, types, is_unsafe) = match d {
        ArcDeclaration::Inductive {
            lparams,
            nparams,
            types,
            is_unsafe,
        } => (lparams, nparams, types, is_unsafe),
        _ => panic!("harness expects ArcDeclaration::Inductive"),
    };
    let base = env.view().store;
    let lparam_ids = intern_lparams(scratch, base, &lparams);
    let id_types = intern_types(scratch, base, &types);
    let view = EnvView {
        consts: env.view().consts,
        extra: Some(extra),
        quot_initialized: env.quot_initialized(),
        store: base,
    };
    add_inductive(scratch, &view, lparam_ids, nparams, id_types, is_unsafe)
}

/// Admit `d` and fold every result into `extra` (the multi-step-test
/// convenience `admit` alone doesn't provide).
fn admit_into(
    scratch: &mut Store,
    env: &Environment,
    extra: &mut HashMap<NameId, ConstantInfo>,
    d: ArcDeclaration,
) -> Result<(), KernelError> {
    let added = admit(scratch, env, extra, d)?;
    for ci in added {
        extra.insert(ci.name(), ci);
    }
    Ok(())
}

/// Bridge an Arc-side `ConstantInfo` directly into `extra` (no
/// checking — the established "opaque stand-in axiom" pattern for
/// whnf-only tests, matching the pre-migration file's own comment on
/// `iota_now_reduces_declared_recursor`: the subject is iota reduction,
/// not axiom-checking).
fn bridge_into(
    scratch: &mut Store,
    env: &Environment,
    extra: &mut HashMap<NameId, ConstantInfo>,
    ci: &ArcConstantInfo,
) {
    let idci = intern_constant_info(scratch, Some(env.view().store), ci).unwrap();
    extra.insert(idci.name(), idci);
}

fn find<'a>(
    scratch: &Store,
    base: &Store,
    added: &'a [ConstantInfo],
    name: &Arc<Name>,
) -> &'a ConstantInfo {
    added
        .iter()
        .find(|ci| &scratch.to_name(Some(base), Some(ci.name())) == name)
        .unwrap_or_else(|| panic!("expected {name} among admitted constants"))
}

fn as_induct(ci: &ConstantInfo) -> InductiveVal {
    match ci {
        ConstantInfo::Induct(v) => v.clone(),
        other => panic!("expected inductive, got {other:?}"),
    }
}

fn as_ctor(ci: &ConstantInfo) -> ConstructorVal {
    match ci {
        ConstantInfo::Ctor(v) => v.clone(),
        other => panic!("expected ctor, got {other:?}"),
    }
}

fn as_rec(ci: &ConstantInfo) -> RecursorVal {
    match ci {
        ConstantInfo::Rec(v) => v.clone(),
        other => panic!("expected recursor, got {other:?}"),
    }
}

fn to_names(scratch: &Store, base: &Store, ids: &[NameId]) -> Vec<Arc<Name>> {
    ids.iter()
        .map(|&id| scratch.to_name(Some(base), Some(id)))
        .collect()
}

/// Look up a constant already admitted into a real `Environment` (e.g.
/// `mini::env()`'s hand-transcribed fixtures) by name.
fn env_const(env: &Environment, n: &Arc<Name>) -> ConstantInfo {
    let mut probe = Store::scratch();
    let id = probe
        .intern_name(Some(env.view().store), n)
        .unwrap()
        .unwrap();
    env.get(id)
        .unwrap_or_else(|| panic!("expected {n} in env"))
        .clone()
}

fn env_name_id(scratch: &mut Store, env: &Environment, n: &Arc<Name>) -> NameId {
    scratch
        .intern_name(Some(env.view().store), n)
        .unwrap()
        .unwrap()
}

// ---- Structural (de-Bruijn) equality ignoring binder *names* and
// `binder_info`, across two possibly-different (store, base) pairs —
// id-native port of the Arc test file's `eq_structural`/`level_eq`. See
// that file's doc comment for why a byte-exact compare isn't the right
// bar for the recursor-shape checks below: the regenerated recursor
// type correctly marks the motive `Implicit` (ported `infer_implicit`)
// and names the induction-hypothesis binder `<field>_ih`, whereas the
// `testenv` transcriptions mark every binder `Default` and use `ih`. ----

fn name_opt_eq(
    sa: &Store,
    ba: Option<&Store>,
    x: Option<NameId>,
    sb: &Store,
    bb: Option<&Store>,
    y: Option<NameId>,
) -> bool {
    sa.to_name(ba, x) == sb.to_name(bb, y)
}

fn level_eq_id(
    sa: &Store,
    ba: Option<&Store>,
    a: LevelId,
    sb: &Store,
    bb: Option<&Store>,
    b: LevelId,
) -> bool {
    use crate::bank::levels::LevelRow;
    match (*sa.level_row(ba, a), *sb.level_row(bb, b)) {
        (LevelRow::Zero, LevelRow::Zero) => true,
        (LevelRow::Succ(x), LevelRow::Succ(y)) => level_eq_id(sa, ba, x, sb, bb, y),
        (LevelRow::Max(x1, y1), LevelRow::Max(x2, y2))
        | (LevelRow::IMax(x1, y1), LevelRow::IMax(x2, y2)) => {
            level_eq_id(sa, ba, x1, sb, bb, x2) && level_eq_id(sa, ba, y1, sb, bb, y2)
        }
        (LevelRow::Param(x), LevelRow::Param(y)) | (LevelRow::MVar(x), LevelRow::MVar(y)) => {
            name_opt_eq(sa, ba, x, sb, bb, y)
        }
        _ => false,
    }
}

fn eq_structural_id(
    sa: &Store,
    ba: Option<&Store>,
    a: ExprId,
    sb: &Store,
    bb: Option<&Store>,
    b: ExprId,
) -> bool {
    match (sa.expr_node(ba, a), sb.expr_node(bb, b)) {
        (Node::BVar { idx: x }, Node::BVar { idx: y }) => x == y,
        (Node::FVar { id: x }, Node::FVar { id: y }) => name_opt_eq(sa, ba, x, sb, bb, y),
        (Node::Sort { level: x }, Node::Sort { level: y }) => level_eq_id(sa, ba, x, sb, bb, y),
        (
            Node::Const {
                name: n1,
                levels: l1,
            },
            Node::Const {
                name: n2,
                levels: l2,
            },
        ) => {
            let ls1 = sa.level_list_at(ba, l1);
            let ls2 = sb.level_list_at(bb, l2);
            name_opt_eq(sa, ba, n1, sb, bb, n2)
                && ls1.len() == ls2.len()
                && ls1
                    .iter()
                    .zip(ls2)
                    .all(|(&x, &y)| level_eq_id(sa, ba, x, sb, bb, y))
        }
        (Node::App { f: f1, arg: a1 }, Node::App { f: f2, arg: a2 }) => {
            eq_structural_id(sa, ba, f1, sb, bb, f2) && eq_structural_id(sa, ba, a1, sb, bb, a2)
        }
        (
            Node::Lam {
                binder_type: t1,
                body: b1,
                ..
            },
            Node::Lam {
                binder_type: t2,
                body: b2,
                ..
            },
        )
        | (
            Node::Forall {
                binder_type: t1,
                body: b1,
                ..
            },
            Node::Forall {
                binder_type: t2,
                body: b2,
                ..
            },
        ) => eq_structural_id(sa, ba, t1, sb, bb, t2) && eq_structural_id(sa, ba, b1, sb, bb, b2),
        (Node::LitNat { v: x }, Node::LitNat { v: y }) => sa.nat_at(ba, x) == sb.nat_at(bb, y),
        (Node::LitStr { v: x }, Node::LitStr { v: y }) => sa.str_at(ba, x) == sb.str_at(bb, y),
        _ => false,
    }
}

/// Collect every binder name appearing in `e` (tests only).
fn binder_names_id(st: &Store, base: Option<&Store>, e: ExprId, out: &mut Vec<String>) {
    match st.expr_node(base, e) {
        Node::Lam {
            binder_name,
            binder_type,
            body,
            ..
        }
        | Node::Forall {
            binder_name,
            binder_type,
            body,
            ..
        } => {
            out.push(st.to_name(base, binder_name).to_string());
            binder_names_id(st, base, binder_type, out);
            binder_names_id(st, base, body, out);
        }
        Node::App { f, arg } => {
            binder_names_id(st, base, f, out);
            binder_names_id(st, base, arg, out);
        }
        _ => {}
    }
}

fn assert_no_nested_leak(scratch: &Store, base: &Store, extra: &HashMap<NameId, ConstantInfo>) {
    for &id in extra.keys() {
        let n = scratch.to_name(Some(base), Some(id));
        assert!(
            !name_has_component(&n, "_nested"),
            "aux `_nested` name leaked into final env: {n}"
        );
    }
}

// ---------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------

#[test]
fn admits_nat_and_regenerates_m1a_shapes() {
    let env = Environment::default();
    let extra = HashMap::new();
    let mut scratch = Store::scratch();
    let base = env.view().store;
    let added = admit(&mut scratch, &env, &extra, nat_decl()).expect("Nat admits");

    let nat = as_induct(find(&scratch, base, &added, &nm("Nat")));
    assert!(nat.is_rec, "Nat is recursive");
    assert!(!nat.is_reflexive);
    assert_eq!(nat.num_params, Nat::from(0));
    assert_eq!(nat.num_indices, Nat::from(0));
    assert_eq!(nat.num_nested, Nat::from(0));
    assert_eq!(to_names(&scratch, base, &nat.all), vec![nm("Nat")]);
    assert_eq!(
        to_names(&scratch, base, &nat.ctors),
        vec![nm2("Nat", "zero"), nm2("Nat", "succ")]
    );

    let zero = as_ctor(find(&scratch, base, &added, &nm2("Nat", "zero")));
    assert_eq!(zero.cidx, Nat::from(0));
    assert_eq!(zero.num_fields, Nat::from(0));
    let succ = as_ctor(find(&scratch, base, &added, &nm2("Nat", "succ")));
    assert_eq!(succ.cidx, Nat::from(1));
    assert_eq!(succ.num_fields, Nat::from(1));

    let got = as_rec(find(&scratch, base, &added, &nm2("Nat", "rec")));
    let mini_env = mini::env();
    let expected_ci = env_const(&mini_env, &nm2("Nat", "rec"));
    let expected = as_rec(&expected_ci);
    let mini_base = mini_env.view().store;
    assert!(!got.k, "Nat.rec is not K-like");
    assert_eq!(got.num_params, Nat::from(0));
    assert_eq!(got.num_indices, Nat::from(0));
    assert_eq!(got.num_motives, Nat::from(1));
    assert_eq!(got.num_minors, Nat::from(2));
    assert_eq!(
        to_names(&scratch, base, &got.val.level_params),
        vec![nm("u")]
    );
    assert_eq!(to_names(&scratch, base, &got.all), vec![nm("Nat")]);
    assert_eq!(got.rules.len(), 2);
    for (gr, er) in got.rules.iter().zip(expected.rules.iter()) {
        assert_eq!(
            scratch.to_name(Some(base), Some(gr.ctor)),
            mini_base.to_name(None, Some(er.ctor))
        );
        assert_eq!(gr.nfields, er.nfields);
        assert!(
            eq_structural_id(&scratch, Some(base), gr.rhs, mini_base, None, er.rhs),
            "rule rhs for {} matches",
            scratch.to_name(Some(base), Some(gr.ctor))
        );
    }
    assert!(
        eq_structural_id(
            &scratch,
            Some(base),
            got.val.ty,
            mini_base,
            None,
            expected.val.ty
        ),
        "Nat.rec type matches structurally"
    );
    let Node::Forall { binder_info, .. } = scratch.expr_node(Some(base), got.val.ty) else {
        panic!("recursor type is a Pi");
    };
    assert_eq!(binder_info, BinderInfo::Implicit);
    let mut succ_rhs_binders = Vec::new();
    binder_names_id(
        &scratch,
        Some(base),
        got.rules[1].rhs,
        &mut succ_rhs_binders,
    );
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
    let env = Environment::default();
    let extra = HashMap::new();
    let mut scratch = Store::scratch();
    let base = env.view().store;
    let added = admit(&mut scratch, &env, &extra, d).expect("Prod admits");

    let prod = as_induct(find(&scratch, base, &added, &nm("Prod")));
    assert_eq!(prod.num_params, Nat::from(2));
    assert_eq!(prod.num_indices, Nat::from(0));
    assert_eq!(prod.ctors.len(), 1);
    assert!(!prod.is_rec);

    let mk = as_ctor(find(&scratch, base, &added, &nm2("Prod", "mk")));
    assert_eq!(mk.num_params, Nat::from(2));
    assert_eq!(mk.num_fields, Nat::from(2));

    let rec = as_rec(find(&scratch, base, &added, &nm2("Prod", "rec")));
    assert_eq!(rec.num_minors, Nat::from(1));
    assert_eq!(rec.num_motives, Nat::from(1));
    assert_eq!(rec.num_params, Nat::from(2));
    assert_eq!(rec.num_indices, Nat::from(0));
    assert!(!rec.k);
}

#[test]
fn admits_eq_with_k() {
    let env = Environment::default();
    let extra = HashMap::new();
    let mut scratch = Store::scratch();
    let base = env.view().store;
    let added = admit(&mut scratch, &env, &extra, eq_decl()).expect("Eq admits");

    let eq = as_induct(find(&scratch, base, &added, &nm("Eq")));
    assert_eq!(eq.num_params, Nat::from(2));
    assert_eq!(eq.num_indices, Nat::from(1));

    let rec = as_rec(find(&scratch, base, &added, &nm2("Eq", "rec")));
    assert!(rec.k, "Eq.rec is K-like");
    assert_eq!(rec.num_minors, Nat::from(1));
    assert_eq!(rec.num_motives, Nat::from(1));
    assert_eq!(rec.num_params, Nat::from(2));
    assert_eq!(rec.num_indices, Nat::from(1));
}

#[test]
fn large_elim_singleton() {
    let env = Environment::default();
    let extra = HashMap::new();
    let mut scratch = Store::scratch();
    let base = env.view().store;
    let added = admit(&mut scratch, &env, &extra, eq_decl()).expect("Eq admits");
    let rec = as_rec(find(&scratch, base, &added, &nm2("Eq", "rec")));
    assert_eq!(
        to_names(&scratch, base, &rec.val.level_params),
        vec![nm("u"), nm("u_1")]
    );
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
    let env = Environment::default();
    let extra = HashMap::new();
    let mut scratch = Store::scratch();
    let base = env.view().store;
    let added = admit(&mut scratch, &env, &extra, d).expect("Or admits");

    let or_ind = as_induct(find(&scratch, base, &added, &nm("Or")));
    assert!(!or_ind.is_rec);
    let rec = as_rec(find(&scratch, base, &added, &nm2("Or", "rec")));
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
    let env = Environment::default();
    let extra = HashMap::new();
    let mut scratch = Store::scratch();
    let base = env.view().store;
    let added = admit(&mut scratch, &env, &extra, d).expect("mutual A/B admits");

    let a = as_induct(find(&scratch, base, &added, &nm("A")));
    let b = as_induct(find(&scratch, base, &added, &nm("B")));
    assert_eq!(to_names(&scratch, base, &a.all), vec![nm("A"), nm("B")]);
    assert_eq!(to_names(&scratch, base, &b.all), vec![nm("A"), nm("B")]);
    assert!(a.is_rec && b.is_rec, "mutual block is recursive");

    let a_rec = as_rec(find(&scratch, base, &added, &nm2("A", "rec")));
    let b_rec = as_rec(find(&scratch, base, &added, &nm2("B", "rec")));
    assert_eq!(a_rec.num_motives, Nat::from(2));
    assert_eq!(b_rec.num_motives, Nat::from(2));
    assert_eq!(a_rec.num_minors, Nat::from(2));
    assert_eq!(b_rec.num_minors, Nat::from(2));
    assert_eq!(to_names(&scratch, base, &a_rec.all), vec![nm("A"), nm("B")]);
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
    let env = Environment::default();
    let extra = HashMap::new();
    let mut scratch = Store::scratch();
    let err = admit(&mut scratch, &env, &extra, d).unwrap_err();
    match err {
        crate::KernelError::InvalidInductive { what, .. } => assert_eq!(what, "positivity"),
        other => panic!("expected positivity error, got {other:?}"),
    }
    // Rollback: nothing was ever inserted into `extra`.
    assert!(extra.is_empty());
}

#[test]
fn rejects_wrong_codomain() {
    let mk_ty = sort_n(1);
    let d = decl(
        vec![],
        0,
        vec![ind("T", mini::type1(), vec![(nm2("T", "mk"), mk_ty)])],
    );
    let env = Environment::default();
    let extra = HashMap::new();
    let mut scratch = Store::scratch();
    let err = admit(&mut scratch, &env, &extra, d).unwrap_err();
    match err {
        crate::KernelError::InvalidInductive { what, .. } => {
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
    let env = Environment::default();
    let extra = HashMap::new();
    let mut scratch = Store::scratch();
    let err = admit(&mut scratch, &env, &extra, d).unwrap_err();
    match err {
        crate::KernelError::InvalidInductive { what, .. } => {
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
    let env = Environment::default();
    let extra = HashMap::new();
    let mut scratch = Store::scratch();
    let err = admit(&mut scratch, &env, &extra, d).unwrap_err();
    match err {
        crate::KernelError::InvalidInductive { what, .. } => {
            assert_eq!(what, "parameters must match")
        }
        other => panic!("expected parameter-mismatch error, got {other:?}"),
    }
    assert!(extra.is_empty(), "rollback: nothing admitted");
}

#[test]
fn rejects_empty_inductive_block() {
    // A crafted `Inductive` with no types must be rejected (never
    // panic): the pipeline indexes `types[0]` in
    // `elim_only_at_universe_zero`/`init_k_target`, so the guard at the
    // head of `run` must fire first. Also asserts the environment is
    // unchanged: `env` here is a REAL `Environment` (built via
    // `from_modules`, matching `mini::env()`'s own "trusted, unchecked
    // base" pattern) holding a `marker` axiom untouched by this test's
    // (never even attempted) mutation of `env` itself.
    let env = Environment::from_modules([vec![axiom("marker", sort_n(1))]]).unwrap();
    let extra = HashMap::new();
    let before = env.len();
    let mut scratch = Store::scratch();
    let err = admit(&mut scratch, &env, &extra, decl(vec![], 0, vec![])).unwrap_err();
    match err {
        crate::KernelError::InvalidInductive { name, what } => {
            assert_eq!(what, "empty inductive block");
            assert!(matches!(name.as_ref(), Name::Anonymous));
        }
        other => panic!("expected empty-inductive-block error, got {other:?}"),
    }
    assert_eq!(env.len(), before, "environment unchanged on rejection");
    let marker_id = env_name_id(&mut scratch, &env, &nm("marker"));
    assert!(env.get(marker_id).is_some());
}

#[test]
fn iota_now_reduces_declared_recursor() {
    // Admit Nat, then reduce `Nat.rec.{1} motive z s (Nat.succ k)` using
    // the REGENERATED recursor + rules — ties this file's iota reduction
    // to the rules produced here. `z`/`s`/`k` are bridged directly into
    // `extra` (no checking — the test's subject is the recursor's iota
    // reduction, not axiom-checking, matching the pre-migration file's
    // own ordering: `nat_decl()` first, then the axioms).
    let env = Environment::default();
    let mut extra = HashMap::new();
    let mut scratch = Store::scratch();
    admit_into(&mut scratch, &env, &mut extra, nat_decl()).expect("Nat admits");
    bridge_into(&mut scratch, &env, &mut extra, &axiom("z", mini::nat()));
    bridge_into(
        &mut scratch,
        &env,
        &mut extra,
        &axiom(
            "s",
            mini::pi("n", mini::nat(), mini::pi("ih", mini::nat(), mini::nat())),
        ),
    );
    bridge_into(&mut scratch, &env, &mut extra, &axiom("k", mini::nat()));

    // motive := fun _ : Nat => Nat  (a `Nat → Sort 1` motive ⇒ u := 1).
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

    let base = env.view().store;
    let major_id = scratch.intern_expr(Some(base), &major).unwrap();
    let view = EnvView {
        consts: env.view().consts,
        extra: Some(&extra),
        quot_initialized: env.quot_initialized(),
        store: base,
    };
    let mut tc = TypeChecker::new(view, &mut scratch);
    let reduced = tc.whnf(major_id).expect("iota reduces");
    // Expect `s k (Nat.rec.{1} motive z s k)`: head is `s` with 2 args.
    let head = get_app_fn(&scratch, Some(base), reduced);
    match scratch.expr_node(Some(base), head) {
        Node::Const { name, .. } => {
            assert_eq!(
                scratch.to_name(Some(base), name),
                nm("s"),
                "reduced head is the succ minor `s`"
            );
        }
        other => panic!("reduced head is not a Const, got {other:?}"),
    }
    assert_eq!(get_app_num_args(&scratch, Some(base), reduced), 2);
}

#[test]
fn admits_nested_via_list() {
    let env = mini::env();
    let extra = HashMap::new();
    let mut scratch = Store::scratch();
    let base = env.view().store;
    let added = admit(&mut scratch, &env, &extra, tree_decl()).expect("Tree admits via nesting");

    let tree = as_induct(find(&scratch, base, &added, &nm("Tree")));
    assert_eq!(tree.num_nested, Nat::from(1), "one aux nested type (List)");
    assert_eq!(
        to_names(&scratch, base, &tree.all),
        vec![nm("Tree")],
        "all restored to the real block"
    );
    assert_eq!(
        to_names(&scratch, base, &tree.ctors),
        vec![nm2("Tree", "node")]
    );
    assert!(tree.is_rec, "Tree is recursive");

    let node = as_ctor(find(&scratch, base, &added, &nm2("Tree", "node")));
    assert_eq!(node.num_params, Nat::from(0));
    assert_eq!(node.num_fields, Nat::from(1));
    let list0_tree = mini::app(
        mini::cstn(nm("List"), vec![Arc::new(Level::Zero)]),
        mini::cstn(nm("Tree"), vec![]),
    );
    let expected_node_ty = mini::pi("a", list0_tree, mini::cstn(nm("Tree"), vec![]));
    let expected_node_ty_id = scratch.intern_expr(Some(base), &expected_node_ty).unwrap();
    assert!(
        eq_structural_id(
            &scratch,
            Some(base),
            node.val.ty,
            &scratch,
            Some(base),
            expected_node_ty_id
        ),
        "Tree.node type restored to `List.{{0}} Tree → Tree`, got {:?}",
        node.val.ty
    );

    let rec = as_rec(find(&scratch, base, &added, &nm2("Tree", "rec")));
    assert_eq!(rec.num_motives, Nat::from(2), "motive for Tree + aux List");
    assert_eq!(rec.num_minors, Nat::from(3), "node + nil + cons minors");
    assert_eq!(rec.num_params, Nat::from(0));
    assert_eq!(rec.num_indices, Nat::from(0));
    assert_eq!(
        to_names(&scratch, base, &rec.all),
        vec![nm("Tree")],
        "recursor all = real block"
    );
    assert_eq!(
        to_names(&scratch, base, &rec.val.level_params),
        vec![nm("u")]
    );
    assert_eq!(rec.rules.len(), 1);
    assert_eq!(
        scratch.to_name(Some(base), Some(rec.rules[0].ctor)),
        nm2("Tree", "node")
    );
    assert_eq!(rec.rules[0].nfields, Nat::from(1));

    let rec1 = as_rec(find(&scratch, base, &added, &nm2("Tree", "rec_1")));
    assert_eq!(rec1.num_motives, Nat::from(2));
    assert_eq!(to_names(&scratch, base, &rec1.all), vec![nm("Tree")]);
    assert_eq!(rec1.rules.len(), 2);
    assert_eq!(
        scratch.to_name(Some(base), Some(rec1.rules[0].ctor)),
        nm2("List", "nil")
    );
    assert_eq!(rec1.rules[0].nfields, Nat::from(0));
    assert_eq!(
        scratch.to_name(Some(base), Some(rec1.rules[1].ctor)),
        nm2("List", "cons")
    );
    assert_eq!(rec1.rules[1].nfields, Nat::from(2));

    let mut extra_map = HashMap::new();
    for ci in &added {
        extra_map.insert(ci.name(), ci.clone());
    }
    assert_no_nested_leak(&scratch, base, &extra_map);
}

#[test]
fn nested_iota_reduces() {
    let env = mini::env();
    let mut extra = HashMap::new();
    let mut scratch = Store::scratch();
    admit_into(&mut scratch, &env, &mut extra, tree_decl()).expect("Tree admits");
    // Opaque stand-ins for the recursor's motives/minors + a List Tree
    // value; whnf's iota is untyped, so any well-typed constants suffice.
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
        bridge_into(&mut scratch, &env, &mut extra, &axiom(n, ty));
    }
    bridge_into(&mut scratch, &env, &mut extra, &axiom("lst", list0_tree));

    // Tree.rec.{1} m1 m2 node_min nil_min cons_min (Tree.node lst).
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

    let base = env.view().store;
    let major_id = scratch.intern_expr(Some(base), &major).unwrap();
    let view = EnvView {
        consts: env.view().consts,
        extra: Some(&extra),
        quot_initialized: env.quot_initialized(),
        store: base,
    };
    let mut tc = TypeChecker::new(view, &mut scratch);
    let reduced = tc.whnf(major_id).expect("nested iota reduces");
    // RHS of the Tree.node rule is `node_min lst (Tree.rec_1 … lst)`.
    let head = get_app_fn(&scratch, Some(base), reduced);
    match scratch.expr_node(Some(base), head) {
        Node::Const { name, .. } => {
            assert_eq!(
                scratch.to_name(Some(base), name),
                nm("node_min"),
                "reduced head is the node minor"
            );
        }
        other => panic!("reduced head is not a Const, got {other:?}"),
    }
    assert_eq!(get_app_num_args(&scratch, Some(base), reduced), 2);
}

#[test]
fn rejects_nested_positivity_violation() {
    let env = mini::env();
    let extra = HashMap::new();
    let mut scratch = Store::scratch();
    let t = mini::cstn(nm("T"), vec![]);
    let t_to_t = mini::pi("x", Arc::clone(&t), Arc::clone(&t));
    let list_tt = mini::app(mini::cstn(nm("List"), vec![Arc::new(Level::Zero)]), t_to_t);
    let mk_ty = mini::pi("a", list_tt, t);
    let d = decl(
        vec![],
        0,
        vec![ind("T", mini::type1(), vec![(nm2("T", "mk"), mk_ty)])],
    );
    let err = admit(&mut scratch, &env, &extra, d).unwrap_err();
    match err {
        crate::KernelError::InvalidInductive { what, .. } => assert_eq!(what, "positivity"),
        other => panic!("expected positivity error, got {other:?}"),
    }
    assert!(
        extra.is_empty(),
        "rollback: nothing admitted, no aux leak possible"
    );
}

#[test]
fn stdlib_shape_smoke() {
    let env = mini::env();
    let mut extra = HashMap::new();
    let mut scratch = Store::scratch();
    admit_into(&mut scratch, &env, &mut extra, array_decl()).expect("Array admits");

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
    let base = env.view().store;
    let added =
        admit(&mut scratch, &env, &extra, d).expect("Stx admits via double nesting (Array + List)");

    let stx = as_induct(find(&scratch, base, &added, &nm("Stx")));
    assert_eq!(stx.num_nested, Nat::from(2));
    assert_eq!(to_names(&scratch, base, &stx.all), vec![nm("Stx")]);
    assert_eq!(
        to_names(&scratch, base, &stx.ctors),
        vec![nm2("Stx", "node"), nm2("Stx", "leaf")]
    );

    let rec = as_rec(find(&scratch, base, &added, &nm2("Stx", "rec")));
    assert_eq!(rec.num_motives, Nat::from(3), "Stx + Array-aux + List-aux");
    assert_eq!(rec.num_minors, Nat::from(5), "node+leaf + mk + nil+cons");
    assert_eq!(to_names(&scratch, base, &rec.all), vec![nm("Stx")]);

    // The two restored aux recursors are present under real names
    // (`find` panics on a miss, so reaching the next line proves it).
    find(&scratch, base, &added, &nm2("Stx", "rec_1"));
    find(&scratch, base, &added, &nm2("Stx", "rec_2"));

    for ci in &added {
        extra.insert(ci.name(), ci.clone());
    }
    assert_no_nested_leak(&scratch, base, &extra);
}
