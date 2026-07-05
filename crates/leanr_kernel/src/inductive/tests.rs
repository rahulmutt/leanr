//! Tests for inductive admission + recursor generation (Task 9).
//!
//! Each test hand-builds a `Declaration::Inductive`, admits it into a
//! fresh environment via `add_decl`, and compares the RESULTING
//! `ConstantInfo`s structurally against hand-transcribed oracle output
//! (`#print` under leanprover/lean4:v4.32.0-rc1). Where the Task 7
//! `testenv` already carries a matching transcription (Nat.rec's rule
//! RHSs), we reuse it as the expected value.

use std::sync::Arc;

use crate::testenv::mini;
use crate::testenv::{nm, nm2};
use crate::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, Declaration, Environment, Expr, ExprNode,
    InductiveType, Level, Name, Nat, RecGuard,
};

// ---- expr helpers -------------------------------------------------------

fn level_eq(a: &Arc<Level>, b: &Arc<Level>) -> bool {
    Level::structural_eq(a, b, &mut RecGuard::new()).unwrap()
}

/// Structural (de-Bruijn) equality ignoring binder *names* and
/// binder_info (small closed terms → bounded recursion; tests only).
///
/// Two cosmetic differences between the regenerated output and the Task
/// 7 `testenv` transcriptions make a byte-exact term compare impossible,
/// even though the regenerated terms are the ones that match REAL Lean
/// (verified below via targeted assertions):
///   - the transcriptions mark every binder `Default`, whereas the
///     regenerated recursor *type* correctly marks the motive `Implicit`
///     (ported `infer_implicit`);
///   - the transcriptions name the induction-hypothesis binder `ih`,
///     whereas the oracle (and this port) names it `<field>_ih`
///     (`#print Nat.rec` shows `n_ih : motive n`).
///
/// Everything else — the de-Bruijn skeleton, every `Const`, level, and
/// literal — must still match exactly.
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

/// Collect every binder name appearing in `e` (tests only).
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

fn induct(env: &Environment, name: &Arc<Name>) -> crate::InductiveVal {
    match env.get(name) {
        Some(ConstantInfo::Induct(v)) => v.clone(),
        other => panic!("expected inductive {name}, got {other:?}"),
    }
}

fn ctor(env: &Environment, name: &Arc<Name>) -> crate::ConstructorVal {
    match env.get(name) {
        Some(ConstantInfo::Ctor(v)) => v.clone(),
        other => panic!("expected ctor {name}, got {other:?}"),
    }
}

fn recursor(env: &Environment, name: &Arc<Name>) -> crate::RecursorVal {
    match env.get(name) {
        Some(ConstantInfo::Rec(v)) => v.clone(),
        other => panic!("expected recursor {name}, got {other:?}"),
    }
}

// ---- Declaration builders for the test inductives -----------------------

/// Nat: `inductive Nat where | zero | succ (n : Nat)` — exactly the
/// testenv shape.
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

// ---- Tests --------------------------------------------------------------

#[test]
fn admits_nat_and_regenerates_m1a_shapes() {
    let mut env = Environment::default();
    env.add_decl(nat_decl()).expect("Nat admits");

    // InductiveVal.
    let nat = induct(&env, &nm("Nat"));
    assert!(nat.is_rec, "Nat is recursive");
    assert!(!nat.is_reflexive);
    assert_eq!(nat.num_params, Nat::from(0));
    assert_eq!(nat.num_indices, Nat::from(0));
    assert_eq!(nat.num_nested, Nat::from(0));
    assert_eq!(nat.all, vec![nm("Nat")]);
    assert_eq!(nat.ctors, vec![nm2("Nat", "zero"), nm2("Nat", "succ")]);

    // ConstructorVals.
    let zero = ctor(&env, &nm2("Nat", "zero"));
    assert_eq!(zero.cidx, Nat::from(0));
    assert_eq!(zero.num_fields, Nat::from(0));
    let succ = ctor(&env, &nm2("Nat", "succ"));
    assert_eq!(succ.cidx, Nat::from(1));
    assert_eq!(succ.num_fields, Nat::from(1));

    // RecursorVal — compare against the testenv transcription.
    let got = recursor(&env, &nm2("Nat", "rec"));
    let expected = recursor(&mini::env(), &nm2("Nat", "rec"));
    assert!(!got.k, "Nat.rec is not K-like");
    assert_eq!(got.num_params, Nat::from(0));
    assert_eq!(got.num_indices, Nat::from(0));
    assert_eq!(got.num_motives, Nat::from(1));
    assert_eq!(got.num_minors, Nat::from(2));
    // level params: [u] ++ lparams, [u].
    assert_eq!(got.val.level_params, vec![nm("u")]);
    // recursor's `all` is the inductive-type names (NOT the rec names —
    // the testenv transcription's `[Nat.rec]` is a Task-7 error).
    assert_eq!(got.all, vec![nm("Nat")]);
    // rules: same order, ctors, nfields, and de-Bruijn RHS skeleton.
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
    // recursor type matches the transcription's de-Bruijn skeleton.
    assert!(
        eq_structural(&got.val.ty, &expected.val.ty),
        "Nat.rec type matches structurally"
    );
    // Targeted checks that the regenerated output matches REAL Lean where
    // the testenv transcription is simplified:
    //   - the motive binder became Implicit (via infer_implicit),
    let ExprNode::ForallE { binder_info, .. } = got.val.ty.node() else {
        panic!("recursor type is a Pi");
    };
    assert_eq!(*binder_info, BinderInfo::Implicit);
    //   - the induction hypothesis binder is named `n_ih`, not `ih`.
    let succ_rhs_binders = binder_names(&got.rules[1].rhs);
    assert!(
        succ_rhs_binders.iter().any(|n| n == "n_ih"),
        "IH binder is `n_ih`, got {succ_rhs_binders:?}"
    );
}

#[test]
fn admits_prod_structure_like() {
    // Monomorphic Prod : Type → Type → Type, one ctor, no indices.
    let prod_ty = mini::pi(
        "α",
        mini::type1(),
        mini::pi("β", mini::type1(), mini::type1()),
    );
    // Prod.mk : Π (α β : Type) (fst : α) (snd : β), Prod α β
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
    let mut env = Environment::default();
    env.add_decl(decl(
        vec![],
        2,
        vec![ind("Prod", prod_ty, vec![(nm2("Prod", "mk"), mk_ty)])],
    ))
    .expect("Prod admits");

    let prod = induct(&env, &nm("Prod"));
    assert_eq!(prod.num_params, Nat::from(2));
    assert_eq!(prod.num_indices, Nat::from(0));
    assert_eq!(prod.ctors.len(), 1);
    assert!(!prod.is_rec);

    let mk = ctor(&env, &nm2("Prod", "mk"));
    assert_eq!(mk.num_params, Nat::from(2));
    assert_eq!(mk.num_fields, Nat::from(2));

    let rec = recursor(&env, &nm2("Prod", "rec"));
    assert_eq!(rec.num_minors, Nat::from(1));
    assert_eq!(rec.num_motives, Nat::from(1));
    assert_eq!(rec.num_params, Nat::from(2));
    assert_eq!(rec.num_indices, Nat::from(0));
    assert!(!rec.k);
}

/// Eq: `inductive Eq {α : Sort u_1} (a : α) : α → Prop | refl : Eq a a`
/// — the canonical K-like, large-eliminating singleton in Prop.
fn eq_decl() -> Declaration {
    // Eq.{u_1} : Π (α : Sort u_1), α → α → Prop
    let eq_ty = mini::pi(
        "α",
        mini::sort_param("u_1"),
        mini::pi(
            "a",
            mini::bvar(0),
            mini::pi("b", mini::bvar(1), mini::sort0()),
        ),
    );
    // Eq.refl.{u_1} : Π (α : Sort u_1) (a : α), @Eq α a a
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
    let mut env = Environment::default();
    env.add_decl(eq_decl()).expect("Eq admits");

    let eq = induct(&env, &nm("Eq"));
    assert_eq!(eq.num_params, Nat::from(2));
    assert_eq!(eq.num_indices, Nat::from(1));

    let rec = recursor(&env, &nm2("Eq", "rec"));
    assert!(rec.k, "Eq.rec is K-like");
    assert_eq!(rec.num_minors, Nat::from(1));
    assert_eq!(rec.num_motives, Nat::from(1));
    assert_eq!(rec.num_params, Nat::from(2));
    assert_eq!(rec.num_indices, Nat::from(1));
}

#[test]
fn large_elim_singleton() {
    // Eq is a Prop-valued singleton whose recursor nevertheless
    // large-eliminates: its motive lives at a fresh universe `u`, so the
    // recursor's level params are [u, u_1] (u prepended).
    let mut env = Environment::default();
    env.add_decl(eq_decl()).expect("Eq admits");
    let rec = recursor(&env, &nm2("Eq", "rec"));
    assert_eq!(rec.val.level_params, vec![nm("u"), nm("u_1")]);
}

#[test]
fn prop_only_elim_small() {
    // Or : Prop → Prop → Prop with two ctors ⇒ eliminates only into Prop.
    let or = mini::cstn(nm("Or"), vec![]);
    let or_ty = mini::pi(
        "a",
        mini::sort0(),
        mini::pi("b", mini::sort0(), mini::sort0()),
    );
    // Or.inl : Π (a b : Prop) (h : a), @Or a b
    let inl_ty = mini::pi(
        "a",
        mini::sort0(),
        mini::pi(
            "b",
            mini::sort0(),
            mini::pi(
                "h",
                mini::bvar(1), // a
                mini::appn(Arc::clone(&or), vec![mini::bvar(2), mini::bvar(1)]),
            ),
        ),
    );
    // Or.inr : Π (a b : Prop) (h : b), @Or a b
    let inr_ty = mini::pi(
        "a",
        mini::sort0(),
        mini::pi(
            "b",
            mini::sort0(),
            mini::pi(
                "h",
                mini::bvar(0), // b
                mini::appn(or, vec![mini::bvar(2), mini::bvar(1)]),
            ),
        ),
    );
    let mut env = Environment::default();
    env.add_decl(decl(
        vec![],
        2,
        vec![ind(
            "Or",
            or_ty,
            vec![(nm2("Or", "inl"), inl_ty), (nm2("Or", "inr"), inr_ty)],
        )],
    ))
    .expect("Or admits");

    let or_ind = induct(&env, &nm("Or"));
    assert!(!or_ind.is_rec);
    let rec = recursor(&env, &nm2("Or", "rec"));
    // small elim: elim level is 0, so NO fresh universe param prepended.
    assert!(rec.val.level_params.is_empty(), "Or.rec small-eliminates");
    assert_eq!(rec.num_minors, Nat::from(2));
    assert_eq!(rec.num_motives, Nat::from(1));
    assert!(!rec.k);
}

#[test]
fn admits_mutual_pair() {
    // Mutually recursive A/B in Type:
    //   inductive A | mk : B → A
    //   inductive B | mk : A → B
    let ca = mini::cstn(nm("A"), vec![]);
    let cb = mini::cstn(nm("B"), vec![]);
    let a_mk = mini::pi("b", Arc::clone(&cb), Arc::clone(&ca)); // B → A
    let b_mk = mini::pi("a", Arc::clone(&ca), Arc::clone(&cb)); // A → B
    let mut env = Environment::default();
    env.add_decl(decl(
        vec![],
        0,
        vec![
            ind("A", mini::type1(), vec![(nm2("A", "mk"), a_mk)]),
            ind("B", mini::type1(), vec![(nm2("B", "mk"), b_mk)]),
        ],
    ))
    .expect("mutual A/B admits");

    let a = induct(&env, &nm("A"));
    let b = induct(&env, &nm("B"));
    assert_eq!(a.all, vec![nm("A"), nm("B")]);
    assert_eq!(b.all, vec![nm("A"), nm("B")]);
    assert!(a.is_rec && b.is_rec, "mutual block is recursive");

    let a_rec = recursor(&env, &nm2("A", "rec"));
    let b_rec = recursor(&env, &nm2("B", "rec"));
    // Both recursors take a motive for EACH type in the block.
    assert_eq!(a_rec.num_motives, Nat::from(2));
    assert_eq!(b_rec.num_motives, Nat::from(2));
    // One minor per constructor across the whole block.
    assert_eq!(a_rec.num_minors, Nat::from(2));
    assert_eq!(b_rec.num_minors, Nat::from(2));
    // recursor `all` is the inductive-type names, listing both types.
    assert_eq!(a_rec.all, vec![nm("A"), nm("B")]);
}

#[test]
fn rejects_positivity_violation() {
    // T : Type with a ctor field of type ((T → T) → T): a non-positive
    // occurrence of T in the domain (T → T).
    let ct = mini::cstn(nm("T"), vec![]);
    let t_to_t = mini::pi("x", Arc::clone(&ct), Arc::clone(&ct)); // T → T
    let field = mini::pi("h", t_to_t, Arc::clone(&ct)); // (T → T) → T
    let mk_ty = mini::pi("f", field, ct); // ((T → T) → T) → T
    let mut env = Environment::default();
    let err = env
        .add_decl(decl(
            vec![],
            0,
            vec![ind("T", mini::type1(), vec![(nm2("T", "mk"), mk_ty)])],
        ))
        .unwrap_err();
    match err {
        crate::KernelError::InvalidInductive { what, .. } => assert_eq!(what, "positivity"),
        other => panic!("expected positivity error, got {other:?}"),
    }
    // rollback: nothing admitted.
    assert!(env.get(&nm("T")).is_none());
    assert!(env.get(&nm2("T", "mk")).is_none());
}

#[test]
fn rejects_wrong_codomain() {
    // A ctor whose result type is not an application of the inductive.
    let mk_ty = sort_n(1); // `mk : Sort 1`, codomain not `T ...`
    let mut env = Environment::default();
    let err = env
        .add_decl(decl(
            vec![],
            0,
            vec![ind("T", mini::type1(), vec![(nm2("T", "mk"), mk_ty)])],
        ))
        .unwrap_err();
    match err {
        crate::KernelError::InvalidInductive { what, .. } => {
            assert_eq!(what, "invalid return type")
        }
        other => panic!("expected invalid-return-type error, got {other:?}"),
    }
}

#[test]
fn rejects_universe_too_small() {
    // NOTE (oracle over brief): the brief's literal example is "Sort 0
    // packing a Type", but a Prop-valued inductive (result level 0) is
    // exempt from the universe bound (inductive.cpp:439 `|| is_zero(
    // m_result_level)`), so that example would ADMIT. We therefore use a
    // non-Prop type: T : Type 0 with a field of type `Type 1`, whose
    // type `Sort 3` exceeds the inductive's level (1).
    let field_ty = sort_n(2); // Type 1 = Sort 2
    let mk_ty = mini::pi("α", field_ty, mini::cstn(nm("T"), vec![]));
    let mut env = Environment::default();
    let err = env
        .add_decl(decl(
            vec![],
            0,
            vec![ind("T", mini::type1(), vec![(nm2("T", "mk"), mk_ty)])],
        ))
        .unwrap_err();
    match err {
        crate::KernelError::InvalidInductive { what, .. } => assert_eq!(what, "universe too small"),
        other => panic!("expected universe-too-small error, got {other:?}"),
    }
}

#[test]
fn rejects_param_mismatch_across_block() {
    // Two-type block with nparams=1 but incompatible parameter types
    // (Type 1 vs Prop).
    let a_ty = mini::pi("α", mini::type1(), mini::type1());
    let b_ty = mini::pi("α", mini::sort0(), mini::type1());
    // ctors are never reached (the param mismatch is caught in
    // check_inductive_types) but must be structurally present.
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
    let mut env = Environment::default();
    let err = env
        .add_decl(decl(
            vec![],
            1,
            vec![
                ind("A", a_ty, vec![(nm2("A", "mk"), a_mk)]),
                ind("B", b_ty, vec![(nm2("B", "mk"), b_mk)]),
            ],
        ))
        .unwrap_err();
    match err {
        crate::KernelError::InvalidInductive { what, .. } => {
            assert_eq!(what, "parameters must match")
        }
        other => panic!("expected parameter-mismatch error, got {other:?}"),
    }
    // rollback: A (added before the mismatch on B) is gone.
    assert!(env.get(&nm("A")).is_none());
}

#[test]
fn rejects_empty_inductive_block() {
    // A crafted Declaration::Inductive with no types must be rejected
    // (never panic): the pipeline indexes `ind_types[0]` in
    // elim_only_at_universe_zero / init_k_target, so the guard at the
    // head of `run` must fire first. Also asserts the env is unchanged.
    let mut env = Environment::default();
    env.add_decl(axiom("marker", sort_n(1))).unwrap();
    let before = env.len();
    let err = env.add_decl(decl(vec![], 0, vec![])).unwrap_err();
    match err {
        crate::KernelError::InvalidInductive { name, what } => {
            assert_eq!(what, "empty inductive block");
            assert!(matches!(name.as_ref(), Name::Anonymous));
        }
        other => panic!("expected empty-inductive-block error, got {other:?}"),
    }
    assert_eq!(env.len(), before, "environment unchanged on rejection");
    assert!(env.get(&nm("marker")).is_some());
}

#[test]
fn iota_now_reduces_declared_recursor() {
    // Admit Nat, then reduce `Nat.rec.{1} motive z s (Nat.succ k)` using
    // the REGENERATED recursor + rules. This ties Task 7's iota reduction
    // to the rules produced here.
    let mut env = Environment::default();
    env.add_decl(nat_decl()).expect("Nat admits");
    env.add_decl(axiom("z", mini::nat())).unwrap();
    env.add_decl(axiom(
        "s",
        mini::pi("n", mini::nat(), mini::pi("ih", mini::nat(), mini::nat())),
    ))
    .unwrap();
    env.add_decl(axiom("k", mini::nat())).unwrap();

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

    let mut tc = crate::TypeChecker::new(&env);
    let reduced = tc.whnf(&major).expect("iota reduces");
    // Expect `s k (Nat.rec.{1} motive z s k)`: head is `s` with 2 args.
    let head = Expr::get_app_fn(&reduced);
    assert!(
        matches!(head.node(), ExprNode::Const { name, .. } if name.as_ref() == nm("s").as_ref()),
        "reduced head is the succ minor `s`, got {:?}",
        head.node()
    );
    assert_eq!(Expr::get_app_num_args(&reduced), 2);
}

// ---- Task 10: nested inductives -----------------------------------------
//
// All four tests hand-build the block from the `#print`/`run_cmd`
// transcriptions taken under leanprover/lean4:v4.32.0-rc1:
//
//   inductive Tree where | node : List Tree → Tree
//     Tree: numNested=1  all=[Tree]
//     Tree.node : List.{0} Tree → Tree
//     Tree.rec.{u} : numMotives=2 numMinors=3 numParams=0 numIndices=0
//         rules: for Tree.node (1 field)
//     Tree.rec_1.{u} (the restored aux List recursor): numMotives=2
//         rules: for List.nil (0), for List.cons (2)
//
//   inductive Stx where | node : Array Stx → Stx | leaf : Stx
//     Stx: numNested=2  all=[Stx]         (Array nests, and Array's
//     Stx.rec.{u} : numMotives=3 numMinors=5   underlying List nests too)

/// `Type u` = `Sort (u+1)`.
fn type_u() -> Arc<Expr> {
    Expr::sort(
        Level::mk_succ(Arc::new(Level::Param(nm("u")))),
        &mut RecGuard::new(),
    )
    .unwrap()
}

/// Does any component of `n` equal `s`? (Leak scan for `_nested`.)
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
    // Tree.node : List.{0} Tree → Tree
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

#[test]
fn admits_nested_via_list() {
    let mut env = mini::env();
    env.add_decl(tree_decl()).expect("Tree admits via nesting");

    // InductiveVal: one nested aux type, `all` fixed to just [Tree].
    let tree = induct(&env, &nm("Tree"));
    assert_eq!(tree.num_nested, Nat::from(1), "one aux nested type (List)");
    assert_eq!(tree.all, vec![nm("Tree")], "all restored to the real block");
    assert_eq!(tree.ctors, vec![nm2("Tree", "node")]);
    assert!(tree.is_rec, "Tree is recursive");

    // Constructor: type restored to `List.{0} Tree → Tree`.
    let node = ctor(&env, &nm2("Tree", "node"));
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

    // Recursor Tree.rec: gains a motive for the aux List type ⇒ 2 motives.
    let rec = recursor(&env, &nm2("Tree", "rec"));
    assert_eq!(rec.num_motives, Nat::from(2), "motive for Tree + aux List");
    assert_eq!(rec.num_minors, Nat::from(3), "node + nil + cons minors");
    assert_eq!(rec.num_params, Nat::from(0));
    assert_eq!(rec.num_indices, Nat::from(0));
    assert_eq!(rec.all, vec![nm("Tree")], "recursor all = real block");
    assert_eq!(rec.val.level_params, vec![nm("u")]);
    // Tree.rec's own rules are for Tree's constructors only.
    assert_eq!(rec.rules.len(), 1);
    assert_eq!(rec.rules[0].ctor, nm2("Tree", "node"));
    assert_eq!(rec.rules[0].nfields, Nat::from(1));

    // The restored aux recursor Tree.rec_1: rules reference the REAL
    // List.nil / List.cons names (restore_constructor_name).
    let rec1 = recursor(&env, &nm2("Tree", "rec_1"));
    assert_eq!(rec1.num_motives, Nat::from(2));
    assert_eq!(rec1.all, vec![nm("Tree")]);
    assert_eq!(rec1.rules.len(), 2);
    assert_eq!(rec1.rules[0].ctor, nm2("List", "nil"));
    assert_eq!(rec1.rules[0].nfields, Nat::from(0));
    assert_eq!(rec1.rules[1].ctor, nm2("List", "cons"));
    assert_eq!(rec1.rules[1].nfields, Nat::from(2));

    // No aux `_nested.*` declaration leaks into the final environment.
    assert_no_nested_leak(&env);
}

#[test]
fn nested_iota_reduces() {
    let mut env = mini::env();
    env.add_decl(tree_decl()).expect("Tree admits");
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
        env.add_decl(axiom(n, ty)).unwrap();
    }
    env.add_decl(axiom("lst", list0_tree)).unwrap();

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

    let mut tc = crate::TypeChecker::new(&env);
    let reduced = tc.whnf(&major).expect("nested iota reduces");
    // RHS of the Tree.node rule is `node_min lst (Tree.rec_1 … lst)`.
    let head = Expr::get_app_fn(&reduced);
    assert!(
        matches!(head.node(), ExprNode::Const { name, .. } if name.as_ref() == nm("node_min").as_ref()),
        "reduced head is the node minor, got {:?}",
        head.node()
    );
    assert_eq!(Expr::get_app_num_args(&reduced), 2);
}

#[test]
fn rejects_nested_positivity_violation() {
    // inductive T where | mk : List (T → T) → T
    // After elimination the aux List copy carries a field `T → T`; the
    // domain occurrence of `T` is non-positive ⇒ rejected.
    let mut env = mini::env();
    let t = mini::cstn(nm("T"), vec![]);
    let t_to_t = mini::pi("x", Arc::clone(&t), Arc::clone(&t)); // T → T
    let list_tt = mini::app(mini::cstn(nm("List"), vec![Arc::new(Level::Zero)]), t_to_t);
    let mk_ty = mini::pi("a", list_tt, t); // List (T → T) → T
    let err = env
        .add_decl(decl(
            vec![],
            0,
            vec![ind("T", mini::type1(), vec![(nm2("T", "mk"), mk_ty)])],
        ))
        .unwrap_err();
    match err {
        crate::KernelError::InvalidInductive { what, .. } => assert_eq!(what, "positivity"),
        other => panic!("expected positivity error, got {other:?}"),
    }
    // Rollback: neither the real names nor any aux `_nested.*` remain.
    assert!(env.get(&nm("T")).is_none());
    assert!(env.get(&nm2("T", "mk")).is_none());
    assert_no_nested_leak(&env);
}

/// `structure Array.{u} (α : Type u) where mk :: (toList : List.{u} α)`.
fn array_decl() -> Declaration {
    let array_ty = mini::pi("α", type_u(), type_u());
    let listu = mini::cstn(nm("List"), vec![Arc::new(Level::Param(nm("u")))]);
    let arrayu = mini::cstn(nm("Array"), vec![Arc::new(Level::Param(nm("u")))]);
    // Array.mk.{u} : {α : Type u} → List.{u} α → Array.{u} α
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

#[test]
fn stdlib_shape_smoke() {
    // The heaviest nested consumer shape in the stdlib: Lean.Syntax nests
    // `Array Syntax`, which pulls in Array *and* its underlying List. A
    // faithful minimal analogue:
    //   inductive Stx where | node : Array Stx → Stx | leaf : Stx
    let mut env = mini::env();
    env.add_decl(array_decl()).expect("Array admits");

    let array0_stx = mini::app(
        mini::cstn(nm("Array"), vec![Arc::new(Level::Zero)]),
        mini::cstn(nm("Stx"), vec![]),
    );
    let node_ty = mini::pi("a", array0_stx, mini::cstn(nm("Stx"), vec![]));
    let leaf_ty = mini::cstn(nm("Stx"), vec![]);
    env.add_decl(decl(
        vec![],
        0,
        vec![ind(
            "Stx",
            mini::type1(),
            vec![(nm2("Stx", "node"), node_ty), (nm2("Stx", "leaf"), leaf_ty)],
        )],
    ))
    .expect("Stx admits via double nesting (Array + List)");

    let stx = induct(&env, &nm("Stx"));
    // Array nests, and Array's underlying List nests ⇒ two aux types.
    assert_eq!(stx.num_nested, Nat::from(2));
    assert_eq!(stx.all, vec![nm("Stx")]);
    assert_eq!(stx.ctors, vec![nm2("Stx", "node"), nm2("Stx", "leaf")]);

    let rec = recursor(&env, &nm2("Stx", "rec"));
    assert_eq!(rec.num_motives, Nat::from(3), "Stx + Array-aux + List-aux");
    assert_eq!(rec.num_minors, Nat::from(5), "node+leaf + mk + nil+cons");
    assert_eq!(rec.all, vec![nm("Stx")]);

    // The two restored aux recursors are present under real names …
    assert!(env.get(&nm2("Stx", "rec_1")).is_some());
    assert!(env.get(&nm2("Stx", "rec_2")).is_some());
    // … and no aux `_nested.*` declaration leaked.
    assert_no_nested_leak(&env);
}
