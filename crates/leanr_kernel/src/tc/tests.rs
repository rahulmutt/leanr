//! Task 6 tests. A small environment is built BY HAND from hand-rolled
//! `ConstantInfo`s (no olean; fixtures arrive in Task 12). The `mini`
//! module is the shared fixture; each test transcribes one brief case.

use super::*;
use crate::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety,
    DefinitionVal, Environment, Expr, ExprNode, InductiveVal, KernelError, Level, Literal, Name,
    Nat, OpaqueVal, QuotKind, QuotVal, RecGuard, RecursorRule, RecursorVal, ReducibilityHints,
};
use std::sync::Arc;

/// Build a single-component `Name` (no `Name::from_str` exists — see
/// every prior task's test helpers).
fn nm(s: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: s.to_string(),
    })
}

/// Build a two-component `Name` `a.b`.
fn nm2(a: &str, b: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: nm(a),
        part: b.to_string(),
    })
}

fn g() -> RecGuard {
    RecGuard::new()
}

/// The hand-rolled kernel environment shared by the tests below.
mod mini {
    use super::*;

    pub fn u() -> Arc<Name> {
        nm("u")
    }

    /// `Sort 0` = `Prop`.
    pub fn sort0() -> Arc<Expr> {
        Expr::sort(Arc::new(Level::Zero), &mut g()).unwrap()
    }

    /// `Sort u`.
    pub fn sort_u() -> Arc<Expr> {
        Expr::sort(Arc::new(Level::Param(u())), &mut g()).unwrap()
    }

    /// `Sort 1` = `Type`.
    pub fn type1() -> Arc<Expr> {
        Expr::sort(Level::mk_succ(Arc::new(Level::Zero)), &mut g()).unwrap()
    }

    /// `Const name levels`.
    pub fn cst(name: &str, levels: Vec<Arc<Level>>) -> Arc<Expr> {
        Expr::const_(nm(name), levels, &mut g()).unwrap()
    }

    fn cval(name: &str, level_params: Vec<Arc<Name>>, ty: Arc<Expr>) -> ConstantVal {
        ConstantVal {
            name: nm(name),
            level_params,
            ty,
        }
    }

    fn axiom(name: &str, ty: Arc<Expr>) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            val: cval(name, vec![], ty),
            is_unsafe: false,
        })
    }

    // ---- Task 7 helpers: dotted names, de Bruijn builders ------------

    /// `ConstantVal` for a (possibly dotted) `Name`.
    fn cvaln(name: Arc<Name>, level_params: Vec<Arc<Name>>, ty: Arc<Expr>) -> ConstantVal {
        ConstantVal {
            name,
            level_params,
            ty,
        }
    }

    fn axiomn(name: Arc<Name>, ty: Arc<Expr>) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            val: cvaln(name, vec![], ty),
            is_unsafe: false,
        })
    }

    /// `Const name levels` for a dotted `Name`.
    pub fn cstn(name: Arc<Name>, levels: Vec<Arc<Level>>) -> Arc<Expr> {
        Expr::const_(name, levels, &mut g()).unwrap()
    }

    pub fn bvar(i: u64) -> Arc<Expr> {
        Expr::bvar(Nat::from(i))
    }

    pub fn app(f: Arc<Expr>, a: Arc<Expr>) -> Arc<Expr> {
        Expr::app(f, a)
    }

    pub fn appn(f: Arc<Expr>, args: Vec<Arc<Expr>>) -> Arc<Expr> {
        Expr::mk_app_spine(f, &args)
    }

    pub fn pi(name: &str, dom: Arc<Expr>, body: Arc<Expr>) -> Arc<Expr> {
        Expr::forall_e(nm(name), dom, body, BinderInfo::Default)
    }

    pub fn lam(name: &str, dom: Arc<Expr>, body: Arc<Expr>) -> Arc<Expr> {
        Expr::lam(nm(name), dom, body, BinderInfo::Default)
    }

    /// `Sort (Param p)`.
    pub fn sort_param(p: &str) -> Arc<Expr> {
        Expr::sort(Arc::new(Level::Param(nm(p))), &mut g()).unwrap()
    }

    pub fn nat() -> Arc<Expr> {
        cstn(nm("Nat"), vec![])
    }

    // ---- Nat ---------------------------------------------------------
    //
    // #print Nat.rec (pp.all), leanprover/lean4:v4.32.0-rc1:
    //   recursor Nat.rec.{u} : {motive : Nat → Sort u} →
    //     (zero : motive Nat.zero) →
    //     (succ : (n : Nat) → (n_ih : motive n) → motive (Nat.succ n)) →
    //     (t : Nat) → motive t
    //   params 0, indices 0, motives 1, minors 2
    //   Nat.zero (0 fields): fun motive zero succ => zero
    //   Nat.succ (1 field):  fun motive zero succ n =>
    //                          succ n (Nat.rec.{u} motive zero succ n)

    /// `motive : Nat → Sort u`.
    fn nat_motive_ty() -> Arc<Expr> {
        pi("t", nat(), sort_param("u"))
    }

    /// `succ`'s type: `(n : Nat) → (motive n) → motive (Nat.succ n)`,
    /// under binders `[motive, zero]`.
    fn nat_succ_minor_ty() -> Arc<Expr> {
        pi(
            "n",
            nat(),
            pi(
                "ih",
                app(bvar(2), bvar(0)), // motive n
                app(bvar(3), app(cstn(nm2("Nat", "succ"), vec![]), bvar(1))), // motive (Nat.succ n)
            ),
        )
    }

    fn nat_rec_type() -> Arc<Expr> {
        pi(
            "motive",
            nat_motive_ty(),
            pi(
                "zero",
                app(bvar(0), cstn(nm2("Nat", "zero"), vec![])), // motive Nat.zero
                pi(
                    "succ",
                    nat_succ_minor_ty(),
                    pi("t", nat(), app(bvar(3), bvar(0))), // motive t
                ),
            ),
        )
    }

    fn nat_rec_rules() -> Vec<RecursorRule> {
        // Nat.zero: fun motive zero succ => zero
        let zero_rhs = lam(
            "motive",
            nat_motive_ty(),
            lam(
                "zero",
                app(bvar(0), cstn(nm2("Nat", "zero"), vec![])),
                lam("succ", nat_succ_minor_ty(), bvar(1)),
            ),
        );
        // Nat.succ: fun motive zero succ n => succ n (Nat.rec.{u} motive zero succ n)
        let nat_rec = cstn(nm2("Nat", "rec"), vec![Arc::new(Level::Param(nm("u")))]);
        let succ_body = app(
            app(bvar(1), bvar(0)),                                   // succ n
            appn(nat_rec, vec![bvar(3), bvar(2), bvar(1), bvar(0)]), // Nat.rec.{u} motive zero succ n
        );
        let succ_rhs = lam(
            "motive",
            nat_motive_ty(),
            lam(
                "zero",
                app(bvar(0), cstn(nm2("Nat", "zero"), vec![])),
                lam("succ", nat_succ_minor_ty(), lam("n", nat(), succ_body)),
            ),
        );
        vec![
            RecursorRule {
                ctor: nm2("Nat", "zero"),
                nfields: Nat::from(0),
                rhs: zero_rhs,
            },
            RecursorRule {
                ctor: nm2("Nat", "succ"),
                nfields: Nat::from(1),
                rhs: succ_rhs,
            },
        ]
    }

    fn nat_decls() -> Vec<ConstantInfo> {
        let nat_ind = ConstantInfo::Induct(InductiveVal {
            val: cvaln(nm("Nat"), vec![], type1()),
            num_params: Nat::from(0),
            num_indices: Nat::from(0),
            all: vec![nm("Nat")],
            ctors: vec![nm2("Nat", "zero"), nm2("Nat", "succ")],
            num_nested: Nat::from(0),
            is_rec: true,
            is_unsafe: false,
            is_reflexive: false,
        });
        let zero = ConstantInfo::Ctor(ConstructorVal {
            val: cvaln(nm2("Nat", "zero"), vec![], nat()),
            induct: nm("Nat"),
            cidx: Nat::from(0),
            num_params: Nat::from(0),
            num_fields: Nat::from(0),
            is_unsafe: false,
        });
        let succ = ConstantInfo::Ctor(ConstructorVal {
            val: cvaln(nm2("Nat", "succ"), vec![], pi("n", nat(), nat())),
            induct: nm("Nat"),
            cidx: Nat::from(1),
            num_params: Nat::from(0),
            num_fields: Nat::from(1),
            is_unsafe: false,
        });
        let rec = ConstantInfo::Rec(RecursorVal {
            val: cvaln(nm2("Nat", "rec"), vec![nm("u")], nat_rec_type()),
            all: vec![nm2("Nat", "rec")],
            num_params: Nat::from(0),
            num_indices: Nat::from(0),
            num_motives: Nat::from(1),
            num_minors: Nat::from(2),
            rules: nat_rec_rules(),
            k: false,
            is_unsafe: false,
        });
        vec![nat_ind, zero, succ, rec, axiomn(nm("n0"), nat())]
    }

    // ---- Bool --------------------------------------------------------

    fn bool_decls() -> Vec<ConstantInfo> {
        let bool_ind = ConstantInfo::Induct(InductiveVal {
            val: cvaln(nm("Bool"), vec![], type1()),
            num_params: Nat::from(0),
            num_indices: Nat::from(0),
            all: vec![nm("Bool")],
            ctors: vec![nm2("Bool", "false"), nm2("Bool", "true")],
            num_nested: Nat::from(0),
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        });
        let bfalse = ConstantInfo::Ctor(ConstructorVal {
            val: cvaln(nm2("Bool", "false"), vec![], cstn(nm("Bool"), vec![])),
            induct: nm("Bool"),
            cidx: Nat::from(0),
            num_params: Nat::from(0),
            num_fields: Nat::from(0),
            is_unsafe: false,
        });
        let btrue = ConstantInfo::Ctor(ConstructorVal {
            val: cvaln(nm2("Bool", "true"), vec![], cstn(nm("Bool"), vec![])),
            induct: nm("Bool"),
            cidx: Nat::from(1),
            num_params: Nat::from(0),
            num_fields: Nat::from(0),
            is_unsafe: false,
        });
        vec![bool_ind, bfalse, btrue]
    }

    // ---- Eq (k-like recursor) ---------------------------------------
    //
    // #print Eq / Eq.refl / Eq.rec (pp.all):
    //   inductive Eq.{u_1} : {α : Sort u_1} → α → α → Prop
    //   Eq.refl.{u_1} : ∀ {α : Sort u_1} (a : α), @Eq.{u_1} α a a
    //   recursor Eq.rec.{u, u_1} : {α : Sort u_1} → {a : α} →
    //     {motive : (a_1 : α) → @Eq α a a_1 → Sort u} →
    //     (refl : motive a (Eq.refl α a)) → {a_1 : α} →
    //     (t : @Eq α a a_1) → motive a_1 t     (params 2, indices 1,
    //     motives 1, minors 1, K-like)
    //   Eq.refl (0 fields): fun {α} a motive refl => refl
    //
    // The recursor's binder domains for `motive`/`refl`/`body` are
    // simplified to `Sort u` below: `get_major_induct` only reads the
    // 6th binder's domain (`@Eq α a a_1`), and iota never infers this
    // type, so their exact shape is irrelevant to Task 7 (Task 9 rebuilds
    // these from the real inductive machinery).

    fn eq_ty() -> Arc<Expr> {
        // Π (α : Sort u_1), α → α → Prop
        pi(
            "α",
            sort_param("u_1"),
            pi("_", bvar(0), pi("_", bvar(1), sort0())),
        )
    }

    fn eq_refl_ty() -> Arc<Expr> {
        // Π {α : Sort u_1} (a : α), @Eq.{u_1} α a a
        let eq = cstn(nm("Eq"), vec![Arc::new(Level::Param(nm("u_1")))]);
        pi(
            "α",
            sort_param("u_1"),
            pi("a", bvar(0), appn(eq, vec![bvar(1), bvar(0), bvar(0)])),
        )
    }

    fn eq_rec_ty() -> Arc<Expr> {
        let eq = cstn(nm("Eq"), vec![Arc::new(Level::Param(nm("u_1")))]);
        // [α, a, motive, refl, a_1] then (t : @Eq α a a_1) then body.
        pi(
            "α",
            sort_param("u_1"),
            pi(
                "a",
                bvar(0),
                pi(
                    "motive",
                    sort_param("u"),
                    pi(
                        "refl",
                        sort_param("u"),
                        pi(
                            "a_1",
                            bvar(3), // α
                            pi(
                                "t",
                                appn(eq, vec![bvar(4), bvar(3), bvar(0)]), // @Eq α a a_1
                                sort_param("u"),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn eq_decls() -> Vec<ConstantInfo> {
        let eq_ind = ConstantInfo::Induct(InductiveVal {
            val: cvaln(nm("Eq"), vec![nm("u_1")], eq_ty()),
            num_params: Nat::from(2),
            num_indices: Nat::from(1),
            all: vec![nm("Eq")],
            ctors: vec![nm2("Eq", "refl")],
            num_nested: Nat::from(0),
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        });
        let refl = ConstantInfo::Ctor(ConstructorVal {
            val: cvaln(nm2("Eq", "refl"), vec![nm("u_1")], eq_refl_ty()),
            induct: nm("Eq"),
            cidx: Nat::from(0),
            num_params: Nat::from(2),
            num_fields: Nat::from(0),
            is_unsafe: false,
        });
        // Eq.refl rule (0 fields): fun {α} a motive refl => refl
        let refl_rhs = lam(
            "α",
            sort_param("u_1"),
            lam(
                "a",
                bvar(0),
                lam(
                    "motive",
                    sort_param("u"),
                    lam("refl", sort_param("u"), bvar(0)),
                ),
            ),
        );
        let rec = ConstantInfo::Rec(RecursorVal {
            val: cvaln(nm2("Eq", "rec"), vec![nm("u"), nm("u_1")], eq_rec_ty()),
            all: vec![nm2("Eq", "rec")],
            num_params: Nat::from(2),
            num_indices: Nat::from(1),
            num_motives: Nat::from(1),
            num_minors: Nat::from(1),
            rules: vec![RecursorRule {
                ctor: nm2("Eq", "refl"),
                nfields: Nat::from(0),
                rhs: refl_rhs,
            }],
            k: true,
            is_unsafe: false,
        });
        // A : Type, a0 : A, h : @Eq.{1} A a0 a0 (an opaque rfl-typed
        // proof — NOT syntactically Eq.refl), Mot / req: motive & minor.
        let eq_at1 = cstn(nm("Eq"), vec![Level::mk_succ(Arc::new(Level::Zero))]);
        let h_ty = appn(
            eq_at1,
            vec![cst("A", vec![]), cst("a0", vec![]), cst("a0", vec![])],
        );
        vec![
            eq_ind,
            refl,
            rec,
            axiomn(nm("a0"), cst("A", vec![])),
            axiomn(nm("h"), h_ty),
            axiomn(nm("Mot"), type1()),
            axiomn(nm("req"), cst("A", vec![])),
        ]
    }

    // ---- Prod (structure eta) & Unit (unit-like) --------------------

    fn prod_decls() -> Vec<ConstantInfo> {
        // Monomorphic Prod : Sort 1 → Sort 1 → Sort 1 (universes are
        // irrelevant to is_structure_like / eta).
        let prod_ind = ConstantInfo::Induct(InductiveVal {
            val: cvaln(
                nm("Prod"),
                vec![],
                pi("α", type1(), pi("β", type1(), type1())),
            ),
            num_params: Nat::from(2),
            num_indices: Nat::from(0),
            all: vec![nm("Prod")],
            ctors: vec![nm2("Prod", "mk")],
            num_nested: Nat::from(0),
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        });
        // Prod.mk : Π (α β : Sort 1) (fst : α) (snd : β), Prod α β
        let mk_ty = pi(
            "α",
            type1(),
            pi(
                "β",
                type1(),
                pi(
                    "fst",
                    bvar(1),
                    pi(
                        "snd",
                        bvar(1),
                        appn(cstn(nm("Prod"), vec![]), vec![bvar(3), bvar(2)]),
                    ),
                ),
            ),
        );
        let mk = ConstantInfo::Ctor(ConstructorVal {
            val: cvaln(nm2("Prod", "mk"), vec![], mk_ty),
            induct: nm("Prod"),
            cidx: Nat::from(0),
            num_params: Nat::from(2),
            num_fields: Nat::from(2),
            is_unsafe: false,
        });
        let prod_ab = appn(
            cstn(nm("Prod"), vec![]),
            vec![cst("A", vec![]), cst("B", vec![])],
        );
        vec![
            prod_ind,
            mk,
            axiomn(nm("p"), prod_ab),
            // ff : B → B (B : Type, so B → B is not a Prop — eta, not
            // proof irrelevance, must decide `ff =?= λ x, ff x`).
            axiomn(nm("ff"), pi("_", cst("B", vec![]), cst("B", vec![]))),
        ]
    }

    fn unit_decls() -> Vec<ConstantInfo> {
        let unit_ind = ConstantInfo::Induct(InductiveVal {
            val: cvaln(nm("Unit"), vec![], type1()),
            num_params: Nat::from(0),
            num_indices: Nat::from(0),
            all: vec![nm("Unit")],
            ctors: vec![nm2("Unit", "unit")],
            num_nested: Nat::from(0),
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        });
        let unit_ctor = ConstantInfo::Ctor(ConstructorVal {
            val: cvaln(nm2("Unit", "unit"), vec![], cstn(nm("Unit"), vec![])),
            induct: nm("Unit"),
            cidx: Nat::from(0),
            num_params: Nat::from(0),
            num_fields: Nat::from(0),
            is_unsafe: false,
        });
        vec![
            unit_ind,
            unit_ctor,
            axiomn(nm("ux"), cstn(nm("Unit"), vec![])),
            axiomn(nm("uy"), cstn(nm("Unit"), vec![])),
        ]
    }

    // ---- String (literal expansion) ---------------------------------

    /// `Type u` = `Sort (u+1)`.
    fn type_u() -> Arc<Expr> {
        Expr::sort(Level::mk_succ(Arc::new(Level::Param(nm("u")))), &mut g()).unwrap()
    }

    fn string_decls() -> Vec<ConstantInfo> {
        // String : Type ; String.ofList : List.{0} Char → String. The
        // expanded literal is `String.ofList (List.cons … Char.ofNat …)`;
        // `is_def_eq` infers the char-list sub-terms, so List/Char/
        // Char.ofNat need real (hand-rolled) entries.
        let list_u = cstn(nm("List"), vec![Arc::new(Level::Param(nm("u")))]);
        let list_char = appn(
            cstn(nm("List"), vec![Arc::new(Level::Zero)]),
            vec![cstn(nm("Char"), vec![])],
        );
        // List.{u} : Type u → Type u
        let list_ind = ConstantInfo::Induct(InductiveVal {
            val: cvaln(nm("List"), vec![nm("u")], pi("α", type_u(), type_u())),
            num_params: Nat::from(1),
            num_indices: Nat::from(0),
            all: vec![nm("List")],
            ctors: vec![nm2("List", "nil"), nm2("List", "cons")],
            num_nested: Nat::from(0),
            is_rec: true,
            is_unsafe: false,
            is_reflexive: false,
        });
        // List.nil.{u} : {α : Type u} → List.{u} α
        let list_nil = ConstantInfo::Ctor(ConstructorVal {
            val: cvaln(
                nm2("List", "nil"),
                vec![nm("u")],
                pi("α", type_u(), app(Arc::clone(&list_u), bvar(0))),
            ),
            induct: nm("List"),
            cidx: Nat::from(0),
            num_params: Nat::from(1),
            num_fields: Nat::from(0),
            is_unsafe: false,
        });
        // List.cons.{u} : {α : Type u} → α → List.{u} α → List.{u} α
        let list_cons_ty = pi(
            "α",
            type_u(),
            pi(
                "head",
                bvar(0),
                pi(
                    "tail",
                    app(Arc::clone(&list_u), bvar(1)),
                    app(Arc::clone(&list_u), bvar(2)),
                ),
            ),
        );
        let list_cons = ConstantInfo::Ctor(ConstructorVal {
            val: cvaln(nm2("List", "cons"), vec![nm("u")], list_cons_ty),
            induct: nm("List"),
            cidx: Nat::from(1),
            num_params: Nat::from(1),
            num_fields: Nat::from(2),
            is_unsafe: false,
        });
        vec![
            axiomn(nm("Char"), type1()),
            axiomn(
                nm2("Char", "ofNat"),
                pi("n", nat(), cstn(nm("Char"), vec![])),
            ),
            list_ind,
            list_nil,
            list_cons,
            axiomn(nm("String"), type1()),
            axiomn(
                nm2("String", "ofList"),
                pi("data", list_char, cstn(nm("String"), vec![])),
            ),
        ]
    }

    // ---- Quotient constants -----------------------------------------

    fn quot_decls() -> Vec<ConstantInfo> {
        // Minimal QuotVals: reduction consults only the head names and the
        // env's `quot_initialized` gate, never these types.
        let q = |name: Arc<Name>, kind: QuotKind, lparams: Vec<Arc<Name>>| {
            ConstantInfo::Quot(QuotVal {
                val: cvaln(name, lparams, type1()),
                kind,
            })
        };
        vec![
            q(nm("Quot"), QuotKind::Type, vec![nm("u")]),
            q(nm2("Quot", "mk"), QuotKind::Ctor, vec![nm("u")]),
            q(nm2("Quot", "lift"), QuotKind::Lift, vec![nm("u"), nm("v")]),
            q(nm2("Quot", "ind"), QuotKind::Ind, vec![nm("u")]),
        ]
    }

    fn special_decls() -> Vec<ConstantInfo> {
        let mut v = Vec::new();
        v.extend(nat_decls());
        v.extend(bool_decls());
        v.extend(eq_decls());
        v.extend(prod_decls());
        v.extend(unit_decls());
        v.extend(string_decls());
        v.extend(quot_decls());
        v
    }

    /// `Π (α : Sort u), α → α` in de Bruijn form.
    pub fn id1_type() -> Arc<Expr> {
        let inner = Expr::forall_e(
            nm("a"),
            Expr::bvar(Nat::from(0u64)), // α
            Expr::bvar(Nat::from(1u64)), // α (one binder deeper)
            BinderInfo::Default,
        );
        Expr::forall_e(nm("α"), sort_u(), inner, BinderInfo::Default)
    }

    /// `λ (α : Sort u) (x : α), x`.
    pub fn id1_value() -> Arc<Expr> {
        let inner = Expr::lam(
            nm("x"),
            Expr::bvar(Nat::from(0u64)), // α
            Expr::bvar(Nat::from(0u64)), // x
            BinderInfo::Default,
        );
        Expr::lam(nm("α"), sort_u(), inner, BinderInfo::Default)
    }

    /// The shared environment:
    ///   axiom A : Prop        axiom a : A
    ///   def   id₁ : Π (α : Sort u), α → α := λ α x, x   (Regular hints)
    ///   opaque w : A := a
    ///   axiom B : Type        axiom bt : B       axiom bf : B
    pub fn env() -> Environment {
        let id1 = ConstantInfo::Defn(DefinitionVal {
            val: cval("id1", vec![u()], id1_type()),
            value: id1_value(),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("id1")],
        });
        let w = ConstantInfo::Opaque(OpaqueVal {
            val: cval("w", vec![], cst("A", vec![])),
            value: cst("a", vec![]),
            is_unsafe: false,
            all: vec![nm("w")],
        });
        let mut module = vec![
            axiom("A", sort0()),
            axiom("a", cst("A", vec![])),
            id1,
            w,
            axiom("B", type1()),
            axiom("bt", cst("B", vec![])),
            axiom("bf", cst("B", vec![])),
        ];
        module.extend(special_decls());
        Environment::from_modules(vec![module]).unwrap()
    }
}

fn deq(tc: &mut TypeChecker, a: &Arc<Expr>, b: &Arc<Expr>) -> bool {
    tc.is_def_eq(a, b).unwrap()
}

#[test]
fn infer_sort_of_sort() {
    // infer(Sort u) = Sort (u+1)
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let r = tc.infer_type(&mini::sort_u()).unwrap();
    let expected = Expr::sort(Level::mk_succ(Arc::new(Level::Param(mini::u()))), &mut g()).unwrap();
    assert!(deq(&mut tc, &r, &expected));
}

#[test]
fn infer_lambda_gives_pi() {
    // infer(λ (x : A), x) ≡ A → A
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let lam = Expr::lam(
        nm("x"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let r = tc.infer_type(&lam).unwrap();
    let a_to_a = Expr::forall_e(
        nm("x"),
        mini::cst("A", vec![]),
        mini::cst("A", vec![]),
        BinderInfo::Default,
    );
    assert!(deq(&mut tc, &r, &a_to_a));
}

#[test]
fn check_rejects_loose_bvar() {
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::bvar(Nat::from(0u64));
    assert_eq!(tc.infer_type(&e).unwrap_err(), KernelError::LooseBVar);
}

#[test]
fn check_rejects_mvar() {
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::mvar(nm("m"));
    assert_eq!(
        tc.infer_type(&e).unwrap_err(),
        KernelError::MetavarEncountered
    );
}

#[test]
fn check_rejects_univ_arity() {
    // Const id₁ [] — decl has 1 level param.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let e = mini::cst("id1", vec![]);
    assert_eq!(
        tc.infer_type(&e).unwrap_err(),
        KernelError::UnivParamArityMismatch { name: nm("id1") }
    );
}

#[test]
fn app_type_mismatch_rejected() {
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let id1_0 = mini::cst("id1", vec![Arc::new(Level::Zero)]);
    // id₁.{0} A a is well-typed.
    let good = Expr::app(
        Expr::app(Arc::clone(&id1_0), mini::cst("A", vec![])),
        mini::cst("a", vec![]),
    );
    assert!(tc.check(&good, &[]).is_ok());
    // id₁.{0} a a — first arg `a : A` where a `Sort 0` is expected.
    let bad = Expr::app(
        Expr::app(id1_0, mini::cst("a", vec![])),
        mini::cst("a", vec![]),
    );
    assert_eq!(
        tc.check(&bad, &[]).unwrap_err(),
        KernelError::AppTypeMismatch
    );
}

#[test]
fn beta_whnf() {
    // whnf((λ x, x) a) = a, ptr-preserved.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let a = mini::cst("a", vec![]);
    let idfun = Expr::lam(
        nm("x"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let e = Expr::app(idfun, Arc::clone(&a));
    let r = tc.whnf(&e).unwrap();
    assert!(Arc::ptr_eq(&r, &a));
}

#[test]
fn zeta_whnf() {
    // whnf(let x := a in x) = a.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let a = mini::cst("a", vec![]);
    let e = Expr::let_e(
        nm("x"),
        mini::cst("A", vec![]),
        Arc::clone(&a),
        Expr::bvar(Nat::from(0u64)),
        false,
    );
    let r = tc.whnf(&e).unwrap();
    assert!(Arc::ptr_eq(&r, &a));
}

#[test]
fn delta_whnf() {
    // whnf(id₁.{0} A a) = a via unfold + beta chain.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let a = mini::cst("a", vec![]);
    let e = Expr::app(
        Expr::app(
            mini::cst("id1", vec![Arc::new(Level::Zero)]),
            mini::cst("A", vec![]),
        ),
        Arc::clone(&a),
    );
    let r = tc.whnf(&e).unwrap();
    assert!(Expr::structural_eq(&r, &a, &mut g()).unwrap());
}

#[test]
fn defeq_alpha_binding() {
    // λ x, x ≡ λ y, y (binder names ignored).
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
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
    assert!(deq(&mut tc, &lx, &ly));
}

#[test]
fn defeq_proof_irrelevance() {
    // a ≡ w (both : A : Prop).
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let a = mini::cst("a", vec![]);
    let w = mini::cst("w", vec![]);
    assert!(deq(&mut tc, &a, &w));
}

#[test]
fn defeq_pi_congruence() {
    // Π(x:A),A ≡ Π(y:A),A ; and NOT ≡ Π(x:A),Prop
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
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
    assert!(deq(&mut tc, &pi_a_x, &pi_a_y));
    let pi_a_prop = Expr::forall_e(
        nm("x"),
        mini::cst("A", vec![]),
        mini::sort0(),
        BinderInfo::Default,
    );
    assert!(!deq(&mut tc, &pi_a_x, &pi_a_prop));
}

#[test]
fn whnf_cache_and_sharing() {
    // whnf twice: the second call returns the same Arc (cache hit).
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let idfun = Expr::lam(
        nm("x"),
        mini::cst("A", vec![]),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let e = Expr::app(idfun, mini::cst("a", vec![]));
    let r1 = tc.whnf(&e).unwrap();
    let r2 = tc.whnf(&e).unwrap();
    assert!(Arc::ptr_eq(&r1, &r2));
}

#[test]
fn check_sets_lparams() {
    // check(λ (α : Sort u), α, [u]) passes; with [] the undefined param
    // `u` is a check_level error (mapped to UnivParamArityMismatch).
    //
    // Independent `TypeChecker`s per check: the `infer_type` memo
    // (`m_infer_type[infer_only]`, oracle state) is keyed by expr pointer,
    // NOT by lparams — so checking the SAME `lam` Arc twice on ONE checker
    // would hit the cache and skip re-validation (identical to the
    // oracle). Real admission (Replay) builds a fresh checker per decl,
    // which is what these two checks model.
    let env = mini::env();
    let lam = Expr::lam(
        nm("α"),
        mini::sort_u(),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
    );
    let mut tc_ok = TypeChecker::new(&env);
    assert!(tc_ok.check(&lam, &[mini::u()]).is_ok());
    let mut tc_bad = TypeChecker::new(&env);
    assert_eq!(
        tc_bad.check(&lam, &[]).unwrap_err(),
        KernelError::UnivParamArityMismatch { name: mini::u() }
    );
}

// ===================================================================
// Task 7: special reductions
// ===================================================================

fn lit_nat(n: u64) -> Arc<Expr> {
    Expr::lit(Literal::NatVal(Nat::from(n)))
}

fn seq(a: &Arc<Expr>, b: &Arc<Expr>) -> bool {
    Expr::structural_eq(a, b, &mut g()).unwrap()
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
    let mut tc = TypeChecker::new(&env);
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
    let r = tc.whnf(&e).unwrap();
    let expected = mini::app(
        mini::app(Arc::clone(&s), Arc::clone(&n)),
        mini::appn(natrec, vec![cc, z, s, n]),
    );
    assert!(seq(&r, &expected), "got {:?}", r);
}

#[test]
fn iota_on_literal_major() {
    // whnf(Nat.rec.{0} C z s 2) = s 1 (Nat.rec.{0} C z s 1) — the literal
    // major `2` is converted to `Nat.succ 1` before rule selection.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
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
    let r = tc.whnf(&e).unwrap();
    let expected = mini::app(
        mini::app(Arc::clone(&s), lit_nat(1)),
        mini::appn(natrec, vec![cc, z, s, lit_nat(1)]),
    );
    assert!(seq(&r, &expected), "got {:?}", r);
}

#[test]
fn k_like_rec_on_eq() {
    // whnf(Eq.rec.{0,1} A a0 Mot req a0 h) = req, where h : @Eq.{1} A a0 a0
    // is an opaque rfl-typed proof. The K-recursor synthesizes `Eq.refl`
    // from h's type and selects the (fields-less) refl rule.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
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
    let r = tc.whnf(&e).unwrap();
    assert!(seq(&r, &mini::cst("req", vec![])), "got {:?}", r);
}

#[test]
fn quot_lift_beta() {
    // whnf(Quot.lift.{0,0} α r β f h (Quot.mk.{0} α r a)) = f a
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
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
    let r = tc.whnf(&e).unwrap();
    assert!(seq(&r, &mini::app(f, a)), "got {:?}", r);
}

#[test]
fn quot_ind_beta() {
    // whnf(Quot.ind.{0} α r β h (Quot.mk.{0} α r a)) = h a
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
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
    let r = tc.whnf(&e).unwrap();
    assert!(seq(&r, &mini::app(h, a)), "got {:?}", r);
}

#[test]
fn nat_add_folds() {
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    // add 2 3 = 5
    assert!(seq(
        &tc.whnf(&nat_binop("add", lit_nat(2), lit_nat(3))).unwrap(),
        &lit_nat(5)
    ));
    // sub 2 5 = 0 (truncated)
    assert!(seq(
        &tc.whnf(&nat_binop("sub", lit_nat(2), lit_nat(5))).unwrap(),
        &lit_nat(0)
    ));
    // div 5 0 = 0
    assert!(seq(
        &tc.whnf(&nat_binop("div", lit_nat(5), lit_nat(0))).unwrap(),
        &lit_nat(0)
    ));
    // mod 5 0 = 5
    assert!(seq(
        &tc.whnf(&nat_binop("mod", lit_nat(5), lit_nat(0))).unwrap(),
        &lit_nat(5)
    ));
    // pow guard: exponent 2^25 > 1<<24 ⇒ un-reduced (still an app).
    let pow = nat_binop("pow", lit_nat(2), lit_nat(1 << 25));
    let r = tc.whnf(&pow).unwrap();
    assert!(matches!(r.node(), ExprNode::App { .. }), "got {:?}", r);
    assert!(!matches!(r.node(), ExprNode::Lit(_)));
    // pow that is allowed: 2^10 = 1024.
    assert!(seq(
        &tc.whnf(&nat_binop("pow", lit_nat(2), lit_nat(10))).unwrap(),
        &lit_nat(1024)
    ));
}

#[test]
fn nat_beq_folds_to_bool() {
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let r = tc.whnf(&nat_binop("beq", lit_nat(2), lit_nat(2))).unwrap();
    assert!(
        seq(&r, &mini::cstn(nm2("Bool", "true"), vec![])),
        "got {:?}",
        r
    );
    let r2 = tc.whnf(&nat_binop("beq", lit_nat(2), lit_nat(3))).unwrap();
    assert!(seq(&r2, &mini::cstn(nm2("Bool", "false"), vec![])));
    // ble 2 3 = true
    let r3 = tc.whnf(&nat_binop("ble", lit_nat(2), lit_nat(3))).unwrap();
    assert!(seq(&r3, &mini::cstn(nm2("Bool", "true"), vec![])));
}

#[test]
fn succ_folds() {
    // whnf(Nat.succ 4) = 5
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let r = tc.whnf(&nat_succ(lit_nat(4))).unwrap();
    assert!(seq(&r, &lit_nat(5)), "got {:?}", r);
}

#[test]
fn offset_defeq() {
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    // succ (succ n0) ≡ succ (succ n0) via offset peeling.
    let n0 = mini::cst("n0", vec![]);
    let t = nat_succ(nat_succ(Arc::clone(&n0)));
    let s = nat_succ(nat_succ(Arc::clone(&n0)));
    assert!(deq(&mut tc, &t, &s));
    // literal-vs-succ: 2 ≡ Nat.succ 1 (offset mixes literal and succ).
    assert!(deq(&mut tc, &lit_nat(2), &nat_succ(lit_nat(1))));
    // negative: succ n0 is not defeq to n0.
    assert!(!deq(&mut tc, &nat_succ(Arc::clone(&n0)), &n0));
}

#[test]
fn eta_lambda() {
    // ff ≡ λ (x : B), ff x
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let ff = mini::cst("ff", vec![]);
    let eta = Expr::lam(
        nm("x"),
        mini::cst("B", vec![]),
        mini::app(Arc::clone(&ff), Expr::bvar(Nat::from(0u64))),
        BinderInfo::Default,
    );
    assert!(deq(&mut tc, &ff, &eta));
}

#[test]
fn eta_struct() {
    // p ≡ Prod.mk A B p.0 p.1
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let p = mini::cst("p", vec![]);
    let proj0 = Expr::proj(nm("Prod"), Nat::from(0u64), Arc::clone(&p));
    let proj1 = Expr::proj(nm("Prod"), Nat::from(1u64), Arc::clone(&p));
    let mk = mini::appn(
        mini::cstn(nm2("Prod", "mk"), vec![]),
        vec![mini::cst("A", vec![]), mini::cst("B", vec![]), proj0, proj1],
    );
    assert!(deq(&mut tc, &p, &mk));
}

#[test]
fn unit_like_defeq() {
    // Any two Unit-typed terms are defeq.
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
    let ux = mini::cst("ux", vec![]);
    let uy = mini::cst("uy", vec![]);
    assert!(deq(&mut tc, &ux, &uy));
}

#[test]
fn string_lit_expansion() {
    // "ab" ≡ String.ofList (List.cons Char (Char.ofNat 97)
    //                        (List.cons Char (Char.ofNat 98)
    //                         (List.nil Char)))
    let env = mini::env();
    let mut tc = TypeChecker::new(&env);
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
    assert!(deq(&mut tc, &str_lit, &expanded));
}
