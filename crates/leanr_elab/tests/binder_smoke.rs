//! Fast, hermetic leanr-side structural checks for the binder
//! elaborators. Uses the committed `Elab0.olean` (no Lean toolchain
//! needed). The AUTHORITATIVE differential check is `oracle_elab` (see
//! Task 5); these assert coarse structure for a quick red/green loop and
//! deliberately do not pin exact encoder bytes (universe levels etc.).

mod support;
use support::{encode_expr, replay_fixture_in, EncSt, Replayed};

use leanr_elab::TermElabM;
use leanr_kernel::bank::Store;
use leanr_kernel::EnvView;
use leanr_meta::{Config, EnvExtensions, MetaCtx};
use leanr_syntax::{builtin, parse_term};

/// Parse `src` through leanr's own parser, elaborate with `expected =
/// None`, `instantiate_mvars`, and return the canonical JSON encoding —
/// exactly the `oracle_elab` pipeline (Task 5 keeps them identical).
fn elab_json(src: &str) -> serde_json::Value {
    let Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
        classes,
        coe_decls,
    } = replay_fixture_in("elab", "Elab0.olean");
    let snap = builtin::snapshot();
    let view: EnvView = env.view();
    let parsed = parse_term(src, &snap);
    assert!(
        parsed.errors.is_empty(),
        "parse errors for {src:?}: {:?}",
        parsed.errors
    );
    let root = parsed.tree.root();
    let term_elem = root
        .first_child_or_token()
        .unwrap_or_else(|| panic!("no term child for {src:?}"));
    let mut scratch = Store::scratch();
    let mctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        EnvExtensions {
            reducibility: &reducibility,
            matchers: &matchers,
            instances: &instances,
            default_instances: &default_instances,
            projection_fns: &projection_fns,
            classes: &classes,
            coe_decls: &coe_decls,
        },
    );
    let mut elab = TermElabM::new(mctx, view);
    let e = elab
        .elab_term_ensuring_type(&term_elem, &parsed.tree.kinds, None)
        .and_then(|e| {
            elab.mctx
                .instantiate_mvars(e)
                .map_err(leanr_elab::ElabError::from)
        })
        .unwrap_or_else(|err| panic!("elaboration failed for {src:?}: {err:?}"));
    let mut st = EncSt::default();
    encode_expr(elab.mctx.store(), Some(view.store), e, &mut st)
}

/// Like `elab_json`, but returns the raw `Result` instead of panicking
/// on failure or encoding to JSON — for tests asserting a specific
/// `ElabError` variant rather than a successful shape.
fn elab_result(src: &str) -> Result<leanr_kernel::bank::ExprId, leanr_elab::ElabError> {
    let Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
        classes,
        coe_decls,
    } = replay_fixture_in("elab", "Elab0.olean");
    let snap = builtin::snapshot();
    let view: EnvView = env.view();
    let parsed = parse_term(src, &snap);
    assert!(
        parsed.errors.is_empty(),
        "parse errors for {src:?}: {:?}",
        parsed.errors
    );
    let root = parsed.tree.root();
    let term_elem = root
        .first_child_or_token()
        .unwrap_or_else(|| panic!("no term child for {src:?}"));
    let mut scratch = Store::scratch();
    let mctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        EnvExtensions {
            reducibility: &reducibility,
            matchers: &matchers,
            instances: &instances,
            default_instances: &default_instances,
            projection_fns: &projection_fns,
            classes: &classes,
            coe_decls: &coe_decls,
        },
    );
    let mut elab = TermElabM::new(mctx, view);
    elab.elab_term_ensuring_type(&term_elem, &parsed.tree.kinds, None)
        .and_then(|e| {
            elab.mctx
                .instantiate_mvars(e)
                .map_err(leanr_elab::ElabError::from)
        })
}

#[test]
fn arrow_is_nondependent_pi() {
    let j = elab_json("Nat -> Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["bi"], "d");
    assert_eq!(
        j["t"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
    assert_eq!(
        j["b"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
}

#[test]
fn arrow_right_associates() {
    // Nat -> Nat -> Nat  ==  Nat -> (Nat -> Nat)
    let j = elab_json("Nat -> Nat -> Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(j["b"]["k"], "pi"); // body is itself an arrow
    assert_eq!(j["b"]["b"]["n"], "Nat");
}

#[test]
fn forall_nondependent() {
    // forall (x : Nat), Nat  — body ignores x → same shape as an arrow
    let j = elab_json("forall (x : Nat), Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["bi"], "d");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(
        j["b"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
}

#[test]
fn forall_dependent_body_is_bvar() {
    // forall (a : Type), a  — body is the binder → bvar 0
    let j = elab_json("forall (a : Type), a");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn forall_two_names_one_group_nests() {
    // forall (x y : Nat), Nat  → pi (pi ...)
    let j = elab_json("forall (x y : Nat), Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["b"]["k"], "pi");
    assert_eq!(j["b"]["b"]["n"], "Nat");
}

#[test]
fn forall_two_groups_nests() {
    let j = elab_json("forall (x : Nat) (y : Nat), Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["b"]["k"], "pi");
}

#[test]
fn dep_arrow_nondependent() {
    // (x : Nat) -> Nat
    let j = elab_json("(x : Nat) -> Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["bi"], "d");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(
        j["b"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
}

#[test]
fn dep_arrow_dependent_body_is_bvar() {
    // (a : Type) -> a
    let j = elab_json("(a : Type) -> a");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn fun_explicit_binder() {
    // fun (x : Nat) => x  →  lam (Nat) (bvar 0)
    let j = elab_json("fun (x : Nat) => x");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "d");
    assert_eq!(
        j["t"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn fun_elided_binder_is_bare_mvar_domain() {
    // fun x => x  →  lam (?m) (bvar 0); the domain mvar is never assigned
    // (no expected type), so instantiate_mvars leaves it a bare `mvar`.
    let j = elab_json("fun x => x");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["t"]["k"], "mvar");
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn fun_two_binders_nests_and_bvar_indexes() {
    // fun (x : Nat) (y : Nat) => x  →  lam (lam (bvar 1))
    let j = elab_json("fun (x : Nat) (y : Nat) => x");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["b"], serde_json::json!({"k": "bvar", "i": 1}));
}

#[test]
fn fun_ascribed_elided_binder_unifies_domain() {
    // (fun x => x : Nat -> Nat)  →  lam (Nat) (bvar 0); the ascription's
    // is_def_eq unifies the elided domain mvar to Nat.
    let j = elab_json("(fun x => x : Nat -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(
        j["t"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn fun_ascribed_explicit_binder() {
    // (fun (x : Nat) => x : Nat -> Nat)  →  lam (Nat) (bvar 0)
    let j = elab_json("(fun (x : Nat) => x : Nat -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(
        j["t"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn fun_implicit_binder_carries_binder_info() {
    // fun {a : Type} => a  →  lam bi=i (Sort ..) (bvar 0)
    let j = elab_json("fun {a : Type} => a");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "i");
    assert_eq!(j["b"]["k"], "bvar");
    assert_eq!(j["b"]["i"], 0);
}

#[test]
fn fun_strict_implicit_binder_carries_binder_info() {
    let j = elab_json("fun ⦃a : Type⦄ => a");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "s");
}

#[test]
fn fun_inst_binder_named_carries_binder_info() {
    // `Add` is in Elab0's environment (Task 10 guarantees it).
    let j = elab_json("fun [inst : Add Nat] => inst");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "c");
    assert_eq!(j["b"]["k"], "bvar");
    assert_eq!(j["b"]["i"], 0);
}

#[test]
fn fun_inst_binder_anonymous_still_binds() {
    // `[Add Nat]` — no name written. The oracle's `expandOptIdent` mints
    // an inaccessible one; leanr interns `None`. Binder names are erased
    // by the encoder, so only the shape and `bi` are asserted.
    let j = elab_json("fun [Add Nat] => Nat.zero");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "c");
}

#[test]
fn fun_implicit_group_binds_every_name() {
    // fun {a b : Type} => a  →  lam (lam (bvar 1))
    let j = elab_json("fun {a b : Type} => a");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "i");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["bi"], "i");
    assert_eq!(j["b"]["b"]["k"], "bvar");
    assert_eq!(j["b"]["b"]["i"], 1);
}

#[test]
fn fun_implicit_binder_without_type_gets_an_mvar_domain() {
    // fun {a} => a — no type written; domain is a fresh type mvar.
    let j = elab_json("fun {a} => a");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "i");
    assert_eq!(j["t"]["k"], "mvar");
}

#[test]
fn fun_opt_type_ascribes_the_body() {
    // fun (x : Nat) : Nat => x
    let j = elab_json("fun (x : Nat) : Nat => x");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["t"]["k"], "const");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(j["b"]["k"], "bvar");
    assert_eq!(j["b"]["i"], 0);
}

#[test]
fn fun_opt_type_may_mention_the_binders() {
    // fun (a : Type) (x : a) : a => x — the optType `a` refers to the
    // first binder, so it must elaborate INSIDE the telescope.
    let j = elab_json("fun (a : Type) (x : a) : a => x");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["b"]["k"], "bvar");
    assert_eq!(j["b"]["b"]["i"], 0);
}

#[test]
fn fun_opt_type_actually_ascribes_not_just_parses() {
    // fun (x : Nat) : Int => x — `Coe Nat Int` (`instCoeNatInt`) is in
    // Elab0's environment, so a body whose optType differs from its own
    // inferred type only elaborates if optType genuinely reaches
    // `elab_term_ensuring_type` as the expected type: `x : Nat` must be
    // COERCED to `Int.ofNat x`. The two tests above (`fun (x : Nat) :
    // Nat => x`, `fun (a : Type) (x : a) : a => x`) both ascribe a type
    // the body already has, so neither discriminates a broken optType
    // path from a correct one — this record does: it caught a real bug
    // where `optType`'s non-empty wrapper holds ONE `typeSpec` node
    // (`[":", T]` is `typeSpec`'s OWN children, not the wrapper's direct
    // children), so a flat `nth(1)` read off the wrapper silently landed
    // on `None` for every `fun x : T => e` — no error, no wrong term,
    // just the ascription dropped.
    let j = elab_json("fun (x : Nat) : Int => x");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["b"]["k"], "app");
    assert_eq!(
        j["b"]["f"],
        serde_json::json!({"k": "const", "n": "Int.ofNat", "us": []})
    );
    assert_eq!(j["b"]["a"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn let_typed_binding() {
    // let x : Nat := Nat.zero; x  →  letE Nat Nat.zero (bvar 0), nd=false
    let j = elab_json("let x : Nat := Nat.zero; x");
    assert_eq!(j["k"], "let");
    assert_eq!(j["nd"], false);
    assert_eq!(
        j["t"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
    assert_eq!(
        j["v"],
        serde_json::json!({"k": "const", "n": "Nat.zero", "us": []})
    );
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn have_is_a_let_with_non_dep_set() {
    // have h : Nat := Nat.zero; h  →  byte-identical to the `let` above
    // EXCEPT nd=true (design spec § Amendment 2).
    let j = elab_json("have h : Nat := Nat.zero; h");
    assert_eq!(j["k"], "let");
    assert_eq!(j["nd"], true);
    assert_eq!(
        j["t"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
    assert_eq!(
        j["v"],
        serde_json::json!({"k": "const", "n": "Nat.zero", "us": []})
    );
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn let_elided_type_is_inferred_from_the_value() {
    // let x := Nat.zero; x — the elided type is a fresh mvar the value's
    // `elab_term_ensuring_type` assigns to Nat; instantiate_mvars fills it.
    let j = elab_json("let x := Nat.zero; x");
    assert_eq!(j["k"], "let");
    assert_eq!(
        j["t"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn let_unused_binding_is_retained() {
    // let x : Nat := Nat.zero; Nat — `usedLetOnly := false` on the oracle
    // side, so the binding survives even though the body ignores it.
    let j = elab_json("let x : Nat := Nat.zero; Nat");
    assert_eq!(j["k"], "let");
    assert_eq!(
        j["b"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
}

#[test]
fn let_anonymous_binder() {
    // let _ : Nat := Nat.zero; Nat — the `Term.hole` letId shape.
    let j = elab_json("let _ : Nat := Nat.zero; Nat");
    assert_eq!(j["k"], "let");
    assert_eq!(
        j["t"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
}

#[test]
fn let_bracketed_binder_telescope() {
    // let f (y : Nat) : Nat := y; f  →  letE (Nat → Nat) (fun y => bvar 0) (bvar 0)
    let j = elab_json("let f (y : Nat) : Nat := y; f");
    assert_eq!(j["k"], "let");
    assert_eq!(j["t"]["k"], "pi");
    assert_eq!(j["v"]["k"], "lam");
    assert_eq!(j["v"]["b"], serde_json::json!({"k": "bvar", "i": 0}));
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn let_bare_ident_binder_unifies_its_domain() {
    // let f y : Nat := y; f — the bare-ident binder's domain is a fresh
    // mvar unified to Nat by the value's use site, so this matches the
    // bracketed form exactly.
    let j = elab_json("let f y : Nat := y; f");
    assert_eq!(j["k"], "let");
    assert_eq!(j["t"]["k"], "pi");
    assert_eq!(
        j["t"]["t"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
    assert_eq!(j["v"]["k"], "lam");
}

#[test]
fn have_hygiene_binder_is_named_this() {
    // have : Nat := Nat.zero; this — the `hygieneInfo` letId shape; the
    // oracle names the binder `this`, and the body's `this` must resolve
    // to it (binder names are erased by the encoder, but resolution is
    // what makes the body a `bvar` rather than an UnknownIdent error).
    let j = elab_json("have : Nat := Nat.zero; this");
    assert_eq!(j["k"], "let");
    assert_eq!(j["nd"], true);
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn let_nested_indexes_bvars() {
    // let x : Nat := Nat.zero; let y : Nat := x; y
    //   →  letE Nat Nat.zero (letE Nat (bvar 0) (bvar 0))
    let j = elab_json("let x : Nat := Nat.zero; let y : Nat := x; y");
    assert_eq!(j["k"], "let");
    assert_eq!(j["b"]["k"], "let");
    assert_eq!(j["b"]["v"], serde_json::json!({"k": "bvar", "i": 0}));
    assert_eq!(j["b"]["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn forall_inst_binder_carries_binder_info() {
    let j = elab_json("forall [inst : Add Nat], Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["bi"], "c");
}

#[test]
fn forall_inst_binder_anonymous() {
    let j = elab_json("forall [Add Nat], Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["bi"], "c");
}

#[test]
fn have_inst_binder_binds_and_abstracts() {
    // have f : forall [inst : Add Nat], Nat := fun [inst : Add Nat] =>
    //   Nat.zero; f
    //
    // The declared type's `forall [inst : Add Nat], Nat` only elaborates
    // through `extract_binder_group`'s new `instBinder` branch — the
    // value's `fun [inst : Add Nat] => …` already went through
    // `extract_fun_binder_views`'s existing `instBinder` arm before this
    // task, so `j["v"]["bi"]` alone would not discriminate a working
    // `extract_binder_group` from a broken one. `j["t"]["bi"]`/`j["t"]["t"]`
    // (the `Add Nat` domain, only reachable once the instBinder's BARE
    // type slot is read correctly) are the assertions this task's change
    // is actually responsible for.
    //
    // The body `f` is NOT a bare `bvar` here: `f`'s type is headed by an
    // instance-implicit `forallE`, so the existing (pre-Task-3) app-elab
    // machinery (`app/args.rs`'s `InstImplicit` arm, exercised via
    // `elab_atom`'s zero-arg path) auto-inserts the synthesized instance
    // — `f` elaborates to `f instAddNat`, the same auto-application the
    // real elaborator performs for any identifier whose type begins with
    // an instance-implicit binder. That is itself a second, independent
    // confirmation that the new `instBinder` pi carries `InstImplicit`
    // (a `Default`/`Implicit` binder-info would never trigger the
    // instance-arg search, and the whole term would fail to elaborate:
    // `instAddNat` would then be a wrong-typed value applied to a
    // pi-expecting `f`).
    let j =
        elab_json("have f : forall [inst : Add Nat], Nat := fun [inst : Add Nat] => Nat.zero; f");
    assert_eq!(j["k"], "let");
    assert_eq!(j["nd"], true);
    assert_eq!(j["t"]["k"], "pi");
    assert_eq!(j["t"]["bi"], "c");
    assert_eq!(
        j["t"]["t"],
        serde_json::json!({
            "k": "app",
            "f": {"k": "const", "n": "Add", "us": []},
            "a": {"k": "const", "n": "Nat", "us": []}
        })
    );
    assert_eq!(
        j["t"]["b"],
        serde_json::json!({"k": "const", "n": "Nat", "us": []})
    );
    assert_eq!(j["v"]["k"], "lam");
    assert_eq!(j["v"]["bi"], "c");
    assert_eq!(
        j["b"],
        serde_json::json!({
            "k": "app",
            "f": {"k": "bvar", "i": 0},
            "a": {"k": "const", "n": "instAddNat", "us": []}
        })
    );
}

/// `ensureType` (`TermElabM.lean:1935-1949`, M4b-3 P4 task 9): a binder
/// domain that is neither a `Sort` nor unifiable with one, and has no
/// `CoeSort` instance, is "type expected" — a distinct error from the
/// value-level `TypeMismatch`, because the oracle's `elabType` never
/// calls `ensureHasType`. `Nat.zero : Nat` is such a domain.
#[test]
fn non_type_binder_domain_without_coe_sort_is_type_expected() {
    match elab_result("fun (x : Nat.zero) => x") {
        Err(leanr_elab::ElabError::TypeExpected { .. }) => {}
        other => panic!("expected TypeExpected, got {other:?}"),
    }
}

/// `propagateExpectedType` (`Binders.lean:410-421`, M4b-3 P5 task 4):
/// an elided `fun` binder's domain comes from the ascribed expected
/// type's own forall domain, not a bare mvar.
#[test]
fn fun_binder_domain_comes_from_the_expected_type() {
    // The seam this closes: `(fun f => f Nat.zero : (Nat -> Nat) -> Nat)`.
    // Without propagation, `f`'s domain stays an unassigned mvar and the
    // application `f Nat.zero` cannot proceed.
    let j = elab_json("(fun f => f Nat.zero : (Nat -> Nat) -> Nat)");
    assert_eq!(j["k"], "lam");
    // f's domain is now `Nat -> Nat`, not a bare mvar.
    assert_eq!(j["t"]["k"], "pi");
    assert_eq!(j["t"]["t"]["n"], "Nat");
    assert_eq!(j["b"]["k"], "app");
}

/// The residual expected type threads one binder at a time: each
/// `propagate_expected_type` call instantiates the forall body with the
/// PREVIOUS binder's fvar before the next binder's domain elaborates.
#[test]
fn fun_propagation_walks_a_multi_binder_telescope() {
    // (fun x y => x : Nat -> Nat -> Nat) — both domains come from the
    // expected type, one binder at a time.
    let j = elab_json("(fun x y => x : Nat -> Nat -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["t"]["n"], "Nat");
    assert_eq!(j["b"]["b"]["i"], 1);
}

/// The non-`forallE` arm of `propagateExpectedType` drops the expected
/// type to `none` rather than keeping the stale one — once the
/// telescope runs out of expected-type domains, propagation ITSELF
/// must not error; the remaining binders' domains just stay mvars.
/// (`builtin/binder.rs`'s own `#[cfg(test)]` module pins that half
/// directly, in isolation from everything below.)
///
/// The BRIEF's own version of this test asserted the ascription still
/// succeeds as a plain `lam` with a bare-mvar second domain — checked
/// against the pinned oracle directly rather than trusted (per this
/// plan's own standing carry-over): `lean probe.lean` on
/// `#check (fun x y => Nat.zero : Nat -> Nat)` reports
///
/// ```text
/// error: Type mismatch
///   fun x y => Nat.zero
/// has type
///   (x : Nat) → ?m.3 x → Nat
/// but is expected to have type
///   Nat → Nat
/// ```
///
/// — a genuine, oracle-matching type mismatch, not a successful lambda:
/// `fun x y => Nat.zero` really is a 2-argument function and `Nat ->
/// Nat` can only type a 1-argument one, no matter how the non-`forallE`
/// arm answers. `elab_json` (`elab_term_ensuring_type` alone, no
/// fixpoint) cannot observe that: the outer ascription's
/// `ensureHasType` finds the mismatch and defers it to a postponed
/// `.coe` synthetic mvar (oracle: `synthesizeSyntheticMVar`'s `.coe`
/// arm) that `elab_json`'s harness never forces, so it silently reports
/// a bare unresolved `mvar` instead of the real answer — the brief's
/// test passed for the wrong reason. `elab_and_synthesize` (the real
/// top-level entry point: `elab_term` + the fixpoint +
/// `instantiate_mvars`) forces it, surfacing `ElabError::StuckCoercion`
/// — the oracle's own `.coe`-arm error (`SyntheticMVars.lean:304-310`),
/// not `TypeMismatch` (`mkCoe`'s IMMEDIATE-failure variant): the
/// failure is reached through the postponement ladder, matching the
/// oracle's own two-phase shape.
#[test]
fn fun_propagation_stops_at_a_non_forall_expected_type() {
    match support::elab_and_synthesize("(fun x y => Nat.zero : Nat -> Nat)") {
        Err(leanr_elab::ElabError::StuckCoercion { .. }) => {}
        other => panic!("expected a stuck coercion once forced, got {other:?}"),
    }
}

/// Mutation-testing note (standing carry-over, this plan's own): probed
/// BEFORE implementing this task, `fun_propagation_walks_a_multi_binder_telescope`
/// above already passes against the UNMODIFIED tree — `elab_ascription`'s
/// own final `isDefEq` between the fun's inferred (mvar-domain) Pi type
/// and the ascribed Pi type assigns both domain mvars post hoc, with no
/// help from `propagate_expected_type`, because neither binder's domain
/// is actually NEEDED before the whole lambda is built (the body `x`
/// never applies a bound variable as a function). That test is the
/// brief's own verbatim text (kept as specified), but it does not by
/// itself discriminate this task's feature, so this test supplies the
/// missing case: `g`, the SECOND binder, is applied to `x` in the body,
/// so `g`'s domain must already be assigned (not just structurally
/// matched later) for `g x` to elaborate at all — this can only work if
/// the residual expected type threaded correctly PAST the first binder
/// to reach the second `forallE`'s domain.
#[test]
fn fun_propagation_pins_the_second_binders_domain_too() {
    // fun x g => g x : Nat -> (Nat -> Nat) -> Nat
    // x : Nat (1st Pi domain), g : Nat -> Nat (2nd Pi domain, reached
    // only via the residual left after x's binder). Elaborating the
    // body `g x` needs g's domain pinned BEFORE the application can
    // proceed — the same seam `fun_binder_domain_comes_from_the_expected_type`
    // closes, but exercised on the SECOND binder rather than the first.
    let j = elab_json("(fun x g => g x : Nat -> (Nat -> Nat) -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["t"]["k"], "pi");
    assert_eq!(j["b"]["t"]["t"]["n"], "Nat");
    assert_eq!(j["b"]["b"]["k"], "app");
}
