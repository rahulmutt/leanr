//! Fast, hermetic leanr-side structural checks for the binder
//! elaborators. Uses the committed `Elab0.olean` (no Lean toolchain
//! needed). The AUTHORITATIVE differential check is `oracle_elab` (see
//! Task 5); these assert coarse structure for a quick red/green loop and
//! deliberately do not pin exact encoder bytes (universe levels etc.).

mod support;
use support::{elab_result, encode_expr, replay_fixture_in, EncSt, Replayed};

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

/// Fix round 1, Finding 1: the ORIGINAL version of this test (and its
/// two neighbors below, all since rewritten) asserted `fun (x : Nat) :
/// Nat => x` elaborates — a term the real oracle REJECTS. Checked
/// directly against the pinned binary: `expandFun`'s `optType` macro
/// arm (`Lean/Elab/Binders.lean:648-651`) distributes `T` over the
/// BINDERS via `expandSimpleBinderWithType` (`:265-270`), which only
/// accepts a bare ident or `_` hole — `(x : Nat)` is neither, so real
/// Lean reports `unexpected type ascription` for that source, not a
/// successful lambda. `fun x : Nat => x` (bare ident) is the shape the
/// macro actually accepts; it also still catches the ORIGINAL
/// regression this test's predecessor was written for: `optType`'s
/// non-empty wrapper holds ONE `typeSpec` node (`[":", T]` is
/// `typeSpec`'s OWN children, not the wrapper's direct children), so a
/// flat `nth(1)` read off the wrapper used to silently land on `None`
/// for every `fun x : T => e` — if that regressed, `x`'s domain would
/// stay an elided mvar here instead of `Nat`.
#[test]
fn fun_opt_type_distributes_to_a_single_binder() {
    // fun x : Nat => x
    let j = elab_json("fun x : Nat => x");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["t"]["k"], "const");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(j["b"]["k"], "bvar");
    assert_eq!(j["b"]["i"], 0);
}

/// oracle: `expandFun`'s `optType` arm distributes `T` to EVERY simple
/// binder in the group, independently — `fun x y : Nat => x` expands to
/// `fun (x : Nat) (y : Nat) => x`, not just the first name.
#[test]
fn fun_opt_type_distributes_across_multiple_binders() {
    // fun x y : Nat => x — both x and y get domain Nat; body refers to
    // the OUTER binder x, bvar index 1 (y is innermost, index 0).
    let j = elab_json("fun x y : Nat => x");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["t"]["n"], "Nat");
    assert_eq!(j["b"]["b"], serde_json::json!({"k": "bvar", "i": 1}));
}

/// oracle: `expandSimpleBinderWithType`'s `else` branch —
/// `Macro.throwErrorAt type "unexpected type ascription"`
/// (`Binders.lean:265-270`), fired when `optType` is present but a
/// binder item is neither a bare ident nor a `_` hole. Verified against
/// the pinned binary directly: `fun (x : Nat) : Nat => x` really does
/// report `unexpected type ascription`, not a successful lambda (see
/// `fun_opt_type_distributes_to_a_single_binder`'s own doc for the
/// history of this being asserted the other way).
#[test]
fn fun_opt_type_rejects_a_non_simple_binder() {
    match elab_result("fun (x : Nat) : Nat => x") {
        Err(leanr_elab::ElabError::IllFormedSyntax(msg)) => {
            assert!(msg.contains("unexpected type ascription"), "got {msg:?}");
        }
        other => panic!("expected IllFormedSyntax(\"unexpected type ascription\"), got {other:?}"),
    }
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

// Fix round 1, Finding 3: `fun_propagation_walks_a_multi_binder_telescope`
// (`(fun x y => x : Nat -> Nat -> Nat)`) lived here and is DELETED, not
// kept — the mutation check in this task's own report showed it passes
// even with `propagate_expected_type` stubbed to `Ok(None)`:
// `elab_ascription`'s own final `isDefEq` between the fun's inferred
// (mvar-domain) Pi type and the ascribed Pi type assigns both domain
// mvars post hoc, with no help from propagation, because neither
// binder's domain is actually NEEDED before the whole lambda is built
// (the body `x` never applies a bound variable as a function).
// `fun_propagation_pins_the_second_binders_domain_too` below subsumes
// its case (also a multi-binder telescope) while actually
// discriminating the feature (confirmed by the same mutation check).

/// The non-`forallE` arm of `propagateExpectedType` drops the expected
/// type to `none` rather than keeping the stale one — once the
/// telescope runs out of expected-type domains, propagation ITSELF
/// must not error; the remaining binders' domains just stay mvars.
/// (`builtin/binder/fun.rs`'s own `#[cfg(test)]` module pins that half
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
/// Renamed from `fun_propagation_stops_at_a_non_forall_expected_type`
/// (fix round 1, minor): the OLD name described the mechanism
/// (propagation stopping), but what this actually pins, end-to-end, is
/// the downstream STUCK COERCION `ensureHasType` produces once that
/// stopped propagation leaves an arity mismatch the fixpoint forces.
#[test]
fn fun_more_binders_than_expected_pi_levels_is_a_stuck_coercion() {
    match support::elab_and_synthesize("(fun x y => Nat.zero : Nat -> Nat)") {
        Err(leanr_elab::ElabError::StuckCoercion { .. }) => {}
        other => panic!("expected a stuck coercion once forced, got {other:?}"),
    }
}

/// Mutation-testing note (standing carry-over, this plan's own): see
/// the deleted `fun_propagation_walks_a_multi_binder_telescope`'s own
/// note above — `elab_ascription`'s own final `isDefEq` between the
/// fun's inferred (mvar-domain) Pi type and the ascribed Pi type
/// assigns both domain mvars post hoc whenever neither binder's domain
/// is actually NEEDED before the whole lambda is built. This test
/// supplies the discriminating case that one didn't: `g`, the SECOND
/// binder, is applied to `x` in the body, so `g`'s domain must already
/// be assigned (not just structurally matched later) for `g x` to
/// elaborate at all — this can only work if the residual expected type
/// threaded correctly PAST the first binder to reach the second
/// `forallE`'s domain.
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

/// Fix round 1, Finding 2: an ELIDED `fun` binder whose domain becomes
/// a CLASS type ONLY via `propagate_expected_type` must still register
/// as a local instance — the oracle's own `elabFunBinderViews` runs
/// `propagateExpectedType` BEFORE its `isClass? type` test
/// (`Binders.lean:442,444`), not after. `NoInst` (`Elab0.lean`) is the
/// fixture's class with ZERO instances anywhere — global or local — so
/// this can only succeed by finding `inst` (binder 1, propagated to
/// `NoInst Nat`) as a LOCAL instance for binder 2's own forall-typed
/// use of `f`. Before this fix, `push_local_decl`'s inline class check
/// ran BEFORE propagation and always saw `inst`'s domain as an
/// unassigned mvar, so it silently missed the instance and this would
/// fail with a synthesis error instead of elaborating.
#[test]
fn fun_elided_binder_registers_as_a_local_instance_only_after_propagation() {
    // fun inst f => f
    //   : NoInst Nat -> (forall [inst2 : NoInst Nat], Nat) -> Nat
    // `inst`'s domain (elided) becomes `NoInst Nat` via propagation.
    // `f`'s own domain (also elided) becomes the inst-implicit forall,
    // so eliding `f` as the body auto-applies its own inst-implicit
    // parameter — findable only via `inst`, the local instance.
    let j =
        elab_json("(fun inst f => f : NoInst Nat -> (forall [inst2 : NoInst Nat], Nat) -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["b"]["k"], "lam");
    // f (bvar 0, innermost) applied to inst (bvar 1, outer) — the
    // LOCAL instance search resolved to the propagation-typed binder.
    assert_eq!(j["b"]["b"]["k"], "app");
    assert_eq!(j["b"]["b"]["f"], serde_json::json!({"k": "bvar", "i": 0}));
    assert_eq!(j["b"]["b"]["a"], serde_json::json!({"k": "bvar", "i": 1}));
}

// -- M4b-3 P5 task 5: implicit-lambda insertion, the `.yes` path -----

#[test]
fn implicit_lambda_wraps_against_an_implicit_forall() {
    // `(Nat.zero : {a : Type} -> Nat)` — the expected type is an
    // implicit forall, so the oracle wraps the WHOLE term in a lambda
    // rather than dispatching on its kind.
    let j = elab_json("(Nat.zero : {a : Type} -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "i");
    assert_eq!(j["b"]["k"], "const");
    assert_eq!(j["b"]["n"], "Nat.zero");
}

#[test]
fn implicit_lambda_wraps_instance_implicit_too() {
    // `Add`/`instAddNat` are in Elab0's environment (controller
    // amendment 2 confirms this record is runnable as written).
    let j = elab_json("(Nat.zero : [inst : Add Nat] -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "c");
    assert_eq!(j["b"]["k"], "const");
    assert_eq!(j["b"]["n"], "Nat.zero");
}

#[test]
fn implicit_lambda_nests_for_several_implicit_binders() {
    let j = elab_json("(Nat.zero : {a : Type} -> {b : Type} -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "i");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["bi"], "i");
    assert_eq!(j["b"]["b"]["n"], "Nat.zero");
}

/// Fix round 1, finding 2: pins `elab_implicit_lambda`'s own headline
/// correction (the loop's stop condition is `c.isExplicit`, i.e.
/// `BinderInfo::Default`, NOT `!(Implicit || InstImplicit)`) with an
/// actual test — the two tests above use two IDENTICAL binder kinds, so
/// a regression back to the brief's wrong predicate (which would stop
/// peeling as soon as it saw the strict-implicit `b` and hand
/// `elab_implicit_lambda_aux` the un-peeled `⦃b : Type⦄ -> Nat`
/// residual) would still pass them both. Confirmed against the pinned
/// `lean` binary (`elab.rs`'s own `elab_implicit_lambda` doc comment):
/// `(Nat.zero : {a : Type} -> ⦃b : Type⦄ -> Nat)` elaborates to `fun
/// {a : Type} ⦃b : Type⦄ => Nat.zero`, both binders absorbed into ONE
/// wrap. Being mixed-kind (`i` then `s`), this also closes the
/// nesting-ORDER gap the two-identical-implicit test above cannot
/// cover: a bug that reversed `fvars`' push order (or otherwise mixed
/// up which binder became the outer vs. inner `lam`) would be invisible
/// there but flips `bi`/`bi` here.
#[test]
fn implicit_lambda_nests_across_implicit_and_strict_implicit() {
    let j = elab_json("(Nat.zero : {a : Type} -> ⦃b : Type⦄ -> Nat)");
    assert_eq!(j["bi"], "i");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["bi"], "s");
    assert_eq!(j["b"]["b"]["n"], "Nat.zero");
}

/// oracle: `unless c.isImplicit || c.isInstImplicit do return .no`, and
/// `useImplicitLambda`'s own doc: "implicit lambdas are not triggered
/// by the strict implicit binder annotation". Confirmed against the
/// pinned `lean` binary: `(Nat.zero : ⦃a : Type⦄ -> Nat)` reports a
/// plain type-mismatch error — `Nat.zero has type Nat ... but is
/// expected to have type ⦃a : Type⦄ → Nat of sort Type 1` — with no
/// lambda wrap and no implicit-lambda-flavoured message at all.
///
/// Controller amendment 3: the brief's own draft of this test ended in
/// `_ => {}`, so it passed on every outcome except an `UnsupportedSyntax`
/// naming "implicit lambda" — including an unrelated failure, and
/// including strict-implicit wrongly firing and reporting some OTHER
/// error. Rewritten to discriminate: `Ok` must not be a `lam`; `Err`
/// must be the ascription's own type-mismatch machinery, not a named
/// implicit-lambda seam (there is no longer any such seam after this
/// task — `check_implicit_lambda`'s old `UnsupportedSyntax("implicit
/// lambda insertion — M4b-3 P5")` is gone, replaced by the real wrap);
/// anything else panics rather than being silently accepted.
#[test]
fn implicit_lambda_does_not_fire_on_strict_implicit() {
    match elab_result("(Nat.zero : ⦃a : Type⦄ -> Nat)") {
        Err(leanr_elab::ElabError::TypeMismatch { .. }) => {}
        Err(other) => panic!("expected the ascription's own TypeMismatch, got {other:?}"),
        Ok(e) => panic!("strict-implicit wrongly succeeded, no wrap should be possible: {e:?}"),
    }
}

/// oracle: `App.lean:2269-2270` — `@` exists partly to disable the
/// implicit-lambda feature: `` `(@($t)) `` and `` `(@$t) `` both
/// elaborate `t` with `implicitLambda := false`.
///
/// Fix round 1, finding 1: the original draft used `@(Nat.succ
/// Nat.zero)`, whose inner kind is `Lean.Parser.Term.paren` — that
/// routes to `app::elab_explicit`'s `other` arm, a SEPARATE,
/// pre-existing, un-implemented seam (`` `(@($t)) ``/`` `(@$t) ``'s own
/// fallback, `seam_audit.rs`'s `("@(Nat.succ Nat.zero)", "later M4")`
/// case — "M4b-3 P5" at the time this test was written, retargeted by
/// Task 12 once P5 completed without that seam) that errors
/// unconditionally, before the expected type — and
/// therefore before `use_implicit_lambda` — is ever consulted. A
/// mutation check confirmed that term's error is IDENTICAL whether or
/// not `block_implicit_lambda` actually blocks the wrap, so it pinned
/// the wrong seam.
///
/// `@Nat.zero`'s inner kind is plain `<ident>`, which `elab_explicit`
/// already routes to `elab_atom` (a real, implemented path,
/// `app/mod.rs:207`) — confirmed against the pinned `lean` binary:
/// `(@Nat.zero : {a : Type} -> Nat)` reports `Type mismatch: Nat.zero
/// has type Nat ... but is expected to have type {a : Type} → Nat`,
/// i.e. `@` disables the wrap and `Nat.zero`'s own (non-implicit) type
/// is checked directly against the un-peeled expected type — NOT a
/// `lam`. With blocking intact this is `Err(TypeMismatch)`; a mutation
/// that breaks `block_implicit_lambda`'s `explicit` arm turns it into
/// `Ok` with a `lam` head (checked below).
#[test]
fn at_sign_disables_implicit_lambda() {
    match elab_result("(@Nat.zero : {a : Type} -> Nat)") {
        Err(leanr_elab::ElabError::TypeMismatch { .. }) => {}
        other => panic!("expected the ascription's own TypeMismatch, got {other:?}"),
    }
}

/// Fix round 1, finding 3: oracle `elabImplicitLambda`
/// (`TermElabM.lean:1814-1815`) hygienizes the wrap's own binder name
/// (`withFreshMacroScope <| .. addMacroScope n ..`) before pushing it,
/// so a user identifier that happens to share the expected type's
/// binder name still resolves to whatever it would have without the
/// wrap. `elab_implicit_lambda` pushes the wrap's fvar with `None`
/// instead of the expected type's own `binder_name` to reproduce that
/// EFFECT (not the mechanism — see this crate's own doc comment on the
/// push site): an unnamed local is never found by
/// `lctx_lookup_by_name`, so lookup falls through to the real outer
/// binder.
///
/// `(fun (a : Type) => (a : {a : Type} -> Type))`: the outer `fun`
/// binds `a`; its body ascribes the SAME identifier `a` against
/// `{a : Type} -> Type`, an implicit forall whose OWN binder is also
/// named `a`. Both readings of the inner `a` typecheck (both the outer
/// binder and the wrap's own fvar have type `Type`, checked against the
/// residual `Type`), so this is exactly the case fix round 1 flagged:
/// silently producing a DIFFERENT (self-referential) term rather than
/// erroring. Confirmed against the pinned `lean` binary's own
/// resolution rule (macro-scope hygiene: an unqualified user `a` always
/// binds to the nearest SOURCE-level `a`, never to a hygienically
/// introduced one) — the oracle's wrap fvar can never be what a plain
/// user identifier resolves to.
///
/// If the wrap's own fvar were pushed under the SHARED name `a`
/// (mutation below), `lctx_lookup_by_name` would find the MOST
/// RECENTLY pushed `a` — the wrap's own fvar, not the outer `fun`'s —
/// and the body would self-reference (`bvar 0`, the identity-shaped
/// inner lambda) instead of reaching the outer binder (`bvar 1`).
#[test]
fn implicit_lambda_wrap_binder_does_not_capture_a_same_named_outer_binder() {
    let j = elab_json("(fun (a : Type) => (a : {a : Type} -> Type))");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "d");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["bi"], "i");
    // bvar 1 = the OUTER `fun`'s `a`, not the wrap's own (unused) fvar
    // at bvar 0.
    assert_eq!(j["b"]["b"], serde_json::json!({"k": "bvar", "i": 1}));
}

/// oracle: `elabBinderViews` (`Elab/Binders.lean:216-218`) — an
/// instance-implicit binder whose type is not a class is rejected ("invalid
/// binder annotation, type is not a class instance"). Each source was run
/// on the pinned binary. `forall [i : _]` is included because an
/// unassigned metavariable is "not a class" too.
#[test]
fn inst_binder_whose_type_is_not_a_class_is_rejected() {
    for src in [
        "forall [i : Nat], Nat",
        "[i : Nat] -> Nat",
        "forall [i : _], Nat",
    ] {
        match elab_result(src) {
            Err(leanr_elab::ElabError::InvalidBinderAnnotation { .. }) => {}
            other => panic!("{src}: expected InvalidBinderAnnotation, got {other:?}"),
        }
    }
}

/// oracle: `checkLocalInstanceParameters` (`Elab/Binders.lean:199-206`) —
/// a function-typed instance binder whose non-instance parameter the body
/// does not depend on is rejected. The third source fails on its SECOND
/// parameter: the first (`a : Type`) has a forward dependency, so only a
/// check that keeps walking after it finds `Nat`.
#[test]
fn parametric_inst_binder_without_forward_dependency_is_rejected() {
    for src in [
        "forall [i : Nat -> Add Nat], Nat",
        "forall [i : forall {a : Type}, Add Nat], Nat",
        "forall [i : forall (a : Type), Nat -> Add a], Nat",
    ] {
        match elab_result(src) {
            Err(leanr_elab::ElabError::InvalidParametricLocalInstance { .. }) => {}
            other => panic!("{src}: expected InvalidParametricLocalInstance, got {other:?}"),
        }
    }
}

/// `check_local_instance_parameters`'s own pushed parameter (the `a` in
/// `forall (a : Type), Add a`) must not escape into the OUTER `forall`'s
/// body: it exists only to test forward dependency and is popped
/// (`lctx_restore`) before `push_binder_group` pushes the outer `i`. Since
/// the outer body's `a` was never bound by anything the elaborator keeps,
/// it is an unknown identifier — confirmed against the pinned `lean`
/// binary: `Unknown identifier 'a'`.
#[test]
fn checked_parameter_does_not_leak_past_the_check() {
    match elab_result("forall [i : forall (a : Type), Add a], a") {
        Err(leanr_elab::ElabError::UnknownIdent(_)) => {}
        other => panic!("expected UnknownIdent, got {other:?}"),
    }
}
