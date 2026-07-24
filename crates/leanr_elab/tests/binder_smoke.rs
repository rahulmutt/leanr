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
use leanr_meta::{Config, MetaCtx};
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
        &reducibility,
        &matchers,
        &instances,
        &default_instances,
        &projection_fns,
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
