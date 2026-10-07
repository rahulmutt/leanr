//! M4b-4b: anonymous-constructor rejections and seams. The corpus
//! (`oracle_elab.rs`) is success-only, so every oracle ERROR this slice
//! ports is pinned here by variant. Each case was run on the pinned
//! oracle (`lean` on a prelude-mode scratch file importing `Elab0`,
//! `LEAN_PATH=tests/fixtures/elab`, one `#check` per case) before it was
//! written; the oracle's message is quoted beside it. Design spec
//! § Evidence.

mod support;

use leanr_elab::{AnonCtorError, ElabError};

fn anon_err(src: &str) -> AnonCtorError {
    match support::elab_and_synthesize(src) {
        Err(ElabError::InvalidAnonymousCtor(e)) => e,
        other => panic!("{src}: expected InvalidAnonymousCtor, got {other:?}"),
    }
}

#[test]
fn expected_type_unknown() {
    // "Invalid `⟨...⟩` notation: The expected type of this term could not
    // be determined"
    assert_eq!(
        anon_err("⟨Nat.zero, Nat.zero⟩"),
        AnonCtorError::ExpectedTypeUnknown
    );
}

#[test]
fn not_inductive() {
    // "Invalid `⟨...⟩` notation: The expected type `Nat → Nat` is not an
    // inductive type"
    assert!(matches!(
        anon_err("(⟨Nat.zero⟩ : Nat -> Nat)"),
        AnonCtorError::NotInductive { .. }
    ));
}

#[test]
fn no_ctors_and_multiple_ctors() {
    // "… The expected type `Empty` has no constructors"
    assert!(matches!(
        anon_err("(⟨⟩ : Empty)"),
        AnonCtorError::NoCtors { .. }
    ));
    // "… The expected type `Bool` has more than one constructor"
    assert!(matches!(
        anon_err("(⟨⟩ : Bool)"),
        AnonCtorError::MultipleCtors { .. }
    ));
}

#[test]
fn insufficient_fields_top_level() {
    // "Insufficient number of fields for `⟨...⟩` constructor: Constructor
    // `Prod.mk` has 2 explicit field, but only 1 was provided". The
    // oracle logs this under `errToSorry` and pads with `sorry`; leanr
    // throws (spec § Architecture, step 7).
    assert_eq!(
        anon_err("(⟨Nat.zero⟩ : Prod Nat Nat)"),
        AnonCtorError::InsufficientFields {
            ctor: "Prod.mk".to_string(),
            explicit: 2,
            provided: 1
        }
    );
}

#[test]
fn no_explicit_fields() {
    // "Insufficient number of fields for `⟨...⟩` constructor: Constructor
    // `True.intro` does not have explicit fields, but 1 was provided"
    assert_eq!(
        anon_err("(⟨Nat.zero⟩ : True)"),
        AnonCtorError::NoExplicitFields {
            ctor: "True.intro".to_string(),
            provided: 1
        }
    );
}

/// `Eq`'s index is promoted to a parameter (`numParams = 2`), so `k = 0`
/// and `⟨⟩` becomes a bare `Eq.refl` whose explicit `a` stays unapplied:
/// the app elaborator's type mismatch, NOT `InsufficientFields`. This
/// is the test that catches "count from 0 instead of numParams".
/// Oracle: "Type mismatch\n  Eq.refl\nhas type\n  ∀ (a : ?m.3), Eq a a\n
/// but is expected to have type\n  Eq Nat.zero Nat.zero". The oracle's
/// `trySynthInstance (CoeT (∀ a : ?m, Eq a a) Eq.refl (Eq Nat.zero
/// Nat.zero))` is `.none` (no `isDefEqStuck`), so `mkCoe`'s `| .none =>
/// failure` (`TermElabM.lean:1307`) reports the mismatch immediately
/// (`:1322`); the postponed `.coe` arm (`SyntheticMVars.lean:304-310`)
/// would have appended "failed to create type class instance for",
/// which the oracle's message lacks.
#[test]
fn eq_counts_fields_after_its_promoted_parameters() {
    match support::elab_and_synthesize("(⟨⟩ : Eq Nat.zero Nat.zero)") {
        Err(ElabError::TypeMismatch { .. }) => {}
        other => panic!("expected an immediate type mismatch, got {other:?}"),
    }
}

/// The oracle accepts a private constructor from its own module
/// (`_private.Anon.0.PrivMk.mk`); to leanr it is an IMPORTED private name, so
/// it is the imported-private-names seam (spec § Architecture,
/// step 5).
#[test]
fn private_constructor_is_the_private_names_seam() {
    match support::elab_and_synthesize("(⟨Nat.zero⟩ : PrivMk)") {
        Err(ElabError::UnsupportedSyntax(m)) => {
            assert!(m.contains("private names"), "{m}")
        }
        other => panic!("expected the private-names seam, got {other:?}"),
    }
}

/// `anon_ctor_args`'s shape assumption, checked end to end: separators,
/// comments and whitespace are not arguments. The oracle elaborates the
/// trivia form to `@Prod.mk … Nat.zero Nat.zero` (corpus `anon/trivia`);
/// a wrong filter shows up here as InsufficientFields or a type mismatch.
#[test]
fn separators_and_trivia_are_not_arguments() {
    support::elab_and_synthesize("(⟨Nat.zero /- c -/ ,   Nat.zero⟩ : Prod Nat Nat)")
        .expect("two arguments");
    support::elab_and_synthesize("(⟨⟩ : PUnit)").expect("zero arguments");
}

#[test]
fn insufficient_fields_in_the_nested_tail() {
    // "Insufficient number of fields for `⟨...⟩` constructor: Constructor
    // `T3.mk` has 3 explicit field, but only 2 were provided" — raised by
    // the synthesized tail `⟨Nat.zero, Nat.zero⟩ : T3`.
    assert_eq!(
        anon_err("(⟨Nat.zero, Nat.zero, Nat.zero⟩ : Prod Nat T3)"),
        AnonCtorError::InsufficientFields {
            ctor: "T3.mk".to_string(),
            explicit: 3,
            provided: 2
        }
    );
}

#[test]
fn a_tail_whose_type_never_resolves_reports_expected_type_unknown() {
    // "Invalid `⟨...⟩` notation: The expected type of this term could not
    // be determined": the tail postponed on `?β`, nothing solved it, and
    // the final resume runs with postponement off. Only the variant is
    // asserted; the error position is not (spec § Landed, error-positions
    // seam).
    assert_eq!(
        anon_err("(⟨Nat.zero, Nat.zero, Nat.zero⟩ : Prod Nat _)"),
        AnonCtorError::ExpectedTypeUnknown
    );
}

/// Review Focus 2: an error inside a RESUMED tail is the oracle's error,
/// not swallowed and not a seam. Oracle: "Invalid `⟨...⟩` notation: The
/// expected type `Nat → Nat` is not an inductive type".
#[test]
fn a_resumed_tail_reports_its_own_error() {
    assert!(matches!(
        anon_err(
            "sameAs (⟨Nat.zero, Nat.zero, Nat.zero⟩ : Prod Nat _) \
             (Prod.mk Nat.zero (fun x : Nat => x))"
        ),
        AnonCtorError::NotInductive { .. }
    ));
}

/// `⟨⟩` in a pattern position belongs to the match slice (later M4):
/// `fun ⟨a, b⟩ => …` expands to a `match` in the oracle and never reaches
/// the term elaborator. leanr must keep it a named seam, never route it
/// through `builtin::anon_ctor`.
#[test]
fn pattern_position_anonymous_constructor_stays_a_seam() {
    match support::elab_and_synthesize("fun ⟨a, b⟩ => a") {
        Err(ElabError::UnsupportedSyntax(m)) => {
            assert!(m.contains("belongs to the match slice"), "{m}")
        }
        other => panic!("expected the pattern-position seam, got {other:?}"),
    }
}

/// `AnonLoop.mk : AnonLoop → AnonLoop` has ONE explicit field, so the
/// flatten tail of `⟨x, y⟩` starts where it began (`from + k - 1 =
/// from`) and never shrinks. The oracle stops at `elabTerm`'s
/// `withIncRecDepth`: "maximum recursion depth has been reached". leanr's
/// tail-depth guard must turn that into `MaxRecDepth`, not a stack
/// overflow (Global Constraint: never panic).
#[test]
fn a_tail_that_never_shrinks_hits_max_rec_depth() {
    match support::elab_and_synthesize("(⟨Nat.zero, Nat.zero⟩ : AnonLoop)") {
        Err(ElabError::MaxRecDepth) => {}
        other => panic!("expected MaxRecDepth, got {other:?}"),
    }
}

/// A flatten tail gets the implicit lambda like any other `elabTerm`.
/// `FI.mk` has one explicit field `f : {α : Type} → α → α`, so ALL of
/// `⟨Nat.zero, Nat.zero⟩` is the tail, elaborated against that implicit
/// forall. The oracle introduces `α` first and reports the arrow under
/// it: "Invalid `⟨...⟩` notation: The expected type `α✝ → α✝` is not an
/// inductive type". A tail that skipped the implicit lambda would report
/// the implicit forall `{α : Type} → α → α` itself.
#[test]
fn a_tail_against_an_implicit_forall_gets_the_implicit_lambda() {
    let ty = support::with_elab("(⟨Nat.zero, Nat.zero⟩ : FI)", |elab, stx, kinds| match elab
        .elab_term_and_synthesize(stx, kinds, None)
    {
        Err(ElabError::InvalidAnonymousCtor(AnonCtorError::NotInductive { ty })) => {
            let base = elab.view.store;
            let mut st = support::EncSt::default();
            support::encode_expr(elab.mctx.store(), Some(base), ty, &mut st)
        }
        other => panic!("expected NotInductive, got {other:?}"),
    });
    assert_eq!(ty["k"], "pi", "{ty}");
    assert_eq!(
        ty["bi"], "d",
        "the arrow `α → α`, not the implicit forall: {ty}"
    );
    assert_eq!(
        ty["t"]["k"], "fvar",
        "`α` is the implicit lambda's local: {ty}"
    );
}
