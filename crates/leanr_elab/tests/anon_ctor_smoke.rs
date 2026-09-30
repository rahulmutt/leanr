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
/// Oracle: "Type mismatch\n  @Eq.refl ?m.2\nhas type\n  ∀ (a : ?m.2), …".
/// leanr reaches that message through the stuck-coercion reporter
/// (`StuckCoercion`: the type still holds an mvar, so the coercion is
/// postponed, then reported as a mismatch); `TypeMismatch` is the
/// immediate-failure twin. Either is the app elaborator's rejection.
#[test]
fn eq_counts_fields_after_its_promoted_parameters() {
    match support::elab_and_synthesize("(⟨⟩ : Eq Nat.zero Nat.zero)") {
        Err(ElabError::TypeMismatch { .. } | ElabError::StuckCoercion { .. }) => {}
        other => panic!("expected a type mismatch, got {other:?}"),
    }
}

/// The oracle accepts a private constructor from its own module
/// (`_private.Anon.0.PrivMk.mk`); leanr models no private names, so any
/// `_private.` constructor is the crate-wide seam (spec § Architecture,
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
