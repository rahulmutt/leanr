//! M4b-4a: dot-notation rejections and seams. The corpus
//! (`oracle_elab.rs`) is success-only, so every oracle ERROR this
//! slice ports is pinned here by variant and reason. Each case was run
//! on the pinned oracle (`lean` on a prelude-mode scratch file importing
//! `Elab0`, `LEAN_PATH=tests/fixtures/elab`, one `#check` per case)
//! before it was written; the oracle's message is quoted beside it.

mod support;

use leanr_elab::{ElabError, InvalidFieldReason, InvalidProjectionReason};

fn proj_reason(src: &str) -> InvalidProjectionReason {
    match support::elab_and_synthesize(src) {
        Err(ElabError::InvalidProjection { reason, .. }) => reason,
        other => panic!("{src}: expected InvalidProjection, got {other:?}"),
    }
}

fn seam(src: &str) -> String {
    match support::elab_and_synthesize(src) {
        Err(ElabError::UnsupportedSyntax(m)) => m,
        other => panic!("{src}: expected a named seam, got {other:?}"),
    }
}

#[test]
fn projection_rejections_match_the_oracle() {
    // "Invalid projection: Projections extract constructor fields for
    // one-constructor inductive types. The expression Nat.zero has type
    // `Nat` which is not a one-constructor inductive type."
    assert_eq!(
        proj_reason("(Nat.zero).1"),
        InvalidProjectionReason::NotOneCtor
    );
    // Same message, the base an identifier rather than a paren.
    assert_eq!(
        proj_reason("Nat.zero.1"),
        InvalidProjectionReason::NotOneCtor
    );
    // "Invalid projection: Index `3` is invalid for this structure; it
    // must be between 1 and 2"
    assert_eq!(
        proj_reason("fun (o : One) => o.3"),
        InvalidProjectionReason::IndexOutOfRange {
            idx: 3,
            num_fields: 2
        }
    );
    // "Invalid projection: Projections cannot be used on functions, and
    // f has function type `Nat → Nat`"
    assert_eq!(
        proj_reason("fun (f : Nat -> Nat) => f.1"),
        InvalidProjectionReason::OnFunction
    );
    // "Invalid projection: Projection operates on types of the form
    // `C ...` where C is a constant. The expression x has type `Type`
    // which does not have the necessary form." — a sort, then an fvar
    // (same message, "has type `a`").
    assert_eq!(
        proj_reason("fun (x : Type) => x.1"),
        InvalidProjectionReason::NotConstApp
    );
    assert_eq!(
        proj_reason("fun (a : Type) (x : a) => x.1"),
        InvalidProjectionReason::NotConstApp
    );
    // "Invalid projection: Explicit universe levels are only supported
    // for inductive types defined using the `structure` command. The
    // expression o has type `One` which is not a `structure`."
    assert_eq!(
        proj_reason("fun (o : One) => o.1.{0}"),
        InvalidProjectionReason::ExplicitUnivsOnInductive
    );
    // Review Focus 4 — "error(lean.projNonPropFromProp): Invalid
    // projection: Cannot project a value of non-propositional type Nat
    // from the expression h which has propositional type PBox"
    assert_eq!(
        proj_reason("fun (h : PBox) => h.1"),
        InvalidProjectionReason::NonPropFromProp
    );
}

#[test]
fn field_rejections_match_the_oracle() {
    // "error(lean.invalidField): Invalid field `zzz`: The environment
    // does not contain `Function.zzz`, so it is not possible to project
    // the field `zzz` from an expression f of type `Nat → Nat`"
    match support::elab_and_synthesize("fun (f : Nat -> Nat) => (f).zzz") {
        Err(ElabError::InvalidField {
            reason: InvalidFieldReason::NotFound { full_name },
            field,
            ..
        }) => {
            assert_eq!(full_name, "Function.zzz");
            assert_eq!(field, "zzz");
        }
        other => panic!("expected InvalidField NotFound, got {other:?}"),
    }
    // "error(lean.invalidField): Invalid field notation: Field
    // projection operates on types of the form `C ...` where C is a
    // constant. The expression x has type `a` which does not have the
    // necessary form."
    match support::elab_and_synthesize("fun (a : Type) (x : a) => (x).foo") {
        Err(ElabError::InvalidField {
            reason: InvalidFieldReason::NotConstApp,
            ..
        }) => {}
        other => panic!("expected InvalidField NotConstApp, got {other:?}"),
    }
}

#[test]
fn placeholder_head_is_rejected() {
    // "A placeholder `_` cannot be used where a function is expected"
    assert!(matches!(
        support::elab_and_synthesize("_ Nat.zero"),
        Err(ElabError::PlaceholderAsFunction)
    ));
}

#[test]
fn p2_p3_p4_constructs_are_named_seams() {
    // tryPostponeIfMVar (App.lean:1680) — P2 owns postponement. The
    // oracle postpones, then (nothing ever pins `x`'s type) reports
    // "Invalid projection: Type of x is not known; cannot resolve
    // projection `1`"; leanr cannot postpone yet, so it seams.
    assert!(seam("fun x => x.1").contains("M4b-4a P2"));
    // `.const` resolution via findMethod? — P3. The oracle elaborates
    // this to `Nat.zero.succ : Nat`.
    assert!(seam("(Nat.zero).succ").contains("M4b-4a P3"));
    // Review Focus 2: a seam is NOT retried through `unfoldDefinition?`
    // — S3Alias must seam, never report S3's InvalidField. The oracle
    // (which has `findMethod?`) retries and reports "Invalid field
    // `zzz`: The environment does not contain `S3.zzz` … of type `S3`".
    // The seam must name `S3Alias`: were it retried, the unfolded `S3`
    // would ALSO seam P3, so the P3 marker alone cannot tell the two
    // apart (controller ruling R1).
    let m = seam("fun (s : S3Alias) => (s).zzz");
    assert!(m.contains("M4b-4a P3"), "{m}");
    assert!(m.contains("`S3Alias`"), "{m}");
}
