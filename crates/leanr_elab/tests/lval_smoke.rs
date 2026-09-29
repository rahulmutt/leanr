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
    // The same holds for a field `S3` DOES have: the oracle's
    // `findMethod?` on `S3Alias` fails, retries, and elaborates this to
    // `S1.a (S2.toS1 (S3.toS2 s))`; leanr must seam on `S3Alias` rather
    // than retry. (The corpus reaches the unfold retry through a field
    // INDEX instead: `lval/unfold-alias-idx`.)
    let m = seam("fun (s : S3Alias) => (s).a");
    assert!(m.contains("M4b-4a P3"), "{m}");
    assert!(m.contains("`S3Alias`"), "{m}");
}

/// Review Focus 2: a postponed projection whose type never becomes
/// known is reported at the last rung with the oracle's error — never
/// as `ElabError::Postpone`, never as a seam. Each message is the
/// pinned oracle's (`#check`, prelude file importing `Elab0`).
#[test]
fn postponed_projections_on_an_unknown_type_report_the_oracle_error() {
    // "Invalid projection: Type of x is not known; cannot resolve projection `1`"
    assert_eq!(
        proj_reason("fun x => x.1"),
        InvalidProjectionReason::TypeUnknown
    );
    // Same message, raised inside `(e :)`'s own `withSynthesize (postpone := .no)`.
    assert_eq!(
        proj_reason("fun x => (x.1 :)"),
        InvalidProjectionReason::TypeUnknown
    );
    // Same message through a reducible alias (`outParam ?m`).
    assert_eq!(
        proj_reason("fun (x : outParam _) => x.1"),
        InvalidProjectionReason::TypeUnknown
    );
    // "Invalid projection: Type of ?m.4 is not known; cannot resolve projection `1`"
    assert_eq!(
        proj_reason("(_ : _).1"),
        InvalidProjectionReason::TypeUnknown
    );
    // "Invalid field notation: Type of x is not known; cannot resolve field `fst`"
    match support::elab_and_synthesize("fun x => (x).fst") {
        Err(ElabError::InvalidField {
            reason: InvalidFieldReason::TypeUnknown,
            ..
        }) => {}
        other => panic!("expected InvalidField TypeUnknown, got {other:?}"),
    }
}

#[test]
fn projection_function_rejections_match_the_oracle() {
    // "too many explicit universe levels for `Poly.val`"
    assert!(matches!(
        support::elab_and_synthesize("fun (q : Poly Nat) => (q).val.{0, 0}"),
        Err(ElabError::TooManyUniverseLevels(_))
    ));
    // Review Focus 3 — "Argument `self` was already set" (`addNamedArg`,
    // Arg.lean:56-59, called at App.lean:1868).
    match support::elab_and_synthesize("fun (s : S3) => (s).a (self := s)") {
        Err(ElabError::DuplicateNamedArg(n)) => assert_eq!(n, "self"),
        other => panic!("expected DuplicateNamedArg(self), got {other:?}"),
    }
}

#[test]
fn recursor_head_with_a_projection_is_not_an_eliminator() {
    // Review Focus 1: `Nat.rec.1` resolves the LVal on `Nat.rec`'s type —
    // consumeImplicits fills `motive`, the next binder is explicit, so
    // `.forallE` + fieldIdx = OnFunction. It must NOT hit the
    // `elabAsElim` recursor seam. Oracle: "Invalid projection:
    // Projections cannot be used on functions, and `@Nat.rec.{?u.1} ?m.1` has
    // function type `(zero : ?m.1 Nat.zero) → (succ : …) → (t : Nat) →
    // ?m.1 t`".
    assert_eq!(
        proj_reason("Nat.rec.1"),
        InvalidProjectionReason::OnFunction
    );
}

#[test]
fn projection_function_missing_from_the_environment_is_an_error_not_a_panic() {
    // Malformed `structureExt`: every `projFn` renamed to its bare field
    // name (`a`, `b`, …), which no fixture declares as a constant. The
    // oracle's `mkConst` (App.lean:1862) throws "unknown constant";
    // leanr must not reach `mk_const`'s `expect`. Not an oracle case —
    // no well-formed `.olean` can produce it.
    let r = support::elab_and_synthesize_doctored("fun (p : Prod Nat Nat) => p.1", |ss| {
        for s in ss.iter_mut() {
            for f in s.field_info.iter_mut() {
                f.proj_fn = f.field_name;
            }
        }
    });
    match r {
        Err(ElabError::Internal(m)) => assert!(m.contains("App.lean:1862"), "{m}"),
        other => panic!("expected Internal (unknown projFn), got {other:?}"),
    }
}

/// `@` on a projection head. The oracle's `@` patterns in FUNCTION
/// position (`elabAppFn`, `App.lean:2110-2118`) accept `@$(_).$_:fieldIdx`,
/// `@$(_).$_:ident` and `@$(_).$_:ident.{$_us,*}` — but there is NO
/// `@$(_).$_:fieldIdx.{us}` row, so `@(e).1.{us} a` falls to
/// `` `(@$_) => throwUnsupportedSyntax `` (`:2118`). Oracle, one `#check`
/// each on a prelude-mode scratch file importing `Elab0`:
///
/// ```text
/// @(Prod.mk Nat.succ Nat.zero).fst Nat.zero         -- @Prod.fst.{0, 0} (Nat → Nat) Nat (…) Nat.zero : Nat
/// @(Prod.mk Nat.succ Nat.zero).1 Nat.zero           -- same
/// @(Prod.mk Nat.succ Nat.zero).fst.{0,0} Nat.zero   -- same
/// @(Prod.mk Nat.succ Nat.zero).1.{0,0} Nat.zero     -- error: unexpected syntax
/// ```
///
/// In TERM position (`elabExplicit`, `App.lean:2260-2271`) the same
/// missing row routes `@(e).1.{us}` to the `` `(@$t) `` arm instead —
/// `elabTerm t (implicitLambda := false)` — which elaborates, so there
/// the oracle gives `@Prod.fst.{0, 0} Nat Nat (…)` for all four forms.
#[test]
fn explicit_on_projection_heads_matches_the_oracle() {
    let ok =
        |src: &str| support::elab_and_synthesize(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    // Function position.
    let want = ok("@(Prod.mk Nat.succ Nat.zero).fst Nat.zero");
    assert_eq!(ok("@(Prod.mk Nat.succ Nat.zero).1 Nat.zero"), want);
    assert_eq!(ok("@(Prod.mk Nat.succ Nat.zero).fst.{0,0} Nat.zero"), want);
    // leanr maps the oracle's `throwUnsupportedSyntax` here exactly as it
    // maps every other `App.lean:2118` shape (`peel_head`'s
    // invalid-`@` arm; `app_smoke.rs`, `seam_audit.rs`).
    let m = seam("@(Prod.mk Nat.succ Nat.zero).1.{0,0} Nat.zero");
    assert!(m.contains("App.lean:2118"), "{m}");
    // Term position.
    let want = ok("@(Prod.mk Nat.zero Nat.zero).1");
    assert_eq!(ok("@(Prod.mk Nat.zero Nat.zero).fst"), want);
    assert_eq!(ok("@(Prod.mk Nat.zero Nat.zero).fst.{0,0}"), want);
    assert_eq!(ok("@(Prod.mk Nat.zero Nat.zero).1.{0,0}"), want);
}

#[test]
fn subobject_cycle_in_structure_ext_is_an_error_not_a_stack_overflow() {
    // Malformed `structureExt`: every subobject field points back at its
    // own structure (`S2.toS1.subobject := S2`, and likewise for every
    // other structure with a parent). The oracle's `findField?` has no
    // cycle guard; well-formed data is acyclic. leanr must report an
    // error rather than recurse until the stack overflows (SIGABRT). Not
    // an oracle case, since no well-formed `.olean` can produce it.
    let r = support::elab_and_synthesize_doctored("fun (s : S2) => (s).zzz", |ss| {
        for s in ss.iter_mut() {
            let me = s.struct_name;
            for f in s.field_info.iter_mut() {
                if f.subobject.is_some() {
                    f.subobject = Some(me);
                }
            }
        }
    });
    // With the cycle cut, `zzz` is simply not a field of `S2`, so the
    // lookup falls through to the `findMethod?` seam as it would on
    // well-formed data.
    match r {
        Err(ElabError::UnsupportedSyntax(m)) => assert!(m.contains(".zzz"), "{m}"),
        other => panic!("expected the P3 field-lookup seam, got {other:?}"),
    }
}

/// Explicit universes on a head the oracle's PARSER rejects. `explicitUniv`
/// is guarded by `checkStackTop isIdentOrDotIdentOrProj`
/// (`Parser/Term.lean:938-950`), which leanr_syntax skips, so these parse
/// in leanr. Oracle, one `#check` each on a prelude-mode scratch file
/// importing `Elab0`:
///
/// ```text
/// (Nat.succ).{0} Nat.zero                 -- error: unexpected token '.{'; expected command
/// (fun (x : Nat) => x).{0} Nat.zero       -- error: unexpected token '.{'; expected command
/// List.{0}.{1} Nat                        -- error: unexpected token '.{'; expected command
/// ```
///
/// leanr must reject them too, not drop (or overwrite) the levels.
#[test]
fn explicit_universes_on_a_non_identifier_head_are_rejected() {
    let wrong: Vec<String> = [
        "(Nat.succ).{0} Nat.zero",
        "(fun (x : Nat) => x).{0} Nat.zero",
        "List.{0}.{1} Nat",
    ]
    .into_iter()
    .filter_map(|src| match support::elab_and_synthesize(src) {
        Err(ElabError::IllFormedSyntax(m)) if m.contains("Parser/Term.lean:938-950") => None,
        other => Some(format!("{src}: expected IllFormedSyntax, got {other:?}")),
    })
    .collect();
    assert!(wrong.is_empty(), "{wrong:#?}");
}
