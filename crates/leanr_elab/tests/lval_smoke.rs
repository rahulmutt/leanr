//! M4b-4a: dot-notation rejections and seams. The corpus
//! (`oracle_elab.rs`) is success-only, so every oracle ERROR this
//! slice ports is pinned here by variant and reason. Each case was run
//! on the pinned oracle (`lean` on a prelude-mode scratch file importing
//! `Elab0`, `LEAN_PATH=tests/fixtures/elab`, one `#check` per case)
//! before it was written; the oracle's message is quoted beside it.

mod support;

use leanr_elab::{
    ElabError, InvalidDottedIdentReason, InvalidFieldReason, InvalidProjectionReason,
};

fn proj_reason(src: &str) -> InvalidProjectionReason {
    match support::elab_and_synthesize(src) {
        Err(ElabError::InvalidProjection { reason, .. }) => reason,
        other => panic!("{src}: expected InvalidProjection, got {other:?}"),
    }
}

fn field_reason(src: &str) -> InvalidFieldReason {
    match support::elab_and_synthesize(src) {
        Err(ElabError::InvalidField { reason, .. }) => reason,
        other => panic!("{src}: expected InvalidField, got {other:?}"),
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
fn alias_field_retry_reports_the_unfolded_type() {
    // Review Focus 4: the unfold retry reaches field NAMES now. The
    // oracle's `findMethod?` on `S3Alias` finds nothing, `resolveLValLoop`
    // retries on the unfolded `S3` (App.lean:1688-1692), which also has
    // no `zzz`, and the LAST error is the one reported: "Invalid field
    // `zzz`: The environment does not contain `S3.zzz` … of type `S3`".
    // (`(Nat.zero).succ` and `(s).a` on `S3Alias`, the P1 seams this
    // test used to pin, are corpus records now: `p3/nat-succ`,
    // `p3/alias-field`.)
    assert_eq!(
        field_reason("fun (s : S3Alias) => (s).zzz"),
        InvalidFieldReason::NotFound {
            full_name: "S3.zzz".to_string()
        }
    );
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
    // Discriminates `(e :)` draining its OWN postponements: the later `(x : Prod Nat Nat)`
    // would fix `x`'s type, but `(x.1 :)` runs `withSynthesize (postpone := .no)` first, so it
    // must fail inside its scope rather than leak to the enclosing fixpoint.
    // "Invalid projection: Type of\n  x\nis not known; cannot resolve projection `1`"
    assert_eq!(
        proj_reason("fun x => Prod.mk (x.1 :) (x : Prod Nat Nat)"),
        InvalidProjectionReason::TypeUnknown
    );
    // Control: without the ascription the projection postpones and the later
    // ascription resolves it (the oracle accepts this too).
    support::elab_and_synthesize("fun x => Prod.mk x.1 (x : Prod Nat Nat)")
        .expect("the oracle accepts the un-ascribed control");
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
    // With the cycle cut, `zzz` is not a field of `S2`, and `findMethod?`
    // finds no `S2.zzz`: the oracle's error on well-formed data.
    match r {
        Err(ElabError::InvalidField {
            reason: InvalidFieldReason::NotFound { full_name },
            ..
        }) => {
            assert_eq!(full_name, "S2.zzz")
        }
        other => panic!("expected InvalidField NotFound, got {other:?}"),
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

/// M4b-4a P3 rejections. Each message is the pinned oracle's (`#check`
/// on a prelude file importing `Elab0`, re-run for this test).
#[test]
fn generalized_field_notation_rejections_match_the_oracle() {
    // "Invalid field `foo`: The environment does not contain `Nat.foo`,
    // so it is not possible to project the field `foo` from an
    // expression Nat.zero of type `Nat`"
    assert_eq!(
        field_reason("(Nat.zero).foo"),
        InvalidFieldReason::NotFound {
            full_name: "Nat.foo".to_string()
        }
    );
    // "… does not contain `S2.zzz` … of type `S2`"
    assert_eq!(
        field_reason("fun (s : S2) => (s).zzz"),
        InvalidFieldReason::NotFound {
            full_name: "S2.zzz".to_string()
        }
    );
    // A non-final `Const` step feeds the next lval: `S1.get s : Nat`,
    // so `.twice` looks in `Nat`, not `Function`. "… does not contain
    // `Nat.twice` … from an expression S1.get s of type `Nat`"
    assert_eq!(
        field_reason("fun (s : S1) => (s).get.twice"),
        InvalidFieldReason::NotFound {
            full_name: "Nat.twice".to_string()
        }
    );
    // "Invalid field notation: `S1.bad` has a parameter with expected
    // type S1 but it cannot be used. Note: The parameter `s` cannot be
    // referred to by name because that function has a preceding
    // parameter of the same name"
    match support::elab_and_synthesize("fun (s : S1) => (s).bad") {
        Err(ElabError::UnusableLValParameter {
            param, allow_named, ..
        }) => {
            assert_eq!(param, "s");
            assert!(allow_named);
        }
        other => panic!("expected UnusableLValParameter, got {other:?}"),
    }
    // "Invalid field notation: Function `S1.none` does not have a usable
    // parameter of type `S1` for which to substitute `s`" — and the same
    // message, `S1.addTo` / `S1.df` in place of `S1.none`, for the next
    // two.
    // Review Focus 3: `(s := s)` consumes the only `S1` parameter
    // (`remainingNamedArgs`, App.lean:1757-1759).
    // Review Focus 5: `S1Df` is a `def`, invisible at
    // `withReducibleAndInstances` (App.lean:1713).
    for src in [
        "fun (s : S1) => (s).none",
        "fun (s : S1) => (s).addTo (s := s)",
        "fun (s : S1) => (s).df",
    ] {
        match support::elab_and_synthesize(src) {
            Err(ElabError::NoLValParameter { base, .. }) => assert_eq!(base, "S1", "{src}"),
            other => panic!("{src}: expected NoLValParameter, got {other:?}"),
        }
    }
    // The non-final `Const` step runs `addLValArg` with `explicit :=
    // false` (App.lean:1881): `s` fills `{s : S1}` by name, leaving
    // `@S1.imp s : Nat → Nat`, so `.succ` looks in `Function`. "… does
    // not contain `Function.succ` … from an expression @S1.imp s of
    // type `Nat → Nat`"
    assert_eq!(
        field_reason("fun (s : S1) => (s).imp.succ"),
        InvalidFieldReason::NotFound {
            full_name: "Function.succ".to_string()
        }
    );
    // "too many explicit universe levels for `Nat.succ`" — `mkConst
    // constName levels` (App.lean:1875).
    assert!(matches!(
        support::elab_and_synthesize("(Nat.zero).succ.{0}"),
        Err(ElabError::TooManyUniverseLevels(_))
    ));
}

/// Review Focus 1: `findMethod?` computes `S`'s resolution order when
/// `S.f` misses (App.lean:1472-1476). A doctored `parent_info` cycle
/// must surface as an error, not a stack overflow.
#[test]
fn parent_cycle_in_structure_ext_is_an_error_not_a_stack_overflow() {
    // Double every `extends` edge back (Task 2's meta test does the
    // same): `S3`'s order recurses S3 → S2 → S3. `find_field` walks
    // `field_info` subobjects, which are untouched, so `zzz` still
    // misses there and the lookup reaches `findMethod?`'s order.
    let r = support::elab_and_synthesize_doctored("fun (s : S3) => (s).zzz", |ss| {
        let edges: Vec<_> = ss
            .iter()
            .flat_map(|s| {
                s.parent_info
                    .iter()
                    .map(move |p| (p.struct_name, s.struct_name, p.proj_fn))
            })
            .collect();
        for (parent, child, proj_fn) in edges {
            if let Some(p) = ss.iter_mut().find(|s| s.struct_name == parent) {
                p.parent_info.push(leanr_olean::StructureParentInfo {
                    struct_name: child,
                    subobject: false,
                    proj_fn,
                });
            }
        }
    });
    match r {
        Err(ElabError::Internal(m)) => assert!(m.contains("cyclic parents"), "{m}"),
        other => panic!("expected Internal (cyclic parents), got {other:?}"),
    }
}

/// `addLValArg` after a `CoeFun` coercion (App.lean:1784-1785):
/// `allowNamed := false`. The error carries `fPreCoercion?.getD f`
/// (`:1785`): the head the user named, never a coerced one.
/// `(s).viaFnI`: "Invalid field notation: `FnI.f` (coerced from
/// `S1.viaFnI`) has a parameter with expected type S1 but it cannot be
/// used. Note: Field notation cannot refer to parameter `s` by name
/// because that constant was coerced to a function".
/// `(s).viaFnJ` coerces twice (`FnJ` to `{n : Nat} → FnI`, then `FnI`):
/// the same message with "(coerced from `S1.viaFnJ`)" — the head as of
/// the FIRST coercion, not the `@FnJ.g S1.viaFnJ` the second starts from.
#[test]
fn coerced_implicit_lval_parameter_is_unusable() {
    for (src, head) in [
        ("fun (s : S1) => (s).viaFnI", "S1.viaFnI"),
        ("fun (s : S1) => (s).viaFnJ", "S1.viaFnJ"),
    ] {
        support::with_elab(src, |elab, term, kinds| {
            match elab.elab_term_and_synthesize(term, kinds, None) {
                Err(ElabError::UnusableLValParameter {
                    f,
                    param,
                    allow_named,
                }) => {
                    assert_eq!(param, "s", "{src}");
                    assert!(!allow_named, "{src}");
                    let base = elab.view.store;
                    let mut st = support::EncSt::default();
                    let f_json = support::encode_expr(elab.mctx.store(), Some(base), f, &mut st);
                    assert_eq!(
                        f_json,
                        serde_json::json!({"k": "const", "n": head, "us": []}),
                        "{src}: the error must name the pre-coercion head"
                    );
                }
                other => panic!("{src}: expected UnusableLValParameter, got {other:?}"),
            }
        });
    }
}

/// Review Focus 2: `Loop` coerces to `{u : Nat} → Loop` forever;
/// `addLValArg.go`'s `withIncRecDepth` (App.lean:1749) stops it.
/// "maximum recursion depth has been reached"
#[test]
fn self_reproducing_coe_fun_hits_max_rec_depth() {
    assert!(matches!(
        support::elab_and_synthesize("fun (s : S1) => (s).loop"),
        Err(ElabError::MaxRecDepth)
    ));
}

/// M4b-4a P4: the field split in identifiers (`resolveName`,
/// TermElabM.lean:2170-2192; `elabAppFnResolutions`, App.lean:1926-1950).
/// Each message is the pinned oracle's (plan § Measured oracle behaviour).
#[test]
fn identifier_field_split_rejections_match_the_oracle() {
    // A field that is neither a structure field nor a method. The base
    // `Nat.zero`'s type is the constant `Nat`, so the structure arm
    // answers (App.lean:1578), not the suffix arm. "Invalid field `foo`:
    // The environment does not contain `Nat.foo`"
    for src in [
        "fun (x : Nat) => x.foo",
        "Nat.zero.foo",
        "fun (p : Prod Nat Nat) => p.fst.foo",
    ] {
        match support::elab_and_synthesize(src) {
            Err(ElabError::InvalidField {
                reason: InvalidFieldReason::NotFound { full_name },
                ..
            }) => assert_eq!(full_name, "Nat.foo", "{src}"),
            other => panic!("{src}: expected InvalidField NotFound, got {other:?}"),
        }
    }
    // Review Focus 3: `c ++ suffix` (App.lean:1584-1586, :1606-1608) fires
    // only for a CONSTANT base, and `suffix?` is ALL the split-off fields
    // (`toName fields`, :1946-1950). `Nat : Type` takes the catch-all arm,
    // `Nat.succ : Nat → Nat` and `Nat.rec` the function arm. `Nat.rec.foo`
    // also shows the recursor guard stays off when fields follow (the
    // head `elabAppArgs` sees is not `Nat.rec`). "Unknown constant `…`"
    for (src, name) in [
        ("Nat.foo", "Nat.foo"),
        ("Nat.foo.bar", "Nat.foo.bar"),
        ("Nat.succ.foo", "Nat.succ.foo"),
        ("Nat.rec.foo", "Nat.rec.foo"),
    ] {
        match support::elab_and_synthesize(src) {
            Err(ElabError::UnknownIdent(s)) => assert_eq!(s, name, "{src}"),
            other => panic!("{src}: expected UnknownIdent({name}), got {other:?}"),
        }
    }
    // Review Focus 3: an fvar base never takes the suffix arm; the second
    // field carries no suffix. "… does not contain `Function.foo`",
    // "… does not contain `Function.succ` … from an expression @S1.imp s"
    for (src, full) in [
        ("fun (f : Nat -> Nat) => f.foo", "Function.foo"),
        ("fun (s : S1) => s.imp.succ", "Function.succ"),
    ] {
        assert_eq!(
            field_reason(src),
            InvalidFieldReason::NotFound {
                full_name: full.to_string()
            },
            "{src}"
        );
    }
    // Review Focus 2: `processLocal` (TermElabM.lean:2172-2179). "invalid
    // use of explicit universe parameters, `x` is a local variable"
    assert!(matches!(
        support::elab_and_synthesize("fun (x : Nat) => x.{0}"),
        Err(ElabError::InvalidExplicitUniversesForLocal(_))
    ));
    // Review Focus 2: levels go to the last field (`mkConsts`,
    // TermElabM.lean:2148). "too many explicit universe levels for
    // `Nat.succ`" / "… for `polyZero`" / "… for `Poly.val`"
    for src in [
        "Nat.zero.succ.{0}",
        "polyZero.{0}",
        "fun (x : Poly Nat) => x.val.{0,0}",
    ] {
        assert!(
            matches!(
                support::elab_and_synthesize(src),
                Err(ElabError::TooManyUniverseLevels(_))
            ),
            "{src}"
        );
    }
}

/// M4b-4a P4: `e |>.f args` (`elabPipeProj`, App.lean:2250-2258, into
/// `elabAppFn`'s pipeProj arms, :2085-2097) and named patterns outside a
/// pattern.
#[test]
fn pipe_projection_and_named_pattern_rejections_match_the_oracle() {
    // "Invalid projection: Index `3` is invalid for this structure; it
    // must be between 1 and 2"
    assert_eq!(
        proj_reason("fun (p : Prod Nat Nat) => p |>.3"),
        InvalidProjectionReason::IndexOutOfRange {
            idx: 3,
            num_fields: 2
        }
    );
    // Postponed, then resumed with postponement off. "Invalid
    // projection: Type of x is not known; cannot resolve projection `1`"
    assert_eq!(
        proj_reason("fun x => x |>.1"),
        InvalidProjectionReason::TypeUnknown
    );
    // The `.{us}` of `$e |>.$f.{us}` (`:2094-2097`) reaches `Nat.succ`.
    // "too many explicit universe levels for `Nat.succ`"
    assert!(matches!(
        support::elab_and_synthesize("fun (x : Nat) => x |>.succ.{0}"),
        Err(ElabError::TooManyUniverseLevels(_))
    ));
}

/// A whole term: `elabNamedPatternErr` (BuiltinTerm.lean:443-444).
/// "`<identifier>@<term>` is a named pattern and can only be used in
/// pattern matching contexts"
#[test]
fn named_pattern_as_a_term_is_rejected() {
    assert!(matches!(
        support::elab_and_synthesize("fun (x : Nat) => x@Nat.zero"),
        Err(ElabError::NamedPatternOutsidePattern { as_function: false })
    ));
}

/// The application-head site is checked in its own test so neither
/// assertion can mask the other.
#[test]
fn named_pattern_as_a_function_is_rejected() {
    // An application head: `elabAppFn` (App.lean:2098-2100). "Expected a
    // function, but found the named pattern x@Nat.succ"
    assert!(matches!(
        support::elab_and_synthesize("fun (x : Nat) => x@Nat.succ Nat.zero"),
        Err(ElabError::NamedPatternOutsidePattern { as_function: true })
    ));
}

fn dotted_reason(src: &str) -> InvalidDottedIdentReason {
    match support::elab_and_synthesize(src) {
        Err(ElabError::InvalidDottedIdent { reason, .. }) => reason,
        other => panic!("{src}: expected InvalidDottedIdent, got {other:?}"),
    }
}

/// M4b-4a P4: `resolveDottedIdentFn` (App.lean:1985-2058). Each message is
/// the pinned oracle's (plan § Measured oracle behaviour).
#[test]
fn dot_identifier_rejections_match_the_oracle() {
    // `:1986-1987`: "The name `a.b` must be atomic"
    assert_eq!(
        dotted_reason("(.a.b : Nat)"),
        InvalidDottedIdentReason::NotAtomic
    );
    // Review Focus 5. `:1988-1990`: postponed, then resumed with no
    // expected type. `@.succ` is `elabAppFn`'s `@.$id` arm (:2115),
    // formerly a P4 seam. `(fun x => x) .zero` resumes against the
    // still-unassigned `?α` and throws at `:2044-2045`. "The expected type
    // of `.zero` could not be determined"
    for src in [".zero", "@.succ", ".succ Nat.zero", "(fun x => x) .zero"] {
        assert_eq!(
            dotted_reason(src),
            InvalidDottedIdentReason::NoExpectedType,
            "{src}"
        );
    }
    // `:2041-2042`: "Not supported on type universe"
    assert_eq!(
        dotted_reason("(.foo : Type)"),
        InvalidDottedIdentReason::Sort
    );
    // `:2046-2048`: "The expected type of `.foo` α is not of the form `C ...`"
    assert_eq!(
        dotted_reason("fun (α : Type) (f : α -> Nat) => f .foo"),
        InvalidDottedIdentReason::NotConstApp
    );
    // `:2038-2040`, with the `unfoldDefinition?` retry (`:2050-2057`)
    // throwing the LAST failure: the oracle logs "Unknown constant
    // `NatAlias.foo`", then throws "Unknown constant `Nat.foo`" (and
    // `S3Alias.zero` → `S3.zero`).
    for (src, full) in [
        ("Nat.succ .foo", "Nat.foo"),
        ("(.foo : NatAlias)", "Nat.foo"),
        ("(.zero : S3Alias)", "S3.zero"),
        ("(.zero : Prod Nat Nat)", "Prod.zero"),
    ] {
        assert_eq!(
            dotted_reason(src),
            InvalidDottedIdentReason::UnknownConstant {
                full_name: full.to_string()
            },
            "{src}"
        );
    }
    // `mkConst resolvedName explicitUnivs` (`:2033`): "too many explicit
    // universe levels for `Nat.zero`"
    assert!(matches!(
        support::elab_and_synthesize("(.zero.{0} : Nat)"),
        Err(ElabError::TooManyUniverseLevels(_))
    ));
}

/// Review Focus 4: `withForallBody` (App.lean:2009-2015) enters
/// `(y : Nat) → Nat` with a local `y` and must drop it afterwards; the
/// next argument's `y` is then unknown. Oracle: "Unknown identifier `y`".
#[test]
fn dot_identifier_telescope_does_not_leak_its_binders() {
    match support::elab_and_synthesize("(fun (g : (y : Nat) -> Nat) (n : Nat) => n) .succ y") {
        Err(ElabError::UnknownIdent(s)) => assert_eq!(s, "y"),
        other => panic!("expected UnknownIdent(y), got {other:?}"),
    }
}
