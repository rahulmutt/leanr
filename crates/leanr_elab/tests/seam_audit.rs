//! M4b-3 P1 seam audit (M4b-1 Task 7's precedent): every construct this
//! plan defers is reachable ONLY through a named `UnsupportedSyntax`
//! carrying the owning slice, never a panic and never a wrong `ExprId`.
//!
//! Scope, stated up front because a seam audit that quietly omits a seam
//! is worse than one that names its own gaps. `app/mod.rs`'s module doc
//! is the full site-by-site index; of the seams listed there, three are
//! not reachable from any source term the hermetic `Elab0` fixture can
//! express, and this file does not pretend otherwise:
//!
//!   * the **P5 optParam/autoParam** seam — no fixture parameter carries
//!     either wrapper, so `app_smoke.rs`'s
//!     `explicit_mode_skips_the_optparam_default` asserts it white-box
//!     against a synthetic `f_type` instead;
//!   * the **P2 instance-implicit** seams (the `InstImplicit` arm and
//!     the three pending-`inst_mvars` guards) — `Elab0.lean` declares no
//!     `class` and no `instance`, so nothing can produce an
//!     `instImplicit` binder or push onto `inst_mvars`. P2 brings the
//!     fixture classes and the tests with them;
//!   * the **P4 coercion** seam, which is an `ElabError::TypeMismatch`
//!     from `ensureArgType` rather than an `UnsupportedSyntax` — that IS
//!     M4b-1's documented behavior (error on a defeq mismatch instead of
//!     inserting a coercion), so it is a deliberately wrong-*shaped*
//!     seam, not a missing one.
//!
//! Everything else is asserted below, end-to-end from source text.

mod support;

use leanr_syntax::{builtin, parse_term};

/// Elaborate `src` through the same construction `oracle_elab.rs` uses
/// — replay `Elab0.olean`, parse with leanr's own parser, dispatch the
/// single term child — and return the elaborator's verdict.
///
/// `support::with_app_harness` is that construction (its own doc
/// comment: "mirrors `oracle_elab.rs:29-93` verbatim"); the `AppElab`
/// it hands back is ignored here beyond its `elab` field, exactly as
/// `app_smoke.rs`'s own `elab_src` does. Duplicated from that file
/// rather than shared: the two are separate integration-test binaries
/// with no path between them, the same reason `head.rs`'s and
/// `resolve.rs`'s `#[cfg(test)]` env builders are duplicated.
fn elab_src(src: &str) -> Result<leanr_kernel::bank::ExprId, leanr_elab::ElabError> {
    support::with_app_harness("Nat.zero", |app| {
        let snap = builtin::snapshot();
        let parsed = parse_term(src, &snap);
        assert!(parsed.errors.is_empty(), "{src}: {:?}", parsed.errors);
        let elem = parsed
            .tree
            .root()
            .first_child_or_token()
            .unwrap_or_else(|| panic!("{src}: no term child"));
        app.elab.elab_term(&elem, &parsed.tree.kinds, None)
    })
}

/// Each source term below exercises one deferred path INSIDE `app/`.
/// The assertion is deliberately on the ERROR SHAPE, not the message
/// text, plus a substring check on the slice name so a seam cannot be
/// silently re-pointed at the wrong owner while wording stays free to
/// improve.
///
/// Every case was run before it was written down, and two of the ones
/// the plan supplied did not survive that:
///
///   * `("Nat.succ ..", "P5")` — `..` is no longer deferred. Task 7
///     implemented it (`args.rs`'s `if app.ctx.ellipsis then
///     add_implicit_arg`, oracle `App.lean:856-857`), so this source
///     now elaborates to `Nat.succ ?m` — which is also exactly what the
///     pinned oracle emits for it. Only optParam/autoParam DEFAULT
///     filling is still P5's, and that is unreachable from source here
///     (see the module doc). Replaced with `@(..)`, the other P5 seam.
///   * `("(Nat.succ : Nat -> Nat) Nat.zero Nat.zero", "P2")` — this
///     never reached P2. Its head is a `typeAscription`, so it stops one
///     step earlier, in `head.rs`, before any argument is processed.
///     Split into the two cases that really do reach each seam: a bare
///     over-application for the P2/P4 one, and the ascribed head for the
///     head seam.
#[test]
fn deferred_constructs_are_named_seams() {
    let cases: &[(&str, &str)] = &[
        // (source, expected slice marker in the message)
        //
        // `main`'s "fType is not a forall but arguments remain" arm:
        // the oracle's `synthesizePendingAndNormalizeFunType`
        // (`App.lean:372-404`) synthesizes pending instances, re-WHNFs,
        // and falls back to `coerceToFunction?`. Both halves are later
        // plans, so the message names both.
        ("Nat.succ Nat.zero Nat.zero", "M4b-3 P2"),
        ("Nat.succ Nat.zero Nat.zero", "M4b-3 P4"),
        // `elabExplicit`'s `` `(@($t)) `` arm (`App.lean:2269`): `@` on
        // a non-atom does NOT enter explicit mode, it disables
        // implicit-lambda insertion — P5's.
        ("@(Nat.succ Nat.zero)", "M4b-3 P5"),
        // `elab_explicit`'s LVal arm: `@` on a projection head.
        ("@(Nat.zero).1", "M4b-4"),
        // `peel_head`'s `App.lean:2118` arm — an INVALID occurrence of
        // `@` in a function position, which is `throwUnsupportedSyntax`
        // in the oracle too, so the citation is the owner.
        ("@(Nat.succ Nat.zero) Nat.zero", "App.lean:2118"),
        // `head.rs`'s two arms. A projection or dot-identifier head is
        // the dot-notation/LVal subsystem...
        ("(Nat.zero).1 Nat.zero", "M4b-4"),
        (".succ Nat.zero", "M4b-4"),
        // ...while a general term in function position is `elabAppFn`'s
        // generic branch (`App.lean:2120-2138`), which succeeds in the
        // oracle. Task 9 split these: one message for both named the
        // wrong owner for the second.
        ("(Nat.succ) Nat.zero", "M4b-4"),
        ("(fun (x : Nat) => x) Nat.zero", "M4b-4"),
        ("(Nat.succ : Nat -> Nat) Nat.zero Nat.zero", "M4b-4"),
    ];
    for (src, marker) in cases {
        match elab_src(src) {
            Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => assert!(
                m.contains(marker),
                "{src}: seam message does not name {marker:?}: {m:?}"
            ),
            other => panic!("{src}: expected a named UnsupportedSyntax seam, got {other:?}"),
        }
    }
}

/// The deferrals that never reach `app/` at all, because `dispatch`'s
/// table does not register their kind. Its catch-all names them by
/// KIND (`UnsupportedSyntax(other.to_string())`), which is the whole
/// contract for an unregistered kind — see `dispatch`'s own doc
/// comment for which slice owns each.
///
/// Asserted here rather than left to the table's doc comment because
/// the failure mode this guards is a kind being *registered* by
/// accident: `Term.proj` and friends alias to `elabAtom` in the oracle
/// (`App.lean:2247-2248`, `:2273-2274`), so routing them to
/// `app::elab_atom` looks correct and is not — their real work is
/// `elabAppFn`'s LVal arms, which M4b-4 owns.
#[test]
fn unregistered_kinds_are_named_by_kind() {
    let cases: &[(&str, &str)] = &[
        // M4b-4, the LVal / dot-notation family.
        ("Nat.zero.1", "Lean.Parser.Term.proj"),
        ("Nat.zero |>.1", "Lean.Parser.Term.pipeProj"),
        ("x@Nat.zero", "Lean.Parser.Term.namedPattern"),
        // M4b-3 P3, the literals that are not leaves.
        ("0", "num"),
        ("'a'", "char"),
    ];
    for (src, kind) in cases {
        assert!(
            leanr_elab::dispatch::elaborator_name_for(kind).is_none(),
            "{kind} must not be registered while its slice is deferred"
        );
        match elab_src(src) {
            Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => {
                assert_eq!(m, *kind, "{src}: seam must name the unregistered kind")
            }
            other => panic!("{src}: expected UnsupportedSyntax({kind}), got {other:?}"),
        }
    }
}

/// The `@[elab_as_elim]` and `@[elab_without_expected_type]` attributes
/// change `elabAppArgs`'s control flow (`App.lean:1373`, `:1330-1333`),
/// and leanr decodes NEITHER extension — so their guards cannot be
/// runtime checks. This test is the fixture-source gate that keeps them
/// inert, and it fails the moment someone reaches for one, which is
/// exactly when a real guard (and an extension decode) becomes
/// necessary.
///
/// It gates TWO things, because the plan's premise — "inert only
/// because no declaration in the hermetic fixture carries the
/// attribute" — is true for `elab_without_expected_type` and FALSE for
/// `elab_as_elim`:
///
///   * `hasElabWithoutExpectedType` (`App.lean:31-32`) really is one
///     `TagAttribute` lookup, so the source check is complete for it;
///   * `shouldElabAsElim` (`App.lean:1322-1328`) is
///     `isRec || isCasesOnRecursor || isBRecOnRecursor ||
///     isRecOnRecursor || elabAsElim.hasTag` — the attribute is only the
///     LAST of five triggers. `Elab0.lean` declares two inductives, so
///     the fixture environment already contains `Nat.rec`, `Nat.recOn`,
///     `Nat.casesOn`, `List.rec`, ... for which that predicate is TRUE
///     without any attribute. Measured against the pinned oracle through
///     `dump_elab.lean`'s own entry point, `Nat.rec` elaborates to a
///     bare `?m` there (the branch postpones on the missing expected
///     type) while leanr emits `const Nat.rec [?u]` — a live, silent
///     divergence, not a hypothetical one. No committed record carries
///     an eliminator head today; the second half of this gate is what
///     keeps it that way until M4b-4 decodes `auxRecExt` and builds
///     `ElabElim`.
///
/// Both halves are TEXT gates over committed fixture files, deliberately
/// so: they must fail on the SOURCE a contributor writes, before the
/// oracle is even consulted, since the corpus dumper silently drops any
/// query whose oracle side errors and would therefore hide the first
/// half of a divergence rather than report it.
#[test]
fn fixture_declares_no_undecoded_elab_attributes() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/fixtures/elab");

    let src =
        std::fs::read_to_string(format!("{dir}/Elab0.lean")).expect("committed fixture source");
    for attr in ["elab_as_elim", "elab_without_expected_type"] {
        assert!(
            !src.contains(attr),
            "Elab0.lean declares `@[{attr}]`, whose extension leanr does not decode: \
             elabAppArgs' control flow would diverge silently. Decode the extension \
             (M4b-4 owns elab_as_elim) before adding such a declaration."
        );
    }

    // The non-attribute half of `shouldElabAsElim`. Matched on the
    // dotted SUFFIX so an unrelated identifier that merely contains the
    // text (`Nat.record`, a local named `rec`) does not trip it: every
    // trigger is a name component, and `Eq.ndrec`/`Eq.ndrecOn` are
    // named outright by `isAuxRecursor` (`AuxRecursor.lean:30-36`).
    let queries = std::fs::read_to_string(format!("{dir}/elab-queries.jsonl"))
        .expect("committed elab corpus");
    for line in queries.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("committed JSONL is valid");
        let (id, src) = (
            q["id"].as_str().expect("id"),
            q["src"].as_str().expect("src"),
        );
        for elim in [
            ".rec", ".recOn", ".casesOn", ".brecOn", ".ndrec", ".ndrecOn",
        ] {
            assert!(
                !src.contains(elim),
                "{id}: query {src:?} has an eliminator-shaped name (`{elim}`). \
                 `shouldElabAsElim` (App.lean:1322-1328) is true for recursors and \
                 auxiliary recursors WITHOUT any attribute, and the oracle then diverts \
                 the whole application to ElabElim — leanr takes the ordinary path and \
                 emits a different Expr. M4b-4 owns elabAsElim; do not add such a query \
                 before it lands."
            );
        }
    }
}
