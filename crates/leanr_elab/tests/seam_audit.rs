//! M4b-3 P1 seam audit (M4b-1 Task 7's precedent): every construct this
//! plan defers is reachable ONLY through a named `UnsupportedSyntax`
//! carrying the owning slice, never a panic and never a wrong `ExprId`.
//!
//! Scope, stated up front because a seam audit that quietly omits a seam
//! is worse than one that names its own gaps. `app/mod.rs`'s module doc
//! is the full site-by-site index; of the seams listed there, two are
//! not reachable from any source term the hermetic `Elab0` fixture can
//! express, and this file does not pretend otherwise:
//!
//!   * the **P5 optParam/autoParam** seam — no fixture parameter carries
//!     either wrapper, so `app_smoke.rs`'s
//!     `explicit_mode_skips_the_optparam_default` asserts it white-box
//!     against a synthetic `f_type` instead;
//!   * the **P4 coercion** seam, which is an `ElabError::TypeMismatch`
//!     from `ensureArgType` rather than an `UnsupportedSyntax` — that IS
//!     M4b-1's documented behavior (error on a defeq mismatch instead of
//!     inserting a coercion), so it is a deliberately wrong-*shaped*
//!     seam, not a missing one.
//!
//! The **P2 instance-implicit** seams (the `InstImplicit` arm and the
//! three pending-`inst_mvars` guards) used to be a third unreachable
//! row here — `Elab0.lean` declared no `class` and no `instance`. As of
//! M4b-3 P2a task 7 it declares `Wrap`/`Pair`/`NoInst`/`Dflt`, both
//! seams are real code, and their behavior is exercised by
//! `tests/oracle_elab.rs`'s `tc/*` records and
//! `tests/synthetic_smoke.rs` rather than by this file.
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
///   * `("Nat.succ Nat.zero Nat.zero", "M4b-3 P2"/"M4b-3 P4")` — task 8
///     closed this seam: `main`'s "fType is not a forall but arguments
///     remain" arm now calls `synthesize_pending_and_normalize_fun_type`,
///     which reports the genuinely-non-function case as
///     `ElabError::FunctionExpected`, not a named `UnsupportedSyntax`
///     seam. Moved to `over_application_reports_function_expected` and
///     `mvar_function_type_is_a_named_seam` below, which assert the two
///     split failure modes directly.
#[test]
fn deferred_constructs_are_named_seams() {
    let cases: &[(&str, &str)] = &[
        // (source, expected slice marker in the message)
        //
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
        // `elab_ident_head`'s PARTIAL `shouldElabAsElim` guard (fix
        // round 1). A genuine recursor — `ConstantInfo::Rec`, the one
        // disjunct of `App.lean:1322-1328` that leanr's environment can
        // decide — is seamed rather than elaborated the ordinary way.
        // Measured before and after: the pinned oracle emits a bare `?m`
        // for both of these (the `elabAsElim` branch postpones on the
        // missing expected type), where leanr used to emit
        // `const Nat.rec [?u]`.
        //
        // NOT covered, and deliberately not claimed to be: `Nat.recOn`,
        // `Nat.casesOn`, `Nat.brecOn` and `@[elab_as_elim]` still take
        // the ordinary path and still emit a different term than the
        // oracle, with no seam — their four disjuncts read `auxRecExt` /
        // the `elabAsElim` tag, extensions leanr does not decode.
        // `fixture_declares_no_undecoded_elab_attributes` below is the
        // backstop for those; M4b-4 owns the real fix.
        ("Nat.rec", "M4b-4"),
        ("List.rec", "M4b-4"),
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

/// An over-applied function reaches `synthesizePendingAndNormalizeFunType`
/// and, when the type is genuinely not a function, reports it as such
/// rather than as a pending-synthesis seam.
#[test]
fn over_application_reports_function_expected() {
    let err = elab_src("Nat.zero Nat.zero").expect_err("Nat is not a function");
    assert!(
        matches!(err, leanr_elab::ElabError::FunctionExpected { .. }),
        "got {err:?}"
    );
}

/// A function type that is still an unassigned mvar after the fixpoint
/// is a named P4/P5 seam, NOT a wrong term.
///
/// This shape diverges from the oracle today and will keep diverging
/// until expected types propagate into `fun` binder domains (plan
/// § Measured facts, item 4). The assertion pins that it stays an
/// ERROR naming its owner — the failure mode this discipline exists to
/// prevent is emitting a different term silently.
#[test]
fn mvar_function_type_is_a_named_seam() {
    let err = elab_src("(fun f => f Nat.zero : (Nat -> Nat) -> Nat)")
        .expect_err("leanr cannot elaborate this yet");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("M4b-3 P4") || msg.contains("M4b-3 P5"),
        "seam must name its owner, got {msg}"
    );
}

/// The `shouldElabAsElim` guard must NOT fire under `@` or `..`.
/// `elabAsElim?` (`App.lean:1398-1399`) returns `none` before it ever
/// consults `shouldElabAsElim` when either is set, so the oracle takes
/// the ORDINARY path for `@Nat.rec` and `Nat.rec ..` — seaming them
/// would be a fresh divergence in the opposite direction, erroring where
/// the oracle succeeds.
///
/// Measured against the pinned oracle rather than reasoned about, since
/// this is the whole justification for threading `heed_elab_as_elim`
/// instead of testing the constant kind unconditionally:
/// ```text
/// @Nat.rec    -> {"k":"const","n":"Nat.rec","us":[{"k":"lmvar","i":0}]}
/// Nat.rec ..  -> Nat.rec ?m ?m ?m ?m
/// ```
/// Both are ordinary applications there, and both must therefore be
/// `Ok` here.
#[test]
fn elab_as_elim_guard_honours_the_explicit_and_ellipsis_early_out() {
    for src in ["@Nat.rec", "Nat.rec .."] {
        assert!(
            elab_src(src).is_ok(),
            "{src}: `explicit || ellipsis` disables the elabAsElim branch in the \
             oracle (App.lean:1399), so leanr must take the ordinary path too"
        );
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
/// and leanr decodes NEITHER extension — so neither can be a runtime
/// check. This test is the fixture-source gate that keeps them inert,
/// and it fails the moment someone reaches for one, which is exactly
/// when a real guard (and an extension decode) becomes necessary.
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
///     `dump_elab.lean`'s own entry point, `Nat.rec` elaborated to a
///     bare `?m` there (the branch postpones on the missing expected
///     type) while leanr emitted `const Nat.rec [?u]` — a live, silent
///     divergence, not a hypothetical one.
///
/// `head::elab_ident_head` now seams the ONE disjunct leanr's
/// environment can decide (`isRec`, i.e. `ConstantInfo::Rec`) — see
/// `deferred_constructs_are_named_seams`'s `Nat.rec` case. That guard is
/// partial by construction, so what is left open, and what this gate
/// exists to backstop, is precisely:
///
///   * **aux recursors** — `Nat.casesOn`, `Nat.recOn`, `Nat.brecOn` and
///     friends. `isAuxRecursorWithSuffix` (`AuxRecursor.lean:39-51`)
///     reads the `auxRecExt` tag extension, which leanr does not decode,
///     so these still take the ordinary path and still emit a different
///     term than the oracle, with NO seam;
///   * **`@[elab_as_elim]` declarations** — same, via the `elabAsElim`
///     tag extension.
///
/// Neither is detectable at runtime today, so both are kept out of the
/// committed corpus by source text instead. M4b-4 decodes `auxRecExt`
/// and builds `ElabElim`; until then this gate is the whole defence.
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

/// Recursively collect every `.rs` file under `dir`.
fn walk_rs_files(dir: &str) -> Vec<std::path::PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![std::path::PathBuf::from(dir)];
    while let Some(d) = stack.pop() {
        for entry in std::fs::read_dir(&d).expect("read_dir") {
            let entry = entry.expect("dir entry").path();
            if entry.is_dir() {
                stack.push(entry);
            } else if entry.extension().is_some_and(|e| e == "rs") {
                out.push(entry);
            }
        }
    }
    out
}

/// No seam message in `leanr_elab` still points at "M4b-3 P2".
///
/// P2 split into P2a (this plan) and P2b (classExtension + outParam), so
/// an unqualified "P2" is now ambiguous. Every remaining seam must name
/// P2b, P3, P4, P5, M4b-4, or later M4.
#[test]
fn no_seam_points_at_the_retired_p2_label() {
    let src_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    let mut offenders = Vec::new();
    for entry in walk_rs_files(src_dir) {
        let text = std::fs::read_to_string(&entry).expect("read source");
        for (n, line) in text.lines().enumerate() {
            // Match the seam label, not prose mentioning the plan.
            if line.contains("M4b-3 P2\"") || line.contains("M4b-3 P2 ") {
                offenders.push(format!("{}:{}", entry.display(), n + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "seams still labelled with the retired `M4b-3 P2`: {offenders:?}"
    );
}
