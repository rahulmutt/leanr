//! M4b-3 P1 seam audit (M4b-1 Task 7's precedent): every construct this
//! plan defers is reachable ONLY through a named `UnsupportedSyntax`
//! carrying the owning slice, never a panic and never a wrong `ExprId`.
//!
//! Scope, stated up front because a seam audit that quietly omits a seam
//! is worse than one that names its own gaps. `app/mod.rs`'s module doc
//! is the full site-by-site index.
//!
//! **The P5 optParam/autoParam seam used to be listed here as
//! unreachable** — "no fixture parameter carries either wrapper", so
//! `app_smoke.rs`'s `explicit_mode_skips_the_optparam_default` asserted
//! it white-box against a synthetic `f_type` instead. That stopped being
//! true once `Elab0.lean` declared `withDefault`/`withTactic` (P5 tasks
//! 8/9), and the seam itself is now RETIRED rather than merely reached:
//! `optParam` fills its declared default with real code (task 8,
//! `app_smoke.rs`'s `opt_param_default_is_the_declared_value`), and an
//! omitted `autoParam` mints a `.tactic` synthetic mvar that the ladder
//! reports unsolved — `omitted_auto_param_is_a_reported_tactic_mvar`
//! below, and `app_smoke.rs`'s
//! `omitted_auto_param_mints_a_reported_tactic_mvar` — rather than
//! raising the old combined `UnsupportedSyntax` seam directly from
//! `args.rs`. `no_seam_points_at_the_retired_p5_optparam_autoparam_label`
//! below is this file's own retired-label gate for it, mirroring the
//! P2/P3/P2b-ii/P4 gates already here. `explicit_mode_skips_the_optparam_default`
//! (`app_smoke.rs`) stays: it is still the only test that exercises
//! `process_explicit_arg`'s `optParam` arm with `explicit == true`,
//! a shape no fixture declaration reaches either way.
//!
//! The mvar-fType seam this file USED TO assert end-to-end,
//! `mvar_function_type_is_a_named_seam` (expected-type propagation into
//! `fun` binder domains), once shared its bullet here with the P4
//! coercion seam — `coerceToFunction?` (`CoeFun`) was tried first at the
//! same site and, on failure, fell through to the same message. M4b-3
//! P4 retired that sharing along with the coercion seam itself: tasks
//! 7-9 landed `CoeT` (`coe.rs`'s `mk_coe`/`ensure_has_type`), `CoeFun`
//! (`app/args.rs`'s `synthesize_pending_and_normalize_fun_type`) and
//! `CoeSort` (`coe.rs`'s `ensure_type`), so coercion insertion is real
//! code now, exercised by `tests/oracle_elab.rs`'s `coe/*` records and
//! `tests/synthetic_smoke.rs` rather than by this file. M4b-3 P5 task 4
//! then closed the mvar-fType seam itself: `propagateExpectedType`
//! (`builtin/binder/fun.rs`) now pins a `fun` binder's domain from the
//! ascription BEFORE `app/args.rs` can ever see an unassigned mvar
//! there, so what remains at that site is a genuine `FunctionExpected`
//! (`over_application_reports_function_expected` above already covers
//! that shape). `mvar_function_type_is_closed_by_propagation` below
//! asserts the now-CLOSED shape end-to-end — the same pattern
//! `postponed_coe_under_a_binder_abstracts_via_elim_mvar_deps` below
//! already uses for a divergence that flipped from wrong to right.
//!
//! One thing this file pins is NOT a seam at all but its opposite — a
//! CLOSED divergence, kept as a regression test:
//! `postponed_coe_under_a_binder_abstracts_via_elim_mvar_deps`. It was
//! written when leanr answered this shape wrongly, and it now asserts
//! the oracle's answer instead; see its own doc comment for the
//! history. It lives here because this file is where the "never a
//! wrong `ExprId`" half of the discipline is audited, and the shape it
//! covers — a synthetic mvar postponed under a binder and resumed after
//! that binder closed — is the one where a wrong `ExprId` was actually
//! emitted, silently, for two slices.
//!
//! The **P2 instance-implicit** seams (the `InstImplicit` arm and the
//! three pending-`inst_mvars` guards) used to be a third unreachable
//! row here — `Elab0.lean` declared no `class` and no `instance`. As of
//! M4b-3 P2a task 7 it declares `Wrap`/`Pair`/`NoInst`/`Dflt`, both
//! seams are real code, and their behavior is exercised by
//! `tests/oracle_elab.rs`'s `tc/*` records and
//! `tests/synthetic_smoke.rs` rather than by this file.
//!
//! **The implicit-lambda `.postpone` arm** (`useImplicitLambda`'s third
//! result, `TermElabM.lean:1753-1778`) used to be a fourth unreachable
//! row here too — P1 wrote it off because it needs `isLocalIdent?` and
//! `isMVarApp` machinery P1 deliberately did not have, AND both of its
//! continuations need the postponement ladder P1 deliberately does not
//! have. `elimMVarDeps` (PR #42) closed the first half of that
//! reasoning: an unassigned `fun` binder's type is now exactly an aux
//! mvar applied to binder fvars — an mvar APPLICATION, the shape
//! `isMVarApp` tests for — and M4b-3 P5 multiplies binder producers on
//! top, so leanr can no longer assume no corpus term reaches it. The
//! second half — leanr still has no term-level postponement — has not
//! closed, so M4b-3 P5 Task 6 models the arm explicitly and reports it
//! as a named `M4b-4` seam (`elab.rs`'s `UseImplicitLambda::Postpone`
//! dispatch) rather than leaving it an unexamined assumption.
//! `implicit_lambda_postpone_is_a_named_seam` below asserts it.
//!
//! **`mod scoping_audit` below is a different kind of section: an
//! AUDIT, not a seam list.** M4b-3 P5 Task 7 (design spec § Amendment
//! 8 item 4). Its own module doc carries the Step 1 enumeration and
//! its findings; nothing above this paragraph is part of it.
//!
//! Everything else is asserted below, end-to-end from source text.

mod support;

use leanr_syntax::{builtin, parse_term};
use support::{elab_and_synthesize, elab_result};

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
///     pinned oracle emits for it. At the time this replacement was
///     written, optParam/autoParam DEFAULT filling was still P5's and
///     unreachable from source here (see the module doc); both have
///     since shipped (tasks 8-9) and are no longer deferred either.
///     Replaced with `@(..)`, the seam below — which itself later moved
///     from "M4b-3 P5" to "later M4" once implicit-lambda insertion
///     shipped but the `@($t)`/`@$t` wrap disabling it did not.
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
///     `mvar_function_type_is_closed_by_propagation` below, which assert
///     the two split failure modes directly — the latter now a CLOSED
///     one, since M4b-3 P5 task 4 (see the module doc above).
#[test]
fn deferred_constructs_are_named_seams() {
    let cases: &[(&str, &str)] = &[
        // (source, expected slice marker in the message)
        //
        // `elabExplicit`'s `` `(@($t)) `` arm (`App.lean:2269`): `@` on
        // a non-atom does NOT enter explicit mode, it disables
        // implicit-lambda insertion. The insertion itself shipped in
        // M4b-3 P5, but wrapping `@($t)`/`@$t` to elaborate with it
        // disabled did not — no plan slice has claimed it, so the seam
        // is "later M4", not "M4b-3 P5" (which is now complete).
        ("@(Nat.succ Nat.zero)", "later M4"),
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

/// Was `mvar_function_type_is_a_named_seam`. M4b-3 P5 Task 4 closed it:
/// `propagateExpectedType` supplies `f`'s domain from the ascription, so
/// the application proceeds instead of reporting an unassigned fType.
///
/// The `CoeFun` half of this seam (`coerceToFunction?`,
/// `App.lean:378-380`) landed in P4 task 8 — a non-forall function type
/// that a `CoeFun` instance can bridge is coerced and the state machine
/// proceeds. What used to remain was the case `coerceToFunction?`
/// cannot help with either: `f`'s type still an unassigned mvar, not a
/// concrete non-function type, so there was nothing yet for a `CoeFun`
/// search to run against. `propagate_expected_type` (`builtin/binder/fun.rs`)
/// now pins that mvar to `Nat -> Nat` before `f Nat.zero` is ever
/// elaborated, so this site is reached with a concrete forall and the
/// seam this test used to pin no longer exists.
#[test]
fn mvar_function_type_is_closed_by_propagation() {
    let j = support::elab_only("(fun f => f Nat.zero : (Nat -> Nat) -> Nat)")
        .expect("propagate_expected_type pins f's domain, so this now elaborates");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["b"]["k"], "app");
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
        // The literals that are not leaves used to be listed here.
        // `num` left with task 6 and `char`/`scientific` with task 7 —
        // all three are registered kinds now (`@OfNat.ofNat.{u}` plus
        // the default-instance rung, `Char.ofNat`,
        // `@OfScientific.ofScientific.{u}`), and their records live in
        // the committed corpus instead.
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
///
/// Word-boundary-style match, not two literal substrings: `M4b-3 P2` is
/// retired whenever it is NOT immediately followed by `a` or `b` (the
/// two live sub-slice labels), regardless of what punctuation or
/// end-of-line follows. An earlier cut of this test checked only
/// `line.contains("M4b-3 P2\"")` and `line.contains("M4b-3 P2 ")` — a
/// floor, not a ceiling — and a measurement against this very tree
/// (recorded in task 10's report) showed it missed two real stale
/// labels that took other punctuation: `dispatch.rs`'s deferral-table
/// row ended the line with no trailing space (`... M4b-3 P2` then a
/// newline), and `lib.rs`'s module-doc bullet ended in a comma
/// (`... M4b-3 P2,`). Both would have passed CI silently. This scan
/// checks the character immediately after `P2` directly instead of
/// enumerating suffixes, so it catches every punctuation form without
/// needing to guess which ones a future seam label might use — while
/// `P2a`/`P2b` (and prose that never carries the `M4b-3` prefix at all,
/// e.g. `app/mod.rs`'s "used to carry as P2 rows") stay invisible to it,
/// same as before.
///
/// **Precondition this test relies on:** `needle` is the literal
/// substring `"M4b-3 P2"`. This is a textual scan, not a semantic one —
/// it has no notion of "a citation of the retired P2 label" beyond that
/// exact prefix appearing in the line. Any prose phrased WITHOUT that
/// literal prefix (a rewritten `app/mod.rs` passage that comes to
/// mention a bare "P2" some other way, a citation that abbreviates or
/// respells `M4b-3`, etc.) passes silently — not because it was checked
/// and found to be fine, but because the gate never looked. A future
/// edit that reintroduces the literal `M4b-3 P2` prefix (unqualified)
/// back into such prose IS caught; only the prefix-less phrasing is the
/// blind spot, and it is a blind spot BY that construction, not an
/// oversight — recorded here so a future prose edit near this needle
/// cannot silently rely on being invisible to it without a reader
/// noticing the precondition changed.
#[test]
fn no_seam_points_at_the_retired_p2_label() {
    let src_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    let needle = "M4b-3 P2";
    let mut offenders = Vec::new();
    for entry in walk_rs_files(src_dir) {
        let text = std::fs::read_to_string(&entry).expect("read source");
        for (n, line) in text.lines().enumerate() {
            for (idx, _) in line.match_indices(needle) {
                let after = line[idx + needle.len()..].chars().next();
                if after != Some('a') && after != Some('b') {
                    offenders.push(format!("{}:{}", entry.display(), n + 1));
                    break;
                }
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "seams still labelled with the retired `M4b-3 P2`: {offenders:?}"
    );
}

/// P3 RETIRED the rung-3 default-instance seam rather than retargeting
/// it. A source tree that still carries the old message is making a
/// stale claim about what is implemented.
///
/// Mirrors [`no_seam_points_at_the_retired_p2_label`] above, which does
/// the same for P1's unqualified "M4b-3 P2" labels, and inherits that
/// test's stated precondition: this is a TEXTUAL scan, so it is a floor
/// (the exact retired wording never comes back) and not a ceiling (a
/// reworded revival of the same seam would pass unseen).
///
/// **Non-vacuity, measured rather than assumed.** The needle is the
/// distinctive subject of P2a's retired message, which read
/// ```text
///     "default instances for a pending typeclass mvar require \
///      synthesizeUsingDefault — M4b-3 P3"
/// ```
/// in `synthetic.rs:607-611` on `main`. It is matched per LINE, and the
/// needle is chosen to lie entirely within the message's FIRST source
/// line: the Rust `\`-continuation puts a newline plus indentation
/// between `require` and `synthesizeUsingDefault`, so a whole-file
/// `contains("require synthesizeUsingDefault")` — the shape task 8's
/// brief proposed — could never have matched even on `main`, and would
/// have been a gate that gates nothing. Verified by running this scan's
/// body against `git show main:crates/leanr_elab/src/synthetic.rs`: one
/// offender there, zero here.
#[test]
fn no_seam_points_at_the_retired_p3_default_instance_label() {
    let src_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    let needle = "default instances for a pending typeclass mvar";
    let mut offenders = Vec::new();
    for path in walk_rs_files(src_dir) {
        let text = std::fs::read_to_string(&path).expect("readable source");
        for (n, line) in text.lines().enumerate() {
            if line.contains(needle) {
                offenders.push(format!("{}:{}", path.display(), n + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "P3 retired the rung-3 seam (it has a real body in \
         `synthetic/default_inst.rs`); stale label at {offenders:?}"
    );
}

/// M4b-3 P2b-ii RETIRED the `resultTypeOutParam?` producer seam — the
/// `add_implicit_arg` and `finalize` messages that both read
/// "... requires the elaborator-side resultTypeOutParam? producer —
/// M4b-3 P2b-ii" — and the ladder's Residue 1. A source tree that still
/// carries that phrase, in a message OR in a doc comment claiming the
/// producer is missing, is making a stale claim about what is
/// implemented.
///
/// Mirrors the two retired-label gates above and inherits their stated
/// precondition: a TEXTUAL scan is a floor (the retired wording never
/// comes back), not a ceiling. The needle is the distinctive subject of
/// both retired messages and lies within one source line of each
/// (verified against the task-3 commit's `args.rs` and `finalize.rs`
/// with `git show <commit>:<path> | grep -c`: one offender in each
/// there, zero here). Prose that names the producer as EXISTING (e.g.
/// "`args::add_implicit_arg` is the producer") does not contain the
/// needle and is not an offender.
#[test]
fn no_seam_points_at_the_retired_p2b_ii_label() {
    let src_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    let needle = "resultTypeOutParam? producer";
    let mut offenders = Vec::new();
    for path in walk_rs_files(src_dir) {
        let text = std::fs::read_to_string(&path).expect("readable source");
        for (n, line) in text.lines().enumerate() {
            if line.contains(needle) {
                offenders.push(format!("{}:{}", path.display(), n + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "P2b-ii retired the resultTypeOutParam? producer seam (it has a real body in \
         `app/args.rs`); stale label at {offenders:?}"
    );
}

/// M4b-3 P4 RETIRED three seams — the ladder's `Coe` arm, the reporter's
/// `Coe` arm, and the `CoeFun` half of `synthesize_pending_and_normalize_fun_type`'s
/// mvar seam — and rewired every `TypeMismatch`-on-defeq-failure site
/// through `mk_coe`. Their messages read "… coercion insertion — M4b-3
/// P4" and "… CoeFun (M4b-3 P4) …". Mirrors the retired-label gates
/// above and inherits their stated precondition: a TEXTUAL scan is a
/// floor (the retired wording never comes back), not a ceiling.
///
/// The two needles are verified against the commits that actually
/// removed them: task 7's `c999696` deleted
/// `"coercion synthetic mvars require coercion insertion — M4b-3 P4"`
/// (`ladder.rs`) and
/// `"stuck coercion reporting requires coercion insertion — M4b-3 P4"`
/// (`report.rs`); task 8's `0ecb795` deleted a message whose Rust
/// string-literal source wrapped across two physical lines —
/// `"...synthesis: needs \"` then `"CoeFun (M4b-3 P4), or
/// expected-type propagation..."` (`args.rs`) — so the needle is
/// `"CoeFun (M4b-3 P4)"` alone (the fragment that survives on ONE
/// physical line), not `"needs CoeFun (M4b-3 P4)"` (which spans the
/// line break and this scanner's per-line `contains` can never match;
/// fix-round-1 finding, see the report).
#[test]
fn no_seam_points_at_the_retired_p4_label() {
    let src_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    let needles = ["coercion insertion — M4b-3 P4", "CoeFun (M4b-3 P4)"];
    let mut offenders = Vec::new();
    for path in walk_rs_files(src_dir) {
        let text = std::fs::read_to_string(&path).expect("readable source");
        for (n, line) in text.lines().enumerate() {
            if needles.iter().any(|needle| line.contains(needle)) {
                offenders.push(format!("{}:{}", path.display(), n + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "P4 retired the coercion seams (real bodies in `coe.rs`, `ladder.rs`, \
         `report.rs`, `app/args.rs`); stale label at {offenders:?}"
    );
}

/// The four literal kinds are REGISTERED, so they must not appear in any
/// of the crate's three deferral ledgers, and `rawNatLit` — which has no
/// producer in leanr's own parser — must stay unregistered.
///
/// This is also where `seam_audit.rs` keeps its literal coverage now
/// that the constructs are implemented. `unregistered_kinds_are_named_by_kind`
/// used to carry a `("0", "num")` row (removed by task 6) and a `char`
/// one (task 7); both were assertions that the kind is NOT registered,
/// which is exactly the fact P3 falsified. The coverage did not shrink,
/// it INVERTED: the same four kinds are asserted here from the positive
/// side, plus the ledger text, which the removed rows never checked.
#[test]
fn literal_kinds_are_registered_not_deferred() {
    for kind in ["str", "num", "char", "scientific"] {
        assert!(
            leanr_elab::dispatch::elaborator_name_for(kind).is_some(),
            "{kind} must be registered after M4b-3 P3"
        );
    }
    // `rawNatLit` is the one literal kind P3 deliberately does NOT
    // register (design spec § P3): `elabRawNatLit`
    // (`BuiltinTerm.lean:231-234`) elaborates a `rawNatLit` NODE, and
    // leanr's parser has no production that builds one, so registering
    // it would be dead code claiming coverage it cannot have.
    assert!(
        leanr_elab::dispatch::elaborator_name_for("rawNatLit").is_none(),
        "rawNatLit has no producer in leanr's parser and must stay unregistered"
    );

    // The three ledgers, by the exact row each one carried. `dispatch.rs`
    // shed its row in task 6 and `app/mod.rs`/`lib.rs` in task 8; all
    // three needles are kept so a re-added deferral is caught wherever
    // it lands.
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    for (file, needle) in [
        ("dispatch.rs", "num / char literals"),
        ("app/mod.rs", "num/char/scientific literals"),
        ("lib.rs", "`num`/`char` literals"),
    ] {
        let text = std::fs::read_to_string(format!("{root}/{file}")).expect("readable ledger");
        assert!(
            !text.contains(needle),
            "{file} still defers the literals ({needle:?}), but P3 registered all four"
        );
    }
}

/// Every `UnsupportedSyntax` message in the crate names a slice that
/// still OWNS something. P3 shipped rung 3 and the three non-leaf
/// literals, and P4 shipped the coercion machinery, so no LIVE line may
/// name "M4b-3 P3" or "M4b-3 P4" any more.
///
/// Only non-comment lines are inspected, deliberately: a doc comment may
/// and should cite a completed slice historically ("real since M4b-3 P3
/// task 5", "shipped in M4b-3 P4 task 9"), and
/// that is a record of what happened, not a claim that work is owed. A
/// string literal handed to `UnsupportedSyntax` is the opposite — the
/// crate's named-seam discipline reads it as "this construct is deferred
/// to that slice", so naming a COMPLETED slice there is a live false
/// claim.
///
/// Two messages tripped this when it was written, and both were
/// mislabelled rather than stale: `builtin::lit::inst_mvar_id` and
/// `synthetic::default_inst::mvar_id_of` each report an unreachable
/// internal invariant (the oracle's `mvarId!`, a partial function), not
/// a deferral. They were reworded to say so instead of being retargeted
/// at a later slice, which would have been a second false claim — no
/// future slice owns "implement this invariant".
///
/// **KNOWN LIMITATION — this is a per-slice tripwire, and whoever
/// completes a slice owes it a needle.** The needles are the two
/// literals in the body below, so the gate says nothing about any OTHER
/// completed slice. A third message of exactly the shape above survived task 8's
/// audit for precisely that reason: `synthetic::report`'s `.postponed`
/// arm read "… — M4b-3 P2a invariant", naming a slice that is also
/// complete, and only the whole-branch review caught it (reworded in
/// the P3 fix wave).
///
/// It is deliberately NOT generalised to "any completed slice", and the
/// reason is that no non-rotting formulation exists. Live source
/// legitimately names INCOMPLETE slices in exactly this position — that
/// is the named-seam discipline itself (`elab.rs`'s `.postpone` seam
/// and `app/mod.rs`'s LVal-on-`@` arm both name "M4b-4"; `app/mod.rs`'s
/// `elabExplicit` "other" arm names "later M4" — none of these are
/// "M4b-3 P5" any more, now that P5 is complete: this example set itself
/// had to be rewritten by Task 12 when the two live seams it used to
/// cite, `elab.rs`'s and `app/args.rs`'s own "M4b-3 P5", were closed or
/// retargeted) — so telling an
/// offender from a correct seam requires knowing which slices are done,
/// i.e. a hand-maintained completed-slice list that rots the same way
/// this needle does, only silently. Widening the scan by SHAPE instead
/// (say, "a message containing the word `invariant` may not name a
/// slice") would have caught the P2a case but is a heuristic with real
/// false negatives — a reworded message evades it — and a gate that
/// quietly stops catching things is worse than one that visibly needs
/// updating. So: when a slice completes, add its label here.
///
/// **`M4b-3 P4` was added by the whole-branch fix wave, and the needle
/// was measured non-vacuous before it was trusted.** P4 completed on
/// this branch, and task 10 shipped only
/// [`no_seam_points_at_the_retired_p4_label`], which pins two EXACT
/// retired strings — so a newly written seam message naming the
/// now-complete P4 as its owner would have passed both gates. Adding
/// the label here first produced one offender, `src/lib.rs:263`
/// (`pub mod coe; // M4b-3 P4` — a trailing comment on a live line, the
/// one shape this scan's `starts_with("//")` filter does not exempt),
/// which the same wave reworded to `// coercions`. Commands and output
/// are in the fix-wave report; the point of recording it is that a
/// needle added without watching it fire is a gate nobody has shown to
/// gate anything.
///
/// **`M4b-3 P5` was added by Task 12's seam-audit sweep, and it too was
/// measured non-vacuous, not merely assumed clean.** Before this
/// needle was added, `app/mod.rs`'s `elab_explicit` "other" arm raised
/// exactly `"... — M4b-3 P5"` for the `@($t)`/`@$t` wrap — a live
/// (non-comment) line naming a slice that, by the end of this same
/// task, is complete. Task 12 retargeted that one message to "later
/// M4" (see [`no_seam_points_at_the_retired_p5_implicit_lambda_label`])
/// before adding the needle here, so by the time this test runs it is
/// vacuous BY CONSTRUCTION for that offender — the non-vacuity claim
/// rests on having found and fixed the one live occurrence directly
/// (`grep -rn 'M4b-3 P5' crates/leanr_elab/src` returned exactly one
/// non-comment hit before the fix), not on this test having caught it
/// itself.
#[test]
fn no_seam_message_names_a_completed_slice() {
    let src_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    let needles = ["M4b-3 P3", "M4b-3 P4", "M4b-3 P5"];
    let mut offenders = Vec::new();
    for path in walk_rs_files(src_dir) {
        let text = std::fs::read_to_string(&path).expect("readable source");
        for (n, line) in text.lines().enumerate() {
            if line.trim_start().starts_with("//") {
                continue;
            }
            if let Some(needle) = needles.iter().find(|needle| line.contains(**needle)) {
                offenders.push(format!("{}:{} ({needle})", path.display(), n + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "M4b-3 P3, P4 and P5 are complete; live (non-comment) source claiming one at \
         {offenders:?}"
    );
}

/// A closed divergence, kept as a regression test.
///
/// `fun (n : Nat) => pairW n Nat.zero` postpones a `.coe` metavariable
/// at the first argument (`CoeT Nat n (Wrapper ?a)` is `.undef` while
/// `?a` is unassigned), the second argument assigns `?a := Nat`, and the
/// fixpoint resumes the coercion. The fixpoint runs AFTER `mk_lambda`
/// has already abstracted the binder, so the coerced value's `n` has to
/// be abstracted by something other than the abstraction that already
/// ran.
///
/// The oracle absorbs this inside `mkLambdaFVars`, via
/// `MkBinding.elimMVarDeps` (`MetavarContext.lean`): a `syntheticOpaque`
/// mvar whose local context contains the abstracted fvars is replaced by
/// a delayed-assigned mvar applied to them, so the occurrence abstracts
/// like any other argument.
///
/// **History, because it is the reason this test is worth its bytes.**
/// For two slices leanr had no counterpart, `MetaCtx::mk_binding` being
/// a plain `abstract_fvars` with no mvar handling — so leanr emitted
/// `pairW Nat (Wrapper.mk Nat <fvar n>) Nat.zero`, an unabstracted
/// `fvar` where the oracle emits `bvar 0`. That is a wrong `ExprId` with
/// no error, and it was pinned here as an `assert_ne!` against the
/// oracle constant below precisely so it would trip the day the gap
/// closed. It tripped: the `elimMVarDeps` slice's task 10 wired
/// `elim_mvar_deps` into `mk_binding`, and the assertion is now the
/// positive one.
///
/// It was never a coercion bug — measured then, and still true: the same
/// postpone-then-resume path with no binder
/// (`pairW Nat.zero Nat.zero`) agreed with the oracle byte-for-byte
/// throughout, and is the corpus record `coe/postponedThenResumed`.
///
/// **The corpus now carries the same query too** — the record
/// `coe/postponedThenResumedUnderBinder` (elimMVarDeps task 11), which
/// could not exist while the gap was open because it would have failed
/// the gate. This test stays as well rather than being replaced by it:
/// `ORACLE` is kept inline and byte-for-byte as it was pinned, so it is
/// a committed copy of the oracle's answer that a corpus regeneration
/// cannot move. The two disagreeing is itself the signal that the
/// regeneration environment drifted.
#[test]
fn postponed_coe_under_a_binder_abstracts_via_elim_mvar_deps() {
    /// The pinned oracle's answer, dumped from `dump_elab.lean` against
    /// `leanprover/lean4:v4.33.0-rc1` and kept INLINE. That is the whole
    /// reason this test is worth keeping now that
    /// `coe/postponedThenResumedUnderBinder` covers the same query in
    /// the corpus: the expected bytes live in this file, so a corpus
    /// regeneration cannot silently move the target. The record and this
    /// constant are checked against each other by construction — they
    /// are byte-identical today — and the day they disagree, the
    /// regeneration environment drifted.
    ///
    /// It was a throwaway query when it was first dumped: while the
    /// `elimMVarDeps` gap was open a record for this shape would have
    /// failed the gate, so there was nowhere to land it. Task 11 of the
    /// `elimMVarDeps` slice landed it.
    const ORACLE: &str = concat!(
        r#"{"b":{"a":{"k":"const","n":"Nat.zero","us":[]},"f":{"a":{"a":{"i":0,"k":"bvar"},"#,
        r#""f":{"a":{"k":"const","n":"Nat","us":[]},"f":{"k":"const","n":"Wrapper.mk","us":[]},"#,
        r#""k":"app"},"k":"app"},"f":{"a":{"k":"const","n":"Nat","us":[]},"#,
        r#""f":{"k":"const","n":"pairW","us":[]},"k":"app"},"k":"app"},"k":"app"},"#,
        r#""bi":"d","k":"lam","t":{"k":"const","n":"Nat","us":[]}}"#,
    );

    let leanr = support::elab_and_synthesize("fun (n : Nat) => pairW n Nat.zero")
        .expect("this term elaborates and synthesizes cleanly")
        .to_string();

    assert_eq!(
        leanr, ORACLE,
        "a `.coe` metavariable postponed under a binder and resumed after that binder \
         closed must still come back ABSTRACTED — `bvar 0`, not `<fvar n>`. That is \
         `MkBinding.elimMVarDeps`' whole job, and `MetaCtx::mk_binding` runs \
         `elim_mvar_deps` over the telescope to get it. A `fvar` here means the \
         body-side `elim_mvar_deps` call is no longer reaching this metavariable"
    );
}

/// M4b-3 P5 Task 6. `useImplicitLambda`'s `.postpone` arm
/// (`TermElabM.lean:1753-1778`) fires when the term is a local
/// identifier whose type is an mvar APPLICATION — `is_mvar_app`'s spine
/// walk classifies a bare (zero-argument) mvar the same way, since it is
/// the degenerate case of the same spine walk. PR #42 (elimMVarDeps)
/// manufactures aux-mvar applications over binder fvars as the type of
/// an as-yet-untyped `fun` binder; the shape THIS test commits is the
/// simpler bare-mvar case (`x`'s type is a fresh anonymous type mvar
/// with no arguments), reached via the same classifier path — so P1's
/// "no corpus term reaches it" is no longer a safe assumption.
///
/// leanr has no term-level postponement (`lib.rs`: `may_postpone` is
/// written, never read), so this must be a NAMED SEAM — an error the
/// caller can see — and never a silently different term.
#[test]
fn implicit_lambda_postpone_is_a_named_seam() {
    // A binder-bound local whose type is an unassigned mvar, used where
    // an implicit forall is expected.
    let src = "fun x => (x : {a : Type} -> Nat)";
    let e = elab_result(src);
    let msg = match e {
        Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => m,
        other => panic!("expected a named seam for {src:?}, got {other:?}"),
    };
    assert!(
        msg.contains("implicit lambda postponement") && msg.contains("M4b-4"),
        "seam must name the postponement gap and its owning slice: {msg}"
    );
}

/// M4b-3 P5 Task 9. An OMITTED autoParam argument mints a `.tactic`
/// synthetic mvar (oracle `App.lean:846`, `mkTacticMVar`). Executing it
/// needs the `by` elaborator and the tactic framework, which the roadmap
/// assigns to a later M4 slice — so the ladder must REPORT it, not solve
/// it, and never fall through to a different term.
///
/// `elab_and_synthesize`, not `elab_result`: the mint site
/// (`app::args::process_explicit_arg`) does not raise eagerly — it
/// returns `Ok(true)` and lets `main` finalize — so the report only
/// surfaces once the synthetic-mvar FIXPOINT runs to completion.
/// `elab_result` (`elab_term_ensuring_type` + `instantiate_mvars`, no
/// fixpoint) would return `Ok` here with the mvar left bare inside the
/// term; measured, not assumed, before this test was written this way.
#[test]
fn omitted_auto_param_is_a_reported_tactic_mvar() {
    let e = elab_and_synthesize("withTactic");
    let msg = match e {
        Err(err) => format!("{err:?}"),
        Ok(j) => panic!("an omitted autoParam must not silently elaborate, got {j}"),
    };
    assert!(
        msg.contains("tactic"),
        "the report must name the tactic mvar: {msg}"
    );
    assert!(
        msg.contains("parameter `n`"),
        "the report must name the stuck parameter: {msg}"
    );
    assert!(
        msg.contains("M4"),
        "the report must name the deferring slice: {msg}"
    );
}

/// M4b-3 P5 task 9 RETIRED the combined optParam/autoParam seam —
/// `args.rs`'s single "optParam default / autoParam tactic argument —
/// M4b-3 P5" message that used to fire for EITHER an omitted `optParam`
/// (task 8 gave it a real body first) or an omitted `autoParam` (this
/// task's own real body: mint-then-report, above). Mirrors the other
/// retired-label gates in this file and inherits their stated
/// precondition: a TEXTUAL scan is a floor (the retired wording never
/// comes back), not a ceiling.
#[test]
fn no_seam_points_at_the_retired_p5_optparam_autoparam_label() {
    let src_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    let needle = "optParam default / autoParam tactic argument";
    let mut offenders = Vec::new();
    for path in walk_rs_files(src_dir) {
        let text = std::fs::read_to_string(&path).expect("readable source");
        for (n, line) in text.lines().enumerate() {
            if line.contains(needle) {
                offenders.push(format!("{}:{}", path.display(), n + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "P5 task 9 retired the combined optParam/autoParam seam (optParam has a real \
         body since task 8, autoParam mints-then-reports since task 9); stale label at \
         {offenders:?}"
    );
}

/// Task 12's own retired-label gate. Implicit-lambda insertion shipped
/// in M4b-3 P5 (tasks 5-6, `elab.rs`), which completes P5 as a slice —
/// but `elabExplicit`'s "other" arm (`app/mod.rs`) used to raise this
/// exact message for the `@($t)`/`@$t` wrap that disables insertion, a
/// DIFFERENT and still-unclaimed piece of work no P5 task actually did.
/// Task 12 retargeted it to "later M4" rather than leave a completed
/// slice's name on an open seam. A bare `"M4b-3 P5"` needle is
/// deliberately NOT used here (unlike the P2/P2b-ii/P4 gates above):
/// this plan's own doc comments legitimately cite "M4b-3 P5 task N" by
/// the dozen as history throughout this crate, so the needle has to be
/// the specific retired MESSAGE text, not the bare slice label.
#[test]
fn no_seam_points_at_the_retired_p5_implicit_lambda_label() {
    let src_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    let needle = "implicit-lambda insertion (App.lean:2269-2270) — M4b-3 P5";
    let mut offenders = Vec::new();
    for path in walk_rs_files(src_dir) {
        let text = std::fs::read_to_string(&path).expect("readable source");
        for (n, line) in text.lines().enumerate() {
            if line.contains(needle) {
                offenders.push(format!("{}:{}", path.display(), n + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "elabExplicit's `@($t)`/`@$t` arm was retargeted from \"M4b-3 P5\" (complete) to \
         \"later M4\" (unclaimed) by Task 12; stale label at {offenders:?}"
    );
}

/// M4b-3 P5 Task 7 — scoping audit at the binder/argument family
/// boundary (design spec § Amendment 8 item 4). Two reasons motivate
/// it, both already realised once as real bugs in this plan:
///
///   1. `elim_mvar_deps` (`leanr_meta/src/mk_binding.rs`, wired into
///      `MetaCtx::mk_binding`) turns an unassigned mvar that depends on
///      a closing binder's fvars into an AUX-MVAR APPLICATION over
///      those fvars, and PLAINLY ASSIGNS the original to it
///      (`mk_binding.rs:665`, `self.mctx.assign(mvar_id, result)` inside
///      `elim_mvar`). The assignment permanently embeds the abstracted
///      fvar — `?a`'s value becomes `?aux_a @ n` FOREVER, in the
///      metavariable context's own assignment table, which the later
///      fvar->bvar abstraction pass never revisits. Any later code
///      that dereferences that assignment (`instantiate_mvars`,
///      `infer_type`, `is_def_eq`) needs the ORIGINAL binder's fvar
///      back in scope to resolve it — the oracle's rule is
///      `mvarId.withContext` before touching a goal. This went live
///      once already: rung 3 (`default_inst.rs`) shipped without it,
///      and `fun (n : Nat) => 0` broke with "unknown free variable"
///      the day `elim_mvar_deps` was wired in, silently, with no
///      corpus record to notice (`default_inst.rs`'s own module doc,
///      "The history" section). Tasks 1-6 of this plan multiplied
///      binder producers — `fun`'s per-binder `BinderInfo` (Task 1),
///      `instBinder` in the bracketed telescope (Task 3),
///      implicit-lambda insertion (Task 5), the `.postpone` seam
///      (Task 6) — so the question is worth re-asking at each one.
///   2. Local instances (PR #43) change *what synthesis finds* under a
///      binder: a goal solved under the wrong local context now
///      silently picks a DIFFERENT instance rather than merely
///      failing. Task 4 found this twice in one task while landing
///      local-instance install for `fun`'s own telescope: an ordering
///      divergence (the oracle propagates the expected type before its
///      `isClass?` test; leanr's install used to run before
///      propagation too and missed an elided-domain binder that only
///      becomes class-typed via propagation), and a stale
///      `lctx_snapshot` memo left in force by the fix for the first
///      bug. Both are cited below as fixed and tested elsewhere; this
///      audit's job is to check every OTHER call site this plan's new
///      binder producers can reach.
///
/// **Step 1 — the enumeration**, the output of
///
/// ```text
/// grep -rn "synth_instance\|synthesize_pending\|infer_type\|is_def_eq" \
///     crates/leanr_elab/src --include=*.rs | grep -v "^.*tests"
/// ```
///
/// filtered to the REAL call sites (doc-comment citations of the same
/// names are not call sites and are omitted). For each: whose local
/// context is ambient when it runs, and why that is either correct or
/// was made correct.
///
/// **That literal grep is not, on its own, a complete search, and this
/// enumeration does not rely on it alone** — `synthesize_inst_mvar_core`
/// (`synthetic/ladder.rs:192`), the LEAF every rung-1 path bottoms out
/// at, contains none of the four grepped substrings in its own NAME, so
/// a caller of it that is not itself named `synth_instance`/
/// `synthesize_pending`/`infer_type`/`is_def_eq` is invisible to the
/// literal command above. Closed with a second, targeted search (fix
/// round 1, after a reviewer caught exactly this gap):
///
/// ```text
/// grep -rn "synthesize_inst_mvar_core\|try_synth_instance\|\.mk_inst_mvar(\|\.synth_instance(" \
///     crates/leanr_elab/src --include=*.rs
/// ```
///
/// `synthesize_inst_mvar_core` has exactly FOUR real callers, not the
/// three the first pass of this audit found: `ladder.rs:276`
/// (`synthesize_pending_inst_mvar`, already listed below, wrapped),
/// `default_inst.rs:422` (already listed, wrapped), `app/state.rs:433,454`
/// (already listed, ambient-by-construction) — and the one the first
/// pass missed, `synthetic/state.rs:205`, inside `TermElabM::mk_inst_mvar`,
/// now listed below. `try_synth_instance` has exactly ONE caller
/// (`ladder.rs:202`, already listed, wrapped). `MetaCtx::synth_instance`
/// (the non-`try_` hard-failing variant) has ZERO callers anywhere in
/// `leanr_elab/src` — negative result, recorded rather than left
/// silent. `TermElabM::mk_inst_mvar` (the function `synthetic/state.rs:205`
/// lives in) has exactly two callers, both in `builtin/lit/mod.rs`
/// (`:309`, `:398`), both already covered by the classification below.
/// A THIRD, unrelated function also named `mk_inst_mvar`
/// (`app/args.rs:826`, `pub(crate)`-private to that module) is a
/// different function entirely — it only mints and registers a pending
/// goal (`app.st.inst_mvars.push(mvar_id)`), calling
/// `synthesize_inst_mvar_core` NOT AT ALL, so it needed no new entry;
/// its own synchronous-processing callers were already covered via
/// `app/state.rs:433,454` above the first time.
///
/// Every function this crate defines whose name starts with
/// `synthesize_`/`synth_`/`try_synth` was also enumerated directly
/// (`grep -rn "fn synthesize_\|fn try_synth\|fn synth_"
/// crates/leanr_elab/src --include=*.rs`) as a cross-check: all 21
/// hits resolve to functions already reachable from one of the entries
/// below (every one of them lives in `ladder.rs`, `default_inst.rs`,
/// `app/state.rs`, `app/args.rs`, or `coe.rs`, all already covered), so
/// this second pass closes the gap rather than merely relocating it.
///
/// For each real call site below: whose local
/// context is ambient when it runs, and why that is either correct or
/// was made correct.
///
/// **Wrapped in `with_mvar_local_context`/`MetaCtx::with_mvar_context`
/// — the mvar's OWN context, reinstalled before the call:**
///   * `synthetic/ladder.rs:149` `synthesize_synthetic_mvar` — wraps
///     ALL FOUR dispatch arms (`.typeClass`, `.postponed`, `.coe`,
///     `.tactic`), matching the oracle's own
///     `resumePostponed`/`synthesizeSyntheticMVar` posture: this is the
///     ladder's own resumption entry point, reached after whatever
///     binder registered the mvar may have long since closed.
///     `synthesize_inst_mvar_core`'s `try_synth_instance` (`:202`),
///     `is_def_eq` (`:216`, `:256`) and `infer_type` (`:234`) inherit
///     this scope; so does `coe.rs`'s `synthesize_coe_mvar` (dispatched
///     from the `.coe` arm — its own doc at `coe.rs:147-149` names this
///     exact wrapper as "not this function's job", i.e. deliberately
///     NOT re-wrapped, because the caller already did it).
///   * `synthetic/report.rs:105` `report_stuck_synthetic_mvars`'s
///     `.coe` arm — the oracle's `:305` runs this arm under
///     `mvarId.withContext` too (its own comment: "A `.coe` mvar
///     registered inside a binder carries `e` as a free variable of
///     that binder ... the binder has closed by the time the reporter
///     runs"). `infer_type(e)` at `:106` is inside the wrap.
///   * `synthetic/default_inst.rs:213`
///     `synthesize_using_default_prio` — rung 3's own re-entry, ported
///     from the oracle's `:114` (this is the site that was the
///     dormant/then-live seam). Everything nested inside it in the
///     SAME call — `synthesize_using_default_instance`'s
///     `infer_type(candidate)` (`:260`) and
///     `with_assignable_synthetic_opaque(|m| m.is_def_eq(..))`
///     (`:288`), and the recursive `synthesize_pending` (`:301`) ->
///     `synthesize_using_instances` ->
///     `synthesize_pending_inst_mvar_committed` chain — inherits this
///     scope UNLESS it re-enters for a DIFFERENT goal id, which is the
///     next bullet.
///   * `synthetic/default_inst.rs:422`
///     `synthesize_pending_inst_mvar_committed` — opens its OWN scope
///     for its OWN `mvar_id` parameter (an instImplicit subgoal a
///     default-instance candidate introduced), ported from the
///     oracle's `commitWhen <| mvarId.withContext do` (`:135`). This is
///     the site the Task 4 fix wave's "found it twice" history lives
///     on: see the module doc above it for the ordering divergence and
///     stale-memo fixes, both closed and tested elsewhere
///     (`metactx.rs`'s own `install_local_instance_for_last_pushed_drops_a_stale_memo`).
///     `synthesize_inst_mvar_core` (dispatched from here) inherits this
///     scope.
///
/// **Ambient by construction — synchronous, in-scope, no stored mvar
/// is being resumed across a closed binder:**
///   * `app/args.rs:127` (`infer_type(f2)`, post-`coerceToFunction?`),
///     `app/args.rs:672` (`infer_type(head)`, an instImplicit binder's
///     class head while walking the CURRENT application's own
///     f_type telescope), `app/mod.rs:367` (`infer_type(f)`, the
///     just-elaborated head), `app/finalize.rs:59,102`
///     (`infer_type(e)`/`is_def_eq(expected, e_type)` — `finalize`'s
///     own doc: "the eta fvars are still live in the ambient `lctx`
///     here"), `app/propagate.rs:88` (`is_def_eq(expected, resulting)`,
///     mid-telescope) — every one of these runs inside the SAME
///     synchronous `main`/`finalize` call that minted whatever it is
///     looking at; the binder it needs, if any, has not closed.
///   * `app/state.rs:433,454`
///     (`try_synthesize_app_inst_mvars`/`synthesize_app_inst_mvars`,
///     both calling `synthesize_inst_mvar_core` DIRECTLY, with no
///     `with_mvar_local_context`) — looked the most suspicious hit in
///     the whole enumeration, since it calls the same core the wrapped
///     sites call, unwrapped. Confirmed correct rather than assumed:
///     every `mvar_id` here is one THIS SAME `AppElab` call minted
///     (`args.rs`'s `mk_inst_mvar`/`process_inst_implicit_arg`) at the
///     CURRENT ambient scope, and both callers run before that scope
///     can close (`propagate.rs:87`, mid-telescope; `finalize.rs:73,95,111`,
///     before `elab_app_aux`'s own bracket restores `lctx` — see
///     `finalize.rs`'s own eta-fvars comment above). A nested argument
///     that is itself a binder (e.g. `f [inst] (fun y => ..)`) restores
///     ITS OWN checkpoint on exit, so ambient is back to identical by
///     the time control returns here either way.
///   * `synthetic/state.rs:205`, inside `TermElabM::mk_inst_mvar` —
///     THE ENTRY THE SECOND SEARCH ABOVE FOUND, missed by the first
///     pass because `mk_inst_mvar` matches none of the brief's four
///     grepped substrings. Same shape as the `app/state.rs` pair right
///     above it, and the SAME reasoning: `mk_fresh_expr_mvar_of_kind`
///     mints `mvar_id` (capturing whatever `lctx` is ambient AT THAT
///     INSTANT as the new mvar's own declared context), and the very
///     next line, still inside the same function call with nothing
///     between them, tries `synthesize_inst_mvar_core(mvar_id)` — no
///     scope can possibly have changed between the mint and the try.
///     Its own two callers, `builtin/lit/mod.rs:309`
///     (`elab_num`) and `:398` (`elab_scientific`), are themselves
///     synchronous leaf elaborators invoked mid-telescope, so whatever
///     binder is open when a numeral or scientific literal is
///     elaborated is still open here too.
///   * `builtin/binder/fun.rs`'s `propagate_expected_type`
///     (`is_def_eq(fvar_type, domain)`) and `builtin/lit/mod.rs:88`
///     (`is_def_eq(e, ty_mvar)`, `mk_fresh_type_mvar_for`) — both run
///     mid-telescope, immediately after minting the fvar/mvar they
///     unify, in the same binder's own still-open scope. This is ALSO
///     the mechanism that quietly resolves an ASCRIBED elided binder
///     without ever reaching rung 3 at all (see
///     `default_instance_rung_reinstalls_the_binder_elim_mvar_deps_abstracted_over`'s
///     own doc below for where that surprised this audit).
///   * `coe.rs:75,111,112,222,239` (`mk_coe`, `ensure_has_type`,
///     `ensure_type`) — every caller is in-crate and synchronous
///     (`coe.rs`'s own doc: "every caller is in-crate"); these never
///     resume a stored goal, they act on an `ExprId` the caller already
///     holds in the current call.
///   * `elab.rs:461` (`infer_type(x)`, `use_implicit_lambda`'s
///     `isLocalIdent?` check) — `x` is an fvar `local_ident_of` just
///     resolved via `lctx_lookup_by_name` against the CURRENT ambient
///     `lctx`, so it is in ambient by construction.
///
/// **Deliberately ambient, by the oracle's own transcription (not a
/// gap):**
///   * `synthetic/report.rs:33` (`pending_class_name`'s
///     `instantiate_mvars`) and `synthetic/report.rs:94`
///     (`report_stuck_synthetic_mvars`'s `.typeClass` arm) —
///     `instantiate_mvars` substitutes ASSIGNED mvars into an `Expr`
///     and consults no `lctx` at all, so which context is ambient when
///     it runs cannot change its answer (`report.rs:98-99`'s own
///     comment makes this contrast explicit against the `.coe` arm
///     right next to it, which DOES need the wrap because it calls
///     `infer_type`, not `instantiate_mvars`). `pending_class_name` is
///     ALSO called from rung 3 (`default_inst.rs:214`, already
///     wrapped there for `infer_type`'s benefit further down the same
///     closure) — its own `instantiate_mvars` call would be safe
///     either way.
///
/// **Conclusion.** Every reachable call site EITHER the brief's literal
/// grep OR the second, targeted search for direct callers of
/// `synthesize_inst_mvar_core`/`try_synth_instance`/`.synth_instance(`
/// turned up is either wrapped, ambient-correct-by-construction, or
/// ambient because the operation itself does not consult `lctx`.
/// Nothing new was found wrong — the one entry the second pass added
/// (`synthetic/state.rs:205`) turned out to be the same
/// ambient-by-construction shape as its already-classified siblings,
/// not a new bug. That does not make the second pass redundant: the
/// literal grep alone could not have found it, and a search that only
/// checks the names the brief happened to grep for is not the same
/// claim as a search over every real call site. Two genuinely NEW paths
/// this plan's own binder producers
/// opened — implicit-lambda-inserted (Task 5) instance-implicit
/// binders, and a default-instance-rung dereference nested two levels
/// under an unrelated local-instance binder — had no existing test
/// discriminating on their SCOPING (as opposed to their shape), so
/// `implicit_lambda_inserted_local_instance_is_preferred` and
/// `nested_local_instance_does_not_disturb_the_default_rungs_scoping`
/// below close that gap. See each test's own doc for its mutation
/// check, INCLUDING one case where building the intended nested test
/// first required correcting which source shape actually reaches rung
/// 3 at all — recorded there rather than silently fixed, since it is
/// itself a finding about how easy this seam is to test around by
/// accident.
mod scoping_audit {
    use super::*;

    /// Reason 2, the shape Task 1/3 introduced and PR #43 makes
    /// observable: synthesis under an explicit instance-implicit binder
    /// must find the LOCAL instance, not `Elab0`'s global
    /// `instAddNat` — `get_instances` appends matching locals ahead of
    /// globals (PR #43's own doc).
    ///
    /// Asserts the FULL body shape, not merely "a `bvar` appears
    /// somewhere" (the brief's own sample test, and this task's
    /// standing carry-over calls that weak by name): the instance
    /// argument slot of `Add.add {Nat} [self] Nat.zero Nat.zero` must
    /// be EXACTLY `bvar 0` (the binder), and nothing else in the term
    /// may have changed shape either. A mutation that made the local
    /// search silently no-op (picking `instAddNat` instead) would put
    /// `const "instAddNat"` in that exact slot instead — caught, not
    /// merely "some bvar somewhere else in the term".
    ///
    /// Mutation check (task 7 report has the full transcript): with
    /// `MetaCtx::install_local_instance_for` (`metactx.rs`) short-circuited
    /// to skip the `local_instances` registration, this test FAILS —
    /// the instance slot becomes `{"k":"const","n":"instAddNat","us":[]}`
    /// — and passes again once restored.
    #[test]
    fn synthesis_under_a_local_instance_binder_prefers_the_local() {
        let j = elab_and_synthesize("fun [inst : Add Nat] => (Add.add Nat.zero Nat.zero : Nat)")
            .expect("fun [inst : Add Nat] => .. must elaborate");
        assert_eq!(j["k"], "lam");
        assert_eq!(j["bi"], "c");
        assert_eq!(
            j["b"],
            serde_json::json!({
                "k": "app",
                "f": {
                    "k": "app",
                    "f": {
                        "k": "app",
                        "f": {
                            "k": "app",
                            "f": {"k": "const", "n": "Add.add", "us": []},
                            "a": {"k": "const", "n": "Nat", "us": []}
                        },
                        "a": {"k": "bvar", "i": 0}
                    },
                    "a": {"k": "const", "n": "Nat.zero", "us": []}
                },
                "a": {"k": "const", "n": "Nat.zero", "us": []}
            }),
            "the instance argument (second application from the head) must be the \
             BINDER's own bvar, not a global constant"
        );
    }

    /// Reason 1, exactly as the design spec cites it: `fun (n : Nat) =>
    /// 0` is the MEASURED historical break (`default_inst.rs`'s own
    /// module doc, "The history" section) — `elim_mvar_deps` PLAINLY
    /// ASSIGNS `0`'s unresolved `OfNat` carrier/instance mvars to aux-mvar
    /// applications over `n` the moment `n`'s lambda closes
    /// (`MetaCtx::mk_binding`, `mk_binding.rs:665`), and that assignment
    /// permanently embeds `n` as a raw fvar reference. Rung 3 (the only
    /// rung that can still ground this goal, since the carrier is
    /// otherwise unconstrained) must reinstall `n`'s own local context
    /// before dereferencing it or this fails with "unknown free
    /// variable".
    ///
    /// **Correction to the brief's own sample test**, checked rather
    /// than trusted (this task's standing carry-over): the brief's
    /// `fun (n : Nat) => (fun x => x : Nat -> Nat)` does NOT exercise
    /// this at all. `x`'s elided domain mvar is unified directly against
    /// the ascription's `Nat` by `propagate_expected_type`'s inline
    /// `is_def_eq` the moment `x` is pushed — it is ASSIGNED long
    /// before `n`'s own `mk_lambda` ever runs `elim_mvar_deps`, so no
    /// aux-mvar application is ever produced and the test would pass
    /// unchanged even with rung 3's scoping wrap deleted entirely
    /// (measured directly: run against the SAME mutation this test's own
    /// check below uses, that shape still elaborates correctly). `fun (n
    /// : Nat) => 0` is the corpus's own `num/zeroUnderBinder` record;
    /// this test pins the SAME source here too, deliberately, as the
    /// scoping story's self-contained anchor rather than sending a
    /// reader to a different file to see why it matters.
    ///
    /// Mutation check: with `synthesize_using_default_prio`'s
    /// `with_mvar_local_context` wrap bypassed (the closure invoked
    /// directly on `self` instead), this test FAILS with a `MetaError`
    /// (`Infer("unknown free variable")` dereferencing `n`) rather than
    /// elaborating — confirmed, restored.
    #[test]
    fn default_instance_rung_reinstalls_the_binder_elim_mvar_deps_abstracted_over() {
        let j =
            elab_and_synthesize("fun (n : Nat) => 0").expect("fun (n : Nat) => 0 must elaborate");
        assert_eq!(
            j,
            serde_json::json!({
                "k": "lam",
                "bi": "d",
                "t": {"k": "const", "n": "Nat", "us": []},
                "b": {
                    "k": "app",
                    "f": {
                        "k": "app",
                        "f": {
                            "k": "app",
                            "f": {"k": "const", "n": "OfNat.ofNat", "us": [{"k": "zero"}]},
                            "a": {"k": "const", "n": "Nat", "us": []}
                        },
                        "a": {"k": "lit", "n": "0"}
                    },
                    "a": {
                        "k": "app",
                        "f": {"k": "const", "n": "instOfNatNat", "us": []},
                        "a": {"k": "lit", "n": "0"}
                    }
                }
            }),
            "must match the oracle's own answer (fixture id num/zeroUnderBinder) byte \
             for byte: instOfNatNat found and applied, no dangling mvar or fvar"
        );
    }

    /// Reason 2's NEW producer: Task 5's implicit-lambda insertion
    /// pushes its instance-implicit binder ANONYMOUSLY
    /// (`elab.rs::elab_implicit_lambda`'s own doc: pushed with `None`,
    /// not the expected type's own binder name, to reproduce hygiene's
    /// effect). `binder_smoke.rs`'s
    /// `implicit_lambda_wraps_instance_implicit_too` already pins the
    /// WRAP's shape (`fun [inst : Add Nat] => Nat.zero`) but its body
    /// never performs an instance search, so it cannot discriminate
    /// whether the anonymous local actually got INSTALLED — a gap this
    /// audit closes rather than assumes closed.
    ///
    /// `elab_implicit_lambda` pushes via the combined `push_local_decl`
    /// (`metactx.rs:706`, mint-and-install in one call), not the split
    /// `push_local_decl_without_instance` /
    /// `install_local_instance_for_last_pushed` pair `fun`'s own
    /// telescope needs (`metactx.rs:723-735`'s own doc: that split
    /// exists only for a domain that still needs `propagateExpectedType`
    /// to refine AFTER the push; the implicit-lambda wrap's binder type
    /// comes straight off an already-fully-elaborated `Forall` node, so
    /// there is nothing left to refine and the plain combined call is
    /// correct here, the same as every OTHER `push_local_decl` caller
    /// `forall`/`let`/`have`).
    ///
    /// `(Add.add Nat.zero Nat.zero : [inst : Add Nat] -> Nat)` produces
    /// byte-identical `j["b"]` to the EXPLICIT-binder test above — two
    /// different producers (a user-written `fun [inst : ..] => ..`
    /// versus an auto-inserted wrap) reaching the same term is the
    /// point: both correctly install, and both correctly search, the
    /// same local instance.
    ///
    /// Mutation check: same mutation as the explicit-binder test above
    /// (`install_local_instance_for` short-circuited) — this test FAILS
    /// the same way, the instance slot becoming `const "instAddNat"`;
    /// restored. A SECOND, narrower mutation — swapping
    /// `elab_implicit_lambda`'s `push_local_decl` call for
    /// `push_local_decl_without_instance` alone (no matching
    /// `install_local_instance_for_last_pushed` added back) — also
    /// fails this test the same way while leaving the EXPLICIT-binder
    /// test untouched, confirming this test discriminates the
    /// IMPLICIT-LAMBDA install path specifically, not just the shared
    /// `install_local_instance_for` machinery both tests exercise.
    #[test]
    fn implicit_lambda_inserted_local_instance_is_preferred() {
        let j = elab_and_synthesize("(Add.add Nat.zero Nat.zero : [inst : Add Nat] -> Nat)")
            .expect("the implicit-lambda wrap must fire and elaborate");
        assert_eq!(j["k"], "lam");
        assert_eq!(j["bi"], "c");
        assert_eq!(
            j["b"],
            serde_json::json!({
                "k": "app",
                "f": {
                    "k": "app",
                    "f": {
                        "k": "app",
                        "f": {
                            "k": "app",
                            "f": {"k": "const", "n": "Add.add", "us": []},
                            "a": {"k": "const", "n": "Nat", "us": []}
                        },
                        "a": {"k": "bvar", "i": 0}
                    },
                    "a": {"k": "const", "n": "Nat.zero", "us": []}
                },
                "a": {"k": "const", "n": "Nat.zero", "us": []}
            }),
            "the auto-inserted implicit-lambda binder's own instance must be found, \
             exactly as the explicit-binder form is"
        );
    }

    /// Both reasons TOGETHER, nested: an outer EXPLICIT local-instance
    /// binder (`[inst : Add Nat]`, unrelated to the goal below it)
    /// enclosing the exact `fun (n : Nat) => 0` aux-mvar shape from
    /// `default_instance_rung_reinstalls_the_binder_elim_mvar_deps_abstracted_over`
    /// above. This is the shape the Task 4 fix wave's own history warns
    /// a reader to expect more of: a local-instance install sitting in
    /// an ENCLOSING scope while a DIFFERENT, inner binder's own
    /// aux-mvar goal gets resolved by rung 3.
    ///
    /// **Measured, not assumed, which source shape actually reaches
    /// rung 3 here.** The first draft ascribed the inner `fun` (`(fun (n
    /// : Nat) => 0 : Nat -> Nat)`, mirroring how the OTHER tests in this
    /// module ascribe their inner binders) and it is WRONG for this
    /// purpose: `ensure_has_type`'s `is_def_eq` between the ascription's
    /// `Nat -> Nat` and the lambda's inferred `Nat -> ?a` PATTERN-SOLVES
    /// `?a` directly (`?a`'s underlying aux-mvar gets assigned `fun _ =>
    /// Nat` while comparing the two `Pi` bodies under a temporary local
    /// for `n` — ordinary unification, no rung 3 involved), which
    /// grounds the `OfNat` carrier before the top-level fixpoint even
    /// starts. Confirmed by instrumentation: with the ascription present,
    /// `synthesize_using_default_prio` is called ZERO times for this
    /// source; `pending_mvars` is already empty by the time rung 3 would
    /// run. Dropping the ascription (`fun [inst : Add Nat] => (fun (n :
    /// Nat) => 0)`, this test's actual source) restores the ORIGINAL,
    /// unascribed `num/zeroUnderBinder` shape as the outer binder's
    /// body, confirmed BY THE SAME INSTRUMENTATION to reach
    /// `synthesize_using_default_prio` exactly as the single-binder test
    /// above does — and it elaborates to byte-identical output either
    /// way, since both paths reach the same ground answer.
    ///
    /// Two ways nesting specifically could break here that the
    /// single-binder test above cannot catch: `lctx_restore`'s
    /// depth-based truncation of `local_instances` (`metactx.rs`'s own
    /// doc on why it truncates by DEPTH, not index) mis-tracking the
    /// depth across a NESTED push, or rung 3's `with_mvar_local_context`
    /// reinstalling only a partial snapshot that drops the outer
    /// binder's entry.
    ///
    /// Mutation check: same `synthesize_using_default_prio` wrap-bypass
    /// mutation as the single-binder aux-mvar test — this test FAILS
    /// the same way (`Infer("unknown free variable")` dereferencing
    /// `n`); restored.
    #[test]
    fn nested_local_instance_does_not_disturb_the_default_rungs_scoping() {
        let j = elab_and_synthesize("fun [inst : Add Nat] => (fun (n : Nat) => 0)")
            .expect("nested binder must still resolve rung 3 correctly");
        assert_eq!(j["k"], "lam");
        assert_eq!(j["bi"], "c");
        assert_eq!(j["b"]["k"], "lam");
        assert_eq!(j["b"]["bi"], "d");
        assert_eq!(
            j["b"]["b"],
            serde_json::json!({
                "k": "app",
                "f": {
                    "k": "app",
                    "f": {
                        "k": "app",
                        "f": {"k": "const", "n": "OfNat.ofNat", "us": [{"k": "zero"}]},
                        "a": {"k": "const", "n": "Nat", "us": []}
                    },
                    "a": {"k": "lit", "n": "0"}
                },
                "a": {
                    "k": "app",
                    "f": {"k": "const", "n": "instOfNatNat", "us": []},
                    "a": {"k": "lit", "n": "0"}
                }
            }),
            "the inner binder's own default-instance goal must resolve exactly as it \
             does with no outer local-instance binder present"
        );
    }
}
