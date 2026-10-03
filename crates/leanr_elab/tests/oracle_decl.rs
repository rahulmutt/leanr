//! M4c-1 P2 declaration differential gate (spec
//! `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md`
//! § Harness). Every committed `{id, src, consts|err}` record of
//! `decl-queries.jsonl` (`tests/fixtures/elab/dump_decls.lean`) is parsed
//! by leanr's own parser as exactly one command.

mod support;

/// `wc -l tests/fixtures/elab/decl-queries.jsonl` at the last deliberate
/// regen. `>=`: adding a record is a one-line bump, not a failing gate.
const CORPUS_FLOOR: usize = 79;

#[test]
fn decl_corpus_sources_parse_as_one_command() {
    let text = std::fs::read_to_string(support::fixture_in("elab", "decl-queries.jsonl"))
        .expect("committed decl corpus");
    let mut n = 0;
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("valid JSONL");
        let src = q["src"].as_str().expect("src field");
        let _ = support::parse_command(src);
        n += 1;
    }
    assert!(
        n >= CORPUS_FLOOR,
        "decl corpus shrank: {n} < {CORPUS_FLOOR}"
    );
}

/// The records the pipeline handles so far. Tasks 7-9 of
/// `docs/superpowers/plans/2026-10-03-m4c1-p2-command-elab.md` append theirs;
/// Task 10 deletes this list and gates the whole corpus.
const ENABLED: &[&str] = &[
    // Task 6 — def/abbrev/opaque/example
    "kind/def",
    "kind/abbrev",
    "kind/opaque",
    "kind/example",
    "kind/exampleParams",
    "type/inferred",
    "type/unify",
    "type/lamValue",
    "type/implicitBinder",
    "type/instBinder",
    "type/optParamCleanup",
    "type/headerMVarSolvedByBody",
    "type/groupHoles",
    "univ/explicit1",
    "univ/explicit2",
    "univ/sortHole",
    "univ/idBody",
    "univ/order",
    "univ/orderRev",
    "univ/skipUsedName",
    "univ/defElevenLex",
    "univ/defHeaderUnivByBody",
    "univ/abbrevUniv",
    "height/pick",
    "height/id",
    "height/overThm",
    "height/abbrev",
    "height/explicitTy",
    "err/already",
    "err/univDup",
    "err/unusedUniv",
    "err/unusedUniv2",
    "err/mismatch",
    "err/exampleMismatch",
    "err/appLast",
    "err/unassignedImplicit",
    "err/holeArg",
    "err/holeBare",
    "err/binderHole",
    "err/funBinderType",
    "err/defTypeHole",
    "err/levelMVarValue",
    "err/unknownIdBody",
    // Task 7 — theorems and Prop-typed headers
    "kind/theorem",
    "kind/propDef",
    "kind/abbrevProp",
    "kind/opaqueProp",
    "univ/thmElevenNumeric",
    "univ/propDefElevenNumeric",
    "univ/thmSortHole",
    "univ/thmExplicit",
    "univ/thmUserAndHole",
    "univ/thmLevelOnlyBody",
    "err/thmAlready",
    "err/thmUnivValueOnly",
    "err/thmTypeNotProp",
    "err/propDefHeaderUniv",
    "err/thmHeaderUnivByBody",
    "err/thmTypeHole",
    "err/levelMVarThm",
];

#[test]
fn oracle_decl_gate() {
    let checked = support::run_decl_corpus("decl-queries.jsonl", |id| ENABLED.contains(&id));
    assert_eq!(
        checked,
        ENABLED.len(),
        "an ENABLED id is missing from the corpus"
    );
}

fn decl_result(src: &str) -> Result<Vec<String>, leanr_elab::ElabError> {
    support::with_command_elab(src, |ce, cmd, kinds| {
        ce.elab_decl(cmd, kinds).map(|ns| {
            ns.iter()
                .map(|&n| support::name_to_string(ce.env().store(), None, Some(n)))
                .collect()
        })
    })
}

fn seam_message(src: &str) -> String {
    match decl_result(src) {
        Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => m,
        other => panic!("{src:?}: expected a named seam, got {other:?}"),
    }
}

#[test]
fn header_unknown_ident_is_the_auto_bound_seam() {
    // The oracle auto-binds `α` (probe: `def ab (a : α) : α := a` admits `ab.{u_1}`).
    let m = seam_message("def ab (a : α) : α := a");
    assert!(m.contains("auto-bound") && m.contains("M4c-2"), "{m}");
}

#[test]
fn header_unknown_universe_is_the_auto_bound_seam() {
    // probe: `def uuh (α : Sort w) : Sort w := α` admits `uuh.{w}`.
    let m = seam_message("def uuh (α : Sort w) : Sort w := α");
    assert!(m.contains("auto-bound"), "{m}");
}

#[test]
fn let_and_have_in_a_value_are_the_let_to_have_seam() {
    assert!(seam_message("def sl : Nat := let x := Nat.zero; x").contains("letToHave"));
    assert!(seam_message("def sh : Nat := have x := Nat.zero; x").contains("letToHave"));
}

#[test]
fn example_is_checked_but_not_added() {
    support::with_command_elab("example : Nat := Nat.zero", |ce, cmd, kinds| {
        let before = ce.env().len();
        assert_eq!(
            ce.elab_decl(cmd, kinds).expect("elaborates"),
            Vec::<leanr_kernel::bank::NameId>::new()
        );
        assert_eq!(ce.env().len(), before, "an example must not add constants");
    });
}

#[test]
fn level_mvar_without_error_info_hits_the_fallback() {
    // No binder registers a level error info here: the level mvar comes from
    // the constant `PUnit.unit.{?w}` (Prod's `v` := ?w). Oracle probe (a
    // scratch copy of `dump_decls.lean`, v4.33.0-rc1): `ensureNoUnassigned
    // LevelMVarsAtPreDef`'s fallback (`PreDefinition/Main.lean:84-93`).
    // Pins Task 6 mutation 7, which `err/levelMVarValue` (a binder-info hit)
    // does not kill.
    match decl_result("def lv2 : Nat := Prod.fst (Prod.mk Nat.zero PUnit.unit)") {
        Err(e) => assert_eq!(
            e.oracle_first_line().as_deref(),
            Some("declaration `lv2` contains universe level metavariables at the expression"),
            "{e:?}"
        ),
        Ok(ns) => panic!("a value with an unassigned level mvar was admitted: {ns:?}"),
    }
}
