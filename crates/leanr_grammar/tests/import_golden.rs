use std::path::{Path, PathBuf};
use std::sync::Arc;

use leanr_grammar::{assemble, SkipReason};
use leanr_kernel::bank::Store;
use leanr_olean::ModuleData;

fn dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/syntax/import")
}

/// Hermetic single-module "closure": NotaDep only. Importer fixtures
/// avoid Init-declared notation, so folding just NotaDep matches the
/// oracle (corpus self-containment discipline — see design spec).
fn notadep_grammar() -> (Store, leanr_grammar::AssembledGrammar) {
    let mut st = Store::persistent();
    let bytes = std::fs::read(dir().join("NotaDep.olean")).unwrap();
    let md = ModuleData::parse(&bytes, &mut st).unwrap();
    let name = Arc::new(leanr_kernel::Name::Anonymous); // display-only
    let g = assemble(&[(name, md)], &st);
    (st, g)
}

#[test]
fn importers_parse_green_against_oracle_dumps() {
    let (_st, g) = notadep_grammar();
    for stem in ["ImportMixfix", "ImportMunch", "ImportCat", "ImportOverload"] {
        let src = std::fs::read_to_string(dir().join(format!("{stem}.lean"))).unwrap();
        let want = std::fs::read_to_string(dir().join(format!("{stem}.stx.jsonl"))).unwrap();
        let r = leanr_syntax::parse_module(&src, &g.snapshot);
        assert_eq!(r.tree.text(), src, "{stem}: byte round-trip");
        assert!(r.errors.is_empty(), "{stem}: {:?}", r.errors);
        let got = leanr_syntax::canon::canon_jsonl(&r.tree);
        for (i, (g_line, w_line)) in got.lines().zip(want.lines()).enumerate() {
            assert_eq!(g_line, w_line, "{stem} line {i}");
        }
        assert_eq!(
            got.lines().count(),
            want.lines().count(),
            "{stem} line count"
        );
    }
}

/// M3b3 Task 5 Step 1 (RED-first at the assemble layer): NotaDep declares
/// exactly one scoped notation — `scoped infixl:65 " ⊖⊖ " => HSub.hSub`
/// inside `namespace NotaDep`, whose decl is `NotaDep.term_⊖⊖_` and whose
/// only `Scoped` parser_entries are `Token("⊖⊖")` and
/// `Parser { decl: NotaDep.term_⊖⊖_, .. }` (confirmed empirically by
/// decoding NotaDep.olean). It is no longer SKIPPED: `assemble` folds it
/// PRESENT-but-INACTIVE, tagged with its activation namespace `NotaDep`,
/// routed through the same `descr::interpret` the `Global` entries use.
#[test]
fn scoped_entry_is_folded_present_but_inactive_not_skipped() {
    let (st, g) = notadep_grammar();
    // No `ScopedInactive` skip is recorded anymore (the reason is no
    // longer produced for parser decls — brief Step 2).
    assert!(
        !g.skipped
            .iter()
            .any(|s| s.reason == SkipReason::ScopedInactive),
        "no ScopedInactive skip must be recorded anymore: {:?}",
        g.skipped
    );
    // It lands in the snapshot's SCOPED storage tagged with its
    // namespace — not the always-active tables.
    assert!(
        g.snapshot.scoped_namespaces().contains("NotaDep"),
        "scoped ⊖⊖ must be folded under activation namespace NotaDep, got {:?}",
        g.snapshot.scoped_namespaces()
    );
    // And it is INACTIVE by default: with no `open`/`namespace NotaDep`
    // in force, `⊖⊖` must not parse as an infix (its token stays
    // unreserved, its production undispatched).
    let r = leanr_syntax::parse_module("#check 1 ⊖⊖ 2\n", &g.snapshot);
    assert!(
        !r.errors.is_empty(),
        "inactive scoped notation must not parse: {:?}",
        r.errors
    );
    let _ = st;
}

/// M3b3 Task 5 Step 3/4 (oracle pin): the imported scoped `⊖⊖` notation
/// ACTIVATES on both `open NotaDep` and `namespace NotaDep`, parsing as
/// `NotaDep.«term_⊖⊖_»`. Byte-compared against real-toolchain elaborating
/// dumps (`dump_syntax_elab.lean`, so the same-file `open`/`namespace`
/// scope commands are live for the later `#check`, exactly as leanr's own
/// command loop reproduces). Pins the SAME `ScopeStack::is_active`
/// predicate same-file scoped entries (Task 4) go through — here for the
/// IMPORTED base.
#[test]
fn imported_scoped_notation_activates_on_open_and_namespace() {
    let (_st, g) = notadep_grammar();
    for stem in ["ImportScopedOpen", "ImportScopedNs"] {
        let src = std::fs::read_to_string(dir().join(format!("{stem}.lean"))).unwrap();
        let want = std::fs::read_to_string(dir().join(format!("{stem}.stx.jsonl"))).unwrap();
        let r = leanr_syntax::parse_module(&src, &g.snapshot);
        assert_eq!(r.tree.text(), src, "{stem}: byte round-trip");
        assert!(r.errors.is_empty(), "{stem}: {:?}", r.errors);
        let got = leanr_syntax::canon::canon_jsonl(&r.tree);
        for (i, (g_line, w_line)) in got.lines().zip(want.lines()).enumerate() {
            assert_eq!(g_line, w_line, "{stem} line {i}");
        }
        assert_eq!(
            got.lines().count(),
            want.lines().count(),
            "{stem} line count"
        );
    }
}

#[test]
fn raw_parser_entry_skips_but_tokens_fold() {
    let mut st = Store::persistent();
    let bytes = std::fs::read(dir().join("NotaDepMeta.olean")).unwrap();
    let md = ModuleData::parse(&bytes, &mut st).unwrap();
    let name = Arc::new(leanr_kernel::Name::Anonymous);
    let g = assemble(&[(name, md)], &st);
    assert!(
        g.skipped
            .iter()
            .any(|s| s.reason == SkipReason::RawParser && s.decl.ends_with("rawWidget")),
        "raw Parser skip missing: {:?}",
        g.skipped
    );

    // The skip above proves the *parser* (rawWidget : Parser, a compiled
    // function — not a ParserDescr — so `descr::interpret` can't walk it)
    // never becomes an active term production. It says nothing about
    // whether the token it's built from folded into the assembled table.
    //
    // Empirically confirmed (temporary debug dump of NotaDepMeta.olean's
    // decoded `parser_entries`, removed after use): `leading_parser
    // "rawwob"` decodes to TWO separate global entries —
    // `ParserEntry::Token("rawwob")` and `ParserEntry::Parser { cat: term,
    // decl: rawWidget }` — exactly as the brief predicted ("token entries
    // are separate `.token` entries"). The `Token` entry is `Global`, so
    // assemble's fold runs `b.token("rawwob")` unconditionally, independent
    // of the sibling `Parser` entry's interpret failure.
    //
    // A folded token is reserved: it stops lexing as a plain identifier.
    // So under the assembled snapshot:
    //   - `#check rawwob`  -- "rawwob" is a reserved token with no term
    //     production (its only would-be production was the skipped raw
    //     parser) -- must be a parse ERROR.
    //   - `#check rawwobz` -- not a token; ordinary identifier -- must
    //     parse clean, as the control.
    let hit = leanr_syntax::parse_module("#check rawwob\n", &g.snapshot);
    assert!(
        !hit.errors.is_empty(),
        "rawwob must be reserved (folded token, no production): {:?}",
        hit.errors
    );
    let miss = leanr_syntax::parse_module("#check rawwobz\n", &g.snapshot);
    assert!(
        miss.errors.is_empty(),
        "rawwobz (not a token) must parse as an ordinary ident: {:?}",
        miss.errors
    );
}

#[test]
fn fingerprint_distinguishes_import_sets() {
    let builtin_fp = leanr_syntax::builtin::snapshot().fingerprint();
    let (_st, g) = notadep_grammar();
    assert_ne!(g.snapshot.fingerprint(), builtin_fp);
    // Deterministic across assemblies.
    let (_st2, g2) = notadep_grammar();
    assert_eq!(g.snapshot.fingerprint(), g2.snapshot.fingerprint());
}

#[test]
fn samefile_overlay_composes_on_imported_base() {
    // ImportOverload declares a same-file `prefix:100 "⊕⊕" => Nat.succ`
    // over the imported infixl ⊕⊕ — already covered by the oracle-dump
    // test above; this pins the *mechanism*: parse must succeed with
    // zero errors, proving M3b1 threading runs on an assembled
    // (non-builtin) base.
    let (_st, g) = notadep_grammar();
    let src = std::fs::read_to_string(dir().join("ImportOverload.lean")).unwrap();
    let r = leanr_syntax::parse_module(&src, &g.snapshot);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
}
