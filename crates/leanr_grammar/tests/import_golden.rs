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
        assert_eq!(got.lines().count(), want.lines().count(), "{stem} line count");
    }
}

#[test]
fn scoped_entry_is_skipped_and_recorded() {
    let (st, g) = notadep_grammar();
    assert!(
        g.skipped.iter().any(|s| s.reason == SkipReason::ScopedInactive),
        "scoped ⊖⊖ should be recorded: {:?}",
        g.skipped
    );
    // And its parser must NOT be active: ⊖⊖ has no term production.
    let r = leanr_syntax::parse_module("#check 1 ⊖⊖ 2\n", &g.snapshot);
    assert!(!r.errors.is_empty(), "scoped notation must not parse");
    let _ = st;
}

#[test]
fn raw_parser_entry_skips_but_tokens_fold() {
    let mut st = Store::persistent();
    let bytes = std::fs::read(dir().join("NotaDepMeta.olean")).unwrap();
    let md = ModuleData::parse(&bytes, &mut st).unwrap();
    let name = Arc::new(leanr_kernel::Name::Anonymous);
    let g = assemble(&[(name, md)], &st);
    assert!(
        g.skipped.iter().any(|s| s.reason == SkipReason::RawParser
            && s.decl.ends_with("rawWidget")),
        "raw Parser skip missing: {:?}",
        g.skipped
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
