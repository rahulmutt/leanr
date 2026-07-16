use std::path::Path;

use leanr_kernel::bank::Store;
use leanr_olean::{CatBehavior, EntryScope, ModuleData, ParserEntry};

fn fixture(name: &str) -> Vec<u8> {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/syntax/import")
        .join(name);
    std::fs::read(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
}

fn name_string(st: &Store, id: Option<leanr_kernel::bank::NameId>) -> String {
    st.to_name(None, id).to_string()
}

#[test]
fn notadep_entries_decode_typed() {
    let mut st = Store::persistent();
    let md = ModuleData::parse(&fixture("NotaDep.olean"), &mut st).unwrap();

    let tokens: Vec<&str> = md
        .parser_entries
        .iter()
        .filter_map(|e| match &e.entry {
            ParserEntry::Token(t) => Some(t.as_str()),
            _ => None,
        })
        .collect();
    for expected in ["⊕⊕", "⊗⊗", "⋄⋄", "‼", "⟪", "⟫", "+++", "wob", "wrap["] {
        assert!(tokens.contains(&expected), "missing token {expected:?} in {tokens:?}");
    }

    // The custom category arrives as a category entry named `widget`.
    let cat = md
        .parser_entries
        .iter()
        .find_map(|e| match &e.entry {
            ParserEntry::Category { cat, behavior, .. } => Some((cat, behavior)),
            _ => None,
        })
        .expect("widget category entry");
    assert_eq!(name_string(&st, Some(*cat.0)), "widget");
    assert_eq!(*cat.1, CatBehavior::Default);

    // Global parser entries exist for the mixfix decls; the scoped one
    // is tagged Scoped with namespace `NotaDep`.
    let scoped: Vec<_> = md
        .parser_entries
        .iter()
        .filter(|e| matches!(e.scope, EntryScope::Scoped(_)))
        .collect();
    assert!(!scoped.is_empty(), "expected a scoped entry for ⊖⊖");
    let EntryScope::Scoped(ns) = scoped[0].scope else { unreachable!() };
    assert_eq!(name_string(&st, Some(ns)), "NotaDep");

    let global_parsers = md
        .parser_entries
        .iter()
        .filter(|e| {
            matches!(e.scope, EntryScope::Global)
                && matches!(e.entry, ParserEntry::Parser { .. })
        })
        .count();
    // 6 mixfix/notation + 3 widget syntaxes + wrap[] = 10 (adjust ONLY
    // if the committed fixture legitimately differs; count them in the
    // fixture source).
    assert_eq!(global_parsers, 10);
}

#[test]
fn notadepmeta_raw_parser_entry_decodes() {
    let mut st = Store::persistent();
    let md = ModuleData::parse(&fixture("NotaDepMeta.olean"), &mut st).unwrap();
    let raw = md
        .parser_entries
        .iter()
        .find_map(|e| match &e.entry {
            ParserEntry::Parser { decl, .. } => Some(name_string(&st, Some(*decl))),
            _ => None,
        })
        .expect("rawWidget parser entry");
    assert!(raw.ends_with("rawWidget"), "got {raw}");
}

#[test]
fn legacy_fixtures_still_decode() {
    // Modules whose parserExtension entries are absent/empty must keep
    // decoding, with an empty typed vector.
    let mut st = Store::persistent();
    let p = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/Sample.olean");
    let md = ModuleData::parse(&std::fs::read(p).unwrap(), &mut st).unwrap();
    let _ = md.parser_entries.len(); // field exists; content unasserted
}
