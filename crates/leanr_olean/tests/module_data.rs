use std::path::PathBuf;

use leanr_kernel::bank::Store;
use leanr_olean::{ModuleData, OleanError};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

fn parse_fixture(name: &str) -> (Store, ModuleData) {
    let mut st = Store::persistent();
    let md = ModuleData::parse(&std::fs::read(fixture(name)).unwrap(), &mut st).unwrap();
    (st, md)
}

fn decls_lines(st: &Store, md: &ModuleData) -> Vec<String> {
    md.constants
        .iter()
        .map(|c| format!("{} {}", c.kind(), st.to_name(None, Some(c.name()))))
        .collect()
}

fn golden_lines(name: &str) -> Vec<String> {
    std::fs::read_to_string(fixture(name))
        .unwrap()
        .lines()
        .map(str::to_string)
        .collect()
}

#[test]
fn sample_constants_match_the_oracle_dump() {
    let (st, md) = parse_fixture("Sample.olean");
    assert_eq!(decls_lines(&st, &md), golden_lines("Sample.decls.txt"));
}

#[test]
fn sample_rich_constants_match_the_oracle_dump() {
    let (st, md) = parse_fixture("SampleRich.olean");
    assert_eq!(decls_lines(&st, &md), golden_lines("SampleRich.decls.txt"));
}

#[test]
fn imports_and_metadata_decode() {
    let (_, md) = parse_fixture("Sample.olean");
    assert!(
        md.imports.iter().any(|i| i.module.to_string() == "Init"),
        "non-prelude modules implicitly import Init, got {:?}",
        md.imports
            .iter()
            .map(|i| i.module.to_string())
            .collect::<Vec<_>>()
    );
    assert_eq!(md.const_names.len(), md.constants.len());
}

/// The spec's sharing guarantee, id form: `constNames` is built by the
/// oracle as `constants.map (·.name)` — one file offset, one id, so
/// the ids must be EQUAL (the interning invariant upgrades the Arc
/// version's ptr-eq assertion to plain equality).
#[test]
fn decoding_preserves_object_sharing() {
    let (_, md) = parse_fixture("SampleRich.olean");
    for (n, c) in md.const_names.iter().zip(md.constants.iter()) {
        assert_eq!(
            *n,
            c.name(),
            "constNames entry not shared with ConstantVal.name"
        );
    }
}

#[test]
fn garbage_still_fails_cleanly() {
    let mut st = Store::persistent();
    assert!(matches!(
        ModuleData::parse(b"definitely not an olean", &mut st),
        Err(OleanError::Truncated(_))
    ));
}
