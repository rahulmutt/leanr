use std::path::PathBuf;
use std::sync::Arc;

use leanr_olean::{ModuleData, OleanError};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

fn parse_fixture(name: &str) -> ModuleData {
    ModuleData::parse(&std::fs::read(fixture(name)).unwrap()).unwrap()
}

fn decls_lines(md: &ModuleData) -> Vec<String> {
    md.constants
        .iter()
        .map(|c| format!("{} {}", c.kind(), c.name()))
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
    let md = parse_fixture("Sample.olean");
    assert_eq!(decls_lines(&md), golden_lines("Sample.decls.txt"));
}

#[test]
fn sample_rich_constants_match_the_oracle_dump() {
    let md = parse_fixture("SampleRich.olean");
    assert_eq!(decls_lines(&md), golden_lines("SampleRich.decls.txt"));
}

#[test]
fn imports_and_metadata_decode() {
    let md = parse_fixture("Sample.olean");
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

/// The spec's sharing guarantee: `constNames` is built by the oracle as
/// `constants.map (·.name)`, so the file shares those Name objects and
/// the decoder must map one file offset to one Arc.
#[test]
fn decoding_preserves_object_sharing() {
    let md = parse_fixture("SampleRich.olean");
    for (n, c) in md.const_names.iter().zip(md.constants.iter()) {
        assert!(
            Arc::ptr_eq(n, c.name()),
            "constNames entry not shared with ConstantVal.name"
        );
    }
}

#[test]
fn garbage_still_fails_cleanly() {
    assert!(matches!(
        ModuleData::parse(b"definitely not an olean"),
        Err(OleanError::Truncated(_))
    ));
}
