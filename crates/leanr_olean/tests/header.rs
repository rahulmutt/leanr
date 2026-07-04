use std::path::PathBuf;

use leanr_olean::{OleanError, OleanHeader};
use proptest::prelude::*;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

#[test]
fn parses_the_oracle_fixture() {
    let bytes = std::fs::read(fixture("Sample.olean")).unwrap();
    let header = OleanHeader::parse(&bytes).unwrap();

    let expected_githash = std::fs::read_to_string(fixture("oracle-githash.txt")).unwrap();
    assert_eq!(header.githash, expected_githash.trim());
    assert!(
        header.base_addr > 0,
        "base address should be a nonzero pointer"
    );
}

#[test]
fn rejects_bad_magic() {
    let bytes = std::fs::read(fixture("Sample.olean")).unwrap();
    let mut corrupted = bytes.clone();
    corrupted[0] ^= 0xFF;
    assert_eq!(OleanHeader::parse(&corrupted), Err(OleanError::BadMagic));
}

#[test]
fn rejects_truncated_input() {
    let bytes = std::fs::read(fixture("Sample.olean")).unwrap();
    let truncated = &bytes[..10];
    assert_eq!(
        OleanHeader::parse(truncated),
        Err(OleanError::Truncated(10))
    );
}

#[test]
fn error_messages_are_human_readable() {
    let msg = OleanError::BadMagic.to_string();
    assert!(msg.contains("olean"), "got: {msg}");
}

proptest! {
    /// .olean bytes are untrusted input (docs/THREAT_MODEL.md): the parser
    /// must never panic, whatever the bytes.
    #[test]
    fn arbitrary_bytes_never_panic(bytes in proptest::collection::vec(any::<u8>(), 0..256)) {
        let _ = OleanHeader::parse(&bytes);
    }
}
