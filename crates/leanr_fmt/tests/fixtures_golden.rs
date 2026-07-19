//! Hermetic fixture gate (mirrors leanr_syntax/tests/oracle_golden.rs).
//! Each `<name>.lean` parses with the builtin snapshot; its formatted
//! output must equal the committed `<name>.expected`, and all four
//! self-consistency invariants must hold.

use leanr_syntax::builtin;

fn fixture_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

#[test]
fn fixtures_format_to_expected_and_hold_invariants() {
    let snap = builtin::snapshot();
    let mut checked = 0;
    for entry in std::fs::read_dir(fixture_dir()).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("lean") {
            continue;
        }
        let src = std::fs::read_to_string(&path).unwrap();
        let got = leanr_fmt::format_src(&src, &snap)
            .unwrap_or_else(|e| panic!("{path:?}: unparseable fixture: {e:?}"));
        let expected = std::fs::read_to_string(path.with_extension("expected")).unwrap();
        assert_eq!(got, expected, "format mismatch: {path:?}");
        leanr_fmt::verify::check_invariants(&src, &snap)
            .unwrap_or_else(|e| panic!("{path:?}: invariant failed: {e}"));
        checked += 1;
    }
    assert!(checked > 0, "no fixtures found — harness wiring broken");
}
