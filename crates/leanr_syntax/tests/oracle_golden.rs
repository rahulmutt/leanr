//! The M3a oracle gate (spec §Testing 4–5): every fixture under
//! tests/fixtures/syntax/ must (a) round-trip byte-exact and (b) —
//! when a committed .stx.jsonl dump exists — match official Lean's
//! parse tree in canonical form, line for line. Hermetic: dumps are
//! committed; regen needs the toolchain (mise run fixtures:regen).

use leanr_syntax::{builtin, canon, parse_module};

fn fixture_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/syntax")
}

#[test]
fn corpus_round_trips_and_matches_oracle_dumps() {
    let snap = builtin::snapshot();
    let mut checked_any = false;
    for entry in std::fs::read_dir(fixture_dir()).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("lean")
            || path.file_name().unwrap() == "dump_syntax.lean"
        {
            continue;
        }
        let src = std::fs::read_to_string(&path).unwrap();
        let result = parse_module(&src, &snap);

        // (a) byte round-trip — EVERY fixture, error files included.
        assert_eq!(result.tree.text(), src, "round-trip failed: {path:?}");

        // (b) oracle equality — fixtures with a committed dump.
        let dump = path.with_extension("stx.jsonl");
        if dump.exists() {
            assert!(
                result.errors.is_empty(),
                "{path:?}: oracle-compared fixtures must parse clean: {:?}",
                result.errors
            );
            let want = std::fs::read_to_string(&dump).unwrap();
            let got = canon::canon_jsonl(&result.tree);
            for (i, (g, w)) in got.lines().zip(want.lines()).enumerate() {
                assert_eq!(g, w, "{path:?} line {}", i + 1);
            }
            assert_eq!(
                got.lines().count(),
                want.lines().count(),
                "{path:?}: line-count mismatch"
            );
            checked_any = true;
        }
    }
    assert!(checked_any, "no oracle dumps found — corpus wiring broken");
}
