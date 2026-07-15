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

/// Error fixtures (spec §Oracle: excluded from oracle-equality — no
/// `.stx.jsonl` dump exists for either, so `corpus_round_trips_and_
/// matches_oracle_dumps` above only round-trip-checks them) round-trip
/// byte-exact through error nodes AND resync: the good commands either
/// side of the garbage still parse as real `declaration` nodes, not
/// swallowed into the error sweep. M3a Task 11, spec §Acceptance item 2.
#[test]
fn error_fixtures_round_trip_and_resync() {
    let snap = builtin::snapshot();
    let src = std::fs::read_to_string(fixture_dir().join("Errors0.lean")).unwrap();
    let r = parse_module(&src, &snap);
    assert_eq!(
        r.tree.text(),
        src,
        "losslessness is TOTAL (spec §Acceptance 2)"
    );
    assert!(!r.errors.is_empty());
    // Resync: both good commands still parse as declarations.
    let kinds = r.tree.kinds.clone();
    let decls = r
        .tree
        .root()
        .children()
        .filter(|c| kinds.name(c.kind()) == "Lean.Parser.Command.declaration")
        .count();
    assert_eq!(decls, 2, "commands after the error must parse normally");
    // The garbage is contained in an <error> node.
    let errs = r
        .tree
        .root()
        .children()
        .filter(|c| kinds.name(c.kind()) == "<error>")
        .count();
    assert_eq!(errs, 1);
}

#[test]
fn every_error_has_a_stable_code_and_a_span_inside_the_file() {
    let snap = builtin::snapshot();
    for name in ["Errors0.lean", "Errors1.lean"] {
        let src = std::fs::read_to_string(fixture_dir().join(name)).unwrap();
        let r = parse_module(&src, &snap);
        assert_eq!(r.tree.text(), src, "{name}");
        for e in &r.errors {
            assert!(e.code.starts_with("E03"), "{name}: {:?}", e);
            assert!((e.span.1 as usize) <= src.len());
            assert!(e.span.0 <= e.span.1);
        }
    }
}

/// Task 11 item (a): `recover_command` must resync at EVERY common
/// command-leading keyword, not just a handful. Before the `first_tok`/
/// `FirstTokens` fix, any production whose body opened with an
/// `Optional` (`declaration`'s `declModifiers` prefix, `section`'s
/// `sectionHeader` prefix, …) was indexed as `FirstTok::Any` — invisible
/// to `starts_command` (which only matches `FirstTok::Sym`) — so a
/// garbage run before ANY of `def`/`theorem`/`structure`/`section`/
/// `private`/`@[..]`/`/-- .. -/` swept all the way to EOF instead of
/// stopping at the keyword. This is a garbage-then-recognized-command
/// matrix, one assertion per keyword, so a future regression in either
/// `first_tokens` or `starts_command` fails loudly and specifically
/// rather than as one aggregate fixture.
#[test]
fn recover_command_resyncs_at_every_common_command_keyword() {
    let snap = builtin::snapshot();
    let cases: &[(&str, &str)] = &[
        ("def", "def resynced := 1\n"),
        ("theorem", "theorem resynced : True := trivial\n"),
        ("structure", "structure Resynced where\n  x : Nat\n"),
        ("section", "section Resynced\nend Resynced\n"),
        ("private", "private def resynced := 1\n"),
        ("@[..]", "@[inline] def resynced := 1\n"),
        ("/-- .. -/ doc comment", "/-- doc -/\ndef resynced := 1\n"),
        ("namespace", "namespace Resynced\nend Resynced\n"),
        ("instance", "instance : Inhabited Nat := ⟨0⟩\n"),
        ("abbrev", "abbrev Resynced := Nat\n"),
    ];
    for (label, good_cmd) in cases {
        let src = format!("prelude\n\n%%% garbage garbage %%%\n\n{good_cmd}");
        let r = parse_module(&src, &snap);
        assert_eq!(r.tree.text(), src, "{label}: round-trip failed");
        assert_eq!(
            r.errors.len(),
            1,
            "{label}: expected exactly one recovery diagnostic, got {:?}",
            r.errors
        );
        assert_eq!(r.errors[0].code, "E0301", "{label}");
        // The error node must NOT have swallowed the good command: at
        // least one non-`<error>` command-level node follows it.
        let kinds = r.tree.kinds.clone();
        let mut saw_error = false;
        let mut saw_real_command_after = false;
        for c in r.tree.root().children() {
            let name = kinds.name(c.kind());
            if name == "<error>" {
                saw_error = true;
            } else if saw_error && name != "Lean.Parser.Command.eoi" {
                saw_real_command_after = true;
            }
        }
        assert!(saw_error, "{label}: no <error> node recorded");
        assert!(
            saw_real_command_after,
            "{label}: recovery swept the good command into the error sweep instead of resyncing"
        );
    }
}
