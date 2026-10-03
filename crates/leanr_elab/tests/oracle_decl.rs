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
