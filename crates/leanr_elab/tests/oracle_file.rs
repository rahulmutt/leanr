//! M4c-2a file-corpus differential gate (spec
//! `docs/superpowers/specs/2026-10-04-m4c2a-file-loop-design.md`
//! § Harness). Every committed `{id, src, cmds}` record of
//! `file-queries.jsonl` (`tests/fixtures/elab/dump_decls.lean files`) is
//! one header-less multi-command source; leanr's parser must split it into
//! exactly the oracle's commands.

mod support;

/// `wc -l tests/fixtures/elab/file-queries.jsonl` at the last deliberate
/// regen. `>=`: adding a record is a one-line bump, not a failing gate.
const CORPUS_FLOOR: usize = 15;

#[test]
fn file_corpus_sources_parse_into_the_oracle_commands() {
    let text = std::fs::read_to_string(support::fixture_in("elab", "file-queries.jsonl"))
        .expect("committed file corpus");
    let mut n = 0;
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("valid JSONL");
        let id = q["id"].as_str().expect("id");
        let src = q["src"].as_str().expect("src field");
        let want = q["cmds"].as_array().expect("cmds").len();
        let (_, cmds) = support::parse_commands(src);
        assert_eq!(
            cmds.len(),
            want,
            "{id}: leanr parses {} command(s), oracle {want}",
            cmds.len()
        );
        n += 1;
    }
    assert!(
        n >= CORPUS_FLOOR,
        "file corpus shrank: {n} < {CORPUS_FLOOR}"
    );
}
