//! macro/binop% P2: the ElabOp fixture (prelude copy of the real Init
//! notations, `tests/fixtures/elab/gen_elab_op.sh`) and the oracle's
//! expansion golden file `op-expansions.jsonl` (`dump_op_expansions.lean`).
//! See the design spec § Harness (amended 2026-10-02).

mod support;

use std::sync::Arc;

use leanr_elab::dispatch::SynElem;
use leanr_kernel::bank::Store;
use leanr_olean::ModuleData;
use leanr_syntax::grammar::GrammarSnapshot;
use leanr_syntax::{parse_term, ParseResult};

/// leanr's parser picks a different kind than the oracle for these
/// sources. `(priority := low)` on `>=`/`<=` (`Init/Notation.lean:370-371`)
/// should put them behind `≥`/`≤`; leanr_syntax picks the low-priority
/// alternative. Both rows of each pair expand to the same head
/// (`:372-373` vs `:389`, `:392`), so elaboration cannot observe it. A
/// leanr_syntax follow-up. Pinned here so a fix shows up as a failure
/// to update, not silently.
const KNOWN_PARSE_DIVERGENCES: &[(&str, &str)] =
    &[("a >= b", "«term_>=_»"), ("a <= b", "«term_<=_»")];

fn elab_op_grammar() -> GrammarSnapshot {
    let bytes =
        std::fs::read(support::fixture_in("elab", "ElabOp.olean")).expect("committed ElabOp.olean");
    let mut st = Store::persistent();
    let md = ModuleData::parse(&bytes, &mut st).expect("decode ElabOp.olean");
    assert!(md.imports.is_empty(), "ElabOp must stay import-free");
    let name = Arc::new(leanr_kernel::Name::Anonymous); // display-only
    leanr_grammar::assemble(&[(name, md)], &st).snapshot
}

fn golden() -> Vec<serde_json::Value> {
    std::fs::read_to_string(support::fixture_in("elab", "op-expansions.jsonl"))
        .expect("committed op-expansions.jsonl")
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str(l).expect("valid JSONL"))
        .collect()
}

/// Parse `src` as a term and insist the term spans ALL of it:
/// `parse_term` stops silently at an unknown token (`a ⊕⊕ b` is
/// `<ident>` with no error), which would test the wrong term.
fn parse_whole(src: &str, snap: &GrammarSnapshot) -> (ParseResult, SynElem) {
    let parsed = parse_term(src, snap);
    assert!(
        parsed.errors.is_empty(),
        "{src:?}: parse errors {:?}",
        parsed.errors
    );
    let elem = parsed
        .tree
        .root()
        .first_child_or_token()
        .unwrap_or_else(|| panic!("{src:?}: no term child"));
    let range = elem.text_range();
    assert_eq!(
        (usize::from(range.start()), usize::from(range.end())),
        (0, src.trim_end().len()),
        "{src:?}: the parsed term does not span the whole source"
    );
    (parsed, elem)
}

/// Every golden source parses whole under ElabOp's grammar, to the
/// oracle's kind or to a pinned known divergence.
#[test]
fn golden_sources_parse_to_the_oracle_kind() {
    let snap = elab_op_grammar();
    let golden = golden();
    assert_eq!(
        golden.len(),
        31,
        "op-expansions.jsonl: 29 samples + 2 forced kinds"
    );
    for g in &golden {
        let src = g["src"].as_str().unwrap();
        let want = g["kind"].as_str().unwrap();
        let (parsed, elem) = parse_whole(src, &snap);
        let got = parsed.tree.kinds.name(elem.kind());
        if got != want {
            assert!(
                KNOWN_PARSE_DIVERGENCES.contains(&(src, got)),
                "{src:?}: leanr kind {got:?}, oracle {want:?}"
            );
        }
    }
}
