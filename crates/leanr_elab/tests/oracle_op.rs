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

use leanr_elab::macros::{self, init};

/// The table and the oracle's golden file agree in BOTH directions: every
/// golden kind has a row with the same expansion kind, head and arity,
/// and every row's kind is in the golden file. Deleting a row, swapping
/// a head, or swapping an op kind fails here.
#[test]
fn table_matches_oracle_expansions() {
    let golden = golden();
    let mut seen = std::collections::HashSet::new();
    for g in &golden {
        let kind = g["kind"].as_str().unwrap();
        let row = init::lookup(kind).unwrap_or_else(|| panic!("table has no row for {kind}"));
        assert_eq!(
            row.expansion_kind(),
            g["exp"].as_str().unwrap(),
            "{kind}: expansion kind"
        );
        assert_eq!(row.f, g["f"].as_str().unwrap(), "{kind}: head");
        assert_eq!(
            row.arity() as u64,
            g["arity"].as_u64().unwrap(),
            "{kind}: arity"
        );
        seen.insert(kind.to_string());
    }
    for row in init::INIT_MACROS {
        assert!(
            seen.contains(row.kind),
            "row {} has no oracle golden line",
            row.kind
        );
    }
    assert_eq!(init::INIT_MACROS.len(), 29);
}

/// `expand` over real ElabOp parse trees: operands in source order,
/// taken from the notation node's own children.
#[test]
fn expand_reads_operands_in_order() {
    let snap = elab_op_grammar();
    for g in &golden() {
        let src = g["src"].as_str().unwrap();
        let (parsed, elem) = parse_whole(src, &snap);
        let exp = macros::expand(&elem, &parsed.tree.kinds)
            .unwrap_or_else(|e| panic!("{src}: {e:?}"))
            .unwrap_or_else(|| panic!("{src}: no expansion"));
        assert_eq!(exp.kind_name(), g["exp"].as_str().unwrap(), "{src}");
        assert_eq!(exp.f(), g["f"].as_str().unwrap(), "{src}");
        let texts: Vec<String> = exp.args().iter().map(|a| a.to_string()).collect();
        let want: Vec<&str> = if g["arity"] == 1 {
            vec!["a"]
        } else {
            vec!["a", "b"]
        };
        assert_eq!(
            texts.iter().map(|s| s.trim()).collect::<Vec<_>>(),
            want,
            "{src}: operands"
        );
    }
}

/// A kind with no row is not expanded: `elab_term_core` must elaborate
/// it as is.
#[test]
fn non_table_kinds_do_not_expand() {
    let snap = elab_op_grammar();
    for src in ["fun x => x", "binop% HAdd.hAdd a b", "(a)"] {
        let (parsed, elem) = parse_whole(src, &snap);
        assert!(
            macros::expand(&elem, &parsed.tree.kinds).unwrap().is_none(),
            "{src}"
        );
    }
}
