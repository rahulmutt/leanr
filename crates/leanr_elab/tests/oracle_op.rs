//! macro/binop% P2: the ElabOp fixture (prelude copy of the real Init
//! notations, `tests/fixtures/elab/gen_elab_op.sh`) and the oracle's
//! expansion golden file `op-expansions.jsonl` (`dump_op_expansions.lean`).
//! See the design spec § Harness (amended 2026-10-02).

mod support;

use leanr_elab::dispatch::SynElem;
use leanr_syntax::grammar::GrammarSnapshot;
use leanr_syntax::{parse_term, ParseResult};
use support::elab_op_grammar;

/// leanr's parser picks a different kind than the oracle for these
/// sources. `(priority := low)` on `>=`/`<=` (`Init/Notation.lean:370-371`)
/// should put them behind `≥`/`≤`; leanr_syntax picks the low-priority
/// alternative. Both rows of each pair expand to the same head
/// (`:372-373` vs `:389`, `:392`), so elaboration cannot observe it. A
/// leanr_syntax follow-up. Pinned here so a fix shows up as a failure
/// to update, not silently.
const KNOWN_PARSE_DIVERGENCES: &[(&str, &str)] =
    &[("a >= b", "«term_>=_»"), ("a <= b", "«term_<=_»")];

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

/// The op corpus: notations elaborated end to end against ElabOp.
#[test]
fn oracle_op_gate() {
    let replayed = support::run_elab_corpus("ElabOp.olean", "op-queries.jsonl", &elab_op_grammar());
    // Raise deliberately when records are added (`wc -l op-queries.jsonl`).
    // 0 -> 19 (macro/binop% P2 T3): the op/* App-notation records (the
    // brief's 18 plus op/implicit-lambda-bare, which the hook-placement
    // mutation needed: op/implicit-lambda's paren re-enters `elab_term`).
    // 19 -> 54 (P3 T3): the binop/unop/act/lazy rows, the depth/stuck rows,
    // and the unknown-head err row; 54 -> 57: three mutation-killing rows
    // (op/hetero-default-homog, op/homog-literal-pow, op/smul-op-lhs).
    // 57 -> 81 (P3 T4): the brief's 18 binrel rows and the unknown-head
    // binrel err row, plus five mutation-killing rows: op/beq-uncomparable-prop
    // (`toBoolIfNecessary`), op/rel-expected (`analyze tree none`),
    // op/rel-no-default (`withSynthesizeLight`, not `withSynthesize`),
    // op/rel-of-coe-rels and op/rel-of-literal-rels (rel operands are leaves).
    // 81 -> 90 (checkAssignment T4): op/depth, op/depth-mid, op/stuck restored
    // to binder form (the closed spellings kept as `-closed`), plus
    // op/binder-F-hole, meta/at-hadd-V, meta/beta-{lt,add,beq}, op/rel-lt-beta.
    // 94 -> 97 (synth pi-goals T4): meta/synth-pi-{beq-nat,deceq-nat,beq-bool};
    // op/beq-prop, op/bne-prop, op/beq-prop-bool, op/beq-uncomparable-prop
    // re-recorded (4 rows) against instBEqOfDecidableEq (suffix `BEq Bool` dropped).
    const CORPUS_FLOOR: usize = 97;
    assert!(
        replayed >= CORPUS_FLOOR,
        "op corpus shrank: {replayed} < {CORPUS_FLOOR}"
    );
}

/// Every op notation, `binrel%` family included, reaches the elaborator:
/// each golden source elaborates over `Z` operands (the corpus pins the
/// terms). `==`/`!=` work on `Z` through `BEq Z`.
#[test]
fn op_notations_elaborate() {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = elab_op_grammar();
    let mut n = 0;
    for g in golden()
        .iter()
        .filter(|g| g["exp"].as_str().unwrap() != "Lean.Parser.Term.app")
    {
        // `•` is `SMul Nat Z`; `^` is `HPow Z Nat Z`.
        let binders = match g["exp"].as_str().unwrap() {
            "Lean.Parser.Term.leftact" => "(a : Nat) (b : Z)",
            "Lean.Parser.Term.rightact" => "(a : Z) (b : Nat)",
            _ => "(a b : Z)",
        };
        let src = format!("fun {binders} => {}", g["src"].as_str().unwrap());
        support::elab_src_in(&r, &src, &snap).unwrap_or_else(|e| panic!("{src}: {e:?}"));
        n += 1;
    }
    assert!(n > 0, "the golden file has op rows");
}

/// Review Focus #1: a 300-operand left-nested chain. One recursion per
/// operator in `to_tree`, `analyze`, `apply_coe` and `to_expr_core`.
#[test]
fn long_chain_elaborates() {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = elab_op_grammar();
    let src = format!("fun (a : Nat) => {}", vec!["a"; 300].join(" + "));
    support::elab_src_in(&r, &src, &snap).unwrap_or_else(|e| panic!("{e:?}"));
}

/// Review Focus #3: a cdot paren operand is a LEAF (Extra.lean:201-203), so
/// it reaches the existing cdot seam rather than being recursed into.
#[test]
fn cdot_paren_operand_is_the_cdot_seam() {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = elab_op_grammar();
    match support::elab_src_in(&r, "fun (a : Nat) => (· + 1) + a", &snap) {
        Err(leanr_elab::ElabError::UnsupportedSyntax(k)) => {
            assert!(k.contains("cdot"), "{k}")
        }
        other => panic!("expected the cdot seam, got {other:?}"),
    }
}

/// The App rows elaborate end to end on Prop operands (the corpus pins
/// the terms; this pins that every App row reaches the elaborator).
#[test]
fn app_notations_elaborate() {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = elab_op_grammar();
    for g in golden()
        .iter()
        .filter(|g| g["exp"] == "Lean.Parser.Term.app")
    {
        let src = format!("fun (a b : Prop) => {}", g["src"].as_str().unwrap());
        support::elab_src_in(&r, &src, &snap).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    }
}

/// Review Focus #2: the hook's recursive call must carry the caller's
/// `implicit_lambda` flag. Oracle (`lean` against ElabOp) rejects
/// `(@(True ∧ False) : {α : Type} → Prop)` with a type mismatch; passing
/// `true` instead would accept it as `fun {α} => And True False`.
#[test]
fn explicit_paren_with_implicit_expected_type_is_rejected() {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = elab_op_grammar();
    let res = support::elab_src_in(&r, "(@(True ∧ False) : {α : Type} → Prop)", &snap);
    assert!(res.is_err(), "oracle rejects; got {res:?}");
}

/// The whole-source span guard in `parse_whole` fires on a partial parse.
#[test]
#[should_panic(expected = "does not span the whole source")]
fn parse_whole_rejects_partial_parse() {
    let _ = parse_whole("a ⊕⊕ b", &elab_op_grammar());
}

/// macro/binop% P3 T1: the test-support suffix is in the fixture.
#[test]
fn elab_op_has_the_test_support_suffix() {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = elab_op_grammar();
    for src in [
        "fun (n : Nat) (z : Z) (a : Arr Nat) (u : U) (x : V n) (y : F n) => z",
        "Z.ofNat",
        "V.mk",
        "F.mk",
        // the closed operands of the depth/stuck rows (P3 T3)
        "vx",
        "k0",
        "fx",
        "z0",
        // the mutation-killing rows' types (P3 T3)
        "fun (a : MArr Nat) => a",
        // Prelude's `BEq Bool` through `instBEqOfDecidableEq`, a pi subgoal (synth pi-goals slice)
        "(inferInstance : BEq Bool)",
        // op/beq-uncomparable-prop's decidable `Prop` over `Nat`/`U` (P3 T4)
        "fun (n : Nat) (u : U) => (inferInstance : Decidable (PU n u))",
    ] {
        support::elab_src_in(&r, src, &snap).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    }
}
