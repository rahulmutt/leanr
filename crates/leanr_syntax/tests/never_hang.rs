//! Task 11b regression suite: the M3a untrusted-input Global Constraint
//! ("the parser must never fail to terminate on any input") through the
//! public `parse_module` API, against the REAL builtin grammar. Before
//! `Ps::category`'s memoization (see its own doc comment for the full
//! citation/design), `register_paren_family`'s `paren`/`tuple`/
//! `typeAscription` — three leading "term" candidates sharing the
//! `"(" >> hygieneInfo` prefix, each independently recursing into
//! `cat("term", 0)` at the SAME inner position — turned nested parens
//! into Θ(3^depth) work: `def a := ((((( 1 )))))` measured 1.0ms at
//! depth 5, 376ms at depth 10, and >30s (killed) at depth 15. These
//! tests pin that it is now linear-ish (a generous wall-clock BUDGET
//! that a real exponential regression trips almost immediately, not a
//! tight perf pin) and — per the acceptance bar — assert the resulting
//! tree/diagnostics, not just "didn't hang".

use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;
use leanr_syntax::{builtin, parse_module};
use std::time::{Duration, Instant};

/// Real timings on this build are millisecond-scale even at depth
/// 1000+ (task-11b report); this only needs to catch a regression back
/// toward exponential, not pin exact numbers — depth 15 alone used to
/// take >30s.
const BUDGET: Duration = Duration::from_secs(10);

fn count_kind(node: &SyntaxNode, kind_name: &str, kinds: &KindInterner) -> usize {
    let mut n = if kinds.name(node.kind()) == kind_name {
        1
    } else {
        0
    };
    for child in node.children() {
        n += count_kind(&child, kind_name, kinds);
    }
    n
}

/// The exact reproduction shape from the bug report, at depths past
/// where the old exponential behavior was already unusable (10, 15)
/// and up to just under `MAX_CATEGORY_DEPTH` (`parse.rs`, currently
/// 40 — see its own doc comment for why it's calibrated against the
/// heaviest real production rather than this comparatively light
/// paren-nesting shape) — all bounded, all a clean, error-free parse
/// with exactly `depth` nested `Term.paren` nodes. Depths at/past the
/// cap are `parens_past_the_depth_cap_degrade_cleanly_not_hang`,
/// below.
#[test]
fn deeply_nested_parens_terminate_fast_and_parse_clean() {
    let snap = builtin::snapshot();
    for depth in [5usize, 10, 15, 20, 30, 35] {
        let src = format!("def a := {}1{}\n", "(".repeat(depth), ")".repeat(depth));
        let start = Instant::now();
        let r = parse_module(&src, &snap);
        let elapsed = start.elapsed();
        assert!(
            elapsed < BUDGET,
            "depth {depth}: took {elapsed:?} (budget {BUDGET:?}) — exponential regression in category-call caching?"
        );
        assert_eq!(r.tree.text(), src, "depth {depth}: losslessness");
        assert!(
            r.errors.is_empty(),
            "depth {depth}: expected a clean parse, got {:?}",
            r.errors
        );
        let n = count_kind(&r.tree.root(), "Lean.Parser.Term.paren", &r.tree.kinds);
        assert_eq!(
            n, depth,
            "depth {depth}: expected exactly {depth} nested Term.paren nodes, got {n}"
        );
    }
}

/// At/past `MAX_CATEGORY_DEPTH` (`parse.rs` — a Rust-stack-safety cap,
/// unrelated to the cache), the parser must still terminate fast and
/// degrade cleanly: exactly one diagnostic, no panic, and — crucially
/// — losslessness holds even through a hard failure (the file's own
/// `Global Constraints`: "Losslessness is total... including files
/// with parse errors").
#[test]
fn parens_past_the_depth_cap_degrade_cleanly_not_hang() {
    let snap = builtin::snapshot();
    for depth in [39usize, 50, 100, 200, 1_000, 10_000] {
        let src = format!("def a := {}1{}\n", "(".repeat(depth), ")".repeat(depth));
        let start = Instant::now();
        let r = parse_module(&src, &snap);
        let elapsed = start.elapsed();
        assert!(
            elapsed < BUDGET,
            "depth {depth}: took {elapsed:?} (budget {BUDGET:?})"
        );
        assert_eq!(
            r.tree.text(),
            src,
            "depth {depth}: losslessness under failure"
        );
        assert_eq!(
            r.errors.len(),
            1,
            "depth {depth}: expected exactly one recursion-depth diagnostic, got {:?}",
            r.errors
        );
        assert_eq!(r.errors[0].code, "E0301", "depth {depth}");
    }
}

/// Other bracket-shaped term leaders (`anonymousCtor`'s `⟨⟩`) — a
/// single-candidate leader, so not itself an exponential-fanout risk,
/// but still an input-driven `Category` recursion depth and worth
/// pinning as a never-hang/clean-parse regression alongside parens.
#[test]
fn deeply_nested_anonymous_ctor_brackets_terminate_fast_and_parse_clean() {
    let snap = builtin::snapshot();
    for depth in [5usize, 20, 35] {
        let src = format!("def a := {}1{}\n", "⟨".repeat(depth), "⟩".repeat(depth));
        let start = Instant::now();
        let r = parse_module(&src, &snap);
        let elapsed = start.elapsed();
        assert!(
            elapsed < BUDGET,
            "depth {depth}: took {elapsed:?} (budget {BUDGET:?})"
        );
        assert_eq!(r.tree.text(), src, "depth {depth}: losslessness");
        assert!(
            r.errors.is_empty(),
            "depth {depth}: expected a clean parse, got {:?}",
            r.errors
        );
        let n = count_kind(
            &r.tree.root(),
            "Lean.Parser.Term.anonymousCtor",
            &r.tree.kinds,
        );
        assert_eq!(
            n, depth,
            "depth {depth}: expected {depth} nested anonymousCtor nodes"
        );
    }
}

/// `do`-block nesting (`Term.do` + `doSeqBracketed`, which — unlike
/// `doSeqIndent` — needs no column tracking, so it can be nested
/// mechanically in a generated fixture): `do{do{do{1}}}` at increasing
/// depth. `term`'s "do" first-token slot has two leading candidates
/// (`doForward`/`Term.do` — `builtin/do_notation.rs`'s
/// `register_term_wrappers`), so this also exercises a (smaller, since
/// `doForward` bails out via its own `atomic` guard before reaching
/// `doSeq` when there's no `<-`) sibling-fanout shape distinct from the
/// paren family. Only the OUTERMOST `do` is in TERM position (`Term.
/// do`); every nested one is a `doElem` (`doNested :=
/// Lean.Parser.Term.doNested`, `register_term_wrappers`'s sibling
/// `doElem` registration) — both kinds together must total `depth`.
#[test]
fn deeply_nested_do_blocks_terminate_fast_and_parse_clean() {
    let snap = builtin::snapshot();
    for depth in [5usize, 15, 30] {
        let src = format!("def a := {}1{}\n", "do{".repeat(depth), "}".repeat(depth));
        let start = Instant::now();
        let r = parse_module(&src, &snap);
        let elapsed = start.elapsed();
        assert!(
            elapsed < BUDGET,
            "depth {depth}: took {elapsed:?} (budget {BUDGET:?})"
        );
        assert_eq!(r.tree.text(), src, "depth {depth}: losslessness");
        assert!(
            r.errors.is_empty(),
            "depth {depth}: expected a clean parse, got {:?}",
            r.errors
        );
        let n = count_kind(&r.tree.root(), "Lean.Parser.Term.do", &r.tree.kinds)
            + count_kind(&r.tree.root(), "Lean.Parser.Term.doNested", &r.tree.kinds);
        assert_eq!(
            n, depth,
            "depth {depth}: expected {depth} nested do/doNested nodes"
        );
    }
}
