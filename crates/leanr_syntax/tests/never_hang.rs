//! Task 11b regression suite: the M3a untrusted-input Global Constraint
//! ("the parser must never fail to terminate on any input") through the
//! public `parse_module` API, against the REAL builtin grammar. Before
//! `Ps::category`'s memoization (see its own doc comment for the full
//! citation/design), `register_paren_family`'s `paren`/`tuple`/
//! `typeAscription` — three leading "term" candidates sharing the
//! `"(" >> hygieneInfo` prefix, each independently recursing into
//! `cat("term", 0)` at the SAME inner position — turned nested parens
//! into Θ(3^depth) work: `def a := ((((( 1 )))))` measured 1.0ms at
//! depth 5, 376ms at depth 10, and >30s (killed) at depth 15.
//!
//! Every parse below runs inside `in_worker`, which is what makes these
//! tests able to FAIL rather than hang (Task 11b review, Important 3): it
//! runs the parse on a worker thread and waits with a `recv_timeout`, so a
//! re-exponentialized cache — or any other non-termination — turns into a
//! loud, bounded test failure instead of a CI-eating hang. An
//! `Instant::elapsed()` assertion placed AFTER `parse_module` returns
//! cannot do that: it never runs.
//!
//! `in_worker` deliberately does NOT size that thread. It used to, because
//! the crate's minimum-stack contract used to be the caller's problem and
//! `libtest` hands every test a 2 MiB thread — far under it. Since Task 11b
//! review wave 2 (Critical 2) `parse_module` spawns its own
//! `MIN_STACK_BYTES` worker, so these tests exercise the same stack a real
//! embedder gets *precisely by not arranging anything*: if the contract
//! ever stopped holding internally, the deep tests below would crash here,
//! which is the point. (The unit tests in `parse.rs` still size their own
//! threads — they drive `Ps::category` directly, below `parse_module`.)
//!
//! Per the acceptance bar, the tests assert the resulting tree/diagnostics,
//! not just "didn't hang".

use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;
use leanr_syntax::{builtin, parse_module, MAX_CATEGORY_DEPTH};
use std::sync::mpsc::{channel, RecvTimeoutError};
use std::time::Duration;

/// Real timings on this build are millisecond-scale even at depth 10,000
/// (task-11b report); this only needs to catch a regression back toward
/// exponential, not pin exact numbers — depth 15 alone used to take >30s.
const BUDGET: Duration = Duration::from_secs(30);

/// Run `f` on a worker thread and fail the test if it has not finished
/// within `BUDGET`. Unlike an after-the-fact `elapsed < BUDGET` assertion,
/// this bounds a HANG: the timeout fires while the parse is still running.
fn in_worker(label: &str, f: impl FnOnce() + Send + 'static) {
    let (tx, rx) = channel();
    let h = std::thread::Builder::new()
        .spawn(move || {
            f();
            let _ = tx.send(());
        })
        .expect("spawn worker");
    match rx.recv_timeout(BUDGET) {
        Ok(()) => h.join().expect("worker thread panicked"),
        // The closure panicked (an assertion inside it failed, or the
        // parser panicked): the sender was dropped without sending.
        Err(RecvTimeoutError::Disconnected) => {
            std::panic::resume_unwind(h.join().expect_err("disconnected without a panic"))
        }
        // Deliberately does NOT join `h`: the whole point is that the
        // worker is still running and we cannot get it back. Rust has no
        // thread cancellation, so the runaway worker is simply left to be
        // reaped when the test process exits (moments later, on this
        // panic). It burns one core until then — acceptable for a failing
        // test, and the only alternative would be to hang forever waiting
        // for exactly the thing we just proved is not going to finish.
        Err(RecvTimeoutError::Timeout) => panic!(
            "{label}: still running after {BUDGET:?} — the parser hung \
             (category-call memoization regressed back to exponential \
             re-parsing, or a loop stopped making progress)"
        ),
    }
}

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

/// The exact reproduction shape from the bug report, at depths past where
/// the old exponential behavior was already unusable (10, 15) and up to
/// just under `MAX_CATEGORY_DEPTH` — all bounded, all a clean, error-free
/// parse with exactly `depth` nested `Term.paren` nodes. One paren level
/// costs one `category()` level, plus a constant 2 for the enclosing
/// `command`/`term` calls, so `MAX_CATEGORY_DEPTH - 4` is comfortably
/// inside the cap. Depths past the cap are
/// `parens_past_the_depth_cap_degrade_cleanly_not_hang`, below.
#[test]
fn deeply_nested_parens_terminate_fast_and_parse_clean() {
    let deepest = MAX_CATEGORY_DEPTH as usize - 4;
    for depth in [5usize, 10, 15, 20, 30, 100, deepest] {
        in_worker(&format!("parens depth {depth}"), move || {
            let snap = builtin::snapshot();
            let src = format!("def a := {}1{}\n", "(".repeat(depth), ")".repeat(depth));
            let r = parse_module(&src, &snap);
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
        });
    }
}

/// Past `MAX_CATEGORY_DEPTH` (a stack-safety cap, unrelated to the cache
/// — see its doc comment for the measured stack budget it is derived
/// from), the parser must still terminate fast and degrade cleanly:
/// exactly one diagnostic, no panic, no stack overflow, and — crucially —
/// losslessness holds even through a hard failure (Global Constraint:
/// "Losslessness is total... including files with parse errors").
#[test]
fn parens_past_the_depth_cap_degrade_cleanly_not_hang() {
    let cap = MAX_CATEGORY_DEPTH as usize;
    for depth in [cap, cap + 1, 2 * cap, 1_000, 10_000] {
        in_worker(&format!("parens past cap, depth {depth}"), move || {
            let snap = builtin::snapshot();
            let src = format!("def a := {}1{}\n", "(".repeat(depth), ")".repeat(depth));
            let r = parse_module(&src, &snap);
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
        });
    }
}

/// Other bracket-shaped term leaders (`anonymousCtor`'s `⟨⟩`) — a
/// single-candidate leader, so not itself an exponential-fanout risk, but
/// still an input-driven `Category` recursion depth and worth pinning as a
/// never-hang/clean-parse regression alongside parens.
#[test]
fn deeply_nested_anonymous_ctor_brackets_terminate_fast_and_parse_clean() {
    for depth in [5usize, 20, 100, MAX_CATEGORY_DEPTH as usize - 4] {
        in_worker(&format!("anonymousCtor depth {depth}"), move || {
            let snap = builtin::snapshot();
            let src = format!("def a := {}1{}\n", "⟨".repeat(depth), "⟩".repeat(depth));
            let r = parse_module(&src, &snap);
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
        });
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
/// paren family. Only the OUTERMOST `do` is in TERM position (`Term.do`);
/// every nested one is a `doElem` (`doNested := Lean.Parser.Term.doNested`,
/// `register_term_wrappers`'s sibling `doElem` registration) — both kinds
/// together must total `depth`.
#[test]
fn deeply_nested_do_blocks_terminate_fast_and_parse_clean() {
    for depth in [5usize, 15, 30, 100, MAX_CATEGORY_DEPTH as usize - 6] {
        in_worker(&format!("do-block depth {depth}"), move || {
            let snap = builtin::snapshot();
            let src = format!("def a := {}1{}\n", "do{".repeat(depth), "}".repeat(depth));
            let r = parse_module(&src, &snap);
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
        });
    }
}

/// The stack-safety contract itself (Task 11b review, Critical 2): the
/// HEAVIEST shape in the builtin grammar, driven all the way past
/// `MAX_CATEGORY_DEPTH`, must not overflow the stack `parse_module` gives
/// itself. `do { if p then do { … } }` costs ~3 `category()` calls (and
/// ~23 KiB of unoptimized native stack) per visible level, ~3x a nested
/// paren — it is the shape the cap is calibrated against, so this is the
/// test that would crash (SIGSEGV, not a failed assert) if the cap were
/// raised, the frame cost grew, or `MIN_STACK_BYTES` shrank.
///
/// Note what is deliberately absent: this test arranges NO stack of its
/// own. It runs on a stock `libtest`/`in_worker` thread (2 MiB — an eighth
/// of the contract) and still must not overflow, because `parse_module`
/// spawns its own `MIN_STACK_BYTES` worker (wave 2, Critical 2). That is
/// precisely the property under test: the guarantee is internal, not a
/// precondition anyone can forget. Before wave 2 this test only passed
/// because the harness hand-fed it the right stack.
#[test]
fn the_heaviest_shape_at_the_depth_cap_fits_in_the_documented_minimum_stack() {
    // 3 category levels per visible level ⇒ this drives `cat_depth` well
    // past the cap and back down, on the contract's stack.
    for depth in [MAX_CATEGORY_DEPTH as usize, 1_000] {
        in_worker(&format!("do/if depth {depth}"), move || {
            let snap = builtin::snapshot();
            let src = format!(
                "def a := {}pure 1{}\n",
                "do{ if p then do{ ".repeat(depth),
                " } }".repeat(depth)
            );
            let r = parse_module(&src, &snap);
            assert_eq!(r.tree.text(), src, "depth {depth}: losslessness");
            assert_eq!(
                r.errors.len(),
                1,
                "depth {depth}: expected exactly one recursion-depth diagnostic, got {:?}",
                r.errors
            );
            assert_eq!(r.errors[0].code, "E0301", "depth {depth}");
        });
    }
}

/// M3b2b Task 9: quotations nest via the same `Category` recursion depth
/// as parens/anonymousCtor/do above (`` `( `( `( 1 ) ) ) ``), so this is
/// the quotation-family sibling of
/// `deeply_nested_parens_terminate_fast_and_parse_clean` — pinning that
/// Task 2's `quot_depth` plumbing costs no more than an ordinary
/// `Category` level and does not reintroduce exponential blowup or a
/// hang as quotations nest.
#[test]
fn nested_quotations_terminate() {
    for depth in [5usize, 20, 100, 1000] {
        let src = format!("def a := {}1{}\n", "`(".repeat(depth), ")".repeat(depth));
        in_worker(&format!("nested quots depth {depth}"), move || {
            let snap = leanr_syntax::builtin::snapshot();
            let r = leanr_syntax::parse_module(&src, &snap);
            assert_eq!(r.tree.text(), src, "lossless at depth {depth}");
        });
    }
}

/// M3b2b Task 9: `$` (antiquot) is the OTHER quotation-family recursion
/// path — Task 3/4's backtracking "try antiquot, else fall through"
/// alternative and Task 4's splice/scope prefix unwinding. A storm of
/// `$` tokens (nested antiquot attempts, `$` immediately followed by
/// whitespace so the antiquot body never resolves, `$[` splice-bracket
/// storms, and depth 0 as a fast-failure control) exercises exactly the
/// atomic-prefix restore paths this task's brief calls out as the
/// suspect for any hang: every early return in `antiquot`/
/// `antiquot_splice` must restore or finish symmetrically, or one of
/// these degenerates into unbounded backtracking instead of a clean
/// (possibly erroring) parse.
#[test]
fn dollar_storms_terminate() {
    for src in [
        format!("def a := `({}x)\n", "$".repeat(500)),
        format!("def a := `({} x)\n", "$ ".repeat(500)),
        format!("def a := `(⟨{}⟩)\n", "$[".repeat(200)),
        "def a := $x\n".to_string(), // depth 0: plain failure, fast
    ] {
        in_worker("dollar storm", move || {
            let snap = leanr_syntax::builtin::snapshot();
            let r = leanr_syntax::parse_module(&src, &snap);
            assert_eq!(r.tree.text(), src, "lossless");
        });
    }
}
