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
    for (src, expect_errors) in [
        (format!("def a := `({}x)\n", "$".repeat(500)), false),
        (format!("def a := `({} x)\n", "$ ".repeat(500)), false),
        (format!("def a := `(⟨{}⟩)\n", "$[".repeat(200)), false),
        // depth 0: plain failure, fast — a bare `$` outside any
        // quotation must be REJECTED (non-empty errors), not silently
        // absorbed into a clean parse.
        ("def a := $x\n".to_string(), true),
    ] {
        in_worker("dollar storm", move || {
            let snap = leanr_syntax::builtin::snapshot();
            let r = leanr_syntax::parse_module(&src, &snap);
            assert_eq!(r.tree.text(), src, "lossless");
            if expect_errors {
                assert!(
                    !r.errors.is_empty(),
                    "depth-0 $-storm must produce parse errors"
                );
            }
        });
    }
}

/// M3b3 Task 6: `dollar_storms_terminate`'s idiom (timing bound via
/// `in_worker`, losslessness) applied to the Task 1-5 scope/activation
/// machinery — `ScopeStack`'s `namespace`/`section`/`end`/`open`
/// tracking must stay total (never panic, never hang) under deep
/// nesting, stray/mismatched `end`s, and `open` storms, and the
/// quotation-isolation invariant (a `namespace` INSIDE a term
/// quotation must never touch the scope stack) must hold under a
/// storm shape too.
///
/// Every case here is a CLEAN (`errors.is_empty()`) parse: `namespace`/
/// `section`/`end`/`open` are unconditional command-loop leading
/// productions (`command_open.rs`'s `namespace_cmd`/`section_cmd`/
/// `end_cmd`/`open` family — `end`'s trailing name is `opt(..)`, so
/// even a completely bare `end` always matches), and `ScopeStack`'s own
/// updates are total by construction (`scope.rs`'s module doc: "Updates
/// are TOTAL: arbitrary stray/mismatched `end`s must never panic —
/// worst case the stack diverges from the oracle's... never a crash");
/// the M3b3 design spec's own Error-handling section says the same
/// ("Worst case the stack is wrong and derivations produce
/// oracle-divergent names... never a crash"). So — unlike
/// `dollar_storms_terminate`'s depth-0 case, which hits a genuine
/// GRAMMAR-level rejection (`$` has no top-level production) — there
/// is no scope-storm shape here that the PARSER itself rejects: a
/// stray/mismatched `end`/`open` is a semantic (scope-tracking)
/// no-op, never a syntax error, so this suite pins clean parses
/// throughout rather than fabricating a non-empty-errors expectation
/// that the code doesn't (and per the design spec, structurally can't)
/// produce. See the "stray end storm" case below for the one place
/// this diverges from the task-6 brief's literal sketch, and the
/// task-6 report for the concern writeup.
#[test]
fn scope_storms_terminate() {
    for src in [
        // Deep namespace nesting (400 * 3 = 1200 pushed components)
        // followed by a BARE `end` storm: bare `end` only pops an
        // ANONYMOUS `section` (`ScopeStack::end_scope`'s `None` arm),
        // never a `namespace` component, so every one of the 1200
        // trailing bare `end`s here is a no-op against the namespace
        // stack — this pins that a long run of no-op `end_scope(None)`
        // calls stays linear, not just that it terminates.
        format!("{}{}", "namespace A.B.C\n".repeat(400), "end\n".repeat(1200)),
        // end-storm on empty stack ("the stray-end storm" — see the
        // dedicated pass below for its error-presence pin).
        "end\n".repeat(2000),
        // open-storm: 2000 same-name opens, each a cheap `Vec` push
        // (`ScopeStack::open_namespace`) with no rollback (top level,
        // no enclosing section) — never a namespace-prefix collision
        // since there both is and isn't a common name repeated.
        "open A\n".repeat(2000),
        // section/namespace interleave with mismatched `end` names:
        // per-iteration, `end X` is a no-op (the innermost entry is
        // `section s`, not a `namespace` component matching `X`) while
        // `end s` pops the section — so `namespace X` never actually
        // closes and 300 unmatched `Namespace` entries accumulate on
        // the stack. Exercises the mismatched-suffix-match path
        // (`end_scope`'s `Some(d)` arm) at volume, not just once
        // (`mismatched_end_is_total_and_best_effort`'s unit-level
        // single case).
        "namespace X\nsection s\nend X\nend s\n".repeat(300),
    ] {
        in_worker("scope storm", move || {
            let snap = leanr_syntax::builtin::snapshot();
            let r = leanr_syntax::parse_module(&src, &snap);
            assert_eq!(r.tree.text(), src, "lossless");
            assert!(
                r.errors.is_empty(),
                "scope-tracking is semantic, not syntactic — no scope-storm \
                 shape should ever produce a parser-level error: {:?}",
                r.errors
            );
        });
    }

    // "The stray-end storm" (task-6 brief, Step 1's closing
    // parenthetical): "add an error-presence assertion on the
    // stray-end storm" — modeled on `dollar_storms_terminate`'s own
    // depth-0 case, which asserts NON-empty errors for a bare `$`
    // outside any quotation. Empirically (and per the design spec's
    // own "never a crash" language quoted above) a stray/mismatched
    // `end` on an empty `ScopeStack` is a semantic no-op, NOT a parse
    // error: `end`'s trailing name is optional
    // (`command_open.rs::end_cmd`), so a bare `end` — or `end` with
    // any name — always matches its own leading production regardless
    // of what (if anything) is open. There is no grammar-level
    // rejection analogous to `$`'s "no top-level production" here to
    // assert non-empty errors against; asserting non-empty errors on
    // this input would be false (verified: `r.errors` is empty for
    // `"end\n".repeat(2000)`). This test therefore pins the actual
    // (empty) behavior instead of the brief's literal expectation —
    // flagged as a concern in the task-6 report rather than silently
    // dropped or fabricated.
    in_worker("stray end storm — error-presence pin", move || {
        let snap = leanr_syntax::builtin::snapshot();
        let src = "end\n".repeat(2000);
        let r = leanr_syntax::parse_module(&src, &snap);
        assert_eq!(r.tree.text(), src, "lossless");
        assert!(
            r.errors.is_empty(),
            "a stray-end storm on an empty ScopeStack is a semantic \
             no-op (scope.rs's own total/best-effort contract), never a \
             parser-level error: got {:?}",
            r.errors
        );
    });

    // Quotation isolation: `namespace`/`end` INSIDE a term quotation
    // must never touch `ScopeStack` — the command loop only inspects
    // the OUTER command's kind (`SCOPE_COMMAND_KINDS`, `parse.rs`), and
    // this whole command's outer kind is `Lean.Parser.Command.
    // declaration` (a `def`), never `Lean.Parser.Command.namespace` —
    // so the quoted `namespace Ghost ... end Ghost` can structurally
    // never reach `scope_command_update`. The subsequent `syntax
    // "wobqt" : term` + `#check wobqt` pins this behaviorally: its
    // derived kind must be the plain unqualified `termWobqt`
    // (`qualify_kind_name("", "termWobqt")` is the identity on an
    // empty namespace — `grammar/notation.rs`), never
    // `Ghost.termWobqt`.
    in_worker("quotation isolation", move || {
        let snap = leanr_syntax::builtin::snapshot();
        let src = "def q := `(namespace Ghost end Ghost)\nsyntax \"wobqt\" : term\n\
                   #check wobqt\n";
        let r = leanr_syntax::parse_module(src, &snap);
        assert_eq!(r.tree.text(), src, "lossless");
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let kinds = r.tree.kinds.clone();
        assert!(
            r.tree
                .root()
                .descendants()
                .any(|n| kinds.name(n.kind()) == "termWobqt"),
            "expected the unqualified derived kind `termWobqt`"
        );
        assert!(
            !r.tree
                .root()
                .descendants()
                .any(|n| kinds.name(n.kind()).starts_with("Ghost.")),
            "a `namespace` inside a quotation must not leak into the \
             derived kind of a later top-level `syntax` command"
        );
    });
}
