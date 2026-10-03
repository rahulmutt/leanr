//! M4b-1 tier-1 elaboration differential gate (design spec § The
//! differential oracle harness): every committed `{id, src, exp}`
//! record's Lean SOURCE TEXT parses — through leanr's OWN parser, not
//! a deserialized copy of the oracle's `Syntax` (design spec's "Input
//! model — source-text, end-to-end": a parse divergence is caught by
//! `leanr_syntax`'s own `oracle_golden.rs` gate, upstream of this one,
//! so a failure here attributes cleanly to the elaborator) — and
//! elaborates to the oracle's canonical `Expr`, byte-for-byte after
//! canonicalization.
//!
//! Hermetic: the committed `Elab0.olean` + `elab-queries.jsonl` are the
//! entire input; CI never installs Lean (docs/ORACLE.md). A REGRESSION
//! gate, exactly like `oracle_fast.rs`/`oracle_synth.rs` (M4a): "every
//! leaf term that used to elaborate to the oracle's result still
//! does" — Mathlib-scale elaboration discovery is a later M4 slice
//! (design spec § Out of scope).

mod support;

use leanr_syntax::builtin;

#[test]
fn oracle_elab_gate() {
    let replayed =
        support::run_elab_corpus("Elab0.olean", "elab-queries.jsonl", &builtin::snapshot());
    // FLOOR on the corpus size. Everything `support::run_elab_corpus` does compares records that
    // are present; nothing above notices records that VANISHED, and a
    // shrinking corpus is silent by construction: `dump_elab.lean`
    // catches a throwing query, prints to stderr and DROPS it, so a
    // fixture declaration that stops elaborating oracle-side takes its
    // records out of the JSONL on the next `mise run fixtures:regen-elab`
    // and this gate still passes on the survivors. M4b-3 P3 is the first
    // slice whose records depend on `Elab0.lean` declarations
    // (`instOfNatNat`'s `@[default_instance]`, `Tag`, `OfScientific`)
    // staying elaborable, so the loss mode is now real.
    //
    // RAISE THIS when records are added deliberately — the number is
    // exactly `wc -l tests/fixtures/elab/elab-queries.jsonl` after the
    // regen. `>=`, not `==`, so adding a record is a one-line bump here
    // rather than a gate that fails before the author has looked.
    //
    // 113 -> 117 (elimMVarDeps task 11): `coe/postponedThenResumedUnderBinder`,
    // `elimMVarDeps/pendingInstanceUnderBinder`, `num/zeroUnderBinder`,
    // `dflt/polyInstImplicitUnderBinder`.
    //
    // 117 -> 142 (M4b-3 close-out task 3): P5's 17 records (never folded
    // into the floor) plus the eight `closeout/impl-detail-*` records.
    //
    // 142 -> 147 (M4b-3 close-out task 4): the five closeout/binder-check-*
    // records.
    //
    // 147 -> 154 (M4b-3 close-out task 5): the seven closeout/let-* and
    // closeout/have-* records.
    // 154 -> 160 (M4b-3 close-out task 6): the six closeout/explicit-*
    // records.
    // 160 -> 208 (M4b-4a P2 final review): every record added since
    // close-out task 6 and never folded into the floor (the nondep
    // slice, M4b-4a P1's `lval/*`, P2's `p2/*`), including
    // `p2/lval-two-postponements`.
    // 208 -> 230 (M4b-4a P3 task 3): the 22 p3/* records.
    // 230 -> 234 (M4b-4a P3 task 4): p3/whnf-continuation, p3/coe-fun, p3/whnf-then-named, p3/explicit-unusable-name.
    // 234 -> 249 (M4b-4a P4 task 1): the 15 p4/local-* and p4/global-* records.
    // 249 -> 259 (M4b-4a P4 task 2): the 10 p4/pipe-* records.
    // 259 -> 273 (M4b-4a P4 task 3): the 14 p4/dot-* records.
    // 273 -> 276 (M4b-4a P4 final fix): p4/pipe-nested-args, p4/pipe-nested-named, p4/pipe-nested-deep.
    // 276 -> 329 (M4b-4c P2): M4b-4b's 17 anon/* records, never folded in, plus the 36 elim/* and elimErr/* records.
    // 329 -> 331 (instantiateBetaRevRange nested redexes): elim/namedMotiveBareIh, elim/explicitAtBareIh.
    // 331 -> 333 (setElabConfig foApprox): elim/ndrec, elim/ndrecExpected.
    //
    // 345 -> 346 (synth-real-depth task 3): `tc/useAnyHole`.
    // 346 -> 350 (level instantiation simplifies): the 4 lvl/* records.
    // 350 -> 358 (numScopeArgs task 2): the 6 nsa/* gate records,
    // p2/app-fn-after-lval and p2/lval-two-binders-holes.
    // 358 -> 359 (numScopeArgs task 3): nsa/let-prefix-search.
    // 359 -> 360 (expandDelayedAssigned?): eda/coe-resume-after-pending.
    const CORPUS_FLOOR: usize = 360;
    assert!(
        replayed >= CORPUS_FLOOR,
        "corpus shrank: replayed {replayed} records, floor is {CORPUS_FLOOR}. \
         Either a query stopped being emitted (check `dump_elab.lean`'s \
         stderr for a dropped query) or records were removed on purpose \
         — in which case lower this constant deliberately."
    );
}
