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
use support::{encode_expr, fixture_in, replay_fixture_in, EncSt};

use leanr_elab::TermElabM;
use leanr_kernel::bank::Store;
use leanr_kernel::EnvView;
use leanr_meta::{Config, EnvExtensions, MetaCtx};
use leanr_syntax::{builtin, parse_term};

#[test]
fn oracle_elab_gate() {
    let support::Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
        classes,
    } = replay_fixture_in("elab", "Elab0.olean");
    let snap = builtin::snapshot();

    let queries = std::fs::read_to_string(fixture_in("elab", "elab-queries.jsonl"))
        .expect("committed elab corpus");
    let mut failures = Vec::new();
    let mut replayed = 0usize;
    for line in queries.lines().filter(|l| !l.trim().is_empty()) {
        replayed += 1;
        let q: serde_json::Value = serde_json::from_str(line).expect("committed JSONL is valid");
        let id = q["id"].as_str().expect("id field");
        let src = q["src"].as_str().expect("src field");

        // Fresh EnvView/Store/MetaCtx per query — same independence
        // contract as oracle_fast/oracle_synth (queries never share
        // state with each other).
        let view: EnvView = env.view();

        // Parse the SAME source text through leanr's OWN parser.
        // `parse_term` wraps its single term child in a synthetic
        // KIND_NULL root (that function's own doc comment); the kind
        // interner used to elaborate MUST be the tree's own
        // (`parsed.tree.kinds`), never a separately-held snapshot
        // handle — `SyntaxNode::kind()` is an index into whichever
        // `KindInterner` built the specific tree it came from, and
        // `GrammarSnapshot::kinds()` and a tree's own `kinds` can
        // diverge once overlays are in play (not today, for
        // `builtin::snapshot()`'s overlay-free snapshot, but this is
        // the general, always-correct rule — see `Ps::merged_kinds`).
        let parsed = parse_term(src, &snap);
        assert!(
            parsed.errors.is_empty(),
            "{id}: leanr parse errors for {src:?}: {:?}",
            parsed.errors
        );
        // `first_child_or_token`, not `first_child` (Task 5
        // reconciliation): a term position is not always a rowan NODE —
        // a bare identifier is an unwrapped leaf TOKEN
        // (`crate::dispatch`'s own module doc has the full citation:
        // `Prim::Ident`'s `self.bump(t, KIND_IDENT)` never node-wraps,
        // unlike `str`/`num`/`char`'s `self.lit`). `SynElem`
        // (`leanr_elab::dispatch::SynElem`, a `rowan::NodeOrToken`)
        // covers both.
        let root = parsed.tree.root();
        let term_elem: leanr_elab::dispatch::SynElem = root
            .first_child_or_token()
            .unwrap_or_else(|| panic!("{id}: parse_term produced no term child for {src:?}"));

        let mut scratch = Store::scratch();
        let mctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            EnvExtensions {
                reducibility: &reducibility,
                matchers: &matchers,
                instances: &instances,
                default_instances: &default_instances,
                projection_fns: &projection_fns,
                classes: &classes,
            },
        );
        let mut elab = TermElabM::new(mctx, view);
        // The pinned entry point, matching `dump_elab.lean`'s own module
        // doc (M4b-3 P2a task 9): `TermElabM::elab_term_and_synthesize`
        // (`elab.rs`) — `elab_term`, then
        // `synthesize_synthetic_mvars_no_postponing`, then
        // `instantiate_mvars` internally — mirroring the oracle's own
        // `elabTermAndSynthesize` (`SyntheticMVars.lean:696-698`).
        // `expected := None`: the committed corpus carries no
        // expected-type field, so the inner `elab_term`'s `is_def_eq`
        // branch never runs.
        let got = elab.elab_term_and_synthesize(&term_elem, &parsed.tree.kinds, None);

        match got {
            Ok(g) => {
                // `base = Some(view.store)` (Task 5 reconciliation,
                // mirroring `oracle_fast.rs`'s own `let base =
                // Some(view.store);`): `g` can now embed a
                // PERSISTENT-region `NameId` (`ident`'s resolved global
                // constant name), which `elab.mctx.store()` — the
                // elaborator's own SCRATCH store — cannot resolve on its
                // own; `encode_expr`'s internal `to_name` needs the
                // persistent store as a fallback base, exactly like
                // every kernel-side `Store` method with a `base`
                // parameter.
                let mut st = EncSt::default();
                let got_json = encode_expr(elab.mctx.store(), Some(view.store), g, &mut st);
                if got_json != q["exp"] {
                    failures.push(format!("{id}: leanr={got_json} oracle={}", q["exp"]));
                }
            }
            Err(e) => failures.push(format!("{id}: leanr errored: {e:?}")),
        }
    }
    assert!(
        failures.is_empty(),
        "{} divergences:\n{}",
        failures.len(),
        failures.join("\n")
    );

    // FLOOR on the corpus size. Everything above compares records that
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
    const CORPUS_FLOOR: usize = 107;
    assert!(
        replayed >= CORPUS_FLOOR,
        "corpus shrank: replayed {replayed} records, floor is {CORPUS_FLOOR}. \
         Either a query stopped being emitted (check `dump_elab.lean`'s \
         stderr for a dropped query) or records were removed on purpose \
         — in which case lower this constant deliberately."
    );
}
