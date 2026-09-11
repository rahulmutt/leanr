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
        coe_decls,
    } = replay_fixture_in("elab", "Elab0.olean");
    let snap = builtin::snapshot();

    let queries = std::fs::read_to_string(fixture_in("elab", "elab-queries.jsonl"))
        .expect("committed elab corpus");
    let mut failures = Vec::new();
    // Fix 2 of the M4b-3 P4 whole-branch fix wave: the WHOLE-CLASS
    // detector for an unabstracted `fvar` leaking into a closed-term
    // answer. See the assertion below.
    let mut leaked_fvars = Vec::new();
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
                coe_decls: &coe_decls,
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
                // EVERY term this corpus elaborates is CLOSED — the
                // queries are standalone terms with no ambient local
                // context (`replay_fixture_in` installs an environment,
                // never an `lctx`), so after `elab_term_and_synthesize`'s
                // internal `instantiate_mvars` the finished `Expr` must
                // contain no `fvar` NODE AT ALL. `EncSt` is fresh per
                // record and `encode_expr` interns every `Node::FVar` it
                // walks into `st.fvars`, so a non-empty map is an exact
                // "this term leaked a free variable" answer, not a
                // heuristic.
                //
                // WHY THIS GUARDS A REAL CLASS, not a hypothetical.
                // Every corpus query is a CLOSED term (no ambient
                // `lctx` — see above), so an `fvar` in a finished answer
                // is a bug, full stop: it means some subterm's free
                // variable never got abstracted before its binder
                // closed. `MetaCtx::mk_binding`
                // (`leanr_meta/src/metactx.rs`) runs the oracle's
                // `elimMVarDeps` (`MetavarContext.lean`,
                // `leanr_meta/src/mk_binding.rs`'s port) over the body
                // and over each binder type before abstracting, at the
                // oracle's own two insertion points — an unassigned
                // metavariable whose own local context holds the fvars
                // being abstracted is rewritten to a fresh metavariable
                // APPLIED to them, so it abstracts like any other
                // argument instead of leaking. Before that port landed
                // (the `elimMVarDeps` slice), a postponed synthetic mvar
                // registered under a binder and resumed by the fixpoint
                // AFTER that binder closed had its value spliced in
                // unabstracted: leanr emitted an `fvar` where the oracle
                // emits a `bvar`, a WRONG `ExprId` with NO error — silent
                // divergence, which this repo's cardinal rule forbids.
                // `seam_audit.rs`'s
                // `postponed_coe_under_a_binder_abstracts_via_elim_mvar_deps`
                // pins that one shape by hand; this assertion turns the
                // whole class loud across the corpus: any future
                // regression fails HERE, named, instead of quietly
                // shifting bytes.
                //
                // PLACEMENT: deliberately here, in the record replay,
                // and NOT in `tests/support`'s shared `elab_and_synthesize`
                // helper — a corpus regression should fail loudly at the
                // corpus, not inside a shared helper other tests also
                // call for unrelated shapes.
                if !st.fvars.is_empty() {
                    leaked_fvars.push(format!("{id}: {got_json}"));
                }
                if got_json != q["exp"] {
                    failures.push(format!("{id}: leanr={got_json} oracle={}", q["exp"]));
                }
            }
            Err(e) => failures.push(format!("{id}: leanr errored: {e:?}")),
        }
    }
    // Asserted BEFORE the byte-comparison below: a leaked `fvar` also
    // shows up there as an ordinary divergence, and this message is the
    // one that says which class it belongs to.
    assert!(
        leaked_fvars.is_empty(),
        "{} record(s) finished with an UNABSTRACTED `fvar` in the term. Every \
         corpus query is a closed term, so an `fvar` in an answer is a bug: \
         `MetaCtx::mk_binding` (`leanr_meta/src/metactx.rs`) runs \
         `elim_mvar_deps` (`leanr_meta/src/mk_binding.rs`, the oracle's \
         `MkBinding.elimMVarDeps`) over the body and over each binder type \
         before abstracting, and `seam_audit.rs`'s \
         `postponed_coe_under_a_binder_abstracts_via_elim_mvar_deps` pins the \
         shape that used to leak. Do NOT relax this assertion and do NOT edit \
         the corpus — track down why a metavariable's value is reaching this \
         point unabstracted; a new record that trips this is a real \
         regression, not a known gap. Offenders:\n{}",
        leaked_fvars.len(),
        leaked_fvars.join("\n")
    );
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
    const CORPUS_FLOOR: usize = 154;
    assert!(
        replayed >= CORPUS_FLOOR,
        "corpus shrank: replayed {replayed} records, floor is {CORPUS_FLOOR}. \
         Either a query stopped being emitted (check `dump_elab.lean`'s \
         stderr for a dropped query) or records were removed on purpose \
         — in which case lower this constant deliberately."
    );
}
