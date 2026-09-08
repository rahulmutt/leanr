# M4b-3 P2b-ii — the elaborator outParam branch: implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Port the oracle's `resultTypeOutParam?` producer
(`isNextOutParamOfLocalInstanceAndResult`) and `finalize`'s outParam
branch into `leanr_elab`, retire the ladder pre-test's "Residue 1" with a
positional exemption, and give `Elab0.lean` its first `outParam` class,
its `Lean.Internal.coeM` gate, and the fourth-priority default instance
that closes P3's carried follow-ups 1–2 — every step differentially
verified against the pinned oracle.

**Architecture:** Everything lands in `leanr_elab` and the `Elab0`
fixture; `leanr_meta` and `leanr_olean` are untouched (P2b-i already
shipped the synthesis-side mechanism and the `pub` class accessors).
Four seams are replaced by real code: `app/args.rs`'s `add_implicit_arg`
gains the producer, `app/finalize.rs` gains the branch,
`synthetic/ladder.rs` gains the `synthesizeSyntheticMVarsUsingDefault`
composite and the positional pre-test exemption. The fixture change that
flips `result_is_out_param_support` on (`Lean.Internal.coeM`) is the LAST
code-bearing task, after every consumer of that flag is real, so no
commit leaves the corpus red (design spec § Amendment 3 item 9 and
§ Amendment 4 item 7).

**Tech Stack:** Rust (workspace crate `leanr_elab`), Lean 4 fixtures
(`prelude`-mode, import-free), `mise` task runner, `serde_json` for the
differential corpus.

## Global Constraints

Copied from the spec
(`docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md`,
§ Global constraints, § Amendment 3 and § Amendment 4) and `AGENTS.md`.
Every task's requirements implicitly include this section.

- **Pinned oracle: `leanprover/lean4:v4.33.0-rc1`** (`lean-toolchain`).
  Every citation in this plan is against that toolchain's sources, found
  locally at
  `/home/dev/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`.
  **Never bump the pin.**
- **Kernel is byte-untouched.** `leanr_kernel` depends on no workspace
  crate and no existing kernel function is modified.
- **`leanr_meta/src` and `leanr_olean/src` are NOT modified by this
  plan** (§ Accessor ledger: "P2b-ii — none expected"). Everything the
  elaborator needs is already `pub`: `MetaCtx::get_out_param_positions`
  / `has_out_params` (`metactx.rs:848,863`), `infer_type`, `whnf`,
  `push_local_decl`, `lctx_checkpoint` / `lctx_restore`,
  `instantiate_beta_rev_range`, `mctx().is_assigned`.
- **Named seams, never silent divergence.** Where the oracle does
  something this plan does not implement, detect the shape and return
  `ElabError::UnsupportedSyntax(..)` naming the seam and its owner. Where
  this plan RETIRES a seam, delete its message entirely and gate that it
  never comes back (`tests/seam_audit.rs`'s retired-label pattern).
- **Correctness is byte-for-byte agreement with the pinned oracle**, via
  the committed corpus `tests/fixtures/elab/elab-queries.jsonl`. Never
  re-baseline a record to make a test pass: a record that moves means
  the code is wrong. **All 101 committed records must stay
  byte-identical through every task**, including the one that declares
  `Lean.Internal.coeM` (§ Amendment 4 item 8).
- **Every discriminator is a claim until measured** (§ Amendment 4 item
  11). Each task that adds a record or a test names the mutation it is
  supposed to kill and includes the step that applies the mutation and
  watches the test go red. A record that survives its mutation is
  replaced, not shipped.
- **`mise run ci` gates `cargo fmt --check` and clippy**, not only tests.
  Run it before every commit; the test tasks alone do not cover it.
- **Fixture regeneration:** `mise run fixtures:regen` rebuilds every
  `.olean` (including `Elab0.olean`) and then, via `depends_post`, runs
  `fixtures:regen-elab` (the `dump_elab.lean` dumper). When only
  `dump_elab.lean`'s query lists changed and `Elab0.lean` did not,
  `mise run fixtures:regen-elab` alone suffices. Both need the pinned
  Lean toolchain on `PATH` (`mise run elan:bootstrap`).
- **Determinism:** no wall-clock, no `maxHeartbeats`; leanr counts
  deterministic `MetaCtx::step`s.
- **Commit messages** end with the session trailer this session was
  given: `Claude-Session: https://claude.ai/code/session_017XRcWKrpV5Dh9bXaQjnafL`.

## File Structure

**Created:**
- none — every change lands in an existing file, following that file's
  established pattern.

**Modified:**
- `tests/fixtures/elab/Elab0.lean` — the P2b-ii declaration block
  (Task 1), then `Lean.Internal.coeM` (Task 5).
- `tests/fixtures/elab/dump_elab.lean` — `defaultPolyQueries` (Task 1),
  `outParamQueries` (Tasks 2 and 5).
- `tests/fixtures/elab/Elab0.olean`,
  `tests/fixtures/elab/elab-queries.jsonl` — regenerated artifacts.
- `crates/leanr_elab/tests/support/mod.rs` — two `Get`-goal builders
  (Task 2), one args-driving harness helper (Task 4).
- `crates/leanr_elab/tests/synthetic_smoke.rs` — priority-count
  re-derivation (Task 1), exemption tests (Task 2), composite test
  (Task 3), end-to-end walk-log tests (Task 5).
- `crates/leanr_elab/tests/app_smoke.rs` — producer and branch tests
  (Task 4).
- `crates/leanr_elab/tests/oracle_elab.rs` — `CORPUS_FLOOR` (Tasks 1, 2,
  5).
- `crates/leanr_elab/tests/seam_audit.rs` — the retired-label gate
  (Task 6).
- `crates/leanr_elab/src/synthetic/ladder.rs` — positional exemption
  (Task 2), `synthesize_synthetic_mvars_using_default` (Task 3), Residue
  1 doc retirement (Task 6).
- `crates/leanr_elab/src/app/state.rs` — `app_fn` / `app_args` /
  `is_out_param` helpers (Task 4), field-doc updates (Task 6).
- `crates/leanr_elab/src/app/args.rs` — the producer and its four
  clauses; the seam is deleted (Task 4).
- `crates/leanr_elab/src/app/finalize.rs` — the branch; the seam is
  deleted; `kinds` parameter (Task 4).
- `crates/leanr_elab/src/app/mod.rs`, `crates/leanr_elab/src/lib.rs`,
  `crates/leanr_elab/src/dispatch.rs` — seam-table reconciliation, doc
  comments only (Task 6).

## Orientation for the implementer

Read these before Task 1. They are short and they are what the code below
mirrors.

- **The oracle:** `App.lean:681-727` (`isNextOutParamOfLocalInstanceAndResult`
  and its four `where` clauses: `isResultType` `:693-697`,
  `hasLocalInstanceWithOutParams` `:700-706`, `isOutParamOfLocalInstance`
  `:708-716`, `isOutParamOf` `:718-727`), `:745-760` (`addImplicitArg`,
  the branch at `:747-755`), `:638-646` (`finalize`'s outParam branch),
  `:141-172` (the `Context.resultIsOutParamSupport` doc comment with the
  `GetElem` worked example), `SyntheticMVars.lean:658-660`
  (`synthesizeSyntheticMVarsUsingDefault`), `Class.lean:85-88`
  (`hasOutParams`), `Expr.lean:1709-1710` (`isOutParam`).
- **leanr's counterpart today:** `crates/leanr_elab/src/app/args.rs:483-514`
  (`add_implicit_arg` with the seam), `app/finalize.rs:56-75` (the seam),
  `synthetic/ladder.rs:48-197` (`try_synth_instance` and its Residue 1
  doc), `synthetic/ladder.rs:456-533` (`synthesize_synthetic_mvars` and
  `synthesize_using_default_loop`), `app/state.rs:236-347` (the
  type-annotation helpers — note which ones strip `semiOutParam`).
- **The spec:** § P2b-ii and § Amendment 4 of
  `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md`.
  Item 6 (why the exemption is positional and load-bearing in both
  directions), item 8 (why declaring `coeM` re-routes the whole corpus),
  item 9 (requirements R1–R4 for the default instance) and item 10 (why
  the else-arm is a smoke test) are the ones the tasks below cite most.
- **How the corpus is made:** `tests/fixtures/elab/dump_elab.lean` —
  each query list is a `List (String × String)` of `(id, source)` and
  the `main` loop concatenates the lists; a query whose oracle-side
  elaboration THROWS is printed to stderr and DROPPED, so every time you
  regen, read the dumper's stderr for `elaboration failed for <id>`.

**One mechanism to hold in mind throughout — why the headline record
needs `Dflt`.** The oracle's own doc (`App.lean:150-166`) says the
branch exists so that `getElem xs 0`'s result type is known *before*
later elaboration steps need it. In a one-term dump, the entry point's
own fixpoint runs the same default instances anyway, so `Get.get cell 0`
elaborates to the SAME term with or without the branch — and the same is
true of the ascribed form. What DOES differ is a term where something
else pending would default the outParam mvar to the WRONG carrier if the
branch did not fix it first: `dpair (Get.get cell 0)`, where
`dpair {a : Type} [Dflt a] (x : a) : a`. With the branch, the inner
application finalizes with `?elem := Unit`, so `a := Unit` and
`Dflt Unit` finds `instDfltUnit`. Without it, `a := ?elem` stays open,
the fixpoint's priority-1000 rung applies `instDfltNat` FIRST
(`?elem := Nat`), and `Get Cell Nat Nat` has no instance — an error on
both sides. That is why the oracle, WITHOUT `Lean.Internal.coeM` in the
fixture, drops that query, and why Task 5 (which declares `coeM`) is
where it lands.

---

### Task 1: fixture declarations and the fourth-priority default instance

The fixture gains every P2b-ii declaration EXCEPT `Lean.Internal.coeM`
(Task 5), plus the record that closes § Follow-ups items 1 and 2. With
`coeM` absent, `result_is_out_param_support` stays `false`, so no
existing record can move; the deliverable is the `.olean`, one new
record, and the smoke assertions re-derived for four priorities.

**Files:**
- Modify: `tests/fixtures/elab/Elab0.lean` (append at end of file)
- Modify: `tests/fixtures/elab/dump_elab.lean` (new list + `main` loop)
- Modify: `crates/leanr_elab/tests/synthetic_smoke.rs:576-618,674-704`
- Modify: `crates/leanr_elab/tests/oracle_elab.rs:154`
- Regenerate: `tests/fixtures/elab/Elab0.olean`,
  `tests/fixtures/elab/elab-queries.jsonl`

**Interfaces:**
- Produces: Lean constants `outParam`, `Get`, `Get.get`, `Cell`, `cell`,
  `instGetCellNat`, `getFst`, `dpair`, `Seed`, `instSeedPUnit`, `Fresh`,
  `instFreshSeed`, `useFresh` in `Elab0.olean`; corpus record
  `dflt/polyInstImplicit`; a fourth default-instance priority (75).
  Every later task names these.

- [ ] **Step 1: Append the declaration block to `tests/fixtures/elab/Elab0.lean`**

```lean
-- === M4b-3 P2b-ii corpus: the elaborator outParam branch ===
--
-- The FIRST `outParam` class in this fixture. Until this block,
-- `Context.resultIsOutParamSupport`'s consumer
-- (`isNextOutParamOfLocalInstanceAndResult`, App.lean:681-727) had
-- nothing to fire on. `Lean.Internal.coeM` — the env gate that turns the
-- flag on (App.lean:1355) — is declared SEPARATELY, further down, by the
-- task that lands the producer: with the gate on and no producer, every
-- non-`@` application in the corpus errors (design spec § Amendment 3
-- item 9, § Amendment 4 item 7).
--
-- `outParam` must be declared here, at the ROOT namespace, because this
-- fixture is `prelude`-mode and imports no `Init`. The oracle's `class`
-- command decides output-parameter positions with `Lean.Expr.isOutParam`
-- (`Expr.lean:1709-1710`), which is `isAppOfArity ``outParam 1` against
-- the ROOT name `outParam` — so this declaration is the real thing, not
-- a look-alike. Copied verbatim from `Init/Prelude.lean:702` of the pin,
-- exactly as `tests/fixtures/Instances.lean` already does.
@[reducible] def outParam (α : Sort u) : Sort u := α

-- `Get` — the `GetElem` shape from the oracle's own worked example
-- (App.lean:150-151, inside the `resultIsOutParamSupport` doc comment):
-- two ordinary parameters, one `outParam`, and a method taking both
-- ordinary parameters. The SAME shape M4b-3 P2b-i proved out at the
-- synthesis tier (`Instances.lean` / `Synth0.lean`, `outParamGet`).
class Get (cont : Type u) (idx : Type v) (elem : outParam (Type w)) where
  get : cont → idx → elem

-- `Cell` — an opaque container (same "minimal opaque stand-in suffices"
-- reasoning as `axiom String` above), with one inhabitant so an
-- application can be written. Its `Get` instance is indexed by `Nat`,
-- deliberately: the worked example's `getElem xs 0` needs the index type
-- to be what `instOfNatNat` (the priority-100 `OfNat` default above)
-- resolves the numeral to, so that the `Get Cell ?idx ?elem` goal is
-- STUCK until the default rung fires and then SOLVED by it.
axiom Cell : Type
axiom cell : Cell

instance instGetCellNat : Get Cell Nat Unit where
  get := fun _ _ => Unit.unit

-- `getFst` exists for the producer's two FALSE directions, which no
-- `Get.get` record can reach. Its `[Get cont Nat elem]` binder is a
-- local instance with an outParam, so `hasLocalInstanceWithOutParams`
-- answers true for BOTH implicits — and the producer must still answer
-- false for both:
--   * for `{cont}`: `isResultType` is TRUE (the result IS `cont`), but
--     `isOutParamOf` finds `cont` at position 0 of `Get`, which is not
--     an `outParam` position (App.lean:718-727);
--   * for `{elem}`: `elem` IS the outParam of the local instance, but
--     `isResultType` is FALSE (App.lean:693-697) — the result is `cont`.
-- Mutating either clause to a constant `true` marks the wrong mvar as
-- `resultTypeOutParam?`; `tests/app_smoke.rs` asserts both directions.
-- The corpus record `outParam/getFst` also needs P2b-ii's ladder
-- exemption: the `Get Cell Nat ?elem` goal at `finalize` has its only
-- mvar in an OUTPUT-PARAMETER position, which the oracle answers and
-- the pre-test (before this plan) postponed forever.
def getFst {cont : Type} {elem : Type} [Get cont Nat elem] (c : cont) : cont := c

-- `dpair` exists for ONE record, `outParam/getElemUnderDflt`, and it is
-- the record that makes the `finalize` branch OBSERVABLE (design spec
-- § Amendment 4 items 10-11, and this plan's orientation note): with the
-- branch, the inner `Get.get cell 0` finalizes with `?elem := Unit` and
-- `Dflt Unit` finds `instDfltUnit`; without it, the entry point's own
-- fixpoint reaches `Dflt ?elem` at priority 1000 FIRST and applies
-- `instDfltNat`, after which `Get Cell Nat Nat` has no instance. `Dflt`
-- is reused rather than a new class precisely because it already has a
-- bare-priority default AND a `Unit` instance.
def dpair {a : Type} [Dflt a] (x : a) : a := x

-- === M4b-3 P2b-ii: the fourth-priority default instance ===
--
-- Closes design spec § Follow-ups items 1 and 2 (owner assigned by
-- § Amendment 3 item 8; requirements R1-R4 in § Amendment 4 item 9):
--   R1  `instFreshSeed` is universe-polymorphic (level parameter `u`),
--       so `mk_default_instance_candidate` building at an EMPTY level
--       list leaves a rigid `u` in the term instead of a fresh level
--       mvar, and the record moves;
--   R2  it carries an `instImplicit` binder `[Seed PUnit.{u+1}]` that is
--       synthesizable only AFTER the candidate is applied, so
--       `synthesize_using_default_instance`'s nested `synthesizePending`
--       collecting NOTHING leaves that argument an unassigned mvar, and
--       the record moves;
--   R3  priority 75 — a FOURTH priority, strictly between `instOfNatNat`'s
--       100 and `instOfNatTag`'s 50, on a class no other goal mentions,
--       so `num/bare`'s walk (solved at 100) never reaches it and no
--       committed record changes;
--   R4  `useFresh` leaves a pending `Fresh ?α` goal with `?α`
--       unconstrained, so the walk descends past 100 to it.
-- The emitted term keeps a RESIDUAL universe metavariable (`?u` is
-- determined by nothing) — the dumper encodes it canonically as `lmvar`,
-- which `ident/List` already exercises.
class Seed (α : Type u) where
  seed : α

instance instSeedPUnit : Seed PUnit.{u+1} where
  seed := PUnit.unit

class Fresh (α : Type u) where
  fresh : α

@[default_instance 75]
instance instFreshSeed [Seed PUnit.{u+1}] : Fresh PUnit.{u+1} where
  fresh := Seed.seed

def useFresh {α : Type u} [Fresh α] : α := Fresh.fresh
```

- [ ] **Step 2: Add the query list to `tests/fixtures/elab/dump_elab.lean`**

Insert immediately before `def emit (id src : String) (expJ : Json) : IO Unit :=`:

```lean
/-- M4b-3 P2b-ii task 1: the fourth-priority default instance (design
spec § Follow-ups items 1-2, § Amendment 4 item 9). `useFresh` alone
leaves `Fresh ?α` pending with nothing else constraining `?α`, so the
default-instance walk descends 1000 → 100 → 75 and applies
`instFreshSeed`, which is universe-polymorphic AND carries an
`instImplicit` binder. The record therefore pins both the fresh-level
refresh (a rigid `param u` here instead of `lmvar` means
`mk_default_instance_candidate` built at the empty level list) and the
nested `synthesizePending` fixpoint (an `mvar` in the `Seed` argument
position means the candidate's instance-implicit binders were not
collected). -/
def defaultPolyQueries : List (String × String) :=
  [ ("dflt/polyInstImplicit", "useFresh")
  ]
```

Then extend the `main` loop's concatenation — the line beginning
`for (id, src) in strQueries ++ ...` — by appending
` ++ defaultPolyQueries` at its end.

- [ ] **Step 3: Rebuild the fixture and regenerate the corpus**

```bash
git status --porcelain tests/fixtures            # expect only the two .lean edits
cp tests/fixtures/elab/elab-queries.jsonl /tmp/claude-1000/-workspace/elab-queries.before
mise run fixtures:regen 2>&1 | tee /tmp/claude-1000/-workspace/regen.log
grep -n "dump_elab: elaboration failed\|dump_elab: parse error" /tmp/claude-1000/-workspace/regen.log
```

Expected: `grep` prints NOTHING. If it prints
`elaboration failed for dflt/polyInstImplicit`, the candidate shape did
not satisfy the oracle — read the message, fix the DECLARATIONS so that
R1–R4 still hold (the requirements, not this shape, are what the spec
pins), and regen again. Do not remove the query.

- [ ] **Step 4: Verify the 101 committed records did not move, and inspect the new one**

```bash
diff <(head -101 tests/fixtures/elab/elab-queries.jsonl) /tmp/claude-1000/-workspace/elab-queries.before && echo "IDENTICAL"
wc -l tests/fixtures/elab/elab-queries.jsonl
jq -c 'select(.id == "dflt/polyInstImplicit") | .exp' tests/fixtures/elab/elab-queries.jsonl
```

Expected: `IDENTICAL`, `102`, and an `exp` whose `us` lists carry
`{"k":"succ","u":{"k":"lmvar","i":0}}` (the `PUnit.{?u+1}` carrier) and
whose spine mentions `instFreshSeed` and `instSeedPUnit` with NO
`{"k":"mvar"...}` node and NO `{"k":"param"...}` level. A `param` is a
Lean-side fixture problem (the record should be universe-mvar-carrying;
check the declarations), not a leanr problem — fix it before continuing.

- [ ] **Step 5: Raise the corpus floor and re-derive the priority-count assertions**

In `crates/leanr_elab/tests/oracle_elab.rs`, `const CORPUS_FLOOR: usize = 101;`
becomes `102`.

In `crates/leanr_elab/tests/synthetic_smoke.rs`,
`default_instance_walk_visits_pending_mvars_in_reverse_creation_order`:

```rust
        let prios = app.elab.mctx.default_instance_priorities();
        assert_eq!(
            prios.len(),
            4,
            "Elab0's four default-instance priorities (1000 / 100 / 75 / 50), got {prios:?}"
        );
        // The TOP priority must apply to none of the three goals (so the
        // walk visits all of them before dropping a rung), and the
        // SECOND must be where `OfNat`'s winning default sits —
        // `instOfNatNat` at 100 since the task-6 review re-prioritised
        // `instOfNatTag` from 500 down to 50. M4b-3 P2b-ii added a
        // fourth priority (`instFreshSeed` at 75) BELOW 100: the walk
        // stops at the first priority that makes progress, so the
        // recorded order below is unchanged — three visits at the top,
        // one at 100 — and only this count moved.
        assert!(prios[0] > 100 && prios[1] == 100, "got {prios:?}");
```

Leave the `order.len() == 4` and `order == vec![...]` assertions exactly
as they are — they still hold, for the reason the new comment states.

In `default_instance_priorities_are_stored_in_descending_order`:

```rust
        assert!(
            prios.len() >= 4,
            "Elab0 must carry four distinct default-instance priorities, got {prios:?}"
        );
```

and, after the existing `prios.contains(&50)` assertion, add:

```rust
        assert!(
            prios.contains(&75),
            "instFreshSeed's priority (M4b-3 P2b-ii), got {prios:?}"
        );
```

- [ ] **Step 6: Run the suite**

```bash
cargo test -p leanr_elab
```

Expected: PASS, including `oracle_elab_gate` at 102 records. If
`dflt/polyInstImplicit` diverges, the divergence is a P3 defect this
record was added to find (§ Follow-ups items 1–2 say exactly that both
mechanisms were untested) — diagnose it in
`crates/leanr_elab/src/synthetic/default_inst.rs` (`mk_default_instance_candidate`
for a level problem, `synthesize_using_default_instance` for a missing
`Seed` argument) and fix the CODE, never the record.

- [ ] **Step 7: Measure the two mutations this record exists for**

Apply each mutation, run the gate, confirm RED, revert. Both must go
red or the record has not earned its place.

Mutation A (§ Follow-ups item 2): in `mk_default_instance_candidate`
(`default_inst.rs:274-304`) replace the `params` computation with
`let params: Vec<NameId> = Vec::new();`.

Mutation B (§ Follow-ups item 1): in `synthesize_using_default_instance`
(`default_inst.rs:245-254`) replace the `for (m, bi) in ...` loop body
so nothing is pushed: `let pending: Vec<MVarId> = Vec::new();` and delete
the loop.

```bash
cargo test -p leanr_elab --test oracle_elab 2>&1 | grep -c "dflt/polyInstImplicit"
git checkout -- crates/leanr_elab/src/synthetic/default_inst.rs
```

Expected for each: a non-zero count (the record is listed among the
divergences), then a clean revert.

- [ ] **Step 8: Commit**

```bash
mise run ci
git add tests/fixtures/elab/Elab0.lean tests/fixtures/elab/Elab0.olean \
        tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl \
        crates/leanr_elab/tests/synthetic_smoke.rs crates/leanr_elab/tests/oracle_elab.rs
git commit -F - <<'MSG'
M4b-3 P2b-ii task 1: outParam fixture declarations + fourth-priority default instance

Elab0.lean gains its first outParam class (Get, the GetElem shape P2b-i
proved out at the synthesis tier), a container with a Nat-indexed
instance, the two helper defs the producer's false directions need
(getFst) and the headline record needs (dpair), and instFreshSeed at
priority 75 — universe-polymorphic with an instImplicit binder — which
closes P3's carried follow-ups 1-2 with the dflt/polyInstImplicit record.
Lean.Internal.coeM is deliberately NOT declared yet (Amendment 3 item 9).
The 101 committed records are byte-identical; both follow-up mutations
measured red.

Claude-Session: https://claude.ai/code/session_017XRcWKrpV5Dh9bXaQjnafL
MSG
```

---

### Task 2: the ladder pre-test's positional exemption

`try_synth_instance` currently answers `Undef` whenever the goal mentions
an unassigned expr mvar. It becomes: `Undef` only when such an mvar sits
OUTSIDE the head class's output-parameter argument positions (design
spec § Amendment 4 item 6). Three corpus records that need nothing else
land with it.

**Files:**
- Modify: `crates/leanr_elab/src/synthetic/ladder.rs:186-197`
- Modify: `crates/leanr_elab/tests/support/mod.rs` (after `wrap_of_fresh_mvar`)
- Test: `crates/leanr_elab/tests/synthetic_smoke.rs`
- Modify: `tests/fixtures/elab/dump_elab.lean`, `crates/leanr_elab/tests/oracle_elab.rs:154`
- Regenerate: `tests/fixtures/elab/elab-queries.jsonl`

**Interfaces:**
- Consumes: `MetaCtx::get_out_param_positions(&self, NameId) -> Option<&[usize]>`
  (P2b-i, `pub`); Task 1's `Get`/`Cell` constants.
- Produces: `TermElabM::has_mvar_outside_out_params(&self, ExprId) -> bool`
  (private, `ladder.rs`); support helpers
  `get_cell_nat_of_fresh_mvar(app) -> ExprId` (`Get Cell Nat ?e`) and
  `get_cell_of_two_fresh_mvars(app) -> ExprId` (`Get Cell ?i ?e`); corpus
  records `outParam/getFst`, `outParam/getElem`, `outParam/getElemIdxNat`.

- [ ] **Step 1: Add the two goal builders to `crates/leanr_elab/tests/support/mod.rs`**

Insert after `wrap_of_fresh_mvar`:

```rust
/// `Get Cell Nat ?e` — a class goal whose ONLY unassigned mvar sits in
/// an OUTPUT-PARAMETER position (`Get`'s third parameter is
/// `outParam (Type w)`). The oracle answers this goal — `preprocessOutParam`
/// swaps `?e` for a search-local mvar and `assignOutParams` assigns the
/// caller's `?e := Unit` afterwards (M4b-3 P2b-i ported both) — so the
/// ladder pre-test must let it reach the real search.
///
/// Built like `wrap_of_fresh_mvar`: the fresh mvar's type is read off the
/// partial application's own inferred type rather than re-elaborated.
pub fn get_cell_nat_of_fresh_mvar(
    app: &mut leanr_elab::app::state::AppElab,
) -> leanr_kernel::bank::ExprId {
    use leanr_kernel::bank::terms::Node;
    let get_cell_nat = elab_type_expr(app, "Get Cell Nat");
    let ty = app
        .elab
        .mctx
        .infer_type(get_cell_nat)
        .expect("Get Cell Nat's own type infers");
    let Node::Forall { binder_type, .. } = app.node(ty) else {
        panic!("get_cell_nat_of_fresh_mvar: `Get Cell Nat` is not a forall: {ty:?}");
    };
    let (mvar, _id) = app
        .elab
        .mk_fresh_expr_mvar_of_kind(binder_type, leanr_meta::MVarKind::Natural)
        .expect("fresh mvar");
    let base = app.elab.view.store;
    app.elab
        .mctx
        .store_mut()
        .expr_app(Some(base), get_cell_nat, mvar)
        .expect("Get Cell Nat ?e applies")
}

/// `Get Cell ?i ?e` — the same class with an unassigned mvar in a
/// NON-output position too (`idx`). This is the shape the `GetElem`
/// worked example depends on staying POSTPONED: `?i` is fixed only when
/// the `OfNat` default instance fires, and an exemption keyed on the
/// class rather than the position would send this goal to a search that
/// answers `.none` (design spec § Amendment 4 item 6).
pub fn get_cell_of_two_fresh_mvars(
    app: &mut leanr_elab::app::state::AppElab,
) -> leanr_kernel::bank::ExprId {
    use leanr_kernel::bank::terms::Node;
    let get_cell = elab_type_expr(app, "Get Cell");
    let ty = app
        .elab
        .mctx
        .infer_type(get_cell)
        .expect("Get Cell's own type infers");
    let Node::Forall {
        binder_type: idx_ty,
        body,
        ..
    } = app.node(ty)
    else {
        panic!("get_cell_of_two_fresh_mvars: `Get Cell` is not a forall: {ty:?}");
    };
    let (idx, _) = app
        .elab
        .mk_fresh_expr_mvar_of_kind(idx_ty, leanr_meta::MVarKind::Natural)
        .expect("fresh idx mvar");
    // The `elem` binder's type is closed only once `idx` is substituted
    // in (the telescope is `∀ (idx : Type v), outParam (Type w) → ...`,
    // non-dependent here, but instantiating is the general shape).
    let rest = app
        .elab
        .mctx
        .instantiate_beta_rev_range(body, &[idx])
        .expect("instantiate");
    let Node::Forall {
        binder_type: elem_ty,
        ..
    } = app.node(rest)
    else {
        panic!("get_cell_of_two_fresh_mvars: `Get Cell ?i` is not a forall: {rest:?}");
    };
    let (elem, _) = app
        .elab
        .mk_fresh_expr_mvar_of_kind(elem_ty, leanr_meta::MVarKind::Natural)
        .expect("fresh elem mvar");
    let base = app.elab.view.store;
    let with_idx = app
        .elab
        .mctx
        .store_mut()
        .expr_app(Some(base), get_cell, idx)
        .expect("Get Cell ?i applies");
    app.elab
        .mctx
        .store_mut()
        .expr_app(Some(base), with_idx, elem)
        .expect("Get Cell ?i ?e applies")
}
```

- [ ] **Step 2: Write the failing tests in `crates/leanr_elab/tests/synthetic_smoke.rs`**

Append after `postpone_yes_leaves_the_mvar_pending`:

```rust
/// **Residue 1 of `try_synth_instance`'s pre-test, retired (M4b-3
/// P2b-ii).** A goal whose only unassigned mvar sits in an
/// OUTPUT-PARAMETER position is answered by the oracle
/// (`preprocessOutParam` + `assignOutParams`, `SynthInstance.lean:775-861`,
/// ported in P2b-i) and must now reach the real search here too — with
/// the caller's mvar ASSIGNED as a result, which is the whole feature.
///
/// Before this task the pre-test answered `Undef` on any expr mvar at
/// all, and the ladder eventually raised `StuckSyntheticMVar` on a goal
/// the oracle solves. Corpus record `outParam/getFst` pins the same fact
/// end-to-end.
#[test]
fn out_param_position_mvar_reaches_the_real_search() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::get_cell_nat_of_fresh_mvar(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        assert!(
            app.elab
                .synthesize_inst_mvar_core(id)
                .expect("an outParam goal is not an error"),
            "`Get Cell Nat ?e` must be SOLVED, not postponed: the only mvar is \
             in an output-parameter position"
        );
        assert!(
            app.elab.mctx.mctx().is_assigned(id),
            "the instance mvar is assigned"
        );
        // The outParam mvar itself must have been assigned by
        // `assign_out_params` — read it back off the goal.
        let goal = app.elab.mctx.instantiate_mvars(goal).expect("instantiate");
        let base = app.elab.view.store;
        assert!(
            !app.elab.mctx.store().expr_data(Some(base), goal).has_expr_mvar(),
            "`?e := Unit` is assigned as a RESULT of synthesis, got {goal:?}"
        );
    });
}

/// The exemption is POSITIONAL, not class-level (design spec
/// § Amendment 4 item 6): `Get Cell ?i ?e` has an unassigned mvar in a
/// NON-output position (`idx`), so it must still postpone. This is
/// load-bearing for the `GetElem` worked example — `?i` is fixed only
/// when the `OfNat` default instance fires, and sending the goal to the
/// search early would answer `.none` and fail the headline record.
#[test]
fn non_out_param_position_mvar_still_postpones() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::get_cell_of_two_fresh_mvars(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        assert!(
            !app.elab
                .synthesize_inst_mvar_core(id)
                .expect("a stuck goal is not an error"),
            "`Get Cell ?i ?e` must be POSTPONED: `?i` is not an output parameter"
        );
        assert!(
            !app.elab.mctx.mctx().is_assigned(id),
            "nothing is committed on a postponed goal"
        );
    });
}
```

- [ ] **Step 3: Run the tests to verify they fail**

```bash
cargo test -p leanr_elab --test synthetic_smoke out_param_position_mvar_reaches_the_real_search non_out_param_position_mvar_still_postpones
```

Expected: `out_param_position_mvar_reaches_the_real_search` FAILS
("must be SOLVED, not postponed"); `non_out_param_position_mvar_still_postpones`
PASSES already (today's pre-test over-postpones; this test pins that
the exemption does not overshoot).

- [ ] **Step 4: Implement the exemption in `crates/leanr_elab/src/synthetic/ladder.rs`**

Replace the body of `try_synth_instance` (`:186-197`):

```rust
    fn try_synth_instance(&mut self, ty: ExprId) -> Result<LOptionExpr, ElabError> {
        if self.has_mvar_outside_out_params(ty) {
            return Ok(LOptionExpr::Undef);
        }
        match self.mctx.synth_instance(ty) {
            Ok(Some(val)) => Ok(LOptionExpr::Some(val)),
            Ok(None) => Ok(LOptionExpr::None),
            Err(leanr_meta::MetaError::IsDefEqStuck(_)) => Ok(LOptionExpr::Undef),
            Err(e) => Err(ElabError::from(e)),
        }
    }

    /// The stuck pre-test, POSITIONAL since M4b-3 P2b-ii: does `ty`
    /// mention an unassigned expr mvar OUTSIDE its head class's
    /// output-parameter argument positions?
    ///
    /// Why positional (design spec § Amendment 4 item 6). An mvar in an
    /// output-parameter position is exactly what `preprocessOutParam`
    /// (`SynthInstance.lean:775-817`) replaces with a search-local mvar
    /// before the search runs, and what `assignOutParams` (`:847-861`)
    /// assigns back afterwards — both ported in P2b-i
    /// (`leanr_meta::synth.rs`) — so the search never unifies against
    /// the caller's mvar and cannot get stuck on it. An mvar ANYWHERE
    /// ELSE is still one the search would unify against directly, which
    /// is the read-only-mvar stuck condition this pre-test reconstructs
    /// (residues 2 and 3 in `try_synth_instance`'s own doc), so it
    /// still postpones.
    ///
    /// Not class-level: the oracle's `PreprocessKind` (`:706-716`) only
    /// says whether the CLASS has outParams, and `Get Cell ?i ?e` — a
    /// class with outParams, an mvar in a non-output position — must
    /// keep postponing or the `GetElem` worked example breaks.
    ///
    /// Conservative on every shape it cannot read: a non-`Const` head, an
    /// unnamed `Const`, or a head that is not a class (`get_out_param_positions`
    /// answers `None`) keeps today's behaviour, `Undef` on any expr mvar.
    /// Argument positions are counted in APPLICATION order, matching
    /// `ClassEntry.outParams` (`Class.lean:11-31`).
    ///
    /// Precondition: `ty` is already `instantiate_mvars`-ed, so
    /// `has_expr_mvar` means "mentions an UNASSIGNED expr mvar".
    fn has_mvar_outside_out_params(&self, ty: ExprId) -> bool {
        let base = self.view.store;
        let store = self.mctx.store();
        if !store.expr_data(Some(base), ty).has_expr_mvar() {
            return false;
        }
        let mut args = Vec::new();
        let mut cur = ty;
        while let Node::App { f, arg } = store.expr_node(Some(base), cur) {
            args.push(arg);
            cur = f;
        }
        args.reverse();
        let Node::Const {
            name: Some(class), ..
        } = store.expr_node(Some(base), cur)
        else {
            return true;
        };
        let Some(out_positions) = self.mctx.get_out_param_positions(class) else {
            return true;
        };
        args.iter().enumerate().any(|(i, arg)| {
            !out_positions.contains(&i) && store.expr_data(Some(base), *arg).has_expr_mvar()
        })
    }
```

- [ ] **Step 5: Run the tests to verify they pass, then the whole crate**

```bash
cargo test -p leanr_elab --test synthetic_smoke
cargo test -p leanr_elab
```

Expected: PASS. In particular `stuck_synthesis_is_not_ready_rather_than_failure`
(`Wrap ?m`, a class with NO outParams) still postpones, and every
`oracle_elab` record is unchanged.

- [ ] **Step 6: Add the three records that need only this task**

In `tests/fixtures/elab/dump_elab.lean`, insert before `def emit`:

```lean
/-- M4b-3 P2b-ii: the elaborator outParam branch. The three records here
land BEFORE `Lean.Internal.coeM` is declared (task 2 of the plan) and
must stay byte-identical when it is (task 5): in a one-term dump the
entry point's own fixpoint runs the same default instances the
`finalize` branch runs eagerly, so on these shapes the branch changes
WHEN `?elem` is assigned, not WHAT it is assigned. The two records that
DO change — `outParam/getElemUnderDflt` and `outParam/getElemAscribed`
— are appended by task 5 once the branch exists on both sides.

  * `outParam/getFst` — `getFst cell`: the `Get Cell Nat ?elem` goal at
    `finalize` has its only mvar in an OUTPUT-PARAMETER position. The
    oracle answers it (`preprocessOutParam` / `assignOutParams`); leanr
    needed the ladder pre-test's positional exemption. Without it the
    goal postpones forever and the fixpoint reports it stuck.
  * `outParam/getElem` — `Get.get cell 0`, the oracle's own worked
    example (App.lean:150-166). `?idx` is fixed by the `OfNat` default
    instance, then `Get Cell Nat ?elem` is solved with `?elem := Unit`
    assigned as a RESULT of synthesis.
  * `outParam/getElemIdxNat` — `Get.get cell (0 : Nat)`: the index is
    ground before `finalize`, so `synthesizeAppInstMVars` solves the
    instance goal there and the outParam is ALREADY ASSIGNED when the
    branch's guard runs — the else arm (App.lean:645-646). -/
def outParamQueries : List (String × String) :=
  [ ("outParam/getFst",        "getFst cell")
  , ("outParam/getElem",       "Get.get cell 0")
  , ("outParam/getElemIdxNat", "Get.get cell (0 : Nat)")
  ]
```

and append ` ++ outParamQueries` to the `main` loop's concatenation
(after `defaultPolyQueries`).

- [ ] **Step 7: Regenerate (dumper only — `Elab0.lean` is unchanged) and check**

```bash
cp tests/fixtures/elab/elab-queries.jsonl /tmp/claude-1000/-workspace/elab-queries.before
mise run fixtures:regen-elab 2>&1 | grep -n "dump_elab:"
diff <(head -102 tests/fixtures/elab/elab-queries.jsonl) /tmp/claude-1000/-workspace/elab-queries.before && echo "IDENTICAL"
wc -l tests/fixtures/elab/elab-queries.jsonl
jq -c 'select(.id | startswith("outParam/")) | {id, exp: (.exp | tostring | .[0:120])}' tests/fixtures/elab/elab-queries.jsonl
```

Expected: no `dump_elab:` lines, `IDENTICAL`, `105`, and three records
each mentioning `instGetCellNat` and `Unit`. Then raise
`CORPUS_FLOOR` to `105` in `crates/leanr_elab/tests/oracle_elab.rs`.

- [ ] **Step 8: Run the gate and measure the mutation**

```bash
cargo test -p leanr_elab --test oracle_elab
```

Expected: PASS at 105. Then revert the exemption to the old one-line
pre-test (`if self.mctx.store().expr_data(Some(base), ty).has_expr_mvar() { return Ok(LOptionExpr::Undef); }`
with `let base = self.view.store;` above it), run the gate, and confirm
that all three `outParam/*` records are listed as divergences (each
errors: "leanr errored: StuckSyntheticMVar" — the `Get Cell Nat ?elem`
goal postpones forever). Restore the implementation from Step 4.

- [ ] **Step 9: Commit**

```bash
mise run ci
git add crates/leanr_elab/src/synthetic/ladder.rs crates/leanr_elab/tests/support/mod.rs \
        crates/leanr_elab/tests/synthetic_smoke.rs crates/leanr_elab/tests/oracle_elab.rs \
        tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -F - <<'MSG'
M4b-3 P2b-ii task 2: positional exemption in the ladder's stuck pre-test

try_synth_instance answers Undef only when an unassigned expr mvar sits
OUTSIDE the head class's output-parameter positions (Amendment 4 item 6):
`Get Cell Nat ?e` now reaches the real search and P2b-i's
assign_out_params assigns `?e := Unit`; `Get Cell ?i ?e` still postpones,
which the GetElem worked example requires. Three records land with it
(outParam/getFst, getElem, getElemIdxNat), each byte-identical across the
coeM flip task 5 makes; reverting the exemption measured two of them red.

Claude-Session: https://claude.ai/code/session_017XRcWKrpV5Dh9bXaQjnafL
MSG
```

---

### Task 3: `synthesize_synthetic_mvars_using_default`

The oracle's `synthesizeSyntheticMVarsUsingDefault`
(`SyntheticMVars.lean:658-660`) is two existing halves under one name.
`finalize`'s branch (Task 4) calls it.

**Files:**
- Modify: `crates/leanr_elab/src/synthetic/ladder.rs` (after `synthesize_using_default_loop`, `:533`)
- Test: `crates/leanr_elab/tests/synthetic_smoke.rs`

**Interfaces:**
- Consumes: `TermElabM::synthesize_synthetic_mvars(&mut self, PostponeBehavior, &KindInterner) -> Result<(), ElabError>`,
  `TermElabM::synthesize_using_default_loop(&mut self, &KindInterner) -> Result<(), ElabError>`.
- Produces: `pub fn synthesize_synthetic_mvars_using_default(&mut self, kinds: &KindInterner) -> Result<(), ElabError>`.

- [ ] **Step 1: Write the failing test**

Append to `crates/leanr_elab/tests/synthetic_smoke.rs`:

```rust
/// oracle: `synthesizeSyntheticMVarsUsingDefault`
/// (`SyntheticMVars.lean:658-660`) — `synthesizeSyntheticMVars
/// (postpone := .yes)` then `synthesizeUsingDefaultLoop`. The composite
/// exists for `finalize`'s outParam branch (M4b-3 P2b-ii); this pins
/// that it (a) applies a default instance to a stuck goal and (b) does
/// NOT report stuck goals it cannot close — `postpone := .yes` means a
/// goal with no applicable default stays pending rather than erroring.
#[test]
fn synthesize_synthetic_mvars_using_default_defaults_and_keeps_the_rest_pending() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        // `Dflt ?a` — closable by `instDfltNat`; `Wrap ?m` — stuck with
        // no default instance, so it must SURVIVE the call.
        let ids = support::register_typeclass_goals(
            app,
            vec![support::dflt_of_fresh_mvar(app), support::wrap_of_fresh_mvar(app)],
        );
        app.elab
            .synthesize_synthetic_mvars_using_default(&kinds)
            .expect("postpone := .yes never reports a stuck goal");
        assert!(
            app.elab.mctx.mctx().is_assigned(ids[0]),
            "`Dflt ?a` is closed by the default rung"
        );
        assert!(
            !app.elab.mctx.mctx().is_assigned(ids[1]),
            "`Wrap ?m` has no default instance and stays open"
        );
        assert_eq!(
            app.elab.pending_mvars,
            vec![ids[1]],
            "the unclosable goal stays PENDING — not reported, not dropped"
        );
    });
}
```

- [ ] **Step 2: Run it to verify it fails**

```bash
cargo test -p leanr_elab --test synthetic_smoke synthesize_synthetic_mvars_using_default_defaults_and_keeps_the_rest_pending
```

Expected: compile error, `no method named synthesize_synthetic_mvars_using_default`.

- [ ] **Step 3: Implement it in `crates/leanr_elab/src/synthetic/ladder.rs`**

Insert after `synthesize_using_default_loop`:

```rust
    /// oracle: `synthesizeSyntheticMVarsUsingDefault`
    /// (`SyntheticMVars.lean:658-660`) — `synthesizeSyntheticMVars
    /// (postpone := .yes)` then `synthesizeUsingDefaultLoop`.
    ///
    /// Both halves existed since M4b-3 P3; the composite was left
    /// unnamed until something called it (this crate's `lib.rs` ledger
    /// said so in as many words). M4b-3 P2b-ii's `finalize` outParam
    /// branch (`App.lean:643`) is that caller: when an application's
    /// result type is the outParam of a local instance and is still an
    /// unassigned mvar after `synthesizeAppInstMVars`, the oracle applies
    /// default instances EAGERLY, here, rather than leaving them to the
    /// enclosing fixpoint — so that `getElem xs 0`'s type is known to
    /// whatever elaborates next.
    pub fn synthesize_synthetic_mvars_using_default(
        &mut self,
        kinds: &KindInterner,
    ) -> Result<(), ElabError> {
        self.synthesize_synthetic_mvars(PostponeBehavior::Yes, kinds)?;
        self.synthesize_using_default_loop(kinds)
    }
```

- [ ] **Step 4: Run the test to verify it passes**

```bash
cargo test -p leanr_elab --test synthetic_smoke synthesize_synthetic_mvars_using_default_defaults_and_keeps_the_rest_pending
```

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
mise run ci
git add crates/leanr_elab/src/synthetic/ladder.rs crates/leanr_elab/tests/synthetic_smoke.rs
git commit -F - <<'MSG'
M4b-3 P2b-ii task 3: synthesize_synthetic_mvars_using_default

SyntheticMVars.lean:658-660 as a named composite of the two P3 halves,
for finalize's outParam branch (task 4). Pinned: applies a default to a
closable goal and leaves an unclosable one pending rather than reported.

Claude-Session: https://claude.ai/code/session_017XRcWKrpV5Dh9bXaQjnafL
MSG
```

---

### Task 4: the producer and the `finalize` branch

`isNextOutParamOfLocalInstanceAndResult` (`App.lean:681-727`) lands in
`args.rs` and replaces the seam in `add_implicit_arg`; the branch
(`App.lean:638-646`) lands in `finalize.rs` and replaces its seam.
`Lean.Internal.coeM` is still absent from the fixture, so
`result_is_out_param_support` is `false` end-to-end and no record can
move; the tests force the flag on through the `AppElab` harness.

**Files:**
- Modify: `crates/leanr_elab/src/app/state.rs` (helpers beside `app_args`, `:369-378`)
- Modify: `crates/leanr_elab/src/app/args.rs:483-514` (`add_implicit_arg`) and `:77,82,87,92,99` (`finalize` call sites)
- Modify: `crates/leanr_elab/src/app/finalize.rs:9,56-75`
- Modify: `crates/leanr_elab/tests/support/mod.rs` (one harness helper)
- Test: `crates/leanr_elab/tests/app_smoke.rs`

**Interfaces:**
- Consumes: Task 3's `synthesize_synthetic_mvars_using_default`;
  `MetaCtx::has_out_params(&self, NameId) -> bool`; `AppElab::whnf_forall`,
  `get_arg_expected_type`, `synthesize_app_inst_mvars(&mut self, &SynElem)`.
- Produces: `AppElab::app_fn(&self, ExprId) -> ExprId`,
  `AppElab::app_args(&self, ExprId) -> Vec<ExprId>` (now `pub(crate)`),
  `AppElab::is_out_param(&self, ExprId) -> bool`;
  `args::is_next_out_param_of_local_instance_and_result(app, arg_type) -> Result<bool, ElabError>`
  (private) with `is_result_type`, `has_local_instance_with_out_params`,
  `is_out_param_of_local_instance`, `is_out_param_of`;
  `finalize::finalize(app: &mut AppElab, kinds: &KindInterner)`;
  support helper `with_app_args(head_src, arg_srcs, k)`.

- [ ] **Step 1: Add the harness helper to `crates/leanr_elab/tests/support/mod.rs`**

Insert after `with_app_harness`:

```rust
/// `with_app_harness` plus POSITIONAL ARGUMENTS, on the RAW head: each
/// entry of `arg_srcs` is parsed through leanr's own parser and queued
/// as an `Arg::Stx`, so `args::main` elaborates it exactly as
/// `elab_app_aux` would — the way `app_smoke.rs`'s ellipsis test drives
/// `main` on `pick`, but with arguments to consume.
///
/// "Raw head", because `with_app_harness` has already run `head_src`
/// through `main` once as a zero-argument application (its own doc, and
/// `strict_implicit_without_args_finalizes`'s comment): for a head with
/// implicit parameters, `app.st.f` arrives as `@Get.get ?c ?i ?e ?inst`
/// with `f_type` already `?c → ?i → ?e`, and the instance goal that
/// elaboration registered is sitting in `pending_mvars`. This helper
/// peels the spine back to the constant (the same universe-mvar-carrying
/// `Const` either way), re-infers its FULL type, resets the per-application
/// state, and retires the harness's leftover pending goals — so the
/// caller's `main` walks every binder itself, from the first implicit.
///
/// The `KindInterner` handed to `k` is `any_kinds()` (every
/// builtin-snapshot parse carries the same kinds, per that helper's
/// doc), which is what `elab_and_add_new_arg` reads.
///
/// `result_is_out_param_support` and `propagate_expected` are left at
/// `with_app_harness`'s defaults (`false`); a caller that wants the
/// oracle's `elabAppArgs` defaults sets them itself before calling
/// `main`.
pub fn with_app_args<R>(
    head_src: &str,
    arg_srcs: &[&str],
    k: impl FnOnce(&mut leanr_elab::app::state::AppElab, &leanr_syntax::kind::KindInterner) -> R,
) -> R {
    use leanr_elab::app::expand::Arg;
    use leanr_kernel::bank::terms::Node;
    use leanr_syntax::{builtin, parse_term};
    let snap = builtin::snapshot();
    let parses: Vec<_> = arg_srcs
        .iter()
        .map(|src| {
            let parsed = parse_term(src, &snap);
            assert!(
                parsed.errors.is_empty(),
                "with_app_args: leanr parse errors for {src:?}: {:?}",
                parsed.errors
            );
            parsed
        })
        .collect();
    let args: Vec<Arg> = parses
        .iter()
        .map(|p| {
            Arg::Stx(
                p.tree
                    .root()
                    .first_child_or_token()
                    .expect("with_app_args: no term child"),
            )
        })
        .collect();
    let kinds = any_kinds();
    with_app_harness(head_src, |app| {
        let mut f = app.st.f;
        while let Node::App { f: inner, .. } = app.node(f) {
            f = inner;
        }
        let f_type = app
            .elab
            .mctx
            .infer_type(f)
            .unwrap_or_else(|e| panic!("with_app_args: infer_type of the raw head failed: {e:?}"));
        app.st.f = f;
        app.st.f_type = f_type;
        app.st.f_args = Vec::new();
        app.st.args = args;
        app.st.named_args = Vec::new();
        app.st.eta_args = Vec::new();
        app.st.to_set_error_ctx = Vec::new();
        app.st.inst_mvars = Vec::new();
        app.st.result_type_out_param = None;
        app.st.found_named_args = Vec::new();
        for id in std::mem::take(&mut app.elab.pending_mvars) {
            app.elab.mark_as_resolved(id);
        }
        k(app, &kinds)
    })
}
```

- [ ] **Step 2: Write the failing tests in `crates/leanr_elab/tests/app_smoke.rs`**

Append:

```rust
/// oracle: `isNextOutParamOfLocalInstanceAndResult` (`App.lean:681-727`)
/// — the `resultTypeOutParam?` PRODUCER (M4b-3 P2b-ii). `Get.get`'s
/// `{elem}` is the result type AND the outParam of the local instance
/// `[self : Get cont idx elem]`, so processing it marks the mvar and
/// disables expected-type propagation (`App.lean:747-755`).
///
/// Driven with the flag FORCED on: `Elab0.lean` does not declare
/// `Lean.Internal.coeM` until task 5, so `elab_app_aux` computes it
/// `false` end-to-end today. `main` finalizes the bare partial
/// application (no arguments), which takes the branch's ELSE arm
/// (`eType` is `?idx → ?elem`, not the outParam mvar itself) — so this
/// also pins that the else arm returns without error.
#[test]
fn producer_marks_the_result_type_out_param_of_a_local_instance() {
    support::with_app_args("Get.get", &[], |app, kinds| {
        app.ctx.result_is_out_param_support = true;
        app.st.propagate_expected = true;
        leanr_elab::app::args::main(app, kinds).expect("bare `Get.get` finalizes");
        let out = app
            .st
            .result_type_out_param
            .expect("`elem` is the outParam of `[Get cont idx elem]` and the result type");
        assert!(
            !app.st.propagate_expected,
            "marking the result type as an outParam disables propagation (App.lean:753)"
        );
        assert!(
            !app.elab.mctx.mctx().is_assigned(out),
            "nothing determines `?elem` on a bare partial application"
        );
    });
}

/// The producer's THREE false directions, each of which a constant-`true`
/// mutation of one clause would flip (design spec § Amendment 4 item 7,
/// `Elab0.lean`'s `getFst` comment):
///
///   * `useWrap` — `Wrap` has no outParams, so
///     `hasLocalInstanceWithOutParams` (`:700-706`) is false;
///   * `getFst`'s `{cont}` — the result type, but position 0 of `Get`
///     is not an `outParam` position, so `isOutParamOf` (`:718-727`)
///     is false;
///   * `getFst`'s `{elem}` — an outParam of the local instance, but not
///     the result type, so `isResultType` (`:693-697`) is false.
///
/// `getFst` covers the last two at once: if EITHER clause were a
/// constant `true`, one of its two implicits would be marked.
#[test]
fn producer_answers_false_on_each_of_its_three_gates() {
    for head in ["useWrap", "getFst"] {
        support::with_app_args(head, &[], |app, kinds| {
            app.ctx.result_is_out_param_support = true;
            app.st.propagate_expected = true;
            leanr_elab::app::args::main(app, kinds)
                .unwrap_or_else(|e| panic!("bare `{head}` finalizes: {e:?}"));
            assert!(
                app.st.result_type_out_param.is_none(),
                "{head}: no implicit is the outParam of a local instance AND the result type"
            );
            assert!(
                app.st.propagate_expected,
                "{head}: propagation stays enabled when the producer answers false"
            );
        });
    }
}

/// `Context.resultIsOutParamSupport = false` short-circuits the producer
/// (`App.lean:682-683`, "if `resultIsOutParamSupport` is `false`, this
/// method returns `false`") — under `@`, and in every env without
/// `Lean.Internal.coeM`, `Get.get` is elaborated with no special support.
#[test]
fn producer_is_inert_when_the_context_flag_is_off() {
    support::with_app_args("Get.get", &[], |app, kinds| {
        assert!(!app.ctx.result_is_out_param_support, "harness default");
        app.st.propagate_expected = true;
        leanr_elab::app::args::main(app, kinds).expect("bare `Get.get` finalizes");
        assert!(app.st.result_type_out_param.is_none());
        assert!(app.st.propagate_expected);
    });
}

/// oracle: `finalize`'s outParam branch, INTERESTING arm
/// (`App.lean:641-644`): the outParam mvar is still unassigned after
/// `synthesizeAppInstMVars` and `eType` IS that mvar, so
/// `synthesizeSyntheticMVarsUsingDefault` runs HERE, inside the
/// application elaborator, and the `OfNat` default instance fires before
/// any enclosing fixpoint gets a chance.
///
/// Observed through P3's `default_walk_log`: the walk visits mvars only
/// when rung 3 runs, and nothing but this branch runs rung 3 inside
/// `args::main`. The `Get Cell ?α ?elem` goal is then solved by the
/// loop's interleaved `synthesizeSyntheticMVars`, so `?elem := Unit`
/// is assigned by the time `main` returns — which is the entire point of
/// the feature (`App.lean:150-166`).
#[test]
fn finalize_applies_default_instances_when_the_out_param_is_still_open() {
    support::with_app_args("Get.get", &["cell", "0"], |app, kinds| {
        app.ctx.result_is_out_param_support = true;
        app.st.propagate_expected = true;
        leanr_elab::synthetic::default_walk_log_reset();
        let e = leanr_elab::app::args::main(app, kinds).expect("`Get.get cell 0` elaborates");
        let visited = leanr_elab::synthetic::default_walk_log_take();
        assert!(
            !visited.is_empty(),
            "rung 3 must run INSIDE finalize on the open-outParam shape"
        );
        let out = app.st.result_type_out_param.expect("producer fired");
        assert!(
            app.elab.mctx.mctx().is_assigned(out),
            "`?elem` is assigned as a RESULT of the eager default (Unit, via instGetCellNat)"
        );
        let ty = app.elab.mctx.infer_type(e).expect("infer");
        let ty = app.elab.mctx.instantiate_mvars(ty).expect("instantiate");
        let base = app.elab.view.store;
        let carrier = match app.node(ty) {
            leanr_kernel::bank::terms::Node::Const { name: Some(n), .. } => {
                app.elab.mctx.store().to_name(Some(base), Some(n)).to_string()
            }
            other => panic!("the application's type is not a constant: {other:?}"),
        };
        assert_eq!(carrier, "Unit", "the application's type is the fixed carrier");
        assert!(
            app.elab.pending_mvars.is_empty(),
            "the interleaved synthesizeSyntheticMVars closed the instance goal too"
        );
    });
}

/// oracle: the branch's ELSE arm (`App.lean:645-646`) — "If `eType !=
/// mkMVar outParamMVarId`, then the function is partially applied, and
/// we do not apply default instances." Design spec § Amendment 4 item
/// 10: this is a smoke test, not a corpus record, because on a green
/// term the arm's effect is invisible in the emitted `Expr` and the
/// oracle's dumper drops a partially-applied query (its instance goal
/// stays stuck through the fixpoint).
///
/// The discriminator is the walk log again: with `Get Cell ?idx ?elem`
/// PENDING and the arm taken, rung 3 must NOT run; a mutation that
/// always applies defaults visits that goal and the log is non-empty.
#[test]
fn finalize_skips_default_instances_on_a_partial_application() {
    support::with_app_args("Get.get", &["cell"], |app, kinds| {
        app.ctx.result_is_out_param_support = true;
        app.st.propagate_expected = true;
        leanr_elab::synthetic::default_walk_log_reset();
        leanr_elab::app::args::main(app, kinds).expect("`Get.get cell` finalizes");
        let visited = leanr_elab::synthetic::default_walk_log_take();
        assert!(
            visited.is_empty(),
            "partially applied: no default-instance walk, got {visited:?}"
        );
        assert_eq!(
            app.elab.pending_mvars.len(),
            1,
            "the stuck `Get Cell ?idx ?elem` goal is registered pending, not solved or reported"
        );
        let out = app.st.result_type_out_param.expect("producer fired");
        assert!(!app.elab.mctx.mctx().is_assigned(out));
    });
}

/// The producer disables expected-type propagation (`App.lean:753`), so
/// with an expected type in hand `?elem` must be assigned by the DEFAULT
/// rung, not by `propagateExpectedType`: the walk log is non-empty.
/// Leaving propagation on assigns `?elem := Unit` at the first explicit
/// argument, the guard's `isAssigned` then sees it, and the log stays
/// EMPTY — which is how this test kills that mutation.
///
/// What it does NOT discriminate, stated so nobody claims it later: the
/// branch's early `return e` (`App.lean:644,646`) also skips `finalize`'s
/// own `isDefEq expectedType eType` (design spec § Amendment 4 item 5),
/// but by the time control would reach that block the default rung has
/// already assigned `?elem`, so falling through changes nothing a leanr
/// term can observe. The early return is transliterated because the
/// oracle has it, not because a test needs it.
#[test]
fn finalize_under_an_expected_type_still_defaults_rather_than_unifies() {
    support::with_app_args("Get.get", &["cell", "0"], |app, kinds| {
        app.ctx.result_is_out_param_support = true;
        app.st.propagate_expected = true;
        app.st.expected_type = Some(support::fixture_const(app, "Unit"));
        leanr_elab::synthetic::default_walk_log_reset();
        leanr_elab::app::args::main(app, kinds).expect("`(Get.get cell 0 : Unit)` elaborates");
        let visited = leanr_elab::synthetic::default_walk_log_take();
        assert!(
            !visited.is_empty(),
            "with propagation off and the finalize unification skipped, only rung 3 can fix `?elem`"
        );
    });
}
```

- [ ] **Step 3: Run the tests to verify they fail**

```bash
cargo test -p leanr_elab --test app_smoke producer_ finalize_
```

Expected: `producer_marks_the_result_type_out_param_of_a_local_instance`
FAILS with the `add_implicit_arg` seam
(`local-instance outParam result type requires ... M4b-3 P2b-ii`); the
three `finalize_*` tests FAIL the same way;
`producer_answers_false_on_each_of_its_three_gates` fails the same way
(the seam fires on the flag alone); `producer_is_inert_when_the_context_flag_is_off`
PASSES (it exercises today's inert path).

- [ ] **Step 4: Add the three `AppElab` helpers in `crates/leanr_elab/src/app/state.rs`**

Make `app_args` `pub(crate)` and add two siblings directly after it:

```rust
    /// An application spine's arguments, in APPLICATION order.
    pub(crate) fn app_args(&self, e: ExprId) -> Vec<ExprId> {
        // (body unchanged)
    }

    /// oracle: `Expr.getAppFn` — the head of an application spine (`e`
    /// itself when it is not an `App`).
    pub(crate) fn app_fn(&self, e: ExprId) -> ExprId {
        let mut cur = e;
        while let Node::App { f, .. } = self.node(cur) {
            cur = f;
        }
        cur
    }

    /// oracle: `Expr.isOutParam` (`Expr.lean:1709-1710`) —
    /// `isAppOfArity ``outParam 1`, and ONLY `outParam`. This is the
    /// predicate `isOutParamOf` (`App.lean:718-727`) tests on a class
    /// type's binder domains, and it deliberately does NOT accept
    /// `semiOutParam`: reusing `type_annotation_at_head` here (which
    /// strips both, as `consumeTypeAnnotations` must) would silently
    /// widen the `resultTypeOutParam?` branch to `semiOutParam` classes
    /// (design spec § Amendment 4 item 2).
    pub(crate) fn is_out_param(&self, t: ExprId) -> bool {
        matches!(self.type_annotation_head(t), Some((name, 1)) if name == "outParam")
    }
```

- [ ] **Step 5: Implement the producer in `crates/leanr_elab/src/app/args.rs`**

Replace `add_implicit_arg` (`:483-514`) with:

```rust
/// oracle: `addImplicitArg` (`App.lean:745-760`). Creates a fresh mvar
/// for the parameter — marking it as the application's
/// `resultTypeOutParam?` and disabling expected-type propagation when
/// `isNextOutParamOfLocalInstanceAndResult` says so (`:747-755`) —
/// records it in `toSetErrorCtx` for error attribution, and continues
/// the loop.
///
/// No `kinds` parameter: unlike `process_explicit_arg`'s eventual
/// `elab_and_add_new_arg` call, nothing here parses or elaborates
/// surface syntax — the argument is a freshly minted mvar, not an
/// `Arg::Stx` — so there is no `KindInterner` use to thread. The
/// brief's own signature carried it only for symmetry with the other
/// two arms and ended in `let _ = kinds;`; dropping the unused
/// parameter here rather than shipping a discard.
fn add_implicit_arg(app: &mut AppElab) -> Result<(), ElabError> {
    let arg_type = app.get_arg_expected_type()?;
    let arg = app.elab.mk_fresh_expr_mvar(arg_type)?;
    let Node::MVar { id: Some(n) } = app.node(arg) else {
        return Err(ElabError::UnsupportedSyntax(
            "internal invariant: mk_fresh_expr_mvar did not return an mvar node (app::args — \
             not a deferred construct)"
                .to_string(),
        ));
    };
    if is_next_out_param_of_local_instance_and_result(app, arg_type)? {
        // oracle (`App.lean:749-753`): "When the result type is an
        // output parameter, we don't want to propagate the expected
        // type. So, we just mark `propagateExpected := false` to disable
        // it. At `finalize`, we check whether `arg` is still unassigned,
        // if it is, we apply default instances, and try to synthesize
        // pending mvars."
        app.st.result_type_out_param = Some(MVarId(n));
        app.st.propagate_expected = false;
    }
    app.st.to_set_error_ctx.push(MVarId(n));
    add_new_arg(app, arg)
}

/// oracle: `isNextOutParamOfLocalInstanceAndResult` (`App.lean:681-727`)
/// — is the implicit parameter about to be inserted BOTH the result type
/// of the remaining function type AND an `outParam` of some
/// instance-implicit binder in it? The worked example (`App.lean:662-679`):
/// for `fType = {Elem : Type u_3} → [self : Get Cont Idx Elem] → Cont →
/// Idx → Elem` the answer is `true`; one binder earlier, for `Cont`, it
/// is `false`.
///
/// `arg_type` is the parameter's type with annotations consumed
/// (`get_arg_expected_type`), used only to type the probe fvar below.
///
/// The probe fvar (design spec § Amendment 4 item 3). The oracle mints a
/// DANGLING `mkFVar (← mkFreshFVarId)` (`:688`) — no local declaration,
/// purely a token to compare `d.getAppArgs` against by structural
/// equality. `leanr_meta` has no dangling-fvar constructor, so this
/// pushes a real `lctx` decl under the `lctx_checkpoint`/`lctx_restore`
/// bracket `AppElab::forall_telescope_reducing` already uses, and drops
/// it on every exit path. The two consumers cannot tell the difference:
/// `is_out_param_of` compares `ExprId`s (hash-consed, so the substituted
/// occurrence IS the probe), and the only `infer_type`/`whnf` in the
/// clauses run on the class CONSTANT and its type, which never mention
/// the probe.
fn is_next_out_param_of_local_instance_and_result(
    app: &mut AppElab,
    arg_type: ExprId,
) -> Result<bool, ElabError> {
    // oracle: `unless (← read).resultIsOutParamSupport && (← get).resultTypeOutParam?.isNone do return false`
    if !app.ctx.result_is_out_param_support || app.st.result_type_out_param.is_some() {
        return Ok(false);
    }
    // oracle: `let type := (← get).fType.bindingBody!` — `main` only
    // reaches this arm when `f_type_is_forall` answered true, so the
    // node is a `Forall`; anything else is the oracle's own `!` panic
    // domain, reported rather than unwrapped.
    let Node::Forall { body, .. } = app.node(app.st.f_type) else {
        return Err(ElabError::IllFormedSyntax(
            "isNextOutParamOfLocalInstanceAndResult on a non-forall fType".to_string(),
        ));
    };
    if !is_result_type(app, body, 0) {
        return Ok(false);
    }
    if !has_local_instance_with_out_params(app, body) {
        return Ok(false);
    }
    let checkpoint = app.elab.mctx.lctx_checkpoint();
    let result = (|| {
        let x = app
            .elab
            .mctx
            .push_local_decl(None, arg_type, BinderInfo::Default)
            .map_err(ElabError::from)?;
        // oracle: `type.instantiate1 x`.
        let body_x = app
            .elab
            .mctx
            .instantiate_beta_rev_range(body, std::slice::from_ref(&x))
            .map_err(ElabError::from)?;
        is_out_param_of_local_instance(app, x, body_x)
    })();
    app.elab.mctx.lctx_restore(checkpoint);
    result
}

/// oracle: `isResultType` (`App.lean:693-697`) — walk the remaining
/// binders counting depth, and answer whether the final body is the
/// bound variable `i` binders out, i.e. the parameter being inserted.
/// Pure de Bruijn arithmetic on an UNINSTANTIATED body: no `whnf`, no
/// telescope, exactly as the oracle has it. A `BVarBig` index can never
/// equal a `u32` depth reachable here and falls to the `false` arm.
fn is_result_type(app: &AppElab, ty: ExprId, i: u32) -> bool {
    match app.node(ty) {
        Node::Forall { body, .. } => is_result_type(app, body, i + 1),
        Node::BVar { idx } => idx == i,
        _ => false,
    }
}

/// oracle: `hasLocalInstanceWithOutParams` (`App.lean:700-706`) — the
/// QUICK FILTER: does any instance-implicit binder in `ty` have, at the
/// head of its domain, a class with output parameters? Reads the
/// `classExtension` through `MetaCtx::has_out_params` (`Class.lean:85-88`)
/// and inspects nothing else; the positional test is
/// `is_out_param_of_local_instance`'s.
fn has_local_instance_with_out_params(app: &AppElab, mut ty: ExprId) -> bool {
    loop {
        let Node::Forall {
            binder_type,
            body,
            binder_info,
            ..
        } = app.node(ty)
        else {
            return false;
        };
        if binder_info == BinderInfo::InstImplicit {
            if let Node::Const { name: Some(class), .. } = app.node(app.app_fn(binder_type)) {
                if app.elab.mctx.has_out_params(class) {
                    return true;
                }
            }
        }
        ty = body;
    }
}

/// oracle: `isOutParamOfLocalInstance` (`App.lean:708-716`) — for each
/// instance-implicit binder `[C a₁ .. aₙ]` whose class has outParams,
/// infer `C`'s own type and ask `is_out_param_of` whether the probe `x`
/// sits at an `outParam` position. Later binders are walked WITHOUT
/// instantiating (the oracle recurses on the raw `b`), so their domains
/// may carry loose bvars — harmless, since only the spine's head
/// constant and the argument `ExprId`s are read.
fn is_out_param_of_local_instance(
    app: &mut AppElab,
    x: ExprId,
    mut ty: ExprId,
) -> Result<bool, ElabError> {
    loop {
        let Node::Forall {
            binder_type,
            body,
            binder_info,
            ..
        } = app.node(ty)
        else {
            return Ok(false);
        };
        if binder_info == BinderInfo::InstImplicit {
            let head = app.app_fn(binder_type);
            if let Node::Const { name: Some(class), .. } = app.node(head) {
                if app.elab.mctx.has_out_params(class) {
                    let c_type = app.elab.mctx.infer_type(head)?;
                    let args = app.app_args(binder_type);
                    if is_out_param_of(app, x, &args, c_type)? {
                        return Ok(true);
                    }
                }
            }
        }
        ty = body;
    }
}

/// oracle: `isOutParamOf` (`App.lean:718-727`) — walk the class type's
/// binders in step with the instance's arguments; `true` at the first
/// position where the argument IS the probe and the binder's domain is
/// `outParam _`. The test is on the class's own TYPE, syntactically
/// (`Expr.isOutParam`), not on `classExtension` positions — that is
/// how the oracle does it, and it is what makes `semiOutParam` a
/// non-match (design spec § Amendment 4 item 2).
///
/// The oracle `whnf`s the class type at every step. A step whose type
/// is already a `Forall` is reduced by nothing, so — as
/// `forall_telescope_reducing` does — reduction is skipped there; a
/// non-`Forall` node goes through `whnf_forall`, and if it is still not
/// a binder the walk ends `false` (`| _ => return false`).
fn is_out_param_of(
    app: &mut AppElab,
    x: ExprId,
    args: &[ExprId],
    mut c_type: ExprId,
) -> Result<bool, ElabError> {
    for &arg in args {
        let reduced = if matches!(app.node(c_type), Node::Forall { .. }) {
            c_type
        } else {
            app.whnf_forall(c_type)?
        };
        let Node::Forall {
            binder_type, body, ..
        } = app.node(reduced)
        else {
            return Ok(false);
        };
        if arg == x && app.is_out_param(binder_type) {
            return Ok(true);
        }
        c_type = body;
    }
    Ok(false)
}
```

- [ ] **Step 6: Thread `kinds` into `finalize` and implement the branch in `crates/leanr_elab/src/app/finalize.rs`**

Change the signature and the import block:

```rust
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_meta::MVarId;
use leanr_syntax::kind::KindInterner;

use crate::app::state::AppElab;
use crate::error::ElabError;

pub fn finalize(app: &mut AppElab, kinds: &KindInterner) -> Result<ExprId, ElabError> {
```

Replace the seam block (`:56-75`, from
`// oracle: the \`resultTypeOutParam?\` branch (\`App.lean:637-648\`).`
through its closing `}`) with:

```rust
    // oracle: the `resultTypeOutParam?` branch (`App.lean:638-646`),
    // M4b-3 P2b-ii. `args::add_implicit_arg` is the producer. BOTH arms
    // `return e` early — skipping the expected-type unification below
    // AND the trailing committing pass — which is observable (design
    // spec § Amendment 4 item 5): with an expected type in hand, the
    // outParam mvar is fixed by the DEFAULT rung, not by `isDefEq`.
    if let Some(out) = app.st.result_type_out_param {
        // oracle: `synthesizeAppInstMVars` (`:639`) — the committing pass,
        // moved ahead of the guard so an instance goal that IS ready
        // (index type already ground) assigns the outParam here and the
        // else arm is taken.
        let stx = app.ctx.stx.clone();
        app.synthesize_app_inst_mvars(&stx)?;
        // oracle (`:640-641`): "If `eType != mkMVar outParamMVarId`, then
        // the function is partially applied, and we do not apply default
        // instances."
        let e_type_is_the_out_param =
            matches!(app.node(e_type), Node::MVar { id: Some(n) } if MVarId(n) == out);
        if !app.elab.mctx.mctx().is_assigned(out) && e_type_is_the_out_param {
            app.elab.synthesize_synthetic_mvars_using_default(kinds)?;
        }
        return Ok(e);
    }
```

Then update the five call sites in `crates/leanr_elab/src/app/args.rs`
(`:77,82,87,92,99`) from `crate::app::finalize::finalize(app)` to
`crate::app::finalize::finalize(app, kinds)`.

- [ ] **Step 7: Run the tests to verify they pass, then the whole crate**

```bash
cargo test -p leanr_elab --test app_smoke producer_ finalize_
cargo test -p leanr_elab
```

Expected: all six PASS; `oracle_elab` unchanged at 105 (the flag is
still `false` end-to-end); `seam_audit` still green — the two seam
messages this task deleted were never in `deferred_constructs_are_named_seams`'s
case list (the flag kept them unreachable from source), so nothing there
asserts on them.

- [ ] **Step 8: Measure the mutations these tests exist for**

Apply each, run `cargo test -p leanr_elab --test app_smoke`, confirm the
named test goes RED, revert with `git checkout -- crates/leanr_elab/src/app/`.

| Mutation | Must go red |
|---|---|
| `is_result_type` → `true` | `producer_answers_false_on_each_of_its_three_gates` (`getFst`'s `{elem}` gets marked) |
| `is_out_param_of` → `Ok(true)` | `producer_answers_false_on_each_of_its_three_gates` (`getFst`'s `{cont}` gets marked) |
| `has_local_instance_with_out_params` → `true` | passes — it is a quick filter re-checked by `is_out_param_of_local_instance`; the `→ false` mutation is what matters: |
| `has_local_instance_with_out_params` → `false` | `producer_marks_the_result_type_out_param_of_a_local_instance` |
| delete `app.st.propagate_expected = false;` | `finalize_under_an_expected_type_still_defaults_rather_than_unifies` |
| delete the `e_type_is_the_out_param &&` half of the guard | `finalize_skips_default_instances_on_a_partial_application` |
| delete the whole `if let Some(out)` block | all three `finalize_*` tests |

- [ ] **Step 9: Commit**

```bash
mise run ci
git add crates/leanr_elab/src/app/ crates/leanr_elab/tests/app_smoke.rs crates/leanr_elab/tests/support/mod.rs
git commit -F - <<'MSG'
M4b-3 P2b-ii task 4: resultTypeOutParam? producer + finalize's outParam branch

isNextOutParamOfLocalInstanceAndResult (App.lean:681-727) with its four
clauses lands in args.rs and replaces add_implicit_arg's seam; the
finalize branch (App.lean:638-646) replaces finalize.rs's, with `kinds`
threaded from main's five call sites for
synthesize_synthetic_mvars_using_default. The probe fvar is a
checkpointed lctx decl (Amendment 4 item 3); isOutParamOf tests the
syntactic `outParam` wrapper only, never semiOutParam (item 2). Driven
with the flag forced on through the harness — Lean.Internal.coeM is
still undeclared, so the corpus is untouched at 105 — and every clause
measured red under its mutation via the default_walk_log.

Claude-Session: https://claude.ai/code/session_017XRcWKrpV5Dh9bXaQjnafL
MSG
```

---

### Task 5: `Lean.Internal.coeM` — the flag flips on, and the two records that prove it

With every consumer of `result_is_out_param_support` real, the fixture
declares the gate. All 105 committed records must stay byte-identical
(§ Amendment 4 item 8), and the two records that the branch CHANGES on
the oracle side land here.

**Files:**
- Modify: `tests/fixtures/elab/Elab0.lean` (append)
- Modify: `tests/fixtures/elab/dump_elab.lean` (`outParamQueries`)
- Modify: `crates/leanr_elab/tests/oracle_elab.rs:154`
- Test: `crates/leanr_elab/tests/synthetic_smoke.rs`
- Regenerate: `tests/fixtures/elab/Elab0.olean`,
  `tests/fixtures/elab/elab-queries.jsonl`

**Interfaces:**
- Consumes: Task 4's producer and branch; `app/mod.rs`'s existing
  `env_contains_coe_m` (`:464-467`, unchanged).
- Produces: Lean constant `Lean.Internal.coeM`; corpus records
  `outParam/getElemUnderDflt`, `outParam/getElemAscribed`.

- [ ] **Step 1: Declare the gate in `tests/fixtures/elab/Elab0.lean`**

Append at the end of the file:

```lean
-- === M4b-3 P2b-ii: the `resultIsOutParamSupport` env gate ===
--
-- `elabAppArgs` computes `resultIsOutParamSupport` as
-- `env.contains ``Lean.Internal.coeM && flag && !explicit`
-- (App.lean:1355), and `crates/leanr_elab/src/app/mod.rs`'s
-- `env_contains_coe_m` computes it the same way. This declaration is an
-- EXISTENCE-ONLY gate: nothing on any path M4b-3 reaches reads its type.
-- It is a minimal opaque stand-in on the `axiom String` / `axiom Char`
-- precedent above, and it deliberately carries NO `@[coe_decl]` — the
-- attribute would put a stand-in into the `coe_decl` name set M4b-3 P4
-- decodes. The real definition (`Init/Coe.lean:336-339`, an `abbrev`
-- over `Monad` and `CoeT`) is owed by the do-notation slice, the only
-- one that reaches coeM's other consumer (`Meta/Coe.lean:211`,
-- `coerceMonadLift?`). Design spec § Amendment 4 item 7.
--
-- Declared LAST, in the task that follows the producer: with this
-- present and no producer, every non-`@` application in the corpus
-- raised the `add_implicit_arg` seam (design spec § Amendment 3 item 9).
-- Every record before this block is byte-identical with it present —
-- no earlier `Elab0` class carries an `outParam`, so
-- `hasLocalInstanceWithOutParams` short-circuits on all of them
-- (§ Amendment 4 item 8).
axiom Lean.Internal.coeM : Type
```

- [ ] **Step 2: Add the two records to `outParamQueries` in `dump_elab.lean`**

Extend the doc comment on `outParamQueries` with:

```lean
  * `outParam/getElemUnderDflt` — `dpair (Get.get cell 0)`: THE record
    that makes the branch observable (design spec § Amendment 4 items
    10-11). With the branch, the inner application finalizes with
    `?elem := Unit`, so `dpair`'s `a := Unit` and `Dflt Unit` is
    `instDfltUnit`. Without it — including on the ORACLE, whenever
    `Lean.Internal.coeM` is absent from this fixture — `a := ?elem`
    stays open, the entry point's fixpoint reaches `Dflt ?elem` at
    priority 1000 FIRST and applies `instDfltNat`, and `Get Cell Nat
    Nat` has no instance: an error, and the dumper drops the query.
  * `outParam/getElemAscribed` — `(Get.get cell 0 : Unit)`: the
    producer disables expected-type propagation and the branch returns
    before `finalize`'s own unification, so `?elem` is fixed by the
    default rung and the ascription's `ensureHasType` merely checks it.
    The emitted term coincides with `outParam/getElem`; the MECHANISM
    is pinned by `tests/app_smoke.rs`'s walk-log test instead.
```

and extend the list:

```lean
  , ("outParam/getElemUnderDflt", "dpair (Get.get cell 0)")
  , ("outParam/getElemAscribed",  "(Get.get cell 0 : Unit)")
```

- [ ] **Step 3: Rebuild, regenerate, and verify nothing moved**

```bash
cp tests/fixtures/elab/elab-queries.jsonl /tmp/claude-1000/-workspace/elab-queries.before
mise run fixtures:regen 2>&1 | grep -n "dump_elab:"
diff <(head -105 tests/fixtures/elab/elab-queries.jsonl) /tmp/claude-1000/-workspace/elab-queries.before && echo "IDENTICAL"
wc -l tests/fixtures/elab/elab-queries.jsonl
jq -c 'select(.id == "outParam/getElemUnderDflt") | .exp | tostring | .[0:200]' tests/fixtures/elab/elab-queries.jsonl
```

Expected: no `dump_elab:` lines (in particular NOT
`elaboration failed for outParam/getElemUnderDflt` — if that appears,
`coeM` did not flip the oracle's flag; check the declaration's exact
name), `IDENTICAL`, `107`, and a term mentioning `instDfltUnit` and
`Unit` (NOT `instDfltNat`). Raise `CORPUS_FLOOR` to `107`.

- [ ] **Step 4: Run the gate**

```bash
cargo test -p leanr_elab --test oracle_elab
```

Expected: PASS at 107, every record — the 105 old ones now running with
`result_is_out_param_support = true` — agreeing with the oracle.

- [ ] **Step 5: Add the end-to-end smoke test**

Append to `crates/leanr_elab/tests/synthetic_smoke.rs`:

```rust
/// End-to-end confirmation that `Elab0.lean`'s `Lean.Internal.coeM`
/// turns the feature ON through `app::elab_app_aux`'s own
/// `env_contains_coe_m` (`App.lean:1355`), with no harness override:
/// `elab_term` ALONE — no enclosing fixpoint — on the worked example
/// runs the default rung inside `finalize`, so the walk log is non-empty
/// and the result is fully determined before anything else elaborates.
/// The oracle's motivating example (`App.lean:150-166`) is exactly this
/// property; corpus record `outParam/getElemUnderDflt` pins its
/// consequence against the oracle.
#[test]
fn coe_m_gate_enables_eager_defaulting_from_source() {
    leanr_elab::synthetic::default_walk_log_reset();
    support::elab_only("Get.get cell 0").expect("elab_term alone succeeds");
    let visited = leanr_elab::synthetic::default_walk_log_take();
    assert!(
        !visited.is_empty(),
        "with coeM declared, finalize's outParam branch ran rung 3 inside elab_term"
    );
}
```

- [ ] **Step 6: Run it, then the whole suite**

```bash
cargo test -p leanr_elab --test synthetic_smoke coe_m_gate_enables_eager_defaulting_from_source
cargo test -p leanr_elab
```

Expected: PASS.

- [ ] **Step 7: Measure the headline mutation against the corpus**

Delete the whole `if let Some(out) = app.st.result_type_out_param {..}`
block in `finalize.rs`, run `cargo test -p leanr_elab --test oracle_elab`,
and confirm `outParam/getElemUnderDflt` is listed as a divergence
(leanr errors — `InstanceSynthesisFailed` on `Get Cell Nat Nat`, or a
stuck report) while `outParam/getElem` still passes. Restore with
`git checkout -- crates/leanr_elab/src/app/finalize.rs`.

- [ ] **Step 8: Commit**

```bash
mise run ci
git add tests/fixtures/elab/Elab0.lean tests/fixtures/elab/Elab0.olean \
        tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl \
        crates/leanr_elab/tests/oracle_elab.rs crates/leanr_elab/tests/synthetic_smoke.rs
git commit -F - <<'MSG'
M4b-3 P2b-ii task 5: Lean.Internal.coeM turns resultIsOutParamSupport on

An existence-only axiom (Amendment 4 item 7; no @[coe_decl], so P4's
coe_decl set stays clean). All 105 prior records are byte-identical with
the flag on (item 8). Two records that the branch CHANGES land with it:
outParam/getElemUnderDflt — the oracle itself drops this query without
coeM, and leanr fails it without the branch (measured) — and
outParam/getElemAscribed. Corpus 105 -> 107.

Claude-Session: https://claude.ai/code/session_017XRcWKrpV5Dh9bXaQjnafL
MSG
```

---

### Task 6: retire the seam ledger entries and gate that they stay retired

Four doc sites still describe P2b-ii as open. This task reconciles them,
adds the retired-label gate in the `seam_audit.rs` style, and runs the
full CI gate.

**Files:**
- Modify: `crates/leanr_elab/src/app/mod.rs:19-56` (module doc seam table)
- Modify: `crates/leanr_elab/src/app/state.rs:27-36,77-83` (field docs)
- Modify: `crates/leanr_elab/src/dispatch.rs:132-155` (deferred table)
- Modify: `crates/leanr_elab/src/lib.rs:30-33,67-103,245-265`
- Modify: `crates/leanr_elab/src/synthetic/ladder.rs:97-135,172-179` (Residue 1)
- Test: `crates/leanr_elab/tests/seam_audit.rs`

**Interfaces:**
- Produces: `seam_audit.rs::no_seam_points_at_the_retired_p2b_ii_label`.

- [ ] **Step 1: Write the failing gate in `crates/leanr_elab/tests/seam_audit.rs`**

Append after `no_seam_points_at_the_retired_p3_default_instance_label`:

```rust
/// M4b-3 P2b-ii RETIRED the `resultTypeOutParam?` producer seam — the
/// `add_implicit_arg` and `finalize` messages that both read
/// "... requires the elaborator-side resultTypeOutParam? producer —
/// M4b-3 P2b-ii" — and the ladder's Residue 1. A source tree that still
/// carries that phrase, in a message OR in a doc comment claiming the
/// producer is missing, is making a stale claim about what is
/// implemented.
///
/// Mirrors the two retired-label gates above and inherits their stated
/// precondition: a TEXTUAL scan is a floor (the retired wording never
/// comes back), not a ceiling. The needle is the distinctive subject of
/// both retired messages and lies within one source line of each
/// (verified against the task-3 commit's `args.rs` and `finalize.rs`
/// with `git show <commit>:<path> | grep -c`: one offender in each
/// there, zero here). Prose that names the producer as EXISTING (e.g.
/// "`args::add_implicit_arg` is the producer") does not contain the
/// needle and is not an offender.
#[test]
fn no_seam_points_at_the_retired_p2b_ii_label() {
    let src_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    let needle = "resultTypeOutParam? producer";
    let mut offenders = Vec::new();
    for path in walk_rs_files(src_dir) {
        let text = std::fs::read_to_string(&path).expect("readable source");
        for (n, line) in text.lines().enumerate() {
            if line.contains(needle) {
                offenders.push(format!("{}:{}", path.display(), n + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "P2b-ii retired the resultTypeOutParam? producer seam (it has a real body in \
         `app/args.rs`); stale label at {offenders:?}"
    );
}
```

- [ ] **Step 2: Run it to see the offenders**

```bash
cargo test -p leanr_elab --test seam_audit no_seam_points_at_the_retired_p2b_ii_label
```

Expected: FAIL on `dispatch.rs:144`'s deferred-table row (the one
remaining line carrying the phrase without backticks around the
identifier). Task 4 already deleted the two seam MESSAGES in
`args.rs`/`finalize.rs`, so measure the gate's non-vacuity against the
tree before that task rather than assuming it:

```bash
git show "$(git log --format=%H --grep='P2b-ii task 3' -1)":crates/leanr_elab/src/app/args.rs | grep -c "resultTypeOutParam? producer"
git show "$(git log --format=%H --grep='P2b-ii task 3' -1)":crates/leanr_elab/src/app/finalize.rs | grep -c "resultTypeOutParam? producer"
```

Expected: `1` and `1` — record both counts in the test's doc comment
where it says "verified against". The doc-comment sites that name the
producer with backticks (`state.rs`, `lib.rs`) are not offenders of this
gate; they are still Step 3 edits, driven by the list there, because
they make the stale claim in different words.

- [ ] **Step 3: Reconcile the docs**

Every edit is a comment. The rule: say what IS implemented and where,
name what is still open with its owner, and do not quote a retired
message's text (the gates are text scans).

1. `crates/leanr_elab/src/app/mod.rs`: in the seam table, delete the row
   `local-instance outParam result type .............. P2b args.rs, finalize.rs`
   and add, to the "IN this plan, so NOT seams" paragraph at the top, a
   sentence: "**Also no longer a seam, as of M4b-3 P2b-ii**: the
   local-instance outParam result type — `args.rs`'s
   `is_next_out_param_of_local_instance_and_result` is the
   `resultTypeOutParam?` producer and `finalize.rs`'s branch is its
   consumer (`App.lean:681-727`, `:638-646`), gated by `Elab0.lean`'s
   `Lean.Internal.coeM` exactly as the oracle's `App.lean:1355` gates it.
   `tests/seam_audit.rs`'s `no_seam_points_at_the_retired_p2b_ii_label`
   gates that its message never comes back." Also drop the sentence
   "P3 changed nothing else in `app/`: the `local-instance outParam
   result type` row below is unchanged and still P2b's, which now runs
   after P3 (design spec § Amendment 2)."
2. `crates/leanr_elab/src/app/state.rs`: `Context.result_is_out_param_support`'s
   doc — replace the last two sentences (from "P1 computes it the SAME
   way" on) with: "Computed the same way here (`app::elab_app_aux`),
   and `true` in the fixture env since M4b-3 P2b-ii declared
   `Lean.Internal.coeM` in `Elab0.lean`. Consumed by
   `args::is_next_out_param_of_local_instance_and_result` (the producer)
   and `finalize`'s outParam branch." `State.result_type_out_param`'s doc
   becomes: "oracle: `State.resultTypeOutParam?`. Written by
   `args::add_implicit_arg` when
   `is_next_out_param_of_local_instance_and_result` answers true
   (`App.lean:747-755`, M4b-3 P2b-ii); read by `finalize`'s outParam
   branch (`App.lean:638-646`)."
3. `crates/leanr_elab/src/dispatch.rs`: delete the
   `local-instance outParam result type ........ M4b-3 P2b-ii (resultTypeOutParam? producer)`
   row, and reword the sentence before the table ("only the
   elaborator-side local-instance outParam feature remains, now
   P2b-ii's ...") to: "Reconciled a THIRD time by M4b-3 P2b-ii: the
   local-instance outParam feature landed (`app/args.rs`,
   `app/finalize.rs`) and is no longer deferred either:".
4. `crates/leanr_elab/src/lib.rs`: the "What is NOT built yet" bullet
   "**local-instance outParam result types**" moves UP into the shipped
   list as a new "**M4b-3 P2b-ii**" entry: the producer and branch, the
   `synthesizeSyntheticMVarsUsingDefault` composite, the positional
   ladder exemption, `Elab0.lean`'s `outParam`/`Get`/`Cell`/`coeM`
   declarations and the fourth-priority default instance, and the
   `outParam/*` + `dflt/polyInstImplicit` records. State plainly that
   `coeM` is an existence-only axiom owed its real definition by the
   do-notation slice (§ Amendment 4 item 7). In the P2a entry (`:30-33`)
   replace "the producer/branch is still a named seam below, owned by
   P2b-ii" with "the producer/branch shipped in P2b-ii". In the residue
   paragraph (`:251-258`) replace "(1) `outParam` goals ... Closed by
   P2b-ii, NOT by the depth model;" with "(1) `outParam` goals — CLOSED
   by M4b-3 P2b-ii's positional exemption in `try_synth_instance`
   (§ Amendment 4 item 6), not by the depth model;".
5. `crates/leanr_elab/src/synthetic/ladder.rs`: rewrite "Residue 1" so
   it records the exemption as SHIPPED — keep the oracle citations and
   the mechanism paragraph, replace everything from "**M4b-3 P2b-i has
   landed the SYNTHESIS half of the fix**" through "must retire this
   residue in the same change." with: "**Closed by M4b-3 P2b-ii.**
   `has_mvar_outside_out_params` below exempts output-parameter
   positions, so `Op N N ?c` / `Get Cell Nat ?e` reach the real search
   and P2b-i's `assign_out_params` assigns the caller's mvar; a goal with
   an mvar in a NON-output position (`Get Cell ?i ?e`) still postpones,
   which the `GetElem` worked example requires. Residues 2 and 3 below
   are unchanged and still the depth model's." Then in the paragraph at
   `:172-179` delete the sentence beginning "Residue 1 does NOT come
   along for free".

- [ ] **Step 4: Run the gate and the whole crate**

```bash
cargo test -p leanr_elab --test seam_audit
cargo test -p leanr_elab
```

Expected: PASS, including the existing `no_seam_points_at_the_retired_p2_label`
(the new prose uses "P2b-ii", which that gate's `after != Some('b')`
filter accepts) and `no_seam_message_names_the_completed_p3_slice`.

- [ ] **Step 5: Full gate and commit**

```bash
mise run ci
git add crates/leanr_elab/src/ crates/leanr_elab/tests/seam_audit.rs
git commit -F - <<'MSG'
M4b-3 P2b-ii task 6: retire the outParam seam ledger entries

app/mod.rs, state.rs, dispatch.rs, lib.rs and ladder.rs's Residue 1 now
say what shipped and where; seam_audit gates that the retired
"resultTypeOutParam? producer" label never comes back.

Claude-Session: https://claude.ai/code/session_017XRcWKrpV5Dh9bXaQjnafL
MSG
```

- [ ] **Step 6: Open the PR**

Follow `superpowers:finishing-a-development-branch`. The PR title is
`M4b-3 P2b-ii: the elaborator outParam branch`; its description
summarises the six tasks, lists the corpus growth (101 → 107) and the
mutations measured red, ends with
`https://claude.ai/code/session_017XRcWKrpV5Dh9bXaQjnafL`, and — per
the standing merge instruction — is merged on green CI with the branch
deleted, not left at "PR opened".

---

## Verification summary

After Task 6, these must all hold:

- `mise run test` — green, including `oracle_elab` at 107 records: the
  101 pre-existing ones byte-identical across every task (including the
  `coeM` flip), plus `dflt/polyInstImplicit`, `outParam/getFst`,
  `outParam/getElem`, `outParam/getElemIdxNat`,
  `outParam/getElemUnderDflt`, `outParam/getElemAscribed`.
- `mise run ci` — green (`cargo fmt --check` + clippy included).
- `git diff` against the merge base touches no `leanr_kernel`,
  `leanr_meta` or `leanr_olean` file.
- Every mechanism this plan adds has a test that goes red when it is
  mutated, and each was MEASURED (Tasks 1.7, 2.8, 4.8, 5.7):
  candidate universe refresh → `dflt/polyInstImplicit`;
  nested `synthesizePending` → `dflt/polyInstImplicit`;
  ladder exemption → `outParam/getFst`, `outParam/getElem`;
  `is_result_type` / `is_out_param_of` → `producer_answers_false_on_each_of_its_three_gates`;
  `has_local_instance_with_out_params` → `producer_marks_the_result_type_out_param_of_a_local_instance`;
  `propagate_expected := false` → `finalize_under_an_expected_type_still_defaults_rather_than_unifies`;
  the else-arm guard → `finalize_skips_default_instances_on_a_partial_application`;
  the branch as a whole → `outParam/getElemUnderDflt` and the three `finalize_*` tests;
  the `coeM` gate → `coe_m_gate_enables_eager_defaulting_from_source`.
- No source line under `crates/leanr_elab/src` contains
  `resultTypeOutParam? producer`.

## What this plan deliberately does NOT do

- **No `leanr_meta` / `leanr_olean` change.** § Accessor ledger's
  "P2b-ii — none expected" holds; if a task finds it needs one, stop and
  amend the spec first (§ Amendment 4 item 6 explains why the one
  tempting candidate — sharing the classification with `preprocess` —
  buys nothing).
- **The real `Lean.Internal.coeM`.** The axiom is an existence-only
  gate; the do-notation slice owns the `abbrev` (§ Seams).
- **The mctx-depth model.** Residues 2 and 3 of `try_synth_instance`
  keep their owner; the pre-test is narrowed, not deleted.
- **§ Follow-ups item 4** (`with_assignable_synthetic_opaque`'s drop
  guard) stays `leanr_meta`'s.
- **`semiOutParam`.** `is_out_param` matches `outParam` only, as the
  oracle's `isOutParamOf` does; no fixture declares a `semiOutParam`
  class and none is added.
- **No `lean-toolchain` bump, no workflow change.**
