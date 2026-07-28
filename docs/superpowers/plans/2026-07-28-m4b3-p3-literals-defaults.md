# M4b-3 Plan 3 — Literals and Default Instances Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Elaborate `num`, `char` and `scientific` literals byte-for-byte identically to the pinned Lean oracle, and build the `synthesizeUsingDefault` rung that makes `42 : Nat` work — retiring P2a's shape-guarded rung-3 seam rather than retargeting it.

**Architecture:** `crates/leanr_elab/src/synthetic.rs` (804 lines) splits into a `synthetic/` directory *before* the new code lands; the `synthesizeUsingDefault*` family arrives as `synthetic/default_inst.rs`. `builtin/lit.rs` becomes `builtin/lit/` with the token decoders separated from the elaborators. `num` is the only construct in leanr's grammar that creates a `TypeClass` mvar whose class carries default instances, so it is the sole source producer for ladder rung 3 — rung and producer ship in the same PR. The `classExtension` decode and the `resultTypeOutParam?` branch are **not** in this plan; they are M4b-3 P2b, which now runs *after* this plan.

**Tech Stack:** Rust (workspace crates `leanr_elab`, `leanr_meta`, `leanr_kernel`, `leanr_syntax`), `cargo test`, mise tasks, Lean 4 `v4.33.0-rc1` as the differential oracle (dumper: `tests/fixtures/elab/dump_elab.lean`).

**Spec:** `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` (§ P3 — literals and default instances; § Amendment 2 — why P3 precedes P2b, why P3 is one plan, and the two P2a deferrals it absorbs).

## Global Constraints

- **Pinned oracle:** `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`). Every oracle citation below is against `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`. **Never bump the pin.**
- **`leanr_kernel` is byte-untouched.** It depends on no workspace crate; no existing kernel function is modified, and no new one is added. `Store::expr_lit_nat` (`bank/terms.rs:535`) is already public and is used as-is.
- **`leanr_meta/src` changes are additive, TCB-neutral and behavior-neutral — with exactly one named exception.** Task 4 *generalizes* `refresh_instance_levels` and `get_subgoals` out of `synth.rs` into public `mk_const_with_fresh_mvar_levels` / `forall_meta_telescope_reducing` and rewires `get_subgoals` to call them. That is a refactor, not an addition; it is sanctioned by the spec's § Accessor ledger and gated on `synth.rs`'s existing tests plus `meta:fast` staying byte-identical. Nothing else in `leanr_meta` changes behavior.
- **`leanr_olean` is untouched by this plan.** The `classExtension` decode is P2b's.
- **Named-seam discipline.** Every unimplemented construct returns `ElabError::UnsupportedSyntax` carrying a message that names the owning slice — never a panic, never a wrong `ExprId`, never a silent fall-through that emits a different term.
- **Oracle discipline.** Correctness is byte-for-byte agreement with the oracle's canonical `Expr` via `crates/leanr_elab/tests/oracle_elab.rs`. **Never hand-write an `exp` value in `elab-queries.jsonl`** — always regenerate with `mise run fixtures:regen-elab` and commit what the oracle emits.
- **Untrusted input.** No new `.olean` decoder lands in this plan, so `docs/THREAT_MODEL.md`'s parser rules are not newly engaged. The *literal token* decoders in Task 6/7 read parser-validated source text, not untrusted bytes, but they still must never panic on an unexpected character — the existing `decode_string_literal` catch-all arm is the precedent to follow.
- **Before every commit:** `mise run fmt`, then `mise run lint`, then `mise run test` (or `mise run ci`, which gates all three plus `cargo fmt --check`). Test gates do not cover formatting; CI does.
- **Regeneration needs the elan toolchain** (`mise run elan:bootstrap` once). It never runs in CI. Rebuilding `Elab0.olean` is `mise run fixtures:regen` (its `Elab0` step is `cd tests/fixtures/elab && lean Elab0.lean -o Elab0.olean`, `mise.toml:159`); regenerating the corpus is `mise run fixtures:regen-elab`.

### Measured facts this plan is built on

Established against the pinned toolchain source and the merged P2a code. They are **not** assumptions — do not re-derive them, but do let a contradiction stop you:

1. **The literal kind names leanr's parser produces are `"num"`, `"scientific"`, `"str"`, `"char"`** (`leanr_syntax/src/parse.rs:1912-1915`), and all four go through `Parser::lit`, which **wraps** the token in a node (`parse.rs:2972-2982`). So all three new dispatch arms match `NodeOrToken::Node`, exactly like the existing `"str"` arm — unlike `"<ident>"`, which is a bare token.
2. **`Term.mkInstMVar` does not exist in leanr.** `app/args.rs:618`'s `mk_inst_mvar` is `ElabAppArgs`'s own same-named `where`-binding (`App.lean:919-923`): mint a synthetic mvar, push it on `instMVars`, `addNewArg`, **defer** synthesis. `Term.mkInstMVar` (`TermElabM.lean:1925-1931`) is a different function: it calls `synthesizeInstMVarCore` *eagerly* and registers `.typeClass` only `unless` that succeeds. `num` and `scientific` need the latter. Both its halves already sit on `TermElabM` (`synthesize_inst_mvar_core`, `register_synthetic_mvar`), so Task 5 adds a short new function; the two stay distinct.
3. **`isClass?` needs no accessor.** `synthesizeUsingDefaultPrio`'s two early-outs (`isClass? → none`, `getDefaultInstances → []`, `SyntheticMVars.lean:115-119`) both `return false`, and a head constant with a non-empty default-instance list is necessarily a class. P2a's `pending_class_name` (`synthetic.rs:620`) already computes the head constant. Faithful by fusion, not a seam.
4. **`mk_raw_nat_lit` needs no accessor either.** `Store::expr_lit_nat` is already `pub` (`leanr_kernel/src/bank/terms.rs:535`) and `MetaCtx::store_mut` is already `pub` — `builtin/lit.rs`'s existing `elab_str` reaches `expr_lit_str` exactly that way. The spec's § Accessor ledger lists `mk_raw_nat_lit` on P3's row; Task 4 corrects it, the same way P2a's Task 1 corrected `with_assignable_synthetic_opaque` off P2a's row.
5. **`config.rs` has a build-breaking size assert.** `ASSERT_CONFIG_SIZE` (`crates/leanr_meta/src/config.rs:97`) fails the build when a `Config` field is added, and the module doc names `assign_synthetic_opaque` as one of the three fields that "arrive with the features that consult them". Task 4 is that feature, so it must update both the assert and `toKey`.
6. **`commitWhen` in `TermElabM` backtracks elaborator state, not just the mctx.** `Term.SavedState` is `Meta.SavedState × Term.State`, and both P3 users of `commitWhen` (`synthesizePendingInstMVar'`, `synthesizeUsingDefaultInstance`) can register synthetic mvars before failing. `MetaCtx::checkpoint`/`rollback` alone is therefore **not** sufficient; Task 5 builds `TermElabM::commit_when`, which snapshots `pending_mvars`, `synthetic_mvars` and `mvar_error_infos` too.
7. **`Elab0.lean`'s `Nat` is a real inductive with `zero`/`succ` constructors** (`tests/fixtures/elab/Elab0.lean:113-116`), which is the shape Lean's kernel special-cases literals against by *name*. This is what makes a `natVal` literal viable in a prelude-mode fixture at all. It is still measured in Task 3 rather than assumed — this is the first literal the elab fixture mints.
8. **The oracle's own `elabCharLit` never reads `Char`'s shape** (`BuiltinTerm.lean:248-252`): it emits `mkApp (mkConst ``Char.ofNat) (mkRawNatLit c)` with no expected type and no typecheck. The real `Char.ofNat` is `dite` over `BitVec.ofNatLT`/`UInt32` (`Init/Prelude.lean:2886-2890`), unreachable in prelude mode. An opaque carrier emits a byte-identical `Expr`.

---

## File Structure

**Created:**

| File | Responsibility |
|---|---|
| `crates/leanr_elab/src/synthetic/mod.rs` | the module's doc comment and `pub use` re-exports, so `leanr_elab::synthetic::*` keeps its current public path |
| `crates/leanr_elab/src/synthetic/state.rs` | `SavedContext`, `SyntheticMVarKind`, `SyntheticMVarDecl`, `MVarErrorKind`, `MVarErrorInfo`, `register_synthetic_mvar`, `synthetic_mvar_decl`, `mark_as_resolved`, the two `register_mvar_error_*` helpers, `save_context`/`with_saved_context`, `without_postponing`; Task 5 adds `mk_inst_mvar` and `commit_when` |
| `crates/leanr_elab/src/synthetic/ladder.rs` | `PostponeBehavior`, `step_with`, `synthesize_synthetic_mvars_step`, `synthesize_synthetic_mvar`, `synthesize_inst_mvar_core`, `synthesize_pending_inst_mvar`, `contains_pending_mvar`, `synthesize_synthetic_mvars`, `synthesize_synthetic_mvars_no_postponing`, `resume_postponed`, `with_synthesize`, `with_synthesize_light`, `with_synthesize_impl`, `process_postponed_universe_constraints` |
| `crates/leanr_elab/src/synthetic/report.rs` | `report_stuck_synthetic_mvars` and its priority sort; `pending_class_name` (its only other caller moves to `default_inst.rs`, which is a sibling) |
| `crates/leanr_elab/src/synthetic/default_inst.rs` | **new (Task 5)** — `synthesize_using_default`, `synthesize_some_using_default_prio`, `synthesize_using_default_prio`, `synthesize_using_default_instance`, `synthesize_using_instances`, `synthesize_pending_inst_mvar_committed`, `synthesize_some_using_default_qm`, `synthesize_pending` |
| `crates/leanr_elab/src/builtin/lit/mod.rs` | **(Task 6)** — the four literal elaborators (`elab_str`, `elab_num`, `elab_char`, `elab_scientific`) and their shared helpers (`mk_fresh_type_mvar_for`, `const_with_level`, `mk_raw_nat_lit`, `app_n`) |
| `crates/leanr_elab/src/builtin/lit/decode.rs` | **(Task 6)** — the literal-token decoders (`decode_string_literal`, `decode_quoted_char`, `hex_digit`, `decode_nat_literal`, `decode_char_literal`, `decode_scientific_literal`) and their unit tests |

**Deleted:**

| File | Reason |
|---|---|
| `crates/leanr_elab/src/synthetic.rs` | replaced by `synthetic/` (Task 1) |
| `crates/leanr_elab/src/builtin/lit.rs` | replaced by `builtin/lit/` (Task 6) |

**Modified:**

| File | Change |
|---|---|
| `crates/leanr_meta/src/infer.rs` | `get_level` becomes `pub(crate)` so `level.rs` can compose `get_dec_level` (Task 4) |
| `crates/leanr_meta/src/level.rs` | add `pub fn get_dec_level` (Task 4) |
| `crates/leanr_meta/src/metactx.rs` | `checkpoint`/`rollback` and `MetaSnapshot` become `pub`; add `is_prop` forwarder and `with_assignable_synthetic_opaque` (Task 4) |
| `crates/leanr_meta/src/instances.rs` | add `pub fn default_instance_priorities` (Task 4) |
| `crates/leanr_meta/src/config.rs` | add `assign_synthetic_opaque` field, update `ASSERT_CONFIG_SIZE` and the cache key (Task 4) |
| `crates/leanr_meta/src/synth.rs` | generalize `refresh_instance_levels` / `get_subgoals` into public `mk_const_with_fresh_mvar_levels` / `forall_meta_telescope_reducing`; `get_subgoals` becomes a caller (Task 4) |
| `crates/leanr_meta/src/lib.rs` | re-export `MetaSnapshot` (Task 4) |
| `crates/leanr_elab/src/lib.rs` | `pub mod synthetic;` stays (directory module); deferral-ledger update (Tasks 1, 8) |
| `crates/leanr_elab/src/error.rs` | `NumeralIsNotData` (both `getDecLevel` failure branches), `IllFormedLiteral` (Task 6) |
| `crates/leanr_elab/src/dispatch.rs` | register `num` / `char` / `scientific`; deferral-table update (Tasks 6, 7, 8) |
| `crates/leanr_elab/src/builtin/mod.rs` | `pub mod lit;` stays (directory module) (Task 6) |
| `crates/leanr_elab/tests/synthetic_smoke.rs` | replace the two rung-3 seam tests with real behavior tests; add the two ordering tests (Task 5) |
| `crates/leanr_elab/tests/support/mod.rs` | helpers for the ordering tests and the literal harness (Tasks 5, 6) |
| `crates/leanr_elab/tests/seam_audit.rs` | drop the retired rung-3 seam; add the retired-label gate (Task 8) |
| `tests/fixtures/elab/Elab0.lean` | second instances (Task 2); the literal scaffold (Task 3) |
| `tests/fixtures/elab/Elab0.olean` | rebuilt whenever `Elab0.lean` changes (Tasks 2, 3) |
| `tests/fixtures/elab/dump_elab.lean` | new query lists (Tasks 6, 7) |
| `tests/fixtures/elab/elab-queries.jsonl` | regenerated, never hand-edited (Tasks 2, 3, 6, 7) |
| `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` | § Accessor ledger correction (Task 4) |

---

## Task 1: Split `synthetic.rs` into `synthetic/`

A **pure move**. No behavior changes, no signature changes, no new code. The deliverable is that the 804-line file becomes four files under 300 lines each and every committed oracle record stays byte-identical — done *before* Task 5 adds ~250 more lines to the same module.

**Files:**
- Create: `crates/leanr_elab/src/synthetic/mod.rs`
- Create: `crates/leanr_elab/src/synthetic/state.rs`
- Create: `crates/leanr_elab/src/synthetic/ladder.rs`
- Create: `crates/leanr_elab/src/synthetic/report.rs`
- Delete: `crates/leanr_elab/src/synthetic.rs`
- Test: `crates/leanr_elab/tests/synthetic_smoke.rs` (unchanged — it is the gate)

**Interfaces:**
- Consumes: nothing new.
- Produces: **exactly the paths that exist today.** `leanr_elab::synthetic::{PostponeBehavior, SavedContext, SyntheticMVarKind, SyntheticMVarDecl, MVarErrorKind, MVarErrorInfo}` must all still resolve, because `elab.rs:60`/`:64` name `crate::synthetic::SyntheticMVarDecl` and `crate::synthetic::MVarErrorInfo` in `TermElabM`'s own field types, and `synthetic_smoke.rs:9` imports `PostponeBehavior` and `SyntheticMVarKind` from the crate's public path. Every `impl<'e> TermElabM<'e>` method keeps its current name and visibility.

- [ ] **Step 1: Record the byte-identical baseline**

The gate for a pure move is "nothing changed", so capture what "nothing" means before touching anything.

```bash
cd /workspace
cargo test --package leanr_elab 2>&1 | tail -20
sha256sum tests/fixtures/elab/elab-queries.jsonl
wc -l crates/leanr_elab/src/synthetic.rs
```

Expected: all `leanr_elab` tests pass; note the JSONL hash and the line count (804) — Step 6 compares against both.

- [ ] **Step 2: Create the directory module**

Create `crates/leanr_elab/src/synthetic/mod.rs`. It carries the module doc that `synthetic.rs:1-15` carries today, verbatim, plus one added paragraph explaining the split, and re-exports every public type so `leanr_elab::synthetic::X` paths are unchanged:

```rust
//! `synthesizeSyntheticMVars` — the elaborator's scheduler. Oracle:
//! `Lean/Elab/SyntheticMVars.lean`, plus the state and registration
//! helpers from `Lean/Elab/Term/TermElabM.lean`.
//!
//! M4b-2 deliberately shipped no scheduler because no closed term in its
//! grammar created a synthetic mvar. M4b-3 P1 created the first ones
//! (implicit-argument mvars) but drained none. This module is where
//! every synthetic mvar leanr creates is finally either solved, resumed,
//! or reported stuck.
//!
//! The state lives on `TermElabM` (see `elab.rs`), mirroring the
//! oracle's `Term.State`/`Term.Context` one-to-one; only the `impl`
//! block is here. A nested sub-struct was rejected: every step touching
//! both the table and `&mut self` would need a `mem::take`/restore dance
//! for no structural gain (design spec § P2a).
//!
//! **Layout (M4b-3 P3 task 1).** P2a shipped this as one 804-line file.
//! It splits here, BEFORE P3's `synthesizeUsingDefault*` family adds
//! ~250 more lines to it (design spec § Amendment 2, item 3), along the
//! oracle's own seams:
//!
//! ```text
//!   state.rs ......... the decl/error tables and their registration
//!                      (`TermElabM.lean`'s half)
//!   ladder.rs ........ the step, the five rungs, `withSynthesize`,
//!                      `resumePostponed` (`SyntheticMVars.lean`'s
//!                      scheduler half)
//!   report.rs ........ stuck reporting and its priority sort
//!   default_inst.rs .. rung 3's real body (P3 task 5)
//! ```
//!
//! Every `impl<'e> TermElabM<'e>` block below is a continuation of the
//! same inherent impl; Rust allows one type's inherent methods to be
//! split across sibling modules of the defining crate, so the split
//! changes no call site and no visibility.

mod ladder;
mod report;
pub mod state;

pub use ladder::PostponeBehavior;
pub use state::{
    MVarErrorInfo, MVarErrorKind, SavedContext, SyntheticMVarDecl, SyntheticMVarKind,
};
```

- [ ] **Step 3: Move the state half into `state.rs`**

Move, verbatim and in source order, from `synthetic.rs`:

- `SavedContext` (lines 40-64) and `SyntheticMVarKind` (66-85), `SyntheticMVarDecl` (87-99), `MVarErrorKind` (101-111), `MVarErrorInfo` (113-121) — all five type definitions with their full doc comments.
- From the `impl<'e> TermElabM<'e>` block: `register_synthetic_mvar` (128), `synthetic_mvar_decl` (140), `mark_as_resolved` (148), `register_mvar_error_implicit_arg_info` (153), `register_mvar_error_hole_info` (167), `save_context` (177), `with_saved_context` (191), `without_postponing` (203).

Head the file with the imports those items actually use and a two-line module doc:

```rust
//! The scheduler's STATE: the synthetic-mvar decl table, the mvar-error
//! table, and the registration/scoping helpers. Oracle:
//! `Lean/Elab/Term/TermElabM.lean`. The scheduling itself is `ladder.rs`.

use leanr_kernel::bank::{ExprId, NameId};
use leanr_meta::MVarId;

use crate::dispatch::SynElem;
use crate::elab::TermElabM;

impl<'e> TermElabM<'e> {
    // ... the eight moved methods, verbatim ...
}
```

Do not reformat, rewrite, or "improve" any moved doc comment. `cargo fmt` may adjust indentation; nothing else changes.

- [ ] **Step 4: Move the ladder half into `ladder.rs` and the reporter into `report.rs`**

`ladder.rs` takes `PostponeBehavior` (26-38) and, from the impl block, `step_with` (220), `synthesize_synthetic_mvars_step` (265), `synthesize_synthetic_mvar` (281), `synthesize_inst_mvar_core` (334), `synthesize_pending_inst_mvar` (420), `contains_pending_mvar` (431), `synthesize_synthetic_mvars` (473), `synthesize_synthetic_mvars_no_postponing` (523), `resume_postponed` (537), `synthesize_using_default` (595), `with_synthesize` (717), `with_synthesize_light` (738), `with_synthesize_impl` (759), `process_postponed_universe_constraints` (792).

`synthesize_using_default`'s P2a seam body moves here **unchanged** — Task 5 replaces it, not this task.

`report.rs` takes `pending_class_name` (620) and `report_stuck_synthetic_mvars` (654). `pending_class_name` is `fn` (private); it is called by `synthesize_using_default` in `ladder.rs` today and by `default_inst.rs` from Task 5 on, so it becomes `pub(crate) fn` in `report.rs`. That visibility widening is the **only** non-verbatim change in this task; note it in the function's doc comment:

```rust
    /// The head constant of a pending typeclass goal, if it has one.
    /// `Wrap ?m` -> `Wrap`; a goal whose head is not a constant has no
    /// class name and cannot have default instances.
    ///
    /// `pub(crate)` rather than private since M4b-3 P3 task 1: the split
    /// put its two callers (`ladder.rs`'s rung 3, and `default_inst.rs`
    /// from task 5 on) in sibling modules. The body is unchanged.
    pub(crate) fn pending_class_name(&mut self, mvar_id: MVarId) -> Result<Option<NameId>, ElabError> {
```

Then delete `crates/leanr_elab/src/synthetic.rs`.

- [ ] **Step 5: Build and run the whole `leanr_elab` suite**

Run: `cargo test --package leanr_elab`
Expected: PASS, with the same test count as Step 1. A compile error here is almost always a missing `use` in one of the four new files — add the import, never a re-export shim or a `pub` widening beyond `pending_class_name`.

- [ ] **Step 6: Verify the move changed nothing observable**

```bash
cd /workspace
sha256sum tests/fixtures/elab/elab-queries.jsonl
wc -l crates/leanr_elab/src/synthetic/*.rs
git diff --stat -- tests/fixtures/elab/
```

Expected: the JSONL hash matches Step 1 exactly; `git diff` over `tests/fixtures/elab/` is **empty** (this task touches no fixture); each of the four files is under 300 lines. If `ladder.rs` is over 300, that is expected and acceptable — it holds the scheduler proper; do not split it further in this task.

- [ ] **Step 7: Commit**

```bash
cd /workspace
mise run fmt && mise run lint && mise run test
git add crates/leanr_elab/src/synthetic crates/leanr_elab/src/synthetic.rs
git commit -m "refactor(elab): split synthetic.rs into synthetic/{state,ladder,report}

Pure move, no behavior change: 804 lines become four files ahead of
P3's synthesizeUsingDefault family (design spec § Amendment 2 item 3).
The only non-verbatim change is pending_class_name becoming pub(crate),
since the split put its two callers in sibling modules. Committed
oracle records are byte-identical."
```

---

## Task 2: A second instance per fixture class

The first of P2a's two deferred follow-ups, and deliberately **second in this plan** so that any divergence it surfaces lands before the literal work is designed around a fixture that may be about to change.

Today `Wrap`, `Pair` and `Dflt` each have exactly one candidate instance. The reviewer's hypothesis is that `tc/useWrapAscribed` and `tc/pairBoth` reach the oracle's answer by a *different route* than the oracle takes — leanr resolving eagerly from the sole candidate, where the oracle keeps the goal stuck and lets the argument fix the type parameter. A second instance separates "leanr got the right answer" from "leanr got it for the right reason".

**Files:**
- Modify: `tests/fixtures/elab/Elab0.lean`
- Modify: `tests/fixtures/elab/Elab0.olean` (rebuilt)
- Modify: `tests/fixtures/elab/elab-queries.jsonl` (regenerated)
- Test: `crates/leanr_elab/tests/oracle_elab.rs` (unchanged — it is the gate)

**Interfaces:**
- Consumes: nothing from Task 1.
- Produces: the fixture constants `instWrapUnit : Wrap Unit`, `instPairNatUnit : Pair Nat Unit`, `instDfltUnit : Dflt Unit`. Later tasks rely only on `Wrap`/`Pair`/`Dflt`/`NoInst` keeping their current *names and arities*; nothing depends on the instance count.

- [ ] **Step 1: Capture the pre-change records**

```bash
cd /workspace
cp tests/fixtures/elab/elab-queries.jsonl /tmp/claude-1000/-workspace/*/scratchpad/elab-queries.before.jsonl
cargo test --release --package leanr_elab --test oracle_elab
```

Expected: PASS. The copy is the diff base for Step 4 — the point of this task is to *read* that diff, not to accept it.

- [ ] **Step 2: Add the second instances**

Edit `tests/fixtures/elab/Elab0.lean`. After `instWrapNat` (currently line 184), after `instPairNatNat` (190), and after `instDfltNat` (200-202), add three instances over `Unit` (already declared at line 25, `abbrev Unit : Type := PUnit`, with `Unit.unit` at line 26 — no new type is needed):

```lean
-- M4b-3 P3 task 2: a SECOND candidate instance per class. With exactly
-- one candidate, `tc/useWrapAscribed` and `tc/pairBoth` could reach the
-- oracle's answer by a different route than the oracle takes — leanr
-- resolving eagerly from the sole candidate where the oracle keeps the
-- goal stuck and lets the argument fix the type parameter. A second
-- candidate separates "right answer" from "right reason".
--
-- `Unit` (not `String`): `String` is an `axiom` here with no
-- constructor, so `Dflt String` has no inhabitant to give `val`.
-- `Unit`/`Unit.unit` are real and already in the scaffold.
--
-- `NoInst` deliberately keeps ZERO instances — `synthetic_smoke.rs`'s
-- `unsolvable_instance_is_a_synthesis_failure` asserts its `.none` arm.
-- None of the three gains a `@[default_instance]`: line 158-163 above
-- records why that would break the stuck-path tests.
instance instWrapUnit : Wrap Unit where
  wrap := fun u => u

instance instPairNatUnit : Pair Nat Unit where
  mk2 := fun x _ => x

instance instDfltUnit : Dflt Unit where
  val := Unit.unit
```

Place each immediately after its class's existing instance, so the file still reads class-by-class.

- [ ] **Step 3: Rebuild the olean and regenerate**

```bash
cd /workspace
mise run elan:bootstrap   # once per machine; a no-op if already bootstrapped
(cd tests/fixtures/elab && lean Elab0.lean -o Elab0.olean)
mise run fixtures:regen-elab
```

Expected: `lean` exits 0 (a failure here means one of the three instances does not typecheck — fix the fixture, do not weaken it), and `elab-queries.jsonl` is rewritten.

- [ ] **Step 4: Read the record diff — this is the deliverable**

```bash
cd /workspace
diff /tmp/claude-1000/-workspace/*/scratchpad/elab-queries.before.jsonl tests/fixtures/elab/elab-queries.jsonl
```

Two outcomes, and they take different paths:

- **Empty diff.** The oracle emits the same terms with two candidates as with one. Go to Step 5.
- **Non-empty diff.** For each changed record, decide whether the *oracle's new output* is the right answer for the new fixture (it always is — the oracle is the definition) and whether leanr still matches it. A record whose `exp` changed is a fixture-semantics change, which is expected and fine. **Do not** hand-edit the JSONL; the regenerated file is the new truth. Record the changed ids in the commit message.

- [ ] **Step 5: Run the gate — this is where a real divergence surfaces**

Run: `cargo test --release --package leanr_elab --test oracle_elab`

Two outcomes:

- **PASS.** The hypothesis was wrong: leanr was already taking the oracle's route. Note that in the commit message and move on — the evidentiary value is exactly that this is now *proven* rather than assumed.
- **FAIL.** The hypothesis was right. The failing record's `exp` is what the oracle emits; leanr emits something else. The fix belongs in P2a's `synthesize_inst_mvar_core` (`crates/leanr_elab/src/synthetic/ladder.rs`, moved there by Task 1) — the arm that decides between "solved", "not ready" and "failed" when more than one candidate matches. Read `TermElabM.lean:1255-1290` and fix leanr to match. Do **not** revert the fixture, and do **not** relax the gate.

- [ ] **Step 6: Run the full suite**

Run: `cargo test --package leanr_elab && cargo test --package leanr_meta`
Expected: PASS. `synthetic_smoke.rs`'s `solvable_instance_is_synthesized_and_assigned` uses `support::wrap_of_nat` (a *ground* `Wrap Nat` goal), which stays uniquely solvable with two candidates; `unsolvable_instance_is_a_synthesis_failure` uses `NoInst`, untouched. If either fails, the failure is real — investigate before proceeding.

- [ ] **Step 7: Commit**

```bash
cd /workspace
mise run fmt && mise run lint && mise run test
git add tests/fixtures/elab/Elab0.lean tests/fixtures/elab/Elab0.olean tests/fixtures/elab/elab-queries.jsonl crates/leanr_elab/src
git commit -m "test(elab): second candidate instance for Wrap/Pair/Dflt

P2a deferral, folded into P3 per design spec § Amendment 2 item 3. With
one candidate per class, tc/useWrapAscribed and tc/pairBoth could reach
the oracle's answer by a different route than the oracle takes; a second
candidate separates right-answer from right-reason. NoInst keeps zero
instances and none of the three gains a @[default_instance]."
```

---

## Task 3: The literal scaffold in `Elab0.lean`

Grow the fixture so `num`, `char` and `scientific` have something to elaborate against. Nothing in `leanr_elab` changes; the deliverable is a rebuilt `Elab0.olean` whose new constants are reachable and whose addition leaves every existing record byte-identical.

**Files:**
- Modify: `tests/fixtures/elab/Elab0.lean`
- Modify: `tests/fixtures/elab/Elab0.olean` (rebuilt)
- Modify: `tests/fixtures/elab/elab-queries.jsonl` (regenerated; expected byte-identical)
- Test: `crates/leanr_elab/tests/support/mod.rs` + `crates/leanr_elab/tests/synthetic_smoke.rs`

**Interfaces:**
- Consumes: Task 2's fixture.
- Produces: fixture constants `Bool`, `Bool.true`, `Bool.false`, `OfNat`, `OfNat.ofNat`, `instOfNatNat`, `OfScientific`, `OfScientific.ofScientific`, `instOfScientificTag`, `Char`, `Char.ofNat`, `Tag`, `Tag.mk`, `instOfNatTag`. Tasks 5-7 name these exact strings.

- [ ] **Step 1: Write the failing test**

Append to `crates/leanr_elab/tests/synthetic_smoke.rs`:

```rust
/// M4b-3 P3 task 3: the literal scaffold is reachable in the fixture
/// env. Every constant the three literal elaborators mint by NAME must
/// resolve — an unresolvable name would surface as `UnknownIdent` deep
/// inside `elab_num` in task 6, far from its cause.
///
/// `Char`/`Char.ofNat` are opaque carriers (`axiom`), not the real
/// definitions: `elabCharLit` (`BuiltinTerm.lean:248-252`) never reads
/// `Char`'s shape, and the real `Char.ofNat` is `dite` over
/// `BitVec.ofNatLT`/`UInt32` (`Init/Prelude.lean:2886-2890`), which a
/// prelude-mode fixture cannot reach. The emitted `Expr` is identical
/// either way (plan § Measured facts, item 8).
#[test]
fn literal_scaffold_constants_resolve_in_the_fixture_env() {
    support::with_app_harness("Nat.zero", |app| {
        for name in [
            "Bool",
            "OfNat",
            "OfNat.ofNat",
            "instOfNatNat",
            "OfScientific",
            "OfScientific.ofScientific",
            "instOfScientificTag",
            "Char",
            "Char.ofNat",
            "Tag",
            "instOfNatTag",
        ] {
            assert!(
                support::fixture_declares(app, name),
                "Elab0 must declare {name} for M4b-3 P3"
            );
        }
    });
}

/// The `natVal` literal is viable against the fixture's own `Nat`.
///
/// Lean's kernel special-cases literals by the NAME `Nat` with
/// `Nat.zero`/`Nat.succ` constructors, which `Elab0.lean:113-116`
/// matches — but this is the first literal the elab fixture mints, so
/// it is MEASURED here rather than assumed (design spec § P3).
#[test]
fn a_nat_literal_infers_as_the_fixture_nat() {
    support::with_app_harness("Nat.zero", |app| {
        let base = app.elab.view.store;
        let lit = app
            .elab
            .mctx
            .store_mut()
            .expr_lit_nat(Some(base), &leanr_kernel::Nat::from(42u64))
            .expect("nat literal interns");
        let ty = app.elab.mctx.infer_type(lit).expect("literal has a type");
        let nat = support::fixture_const(app, "Nat");
        assert!(
            app.elab.mctx.is_def_eq(ty, nat).expect("defeq runs"),
            "Expr.lit (.natVal 42) must infer as the fixture's own Nat"
        );
    });
}
```

Add the two helpers to `crates/leanr_elab/tests/support/mod.rs`, next to the existing `wrap_of_nat`/`dflt_of_nat` fixture helpers:

```rust
/// The `ExprId` of a fixture constant with no universe arguments,
/// resolved by dotted source name exactly as `app::head::elab_ident_head`
/// does. Panics if the fixture does not declare it — a test helper's
/// contract, not elaborator code.
pub fn fixture_const(
    app: &mut leanr_elab::app::state::AppElab,
    name: &str,
) -> leanr_kernel::bank::ExprId {
    let base = app.elab.view.store;
    let mut id: Option<leanr_kernel::bank::NameId> = None;
    for part in name.split('.') {
        let store = app.elab.mctx.store_mut();
        let s = store.intern_str(Some(base), part).expect("intern");
        id = Some(store.name_str(Some(base), id, s).expect("name"));
    }
    let cname = id.expect("non-empty name");
    assert!(
        app.elab.view.get(cname).is_some(),
        "fixture must declare {name}"
    );
    let levels = app
        .elab
        .mctx
        .store_mut()
        .intern_level_list(None, &[])
        .expect("empty level list");
    app.elab
        .mctx
        .store_mut()
        .expr_const(Some(base), Some(cname), levels)
        .expect("const")
}

/// Whether the fixture env declares `name` (dotted source form).
pub fn fixture_declares(app: &mut leanr_elab::app::state::AppElab, name: &str) -> bool {
    let base = app.elab.view.store;
    let mut id: Option<leanr_kernel::bank::NameId> = None;
    for part in name.split('.') {
        let store = app.elab.mctx.store_mut();
        let s = store.intern_str(Some(base), part).expect("intern");
        id = Some(store.name_str(Some(base), id, s).expect("name"));
    }
    app.elab.view.get(id.expect("non-empty name")).is_some()
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test --package leanr_elab --test synthetic_smoke literal_scaffold a_nat_literal`
Expected: FAIL — `literal_scaffold_constants_resolve_in_the_fixture_env` panics with `Elab0 must declare Bool for M4b-3 P3`.

- [ ] **Step 3: Add the scaffold**

Append to `tests/fixtures/elab/Elab0.lean`, after the class/instance block Task 2 extended:

```lean
-- === M4b-3 P3 corpus: literals and default instances ===
--
-- Copied VERBATIM from `Init` where the shape is what the emitted
-- `Expr` references (`Bool`, `OfNat`, `instOfNatNat`, `OfScientific`);
-- opaque carriers where it is not (`Char`). See the design spec's § P3
-- for the reasoning behind each choice.

-- `Bool` is needed for `scientific`: `elabScientificLit` emits the
-- exponent SIGN as `toExpr sign` (`BuiltinTerm.lean:243`), a `Bool`
-- literal. Verbatim from `Init/Prelude.lean`.
inductive Bool : Type where
  | false : Bool
  | true : Bool

-- Verbatim from `Init/Prelude.lean:1270-1279`, including the
-- `@[default_instance 100]` priority. That priority is load-bearing:
-- `instDfltNat` above carries a bare `@[default_instance]` (priority
-- 1000) and `instOfNatTag` below carries 500, so the environment has
-- THREE distinct default-instance priorities and
-- `synthesizeUsingDefault`'s descending-priority walk is
-- differentially observable rather than vacuous (design spec § P3).
class OfNat (α : Type u) (_ : Nat) where
  ofNat : α

@[default_instance 100]
instance instOfNatNat (n : Nat) : OfNat Nat n where
  ofNat := n

-- `Tag`: a fixture-local SECOND numeric type, standing in for the
-- design spec's original `(42 : Int)` corpus example. `Int` needs
-- `Init.Data.Int`, unreachable in prelude mode; what the record
-- actually tests is "a numeral against a non-default expected type",
-- which any second `OfNat` carrier provides. Its instance sits at a
-- THIRD priority so the priority walk has more than two rungs to order.
structure Tag where
  raw : Nat

@[default_instance 500]
instance instOfNatTag (n : Nat) : OfNat Tag n where
  ofNat := Tag.mk n

-- Verbatim from `Init/Data/OfScientific/Basic.lean:20-30`.
class OfScientific (α : Type u) where
  ofScientific : Nat -> Bool -> Nat -> α

instance instOfScientificTag : OfScientific Tag where
  ofScientific := fun m _ _ => Tag.mk m

-- OPAQUE CARRIERS, deliberately (design spec § P3; plan § Measured
-- facts, item 8). `elabCharLit` emits `Char.ofNat (rawNatLit c)`
-- without ever reading `Char`'s shape, using no expected type and
-- performing no typecheck, so the emitted `Expr` is byte-identical to
-- what the real definition would produce. The real `Char` is a
-- structure over `UInt32` with a validity proof and the real
-- `Char.ofNat` is `dite` over `BitVec.ofNatLT` — `Fin`, `BitVec`,
-- `UInt32`, `Nat.lt`, `decide` and `Or` would all have to come with
-- them. Same "minimal opaque stand-in suffices" reasoning as
-- `axiom String` above; grow to the real definitions in whichever
-- later slice first needs `Char`'s actual shape.
axiom Char : Type
axiom Char.ofNat : Nat -> Char
```

- [ ] **Step 4: Rebuild the olean and run the tests**

```bash
cd /workspace
(cd tests/fixtures/elab && lean Elab0.lean -o Elab0.olean)
cargo test --package leanr_elab --test synthetic_smoke literal_scaffold a_nat_literal
```

Expected: PASS, both. If `lean` rejects the fixture, fix the fixture — most likely `structure Tag` needs `set_option genCtorIdx false in` if the auto-generated `ctorIdx` machinery trips the same prelude gap `Nat`/`List` hit (`Elab0.lean:98-112` documents that tripwire); a single-constructor structure should not, but if it does, add the option with a comment citing that block.

If `a_nat_literal_infers_as_the_fixture_nat` fails, **stop**. That is the one risk this task exists to measure: it means `Expr.lit (.natVal _)` does not type against the fixture's `Nat`, and the whole `num` design needs revisiting before Task 6 is written. Report it rather than working around it.

- [ ] **Step 5: Regenerate and confirm the empty diff**

```bash
cd /workspace
cp tests/fixtures/elab/elab-queries.jsonl /tmp/claude-1000/-workspace/*/scratchpad/elab-queries.task3.before.jsonl
mise run fixtures:regen-elab
diff /tmp/claude-1000/-workspace/*/scratchpad/elab-queries.task3.before.jsonl tests/fixtures/elab/elab-queries.jsonl
```

Expected: **empty diff**. This task adds declarations and no queries, so no record may change. In particular `@[default_instance 100] instOfNatNat` must not perturb the existing typeclass records: rung 3's guard fires only for a pending `TypeClass` mvar whose class has default instances, and no existing record produces an `OfNat` goal. A non-empty diff here is a finding to run down, not a fixture to update.

- [ ] **Step 6: Run the full gate and commit**

```bash
cd /workspace
cargo test --release --package leanr_elab --test oracle_elab
mise run fmt && mise run lint && mise run test
git add tests/fixtures/elab crates/leanr_elab/tests
git commit -m "test(elab): literal + default-instance scaffold in Elab0

Bool/OfNat/instOfNatNat/OfScientific verbatim from Init (their shape is
what the emitted Expr references); Char/Char.ofNat as opaque carriers
(elabCharLit never reads Char's shape and the real definition needs
BitVec/UInt32); Tag as a fixture-local second numeric type replacing the
unreachable (42 : Int). Three distinct default-instance priorities
(100/500/1000) make the descending-priority walk observable. Existing
records byte-identical."
```

---

## Task 4: `leanr_meta` accessors and the `synth.rs` generalization

**Files:**
- Modify: `crates/leanr_meta/src/infer.rs` (visibility of `get_level`)
- Modify: `crates/leanr_meta/src/level.rs` (add `get_dec_level`)
- Modify: `crates/leanr_meta/src/metactx.rs` (`checkpoint`/`rollback`/`MetaSnapshot` public; `is_prop`; `with_assignable_synthetic_opaque`)
- Modify: `crates/leanr_meta/src/instances.rs` (add `default_instance_priorities`)
- Modify: `crates/leanr_meta/src/config.rs` (add `assign_synthetic_opaque`)
- Modify: `crates/leanr_meta/src/synth.rs` (generalize two private helpers)
- Modify: `crates/leanr_meta/src/lib.rs` (re-export `MetaSnapshot`)
- Modify: `crates/leanr_meta/src/assign.rs` (honour the new config flag)
- Modify: `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` (§ Accessor ledger)
- Test: `crates/leanr_meta/src/level.rs`, `crates/leanr_meta/src/instances.rs`, `crates/leanr_meta/src/synth.rs` (each module's existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: nothing from Tasks 1-3.
- Produces:
  - `MetaCtx::get_dec_level(&mut self, ty: ExprId) -> Result<LevelId, MetaError>`
  - `MetaCtx::is_prop(&mut self, e: ExprId) -> Result<bool, MetaError>`
  - `MetaCtx::checkpoint(&self) -> MetaSnapshot` and `MetaCtx::rollback(&mut self, snap: MetaSnapshot)`, both `pub`; `leanr_meta::MetaSnapshot` re-exported
  - `MetaCtx::default_instance_priorities(&self) -> Vec<usize>` — descending, distinct, across all classes
  - `MetaCtx::with_assignable_synthetic_opaque<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R`
  - `MetaCtx::mk_const_with_fresh_mvar_levels(&mut self, val: ExprId) -> Result<ExprId, MetaError>`
  - `MetaCtx::forall_meta_telescope_reducing(&mut self, ty: ExprId) -> Result<(Vec<ExprId>, Vec<BinderInfo>, ExprId), MetaError>`

**Spec-ledger correction to make in this task.** § Accessor ledger's P3 row lists `mk_raw_nat_lit`. It is not needed: `Store::expr_lit_nat` is already `pub` (`leanr_kernel/src/bank/terms.rs:535`) and `MetaCtx::store_mut` is already `pub`, which is exactly how `builtin/lit.rs`'s existing `elab_str` reaches `expr_lit_str`. Strike it from the row in the same commit, with that one-sentence reason — the same discipline P2a's Task 1 applied to `with_assignable_synthetic_opaque`.

- [ ] **Step 1: Write the failing tests**

Append to `crates/leanr_meta/src/level.rs`'s `#[cfg(test)] mod tests`:

```rust
    /// oracle: `getDecLevel` (`Lean/Meta/DecLevel.lean:73-76`) — infer
    /// the type's own level, normalize, then DECREMENT by one. `Type u`
    /// is `Sort (u+1)`, so a value type at `Sort 1` (`Type`) has
    /// dec-level `0`. This is what `elabNumLit` needs for
    /// `OfNat.{u}`'s universe argument.
    #[test]
    fn get_dec_level_decrements_a_concrete_sort() {
        with_prelude0_ctx(|ctx| {
            // `Type` = `Sort 1`; its own type is `Sort 2`, so getLevel
            // yields 2 and decLevel yields 1.
            let zero = ctx.store_mut().level_zero(None).expect("zero");
            let one = ctx.store_mut().level_succ(None, zero).expect("succ");
            let ty = ctx.store_mut().expr_sort(None, one).expect("Sort 1");
            let u = ctx.get_dec_level(ty).expect("Sort 1 has a dec level");
            assert_eq!(u, one, "getDecLevel (Sort 1) = 1");
        });
    }

    /// A `Prop`-valued type has level `0`, which cannot be decremented:
    /// the oracle throws "invalid universe level". `elabNumLit` catches
    /// exactly this to produce its "numerals are data" error.
    #[test]
    fn get_dec_level_rejects_prop() {
        with_prelude0_ctx(|ctx| {
            let zero = ctx.store_mut().level_zero(None).expect("zero");
            let prop = ctx.store_mut().expr_sort(None, zero).expect("Sort 0");
            assert!(
                ctx.get_dec_level(prop).is_err(),
                "Sort 0's level is 0 and cannot be decremented"
            );
        });
    }
```

Append to `crates/leanr_meta/src/instances.rs`'s `#[cfg(test)] mod tests`:

```rust
    /// oracle: `getDefaultInstancesPriorities` — the GLOBAL set of
    /// default-instance priorities, DESCENDING and distinct, across
    /// every class. `default_instances` is per-class and cannot produce
    /// it, which is why this is a new accessor rather than a forwarder.
    #[test]
    fn default_instance_priorities_are_descending_and_distinct() {
        with_instances_ctx(|ctx| {
            let prios = ctx.default_instance_priorities();
            let mut sorted = prios.clone();
            sorted.sort_unstable();
            sorted.dedup();
            sorted.reverse();
            assert_eq!(prios, sorted, "descending and distinct");
        });
    }
```

Append to `crates/leanr_meta/src/synth.rs`'s `#[cfg(test)] mod tests`:

```rust
    /// `forall_meta_telescope_reducing` peels every `forallE` binder off
    /// a type, minting one fresh mvar per binder, and returns the
    /// binder infos alongside — which is what
    /// `synthesizeUsingDefaultInstance` needs to pick the
    /// `instImplicit` binders out as new pending goals.
    ///
    /// oracle: `forallMetaTelescopeReducing` (`Lean/Meta/Basic.lean`),
    /// the loop `get_subgoals` already ran privately before M4b-3 P3
    /// task 4 generalized it out.
    #[test]
    fn forall_meta_telescope_reducing_returns_one_mvar_and_info_per_binder() {
        with_instances_ctx(|ctx| {
            // `{α : Type} -> [Wrap α] -> α -> α`-shaped: three binders,
            // the middle one instance-implicit.
            let ty = three_binder_test_type(ctx);
            let (mvars, bis, body) = ctx
                .forall_meta_telescope_reducing(ty)
                .expect("telescope runs");
            assert_eq!(mvars.len(), 3, "one mvar per binder");
            assert_eq!(bis.len(), 3, "one binder info per binder");
            assert_eq!(
                bis.iter().filter(|b| **b == BinderInfo::InstImplicit).count(),
                1,
                "exactly the middle binder is instance-implicit"
            );
            assert!(
                !matches!(ctx.node(body), Node::Forall { .. }),
                "the body is fully peeled"
            );
        });
    }
```

`three_binder_test_type` is a fixture helper this test defines locally: build `∀ {α : Type}, [Wrap α] → α → α` against `with_instances_ctx`'s environment using `store_mut().expr_forall(..)` with `BinderInfo::Implicit`, `BinderInfo::InstImplicit`, `BinderInfo::Default` in that order. Follow the shape of the existing `#[cfg(test)]` builders in this module.

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test --package leanr_meta get_dec_level default_instance_priorities forall_meta_telescope`
Expected: FAIL to compile — `no method named get_dec_level` / `default_instance_priorities` / `forall_meta_telescope_reducing`.

- [ ] **Step 3: Add the additive accessors**

In `crates/leanr_meta/src/infer.rs`, widen `get_level` (line 751) from `fn` to `pub(crate) fn` — inherent methods are private to their defining *module*, and `level.rs` is a sibling. Add one line to its doc:

```rust
    /// `pub(crate)` since M4b-3 P3 task 4: `level.rs`'s `get_dec_level`
    /// composes it, and inherent methods are module-private by default.
    pub(crate) fn get_level(&mut self, ty: ExprId) -> Result<LevelId, MetaError> {
```

In `crates/leanr_meta/src/level.rs`, add next to `dec_level_top`:

```rust
    /// oracle: `getDecLevel` (`Lean/Meta/DecLevel.lean:73-76`) —
    /// `getLevel`, `normalizeLevel`, then `decLevel`. Used by
    /// `elabNumLit`/`elabScientificLit` to infer the universe argument
    /// of `OfNat.{u}`/`OfScientific.{u}` from the expected type.
    ///
    /// The oracle's `decLevel` throws "invalid universe level, {u} is
    /// not greater than 0" on `none`; that message is a diagnostic, and
    /// the caller (`elab_num`) replaces it with its own
    /// "numerals are data" error anyway, so this returns a plain
    /// `MetaError::Infer` carrying the same fact.
    pub fn get_dec_level(&mut self, ty: ExprId) -> Result<LevelId, MetaError> {
        let l = self.get_level(ty)?;
        let l = self.level_normalize(l)?;
        match self.dec_level_top(l)? {
            Some(v) => Ok(v),
            None => Err(MetaError::Infer(
                "invalid universe level: not greater than 0".into(),
            )),
        }
    }
```

In `crates/leanr_meta/src/metactx.rs`, widen `checkpoint` and `rollback` from `pub(crate)` to `pub`, widen `MetaSnapshot` to `pub` if it is not already, and add:

```rust
    /// oracle: `isProp` (`Lean/Meta/Basic.lean`) — a public forwarder to
    /// the existing `pub(crate)` implementation (`lazy_delta.rs:161`).
    /// Needed by `elabNumLit`'s Prop failure branch
    /// (`BuiltinTerm.lean:222-224`), which distinguishes "the expected
    /// type is a proposition" from "the expected type is universe
    /// polymorphic" — two distinct oracle errors.
    pub fn is_prop_pub(&mut self, e: ExprId) -> Result<bool, MetaError> {
        self.is_prop(e)
    }
```

Name it `is_prop_pub` only if a `pub(crate) fn is_prop` already occupies the name on the same type; otherwise widen `lazy_delta.rs:161`'s `is_prop` to `pub` directly and add no forwarder. Check with `grep -n "fn is_prop" crates/leanr_meta/src/*.rs` and take the simpler option — a forwarder whose only reason is a name clash is worse than the widening.

In `crates/leanr_meta/src/instances.rs`, add to the `impl MetaCtx` block that holds `default_instances`:

```rust
    /// oracle: `getDefaultInstancesPriorities` — the GLOBAL priority set
    /// across every class, DESCENDING and distinct. `synthesizeUsingDefault`
    /// (`SyntheticMVars.lean:225-230`) walks it outermost, trying every
    /// pending mvar at one priority before dropping to the next.
    ///
    /// New rather than derived: `default_instances`/`default_instances_of`
    /// are per-class, and the priority walk is not.
    pub fn default_instance_priorities(&self) -> Vec<usize> {
        let mut prios: Vec<usize> = self.instances.defaults.iter().map(|(_, _, p)| *p).collect();
        prios.sort_unstable();
        prios.dedup();
        prios.reverse();
        prios
    }
```

- [ ] **Step 4: Add the `assign_synthetic_opaque` config flag**

`config.rs`'s module doc already names this field as one that "arrives with the feature that consults it", and `ASSERT_CONFIG_SIZE` (`config.rs:97`) breaks the build until it is handled. Add the field to `Config`:

```rust
    /// Allow `isDefEq` to assign a `syntheticOpaque` metavariable.
    /// oracle: `Config.assignSyntheticOpaque` (Basic.lean), scoped by
    /// `withAssignableSyntheticOpaque` (Basic.lean:1312).
    ///
    /// Default `false` — the whole point of `syntheticOpaque` is that
    /// ordinary unification must not assign it. Exactly one caller sets
    /// it: `synthesizeUsingDefaultPrio` (`SyntheticMVars.lean:164`),
    /// because a default instance must be able to assign an outParam
    /// mvar that `coeAtOutParam` marked opaque. IN the cache key: it
    /// changes which terms unify, so two queries under different values
    /// are different questions (this module's own doc, and Lean's
    /// #13772).
    pub assign_synthetic_opaque: bool,
```

Update `ASSERT_CONFIG_SIZE`'s expected size, add the field to the `Hash`/`toKey` derivation the way every other `bool` field is handled, set it to `false` in every `Config` constructor/`Default`, and update the module doc's "covers 15 fields" count to 16 and its list of three deferred fields to two.

Then honour it in `crates/leanr_meta/src/assign.rs:157`:

```rust
                match self.mctx.decl(mid) {
                    // oracle: `isAssignable`'s `isReadOnlyOrSyntheticOpaque`
                    // (ExprDefEq.lean:1731-1734), now gated by
                    // `Config.assignSyntheticOpaque` (M4b-3 P3 task 4):
                    // `withAssignableSyntheticOpaque` flips it so a
                    // default instance can assign an opaque outParam.
                    Some(d)
                        if d.kind == MVarKind::SyntheticOpaque
                            && !self.config.assign_synthetic_opaque =>
                    {
                        None
                    }
                    Some(_) => Some(mid),
                    None => None,
                }
```

Adjust `self.config` to whatever the field is actually called on `MetaCtx` (`grep -n "config" crates/leanr_meta/src/metactx.rs | head`). Add the scoping helper next to `checkpoint` in `metactx.rs`:

```rust
    /// oracle: `withAssignableSyntheticOpaque` (`Lean/Meta/Basic.lean:1312`)
    /// — run `f` with `Config.assignSyntheticOpaque := true`, restoring
    /// the previous value on both the normal and the panic-free error
    /// path (`f` returns rather than unwinding, so a plain
    /// save/run/restore is faithful).
    ///
    /// The config is part of the defeq CACHE KEY (`config.rs`'s own
    /// doc), so entries cached inside the scope cannot leak out to
    /// queries asked with the flag off. That is why this is a config
    /// field rather than an ambient toggle.
    pub fn with_assignable_synthetic_opaque<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = self.config.assign_synthetic_opaque;
        self.config.assign_synthetic_opaque = true;
        let r = f(self);
        self.config.assign_synthetic_opaque = saved;
        r
    }
```

- [ ] **Step 5: Generalize the two `synth.rs` helpers**

This is the plan's one non-additive `leanr_meta` change. `refresh_instance_levels` (`synth.rs:2006`) and the telescope loop inside `get_subgoals` (`synth.rs:1946`) are exactly `mkConstWithFreshMVarLevels` and `forallMetaTelescopeReducing`, but private, specialized to `&Instance`, and discarding binder infos. Generalize them; do **not** duplicate the loop in `leanr_elab`.

Rename `refresh_instance_levels` to `mk_const_with_fresh_mvar_levels` and make it `pub`, keeping the body and the whole doc comment (its "HARD REQUIREMENT 1" note is still exactly why it exists), with one added paragraph:

```rust
    /// `pub` and renamed to the oracle's own name since M4b-3 P3 task 4:
    /// `synthesizeUsingDefaultInstance` (`SyntheticMVars.lean:155-157`)
    /// needs the same "replace every universe argument with a fresh
    /// level mvar" step for a default-instance CONSTANT, not only for a
    /// tabled `Instance`. The body is unchanged.
```

Add `forall_meta_telescope_reducing` as a `pub` method carrying the loop that `get_subgoals` runs today, extended to collect binder infos:

```rust
    /// oracle: `forallMetaTelescopeReducing` (`Lean/Meta/Basic.lean`) —
    /// peel every `forallE` binder off `ty`, minting one fresh mvar per
    /// binder at that binder's (substituted) domain, `whnf`-ing whenever
    /// the type stops being a syntactic forall to see whether more
    /// binders hide behind a definition. Returns
    /// `(mvars in binder order, their binder infos, the peeled body)`.
    ///
    /// Generalized out of `get_subgoals` by M4b-3 P3 task 4 (design spec
    /// § Accessor ledger, the one non-additive item): the loop is
    /// fidelity-critical and duplicating it in `leanr_elab` for
    /// `synthesizeUsingDefaultInstance` would be worse than sharing it.
    /// `get_subgoals` is now a caller; the binder infos are new — it
    /// discards them, `synthesizeUsingDefaultInstance` picks the
    /// `InstImplicit` ones out as new pending goals.
    #[allow(clippy::type_complexity)]
    pub fn forall_meta_telescope_reducing(
        &mut self,
        ty: ExprId,
    ) -> Result<(Vec<ExprId>, Vec<BinderInfo>, ExprId), MetaError> {
        let base = Some(self.view.store);
        let mut cur = ty;
        let mut mvars: Vec<ExprId> = Vec::new();
        let mut bis: Vec<BinderInfo> = Vec::new();
        let mut subst: Vec<ExprId> = Vec::new();
        loop {
            self.step()?;
            if let Node::Forall {
                binder_type,
                body,
                binder_info,
                ..
            } = self.node(cur)
            {
                let d = instantiate_rev(self.scratch, base, binder_type, &subst, &mut self.guard)?;
                let (m, _) = self.mk_aux_mvar(d)?;
                subst.push(m);
                mvars.push(m);
                bis.push(binder_info);
                cur = body;
            } else {
                let t = instantiate_rev(self.scratch, base, cur, &subst, &mut self.guard)?;
                cur = self.whnf(t)?;
                subst.clear();
                if !matches!(self.node(cur), Node::Forall { .. }) {
                    break;
                }
            }
        }
        let body = instantiate_rev(self.scratch, base, cur, &subst, &mut self.guard)?;
        Ok((mvars, bis, body))
    }
```

Rewrite `get_subgoals` as a caller. The oracle's own `getSubgoals` is `forallMetaTelescopeReducing` followed by `mkAppN candidate mvars` (`SynthInstance.lean:317-337`), so applying the mvars *after* the telescope rather than interleaving `expr_app` inside the loop is the oracle's own structure, not a rewrite of it:

```rust
    fn get_subgoals(
        &mut self,
        inst: &Instance,
    ) -> Result<(Vec<ExprId>, ExprId, ExprId), MetaError> {
        let base = Some(self.view.store);
        let inst_val = self.mk_const_with_fresh_mvar_levels(inst.val)?;
        let inst_type = self.infer_type(inst_val)?;
        let (mvars, _bis, inst_type_body) = self.forall_meta_telescope_reducing(inst_type)?;
        // oracle: `mkAppN candidate mvars` (:330). Applying after the
        // telescope rather than inside it is the oracle's own shape.
        let mut applied = inst_val;
        for m in &mvars {
            applied = self.scratch.expr_app(base, applied, *m)?;
        }
        Ok((mvars, applied, inst_type_body))
    }
```

- [ ] **Step 6: Run the tests to verify they pass — and that nothing else moved**

```bash
cd /workspace
cargo test --package leanr_meta
cargo test --release --package leanr_meta --test oracle_synth
mise run meta:fast
```

Expected: PASS, all three. `meta:fast` and `oracle_synth` are the behavior-neutrality gate on the `synth.rs` rewrite — they replay committed synthesis records, so a changed instantiation order shows up there. **If any synthesis test fails, stop and report it rather than adjusting the test**: the whole justification for generalizing rather than duplicating is that the rewrite is behavior-neutral, and a failure falsifies that.

- [ ] **Step 7: Correct the spec's accessor ledger**

In `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` § Accessor ledger, strike `mk_raw_nat_lit` from the P3 row and replace it with the reason:

```text
`mk_raw_nat_lit` is NOT needed (M4b-3 P3 task 4): `Store::expr_lit_nat`
(`leanr_kernel/src/bank/terms.rs:535`) and `MetaCtx::store_mut` are both
already public, which is exactly how `builtin/lit.rs`'s `elab_str`
reaches `expr_lit_str`.
```

- [ ] **Step 8: Commit**

```bash
cd /workspace
mise run fmt && mise run lint && mise run test
git add crates/leanr_meta docs/superpowers/specs
git commit -m "feat(meta): getDecLevel, default-instance priorities, assignable syntheticOpaque

Additive: get_dec_level (composing the private get_level/level_normalize/
dec_level_top), public checkpoint/rollback/MetaSnapshot, an is_prop
forwarder, default_instance_priorities (global, descending, distinct --
default_instances is per-class and cannot produce it), and the
assign_synthetic_opaque Config field with its withAssignableSyntheticOpaque
scope, honoured at assign.rs's isAssignable.

Non-additive, per the spec's ledger: refresh_instance_levels and
get_subgoals' telescope loop are generalized out of synth.rs into public
mk_const_with_fresh_mvar_levels / forall_meta_telescope_reducing (now
returning binder infos), with get_subgoals rewritten as a caller in the
oracle's own telescope-then-mkAppN shape. Gated by oracle_synth and
meta:fast staying green.

Also strikes mk_raw_nat_lit from the spec's P3 accessor row: expr_lit_nat
and store_mut are already public."
```

---

## Task 5: `Term.mkInstMVar`, `commit_when`, and the real `synthesizeUsingDefault`

The heart of the plan. Rung 3 stops being a shape-guarded seam and becomes the oracle's actual default-instance machinery.

**Files:**
- Create: `crates/leanr_elab/src/synthetic/default_inst.rs`
- Modify: `crates/leanr_elab/src/synthetic/mod.rs` (declare the module)
- Modify: `crates/leanr_elab/src/synthetic/state.rs` (`mk_inst_mvar`, `commit_when`)
- Modify: `crates/leanr_elab/src/synthetic/ladder.rs` (delete the seam body; rung 3 calls the real one)
- Modify: `crates/leanr_elab/tests/support/mod.rs`
- Test: `crates/leanr_elab/tests/synthetic_smoke.rs`

**Interfaces:**
- Consumes: Task 3's fixture (`instOfNatNat` at priority 100, `instOfNatTag` at 500, `instDfltNat` at 1000); Task 4's `MetaCtx::{default_instance_priorities, mk_const_with_fresh_mvar_levels, forall_meta_telescope_reducing, with_assignable_synthetic_opaque, checkpoint, rollback}`.
- Produces:
  - `TermElabM::mk_inst_mvar(&mut self, ty: ExprId, stx: SynElem) -> Result<ExprId, ElabError>`
  - `TermElabM::commit_when(&mut self, f: impl FnOnce(&mut Self) -> Result<bool, ElabError>) -> Result<bool, ElabError>`
  - `TermElabM::synthesize_using_default(&mut self, kinds: &KindInterner) -> Result<bool, ElabError>` — **signature change**: it gains `kinds`, because `synthesize_pending` reaches `synthesize_inst_mvar_core`, which already takes it. `ladder.rs`'s rung-3 call site passes the `kinds` it already holds.

- [ ] **Step 1: Write the failing tests**

Replace `synthetic_smoke.rs`'s two rung-3 seam tests — `synthesize_using_default_is_a_shape_guarded_seam` (line 384) and `synthesize_using_default_errors_when_a_default_instance_is_registered` (line 408) — with real behavior tests, and add the two ordering tests the design spec assigns to P3:

```rust
/// Rung 3 with nothing pending is a no-progress no-op — unchanged
/// behavior from P2a's seam, but now for the real reason (the priority
/// walk finds no pending `TypeClass` mvar) rather than a shape guard.
#[test]
fn synthesize_using_default_is_a_no_op_with_nothing_pending() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        assert!(!app
            .elab
            .synthesize_using_default(&kinds)
            .expect("no pending mvars -> no-op"));
    });
}

/// The case P2a's seam existed for, now solved rather than refused: a
/// pending `Dflt ?a` goal is closed by applying `@[default_instance]
/// instDfltNat`, which assigns `?a := Nat`.
///
/// oracle: `synthesizeUsingDefaultPrio` (`SyntheticMVars.lean:113-127`)
/// -> `synthesizeUsingDefaultInstance` (`:155-175`).
#[test]
fn synthesize_using_default_applies_a_default_instance() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        let goal = support::dflt_of_fresh_mvar(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        app.elab.register_synthetic_mvar(
            support::any_syn_elem(),
            id,
            leanr_elab::synthetic::SyntheticMVarKind::TypeClass,
        );
        assert!(
            app.elab
                .synthesize_using_default(&kinds)
                .expect("rung 3 runs"),
            "a registered default instance must make progress"
        );
        assert!(
            app.elab.mctx.mctx().is_assigned(id),
            "the goal mvar is assigned by the default instance"
        );
    });
}

/// **Ordering test 1 of 2 (design spec § Verification, tier 2).**
/// `synthesizeSomeUsingDefaultPrio` walks `pendingMVars.reverse` —
/// REVERSE CREATION ORDER — and the oracle's own comment
/// (`SyntheticMVars.lean:222-224`) explains why: otherwise `toString 0`
/// fails with an `OfNat String ?_` error. `pending_mvars`' head is the
/// MOST RECENT (P2a's invariant), so the walk must visit the OLDEST
/// first.
///
/// The corpus cannot catch this: on a term with one numeral both orders
/// agree.
#[test]
fn default_instance_walk_visits_pending_mvars_in_reverse_creation_order() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        // Three pending goals, registered oldest-first. Only the OLDEST
        // has a class with default instances, so if the walk ran in
        // `pending_mvars` order (newest first) it would reach it last —
        // and `support::visit_order_of_default_walk` records which
        // goals were considered, in order.
        let ids = support::register_three_goals_oldest_defaultable(app);
        let order = support::visit_order_of_default_walk(app, &kinds);
        assert_eq!(
            order,
            vec![ids[0], ids[1], ids[2]],
            "reverse creation order: oldest pending mvar first"
        );
    });
}

/// **Ordering test 2 of 2.** `synthesizeUsingDefault` walks the priority
/// set in DESCENDING order (`SyntheticMVars.lean:225-230`, "Recall that
/// `prioSet` is stored in descending order"), trying every pending mvar
/// at one priority before dropping to the next.
///
/// `Elab0` carries three distinct priorities (`instDfltNat` 1000,
/// `instOfNatTag` 500, `instOfNatNat` 100), which is what makes this
/// non-vacuous.
#[test]
fn default_instance_priorities_are_walked_in_descending_order() {
    support::with_app_harness("Nat.zero", |app| {
        let prios = app.elab.mctx.default_instance_priorities();
        assert!(
            prios.len() >= 3,
            "Elab0 must carry three distinct default-instance priorities, got {prios:?}"
        );
        let mut descending = prios.clone();
        descending.sort_unstable();
        descending.reverse();
        assert_eq!(prios, descending);
        // The two priorities the fixture writes EXPLICITLY are pinned;
        // the bare `@[default_instance]` on `instDfltNat` is only
        // required to outrank both. Lean's own default for the bare
        // attribute is not restated here — it is the oracle's to
        // choose, and pinning it would make this test fail on a
        // toolchain bump for a reason unrelated to the ordering it
        // exists to check.
        assert!(prios.contains(&500), "instOfNatTag's priority, got {prios:?}");
        assert!(prios.contains(&100), "instOfNatNat's priority, got {prios:?}");
        assert!(
            prios[0] > 500,
            "instDfltNat's bare @[default_instance] outranks both explicit ones, got {prios:?}"
        );
    });
}
```

Add the three new helpers to `crates/leanr_elab/tests/support/mod.rs`:

```rust
/// `Dflt ?a` with a FRESH type mvar — the shape rung 3 actually closes,
/// unlike `dflt_of_nat`'s ground `Dflt Nat` (which ordinary synthesis
/// already solves at rung 1).
pub fn dflt_of_fresh_mvar(
    app: &mut leanr_elab::app::state::AppElab,
) -> leanr_kernel::bank::ExprId {
    let base = app.elab.view.store;
    let dflt = fixture_const(app, "Dflt");
    // `Dflt (a : Type)`, and `Type` is `Sort 1` — a SORT, not a
    // declared constant, so it is built rather than resolved.
    let ty = {
        let store = app.elab.mctx.store_mut();
        let zero = store.level_zero(None).expect("zero");
        let one = store.level_succ(None, zero).expect("succ");
        store.expr_sort(None, one).expect("Sort 1")
    };
    let (a, _) = app
        .elab
        .mk_fresh_expr_mvar_of_kind(ty, leanr_meta::MVarKind::Natural)
        .expect("fresh type mvar");
    app.elab
        .mctx
        .store_mut()
        .expr_app(Some(base), dflt, a)
        .expect("Dflt ?a")
}

/// Three pending `TypeClass` goals registered oldest-first, where only
/// the OLDEST has a class carrying default instances. Returns their ids
/// in CREATION order.
pub fn register_three_goals_oldest_defaultable(
    app: &mut leanr_elab::app::state::AppElab,
) -> Vec<leanr_meta::MVarId> {
    let goals = [
        dflt_of_fresh_mvar(app),
        wrap_of_fresh_mvar(app),
        no_inst_of_nat(app),
    ];
    let mut ids = Vec::new();
    for g in goals {
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(g, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        app.elab.register_synthetic_mvar(
            any_syn_elem(),
            id,
            leanr_elab::synthetic::SyntheticMVarKind::TypeClass,
        );
        ids.push(id);
    }
    ids
}

/// The order in which the default-instance walk CONSIDERS pending
/// mvars. Drives the real `synthesize_using_default` and reads the
/// visit log the implementation records under `#[cfg(test)]`; see
/// `synthetic/default_inst.rs`'s `DEFAULT_WALK_LOG`.
pub fn visit_order_of_default_walk(
    app: &mut leanr_elab::app::state::AppElab,
    kinds: &leanr_syntax::kind::KindInterner,
) -> Vec<leanr_meta::MVarId> {
    leanr_elab::synthetic::default_walk_log_reset();
    let _ = app.elab.synthesize_using_default(kinds);
    leanr_elab::synthetic::default_walk_log_take()
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test --package leanr_elab --test synthetic_smoke default_instance synthesize_using_default`
Expected: FAIL to compile — `synthesize_using_default` takes no `kinds` argument, and `default_walk_log_reset`/`default_walk_log_take`/`dflt_of_fresh_mvar` do not exist.

- [ ] **Step 3: Add `mk_inst_mvar` and `commit_when` to `state.rs`**

```rust
    /// oracle: `Term.mkInstMVar` (`TermElabM.lean:1925-1931`).
    ///
    /// **Not** `ElabAppArgs`'s same-named `where`-binding
    /// (`App.lean:919-923`, ported at `app/args.rs:618`), which mints
    /// the mvar, pushes it on `instMVars` and DEFERS synthesis to
    /// `finalize`. This one synthesizes EAGERLY and registers
    /// `.typeClass` only `unless` that succeeds — the shape a literal
    /// needs, since a numeral has no enclosing application to defer to.
    /// The two are deliberately distinct; do not merge them.
    ///
    /// The oracle's `extraErrorMsg?` is prose (design spec § Amendment,
    /// item 2) and is not carried.
    pub fn mk_inst_mvar(&mut self, ty: ExprId, stx: SynElem) -> Result<ExprId, ElabError> {
        let (mvar, mvar_id) = self.mk_fresh_expr_mvar_of_kind(ty, MVarKind::Synthetic)?;
        if !self.synthesize_inst_mvar_core(mvar_id)? {
            self.register_synthetic_mvar(stx, mvar_id, SyntheticMVarKind::TypeClass);
        }
        Ok(mvar)
    }

    /// oracle: `commitWhen` over `Term.SavedState`
    /// (`Lean/Elab/Term/TermElabM.lean`'s `MonadBacktrack` instance) —
    /// run `f`; keep its effects if it returns `true`, roll them back if
    /// it returns `false` or errors.
    ///
    /// **`MetaCtx::checkpoint`/`rollback` alone is NOT enough.**
    /// `Term.SavedState` is `Meta.SavedState × Term.State`, and both P3
    /// callers can register synthetic mvars before failing:
    /// `synthesizeUsingDefaultInstance` calls `synthesizePending`, and
    /// `synthesizePendingInstMVar'` calls `synthesizeInstMVarCore`.
    /// Rolling back only the mctx would leave a rejected default
    /// instance's subgoals pending forever, and the ladder would then
    /// report them stuck. So the elaborator's three tables are
    /// snapshotted too.
    ///
    /// `level_names` is NOT snapshotted: it is scoped by
    /// `with_saved_context` alone and no path below `f` touches it.
    /// The three fresh-name counters are likewise not restored —
    /// rewinding them would let a rolled-back attempt's names be REUSED
    /// by the next attempt, which is exactly the collision the counters
    /// exist to prevent. The oracle's `mkFreshId` counter is
    /// monotone across backtracking for the same reason.
    pub fn commit_when(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<bool, ElabError>,
    ) -> Result<bool, ElabError> {
        let meta_snap = self.mctx.checkpoint();
        let pending = self.pending_mvars.clone();
        let synthetic = self.synthetic_mvars.clone();
        let errors = self.mvar_error_infos.clone();
        let restore = |s: &mut Self| {
            s.mctx.rollback(meta_snap);
            s.pending_mvars = pending;
            s.synthetic_mvars = synthetic;
            s.mvar_error_infos = errors;
        };
        match f(self) {
            Ok(true) => Ok(true),
            Ok(false) => {
                restore(self);
                Ok(false)
            }
            Err(e) => {
                restore(self);
                Err(e)
            }
        }
    }
```

The closure captures by move, so write `restore` as a small private `fn` taking the four saved values, or clone them into the closure — whichever compiles cleanly under the borrow checker without `unsafe`. Do not reach for `RefCell`.

- [ ] **Step 4: Write `default_inst.rs`**

```rust
//! Rung 3 of the escalation ladder: default instances. Oracle:
//! `Lean/Elab/SyntheticMVars.lean:113-230`.
//!
//! P2a shipped `synthesize_using_default` as a shape-guarded seam that
//! ERRORED when a pending typeclass mvar's class had default instances
//! registered. This module is that seam's replacement (design spec
//! § Amendment 2, item 2): `num` is the first construct in leanr's
//! grammar that creates such a goal from source, so the rung and its
//! producer land together.
//!
//! Two orderings are transliterated verbatim because they are
//! fidelity-critical and invisible on simple corpus terms:
//!
//!   * the priority set is walked DESCENDING (`:225-230`);
//!   * within a priority, `synthesizeSomeUsingDefaultPrio` walks
//!     `pendingMVars.reverse` — REVERSE CREATION ORDER — with the
//!     oracle's own comment explaining why (`:222-224`: otherwise
//!     `toString 0` fails with an `OfNat String ?_` error). On success
//!     the queue is rebuilt as `pendingMVars.reverse ++
//!     pendingMVarsNew`.
//!
//! Both have direct unit tests in `tests/synthetic_smoke.rs`; the
//! corpus cannot be relied on to catch them.

use leanr_kernel::bank::{BinderInfo, ExprId, NameId};
use leanr_meta::MVarId;
use leanr_syntax::kind::KindInterner;

use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::synthetic::SyntheticMVarKind;

impl<'e> TermElabM<'e> {
    /// oracle: `synthesizeUsingDefault` (`SyntheticMVars.lean:225-230`)
    /// — the ladder's rung 3. Walk the GLOBAL priority set in
    /// descending order; the first priority that makes progress wins.
    pub fn synthesize_using_default(&mut self, kinds: &KindInterner) -> Result<bool, ElabError> {
        // oracle: "Recall that `prioSet` is stored in descending order".
        // `MetaCtx::default_instance_priorities` guarantees that
        // (M4b-3 P3 task 4); the ordering test asserts it independently
        // rather than trusting the accessor.
        for prio in self.mctx.default_instance_priorities() {
            if self.synthesize_some_using_default_prio(prio, kinds)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// oracle: `synthesizeSomeUsingDefaultPrio` (`:206-224`).
    ///
    /// `pending_mvars`' head is the MOST RECENT (P2a's invariant), and
    /// the oracle walks `pendingMVars.reverse`, so this iterates the
    /// REVERSED list — oldest first. `pending_new` accumulates the
    /// skipped entries in the oracle's own consing order, so the
    /// rebuilt queue is `remaining.reverse() ++ pending_new`.
    fn synthesize_some_using_default_prio(
        &mut self,
        prio: usize,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        let mut walk: Vec<MVarId> = self.pending_mvars.clone();
        walk.reverse();
        let mut pending_new: Vec<MVarId> = Vec::new();
        for i in 0..walk.len() {
            let mvar_id = walk[i];
            #[cfg(test)]
            default_walk_log_push(mvar_id);
            let is_tc = matches!(
                self.synthetic_mvar_decl(mvar_id).map(|d| &d.kind),
                Some(SyntheticMVarKind::TypeClass)
            );
            if is_tc && self.synthesize_using_default_prio(mvar_id, prio, kinds)? {
                // oracle: `pendingMVars := pendingMVars.reverse ++
                // pendingMVarsNew` — `pendingMVars` here is what is
                // LEFT of the walk after the successful entry.
                let mut rest: Vec<MVarId> = walk[i + 1..].to_vec();
                rest.reverse();
                rest.extend(pending_new.into_iter());
                self.pending_mvars = rest;
                return Ok(true);
            }
            // oracle: `visit pendingMVars (mvarId :: pendingMVarsNew)`.
            pending_new.insert(0, mvar_id);
        }
        Ok(false)
    }

    /// oracle: `synthesizeUsingDefaultPrio` (`:113-127`).
    ///
    /// The oracle's `isClass? mvarType` early-out is FUSED with the
    /// `getDefaultInstances className` one: both `return false`, and a
    /// head constant with a non-empty default-instance list is
    /// necessarily a class, so `pending_class_name` plus an empty-list
    /// test decides both (plan § Measured facts, item 3). This is a
    /// fusion, not a seam — no oracle behavior is skipped.
    fn synthesize_using_default_prio(
        &mut self,
        mvar_id: MVarId,
        prio: usize,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        let Some(class) = self.pending_class_name(mvar_id)? else {
            return Ok(false);
        };
        for (inst, inst_prio) in self.mctx.default_instances_of(class) {
            if inst_prio != prio {
                continue;
            }
            if self.synthesize_using_default_instance(mvar_id, inst, kinds)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// oracle: `synthesizeUsingDefaultInstance` (`:155-175`).
    ///
    /// Mint the default instance with fresh universe mvars, telescope
    /// its type into argument mvars, unify the goal against the applied
    /// candidate under `withAssignableSyntheticOpaque`, and — on
    /// success — recursively synthesize the instance-implicit binders
    /// the candidate introduced. That recursion is a NESTED FIXPOINT,
    /// not a single pass.
    ///
    /// `withAssignableSyntheticOpaque` (`:164`) is required because
    /// `coeAtOutParam` may mark a local instance's output parameter
    /// `syntheticOpaque`, which ordinary unification refuses to assign.
    /// leanr has no `coeAtOutParam` producer yet (that is P2b/P4), so
    /// the scope is currently a no-op on every reachable term — it is
    /// ported anyway because it is one line and its absence would be a
    /// silent divergence the moment P2b lands.
    fn synthesize_using_default_instance(
        &mut self,
        mvar_id: MVarId,
        inst: NameId,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        self.commit_when(|s| {
            let base = s.view.store;
            let levels = s
                .mctx
                .store_mut()
                .intern_level_list(None, &[])
                .map_err(leanr_meta::MetaError::from)?;
            let raw = s
                .mctx
                .store_mut()
                .expr_const(Some(base), Some(inst), levels)
                .map_err(leanr_meta::MetaError::from)?;
            let candidate = s.mctx.mk_const_with_fresh_mvar_levels(raw)?;
            let cand_type = s.mctx.infer_type(candidate)?;
            let (mvars, bis, _body) = s.mctx.forall_meta_telescope_reducing(cand_type)?;
            let mut applied = candidate;
            for m in &mvars {
                applied = s
                    .mctx
                    .store_mut()
                    .expr_app(Some(base), applied, *m)
                    .map_err(leanr_meta::MetaError::from)?;
            }
            let goal = s
                .mctx
                .store_mut()
                .expr_mvar(None, Some(mvar_id.0))
                .map_err(leanr_meta::MetaError::from)?;
            // oracle: `isDefEqGuarded` — a FAILED unification is `false`,
            // not an error; only a genuine `MetaError` propagates.
            let ok = s
                .mctx
                .with_assignable_synthetic_opaque(|m| m.is_def_eq(goal, applied))?;
            if !ok {
                return Ok(false);
            }
            // oracle: collect the instImplicit binders as new pending
            // goals, CONSED (so the resulting list is reverse binder
            // order), then `synthesizePending`.
            let mut pending: Vec<MVarId> = Vec::new();
            for (m, bi) in mvars.iter().zip(bis.iter()) {
                if *bi == BinderInfo::InstImplicit {
                    if let Some(id) = s.mvar_id_of(*m) {
                        pending.insert(0, id);
                    }
                }
            }
            s.synthesize_pending(pending, kinds)
        })
    }

    /// oracle: `synthesizePending` (`:186-190`) — the nested fixpoint:
    /// solve what ordinary instance synthesis can, then apply ONE
    /// default instance, then repeat. Returns `false` if any goal is
    /// left that neither can close.
    fn synthesize_pending(
        &mut self,
        mvar_ids: Vec<MVarId>,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        let mut ids = self.synthesize_using_instances(mvar_ids, kinds)?;
        loop {
            if ids.is_empty() {
                return Ok(true);
            }
            let Some(next) = self.synthesize_some_using_default_qm(ids, kinds)? else {
                return Ok(false);
            };
            ids = self.synthesize_using_instances(next, kinds)?;
        }
    }

    /// oracle: `synthesizeUsingInstances` (`:147-153`) — repeatedly
    /// filter out the goals ordinary synthesis can close, until a pass
    /// closes none.
    fn synthesize_using_instances(
        &mut self,
        mvar_ids: Vec<MVarId>,
        kinds: &KindInterner,
    ) -> Result<Vec<MVarId>, ElabError> {
        let mut cur = mvar_ids;
        loop {
            let before = cur.len();
            let mut next = Vec::with_capacity(before);
            for id in cur {
                if !self.synthesize_pending_inst_mvar_committed(id, kinds)? {
                    next.push(id);
                }
            }
            if next.len() == before {
                return Ok(next);
            }
            cur = next;
        }
    }

    /// oracle: `synthesizePendingInstMVar'` (`:134-139`) —
    /// `commitWhen <| try synthesizeInstMVarCore catch _ => false`. A
    /// synthesis ERROR is swallowed into `false` here, unlike the
    /// ladder's own `synthesize_pending_inst_mvar`, because a default
    /// instance's subgoal that cannot be solved is a reason to reject
    /// the candidate, not to fail the elaboration.
    fn synthesize_pending_inst_mvar_committed(
        &mut self,
        mvar_id: MVarId,
        _kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        self.commit_when(|s| Ok(s.synthesize_inst_mvar_core(mvar_id).unwrap_or(false)))
    }

    /// oracle: `synthesizeSomeUsingDefault?` (`:176-185`) — apply a
    /// default instance to the FIRST goal that accepts one, returning
    /// the remaining goals with that one removed; `None` if none does.
    fn synthesize_some_using_default_qm(
        &mut self,
        mvar_ids: Vec<MVarId>,
        kinds: &KindInterner,
    ) -> Result<Option<Vec<MVarId>>, ElabError> {
        for (i, id) in mvar_ids.iter().enumerate() {
            if self.synthesize_using_default_for(*id, kinds)? {
                let mut rest = mvar_ids.clone();
                rest.remove(i);
                return Ok(Some(rest));
            }
        }
        Ok(None)
    }

    /// oracle: the inner `synthesizeUsingDefault` (`:128-132`) — the
    /// per-MVAR priority walk, distinct from the top-level per-QUEUE
    /// walk above.
    fn synthesize_using_default_for(
        &mut self,
        mvar_id: MVarId,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        for prio in self.mctx.default_instance_priorities() {
            if self.synthesize_using_default_prio(mvar_id, prio, kinds)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// The `MVarId` an `Expr.mvar` node refers to, if it is one.
    fn mvar_id_of(&self, e: ExprId) -> Option<MVarId> {
        let base = self.view.store;
        match self.mctx.store().expr_node(Some(base), e) {
            leanr_kernel::bank::terms::Node::MVar { id: Some(n) } => Some(MVarId(n)),
            _ => None,
        }
    }
}
```

Add the `#[cfg(test)]` visit log at the bottom of the same file, and export the two accessors from `synthetic/mod.rs` under `#[cfg(test)]`-independent `pub` (integration tests link against the crate as an external consumer, so a `#[cfg(test)]`-gated item is invisible to them — gate the *recording* on a runtime flag instead):

```rust
/// Visit-order instrumentation for `tests/synthetic_smoke.rs`'s
/// reverse-creation-order test. The corpus cannot express that ordering
/// (on a term with one numeral both orders agree), and asserting it
/// through the public API alone would only observe the OUTCOME, not the
/// order — so the walk records which mvars it considered.
///
/// Not `#[cfg(test)]`: integration tests link this crate as an external
/// consumer, where `#[cfg(test)]` items do not exist. The log is inert
/// unless `default_walk_log_reset` has armed it, so the cost in
/// production is one relaxed atomic load per visited mvar.
mod walk_log {
    use leanr_meta::MVarId;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Mutex;

    static ARMED: AtomicBool = AtomicBool::new(false);
    static LOG: Mutex<Vec<MVarId>> = Mutex::new(Vec::new());

    pub fn push(id: MVarId) {
        if ARMED.load(Ordering::Relaxed) {
            LOG.lock().expect("walk log").push(id);
        }
    }

    pub fn reset() {
        ARMED.store(true, Ordering::Relaxed);
        LOG.lock().expect("walk log").clear();
    }

    pub fn take() -> Vec<MVarId> {
        ARMED.store(false, Ordering::Relaxed);
        std::mem::take(&mut *LOG.lock().expect("walk log"))
    }
}

pub fn default_walk_log_reset() {
    walk_log::reset();
}

pub fn default_walk_log_take() -> Vec<MVarId> {
    walk_log::take()
}
```

Replace the `#[cfg(test)] default_walk_log_push(mvar_id);` line in `synthesize_some_using_default_prio` with an unconditional `walk_log::push(mvar_id);`. `MVarId` must be `Copy` for this; it is (`leanr_meta`'s own derive) — if it is not, store `mvar_id.0` instead.

- [ ] **Step 5: Rewire rung 3 and delete the seam**

In `synthetic/ladder.rs`, delete the whole P2a `synthesize_using_default` body (its doc comment included) and update the rung-3 call site:

```rust
            // Rung 3: default instances. Real since M4b-3 P3 task 5 —
            // P2a's shape-guarded seam is gone, not retargeted.
            if self.synthesize_using_default(kinds)? {
                continue;
            }
```

In `synthetic/mod.rs`, add `mod default_inst;` and `pub use default_inst::{default_walk_log_reset, default_walk_log_take};`.

- [ ] **Step 6: Run the tests to verify they pass**

```bash
cd /workspace
cargo test --package leanr_elab --test synthetic_smoke
cargo test --package leanr_elab
cargo test --release --package leanr_elab --test oracle_elab
```

Expected: PASS, all three. The oracle gate must stay green: nothing in the committed corpus yet produces a goal with default instances, so rung 3 going live must not change a single record. If a record changes here, that is a finding — the most likely cause is `commit_when` failing to restore a table, leaving a rejected candidate's subgoals pending.

- [ ] **Step 7: Commit**

```bash
cd /workspace
mise run fmt && mise run lint && mise run test
git add crates/leanr_elab
git commit -m "feat(elab): real synthesizeUsingDefault, retiring P2a's rung-3 seam

Adds synthetic/default_inst.rs with the whole family
(synthesizeUsingDefault / SomeUsingDefaultPrio / UsingDefaultPrio /
UsingDefaultInstance / UsingInstances / Pending), plus Term.mkInstMVar
(distinct from ElabAppArgs' same-named where-binding, which defers
synthesis) and TermElabM::commit_when.

commit_when snapshots pending_mvars/synthetic_mvars/mvar_error_infos as
well as the mctx: Term.SavedState is Meta.SavedState x Term.State, and a
rejected default instance would otherwise leave its subgoals pending
forever. Fresh-name counters are deliberately NOT rewound.

Both fidelity-critical orderings get direct unit tests: the descending
priority set, and the reverse-creation-order walk over pendingMVars.
Committed records are byte-identical -- nothing in the corpus creates a
defaultable goal until the next task."
```

---

## Task 6: The `num` elaborator

**Files:**
- Create: `crates/leanr_elab/src/builtin/lit/mod.rs`
- Create: `crates/leanr_elab/src/builtin/lit/decode.rs`
- Delete: `crates/leanr_elab/src/builtin/lit.rs`
- Modify: `crates/leanr_elab/src/dispatch.rs`
- Modify: `crates/leanr_elab/src/error.rs`
- Modify: `tests/fixtures/elab/dump_elab.lean`
- Modify: `tests/fixtures/elab/elab-queries.jsonl` (regenerated)
- Test: `crates/leanr_elab/src/builtin/lit/decode.rs` (`#[cfg(test)] mod tests`), `crates/leanr_elab/tests/oracle_elab.rs`

**Interfaces:**
- Consumes: Task 3's `OfNat`/`instOfNatNat`/`Tag`/`instOfNatTag`; Task 4's `MetaCtx::get_dec_level` and `is_prop`; Task 5's `TermElabM::mk_inst_mvar`.
- Produces:
  - `builtin::lit::elab_num(elab, node, kinds, expected) -> Result<ExprId, ElabError>`
  - `builtin::lit::mk_fresh_type_mvar_for(elab, expected) -> Result<ExprId, ElabError>`
  - `builtin::lit::const_with_level(elab, name: &str, u: LevelId) -> Result<ExprId, ElabError>`
  - `builtin::lit::decode::{decode_nat_literal, decode_quoted_char, hex_digit}` — Task 7 uses all three
  - `ElabError::NumeralIsNotData { expected: ExprId, is_prop: bool }`, `ElabError::IllFormedLiteral(String)`

- [ ] **Step 1: Split `lit.rs` into `lit/` (mechanical), then write the failing tests**

Create `crates/leanr_elab/src/builtin/lit/decode.rs` and move `decode_string_literal`, `hex_digit` and the whole `#[cfg(test)] mod tests` block from `lit.rs` into it verbatim, making the two functions `pub(crate)`. Create `crates/leanr_elab/src/builtin/lit/mod.rs` with `elab_str` moved verbatim, `mod decode;` and `pub(crate) use` for what `dispatch.rs` needs. Delete `lit.rs`. Run `cargo test --package leanr_elab` and confirm green before adding anything.

Then add the new decoder tests to `decode.rs`:

```rust
    /// oracle: `decodeNatLitVal?` (`Init/Meta/Defs.lean:964-979`) and
    /// its four radix helpers (`:923-962`). Underscores are separators
    /// in every radix; a leading `0` is only a radix prefix when a
    /// radix letter follows.
    #[test]
    fn nat_literal_radixes_and_separators() {
        assert_eq!(decode_nat_literal("42"), Some(42));
        assert_eq!(decode_nat_literal("0"), Some(0));
        assert_eq!(decode_nat_literal("007"), Some(7));
        assert_eq!(decode_nat_literal("1_000_000"), Some(1_000_000));
        assert_eq!(decode_nat_literal("0x2A"), Some(42));
        assert_eq!(decode_nat_literal("0X2a"), Some(42));
        assert_eq!(decode_nat_literal("0b1010"), Some(10));
        assert_eq!(decode_nat_literal("0o52"), Some(42));
        assert_eq!(decode_nat_literal("0xff_ff"), Some(65535));
        assert_eq!(decode_nat_literal(""), None);
        assert_eq!(decode_nat_literal("0z1"), None);
        assert_eq!(decode_nat_literal("12a"), None);
    }
```

And the elaborator test to `crates/leanr_elab/tests/synthetic_smoke.rs`:

```rust
/// `42` with no expected type elaborates to
/// `@OfNat.ofNat.{?u} ?α 42 ?inst`, with the instance goal PENDING
/// (nothing determines `?α` yet) — and the ladder then closes it via
/// `instOfNatNat` at rung 3, assigning `?α := Nat`.
///
/// oracle: `elabNumLit` (`BuiltinTerm.lean:210-230`) followed by the
/// entry point's `synthesizeSyntheticMVarsNoPostponing`. This is the
/// first term in leanr's grammar for which rung 3 does real work.
#[test]
fn a_bare_numeral_defaults_to_nat_through_rung_three() {
    let got = support::elab_and_synthesize("42").expect("42 elaborates");
    let rendered = got.to_string();
    assert!(
        rendered.contains("OfNat.ofNat"),
        "emits an OfNat.ofNat application, got {rendered}"
    );
    assert!(
        !rendered.contains("mvar"),
        "the fixpoint leaves no dangling metavariable, got {rendered}"
    );
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test --package leanr_elab nat_literal_radixes a_bare_numeral`
Expected: FAIL — `decode_nat_literal` does not exist; `elab_and_synthesize("42")` returns `Err(UnsupportedSyntax("num"))`.

- [ ] **Step 3: Write `decode_nat_literal`**

In `decode.rs`, transcribing `Init/Meta/Defs.lean:923-979`:

```rust
/// oracle: `decodeNatLitVal?` (`Init/Meta/Defs.lean:964-979`).
///
/// A leading `0` is a radix prefix only when `x`/`X`, `b`/`B` or `o`/`O`
/// follows; `007` is decimal seven, and `0` alone is zero. `_` is a
/// digit separator in every radix. Returns `None` for anything the
/// oracle rejects — the caller turns that into `IllFormedLiteral`
/// rather than panicking, even though leanr's own lexer has already
/// validated the token.
pub(crate) fn decode_nat_literal(s: &str) -> Option<u64> {
    let cs: Vec<char> = s.chars().collect();
    if cs.is_empty() {
        return None;
    }
    if cs[0] == '0' {
        if cs.len() == 1 {
            return Some(0);
        }
        return match cs[1] {
            'x' | 'X' => digits(&cs[2..], 16),
            'b' | 'B' => digits(&cs[2..], 2),
            'o' | 'O' => digits(&cs[2..], 8),
            c if c.is_ascii_digit() => digits(&cs, 10),
            _ => None,
        };
    }
    if cs[0].is_ascii_digit() {
        return digits(&cs, 10);
    }
    None
}

/// The shared body of `decodeDecimalLitAux`/`decodeBinLitAux`/
/// `decodeOctalLitAux`/`decodeHexLitAux` (`:923-962`): fold digits of
/// the given radix, skipping `_`, rejecting anything else. An empty
/// digit run is `Some(0)` — the oracle's own `atEnd -> some val` base
/// case with `val = 0`.
fn digits(cs: &[char], radix: u32) -> Option<u64> {
    let mut val: u64 = 0;
    for c in cs {
        if *c == '_' {
            continue;
        }
        let d = c.to_digit(radix)?;
        val = val.checked_mul(radix as u64)?.checked_add(d as u64)?;
    }
    Some(val)
}
```

`checked_mul`/`checked_add` are a deliberate departure from the oracle's arbitrary-precision `Nat`: leanr's `Nat` is arbitrary-precision too, but the elaborator only ever needs the value to build `Store::expr_lit_nat`, and a literal wider than `u64` is not reachable from the committed corpus. Document that as a **named seam** in the doc comment and make the `None` path produce `IllFormedLiteral("numeric literal exceeds u64 — M4b-3 P3 seam")` at the call site, so an overflow is an attributable error rather than a wrapped value.

- [ ] **Step 4: Write `elab_num` and its helpers**

In `lit/mod.rs`:

```rust
/// oracle: `mkFreshTypeMVarFor` (`BuiltinTerm.lean:202-208`) — a fresh
/// SYNTHETIC type mvar, unified with the expected type if there is one.
///
/// The unification result is DELIBERATELY discarded (`discard <|
/// isDefEq expectedType typeMVar`): a numeral against an expected type
/// the instance cannot satisfy still elaborates, and the mismatch is
/// reported by `ensureHasType` with better context. A genuine
/// `MetaError` still propagates.
pub(crate) fn mk_fresh_type_mvar_for(
    elab: &mut TermElabM,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let u = elab.mk_fresh_level_mvar()?;
    let sort = elab
        .mctx
        .store_mut()
        .expr_sort(None, u)
        .map_err(leanr_meta::MetaError::from)?;
    let (ty_mvar, _) = elab.mk_fresh_expr_mvar_of_kind(sort, MVarKind::Synthetic)?;
    if let Some(e) = expected {
        let _ = elab.mctx.is_def_eq(e, ty_mvar)?;
    }
    Ok(ty_mvar)
}

/// A fixture constant applied to exactly one universe level:
/// `OfNat.{u}`, `OfNat.ofNat.{u}`, `OfScientific.{u}`.
///
/// `base = Some(view.store)` for the const row (matching
/// `app::head::elab_ident_head`, which is the only other site that
/// builds a constant), `None` for the level list (matching that same
/// site: a freshly-minted level mvar is scratch data with nothing in
/// the persistent store to dedup against).
pub(crate) fn const_with_level(
    elab: &mut TermElabM,
    name: &str,
    u: LevelId,
) -> Result<ExprId, ElabError> {
    let cname = crate::app::head::intern_dotted(elab, name)?;
    let resolved = crate::resolve::resolve_global(&elab.view, cname, name)?;
    let base = elab.view.store;
    let levels = elab
        .mctx
        .store_mut()
        .intern_level_list(None, &[u])
        .map_err(leanr_meta::MetaError::from)?;
    elab.mctx
        .store_mut()
        .expr_const(Some(base), Some(resolved), levels)
        .map_err(|e| ElabError::from(leanr_meta::MetaError::from(e)))
}

/// A raw `Nat` literal.
///
/// `base = Some(view.store)` — NOT `elab_str`'s `None`. A string
/// literal is the whole term and never unifies against a
/// persistent-region literal; a numeral's `Expr.lit` becomes an
/// ARGUMENT of `OfNat ?α (lit v)`, which is unified against
/// `instOfNatNat`'s own type from the persistent store, and every
/// application row this crate builds around it uses `Some(base)`
/// (`app/args.rs::add_new_arg`'s own convention and its stated reason).
pub(crate) fn mk_raw_nat_lit(elab: &mut TermElabM, v: u64) -> Result<ExprId, ElabError> {
    let base = elab.view.store;
    elab.mctx
        .store_mut()
        .expr_lit_nat(Some(base), &Nat::from(v))
        .map_err(|e| ElabError::from(leanr_meta::MetaError::from(e)))
}

/// Left-associated application, `base = Some(view.store)` throughout.
pub(crate) fn app_n(
    elab: &mut TermElabM,
    f: ExprId,
    args: &[ExprId],
) -> Result<ExprId, ElabError> {
    let base = elab.view.store;
    let mut cur = f;
    for a in args {
        cur = elab
            .mctx
            .store_mut()
            .expr_app(Some(base), cur, *a)
            .map_err(leanr_meta::MetaError::from)?;
    }
    Ok(cur)
}

/// oracle: `elabNumLit` (`BuiltinTerm.lean:210-230`).
///
/// `@OfNat.ofNat.{u} ?α (rawNatLit v) ?inst`, where `?α` is a fresh
/// synthetic type mvar unified with the expected type, `u` is
/// `getDecLevel ?α`, and `?inst` is a `Term.mkInstMVar` for
/// `OfNat.{u} ?α (rawNatLit v)` — so it is synthesized eagerly and
/// registered `.typeClass` only if that is not yet possible.
///
/// The oracle's `extraErrorMsg` ("numerals are polymorphic in Lean…")
/// is prose and is not carried (design spec § Amendment, item 2).
pub fn elab_num(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    _kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let raw = node.text().to_string();
    let Some(val) = decode::decode_nat_literal(&raw) else {
        return Err(ElabError::IllFormedLiteral(format!(
            "numeric literal `{raw}` is not a Nat literal \
             (or exceeds u64 — M4b-3 P3 seam)"
        )));
    };
    let type_mvar = mk_fresh_type_mvar_for(elab, expected)?;
    // oracle: `try getDecLevel typeMVar catch ex => ...` (`:216-224`) —
    // the two failure branches are DISTINCT oracle errors and stay
    // distinct: expected type is a `Prop`, versus expected type is
    // universe-polymorphic and MAY be a proposition. With no expected
    // type at all the oracle rethrows the original level error.
    let u = match elab.mctx.get_dec_level(type_mvar) {
        Ok(u) => u,
        Err(e) => {
            return match expected {
                Some(t) => {
                    let is_prop = elab.mctx.is_prop(t)?;
                    Err(ElabError::NumeralIsNotData { expected: t, is_prop })
                }
                None => Err(ElabError::from(e)),
            }
        }
    };
    let lit = mk_raw_nat_lit(elab, val)?;
    let of_nat = const_with_level(elab, "OfNat", u)?;
    let goal = app_n(elab, of_nat, &[type_mvar, lit])?;
    let inst = elab.mk_inst_mvar(goal, SynElem::Node(node.clone()))?;
    let of_nat_of_nat = const_with_level(elab, "OfNat.ofNat", u)?;
    let r = app_n(elab, of_nat_of_nat, &[type_mvar, lit, inst])?;
    // oracle: `registerMVarErrorImplicitArgInfo mvar.mvarId! stx r`
    // (`:229`) — attribute a later "cannot synthesize" report to this
    // literal rather than to whatever enclosing term holds it.
    if let Node::MVar { id: Some(n) } = {
        let base = elab.view.store;
        elab.mctx.store().expr_node(Some(base), inst)
    } {
        elab.register_mvar_error_implicit_arg_info(MVarId(n), SynElem::Node(node.clone()), r);
    }
    Ok(r)
}
```

Add the two `ElabError` variants:

```rust
    /// oracle: `elabNumLit`'s two `getDecLevel` failure branches
    /// (`BuiltinTerm.lean:220-224`) — "numerals are data in Lean, but
    /// the expected type is a proposition" and "…is universe
    /// polymorphic and may be a proposition". Two distinct oracle
    /// errors, kept distinct by `is_prop` rather than collapsed: they
    /// say different things about what the user must change.
    NumeralIsNotData {
        expected: ExprId,
        is_prop: bool,
    },
    /// A literal TOKEN that leanr's lexer accepted but the oracle's own
    /// decoder rejects, or one whose value exceeds `u64` (a named seam;
    /// see `builtin::lit::decode::decode_nat_literal`). Distinct from
    /// `IllFormedSyntax`, which is about tree SHAPE.
    IllFormedLiteral(String),
```

- [ ] **Step 5: Register the dispatch arm**

In `dispatch.rs`, add `"num" => Some("num"),` to `elaborator_name_for` and the arm to `dispatch`:

```rust
        ("num", NodeOrToken::Node(node)) => {
            crate::builtin::lit::elab_num(elab, node, kinds, expected)
        }
```

Update the module doc's deferral list: remove the `num / char literals (OfNat / Char.ofNat) ... M4b-3 P3` line's `num` half (Task 7 removes the rest), and update the trailing paragraph that currently says "`num`/`char` are the M4b-3 P3 seam and likewise land on the catch-all" to name only `char`/`scientific` until Task 7.

- [ ] **Step 6: Run the tests to verify they pass**

Run: `cargo test --package leanr_elab nat_literal_radixes a_bare_numeral`
Expected: PASS. If `a_bare_numeral_defaults_to_nat_through_rung_three` still shows a metavariable, the ladder is reaching rung 3 but `synthesize_using_default_instance` is rejecting `instOfNatNat` — check `forall_meta_telescope_reducing` against `instOfNatNat`'s `(n : Nat) → OfNat Nat n` shape first.

- [ ] **Step 7: Add the corpus records and regenerate**

In `tests/fixtures/elab/dump_elab.lean`, add a query list and wire it into `main`'s concatenation:

```lean
/-- M4b-3 P3 task 6: numerals. `num/bare` is the whole point — a
numeral with NO expected type reaches the oracle's answer only through
the default-instance rung, so it is the first corpus record for which
`synthesizeSyntheticMVarsNoPostponing` does real work. The rest pin the
paths around it:
  * `num/ascribedNat` — an expected type that the DEFAULT instance also
    satisfies, so the record discriminates "propagated" from
    "defaulted" only in combination with `num/ascribedTag`;
  * `num/ascribedTag` — an expected type satisfied by a NON-default
    instance at a different priority, so defaulting must NOT win;
  * `num/hex`, `num/underscores` — token decoding, same elaborated
    shape as `num/bare` but a different `decodeNatLitVal?` path;
  * `num/inApp` — a numeral as an APPLICATION ARGUMENT, where the
    parameter type fixes `?α` before the fixpoint runs, so rung 1
    closes the instance goal and rung 3 never fires. The contrast with
    `num/bare` is what shows the ladder escalating only when it must;
  * `num/zero` — the `decodeNatLitVal?` single-`0` special case. -/
def numQueries : List (String × String) :=
  [ ("num/bare",        "42")
  , ("num/zero",        "0")
  , ("num/hex",         "0x2A")
  , ("num/underscores", "1_000_000")
  , ("num/ascribedNat", "(42 : Nat)")
  , ("num/ascribedTag", "(42 : Tag)")
  , ("num/inApp",       "pick 1 2")
  ]
```

Then:

```bash
cd /workspace
mise run fixtures:regen-elab
git diff --stat -- tests/fixtures/elab/elab-queries.jsonl
cargo test --release --package leanr_elab --test oracle_elab
```

Expected: seven new records appear, **no existing record changes**, and the gate passes. A dropped record (the dumper prints `dump_elab: elaboration failed for …` to stderr and emits nothing) means the *oracle* rejected the query — read the message and fix the query or the fixture, never the gate.

- [ ] **Step 8: Commit**

```bash
cd /workspace
mise run fmt && mise run lint && mise run test
git add crates/leanr_elab tests/fixtures/elab
git commit -m "feat(elab): num literals via OfNat and the default-instance rung

builtin/lit.rs becomes builtin/lit/ (mod.rs + decode.rs). elabNumLit is
transcribed whole: mkFreshTypeMVarFor with its deliberately-discarded
unification, getDecLevel with both failure branches kept distinct
(Prop vs universe-polymorphic), Term.mkInstMVar for the OfNat goal, and
registerMVarErrorImplicitArgInfo.

decode_nat_literal transcribes decodeNatLitVal? and its four radix
helpers, with a named u64-overflow seam rather than a silent wrap.

Seven corpus records: num/bare is the first term in leanr's grammar for
which ladder rung 3 does real work, and num/inApp is the contrast where
the parameter type fixes the carrier and rung 1 suffices."
```

---

## Task 7: The `char` and `scientific` elaborators

**Files:**
- Modify: `crates/leanr_elab/src/builtin/lit/mod.rs`
- Modify: `crates/leanr_elab/src/builtin/lit/decode.rs`
- Modify: `crates/leanr_elab/src/dispatch.rs`
- Modify: `tests/fixtures/elab/dump_elab.lean`
- Modify: `tests/fixtures/elab/elab-queries.jsonl` (regenerated)
- Test: `crates/leanr_elab/src/builtin/lit/decode.rs`, `crates/leanr_elab/tests/oracle_elab.rs`

**Interfaces:**
- Consumes: Task 6's `mk_fresh_type_mvar_for`, `const_with_level`, `mk_raw_nat_lit`, `app_n`, `decode::hex_digit`; Task 3's `Char`/`Char.ofNat`/`OfScientific`/`Bool`.
- Produces: `builtin::lit::{elab_char, elab_scientific}`, `decode::{decode_char_literal, decode_scientific_literal}`.

- [ ] **Step 1: Write the failing tests**

In `decode.rs`:

```rust
    /// oracle: `decodeCharLit` (`Init/Meta/Defs.lean:1177-1183`) — the
    /// character at index 1; if it is `\`, `decodeQuotedChar` from
    /// index 2. Exactly the escape set `decode_string_literal` already
    /// handles, which is why task 7 factors `decode_quoted_char` out of
    /// it rather than writing a second copy.
    #[test]
    fn char_literal_plain_and_escaped() {
        assert_eq!(decode_char_literal("'a'"), Some('a'));
        assert_eq!(decode_char_literal("'\\n'"), Some('\n'));
        assert_eq!(decode_char_literal("'\\\\'"), Some('\\'));
        assert_eq!(decode_char_literal("'\\''"), Some('\''));
        assert_eq!(decode_char_literal("'\\x41'"), Some('A'));
        assert_eq!(decode_char_literal("'\\u00e9'"), Some('é'));
        assert_eq!(decode_char_literal("'é'"), Some('é'));
    }

    /// oracle: `decodeScientificLitVal?` (`Init/Meta/Defs.lean:1008-1071`).
    /// Returns `(mantissa, negativeExponent, exponent)`:
    ///   `1.5`     -> (15, true, 1)     -- one digit after the dot
    ///   `1.25`    -> (125, true, 2)
    ///   `121e100` -> (121, false, 100)
    ///   `1e-3`    -> (1, true, 3)
    ///   `1.5e2`   -> (15, false, 1)    -- exp 2 minus 1 dot digit
    ///   `1.5e-2`  -> (15, true, 3)     -- exp 2 plus 1 dot digit
    #[test]
    fn scientific_literal_mantissa_sign_and_exponent() {
        assert_eq!(decode_scientific_literal("1.5"), Some((15, true, 1)));
        assert_eq!(decode_scientific_literal("1.25"), Some((125, true, 2)));
        assert_eq!(decode_scientific_literal("121e100"), Some((121, false, 100)));
        assert_eq!(decode_scientific_literal("1e-3"), Some((1, true, 3)));
        assert_eq!(decode_scientific_literal("1.5e2"), Some((15, false, 1)));
        assert_eq!(decode_scientific_literal("1.5e-2"), Some((15, true, 3)));
        assert_eq!(decode_scientific_literal("42"), None);
    }
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test --package leanr_elab char_literal_plain scientific_literal_mantissa`
Expected: FAIL — neither decoder exists.

- [ ] **Step 3: Factor out `decode_quoted_char` and add the two decoders**

In `decode.rs`, extract the escape-handling `match` from `decode_string_literal`'s loop into:

```rust
/// oracle: `decodeQuotedChar` (`Init/Meta/Defs.lean:1114-1140`) —
/// decode the escape sequence starting at `i` (the character AFTER the
/// backslash), returning the character and the index just past it.
/// `None` for a string GAP (`\` + whitespace), which contributes no
/// character; `decode_string_literal` handles that case, and a char
/// literal cannot contain one.
pub(crate) fn decode_quoted_char(cs: &[char], i: usize) -> Option<(char, usize)> {
    match cs[i] {
        '\\' => Some(('\\', i + 1)),
        '"' => Some(('"', i + 1)),
        '\'' => Some(('\'', i + 1)),
        'r' => Some(('\r', i + 1)),
        'n' => Some(('\n', i + 1)),
        't' => Some(('\t', i + 1)),
        'x' => {
            let code = hex_digit(cs[i + 1]) * 16 + hex_digit(cs[i + 2]);
            Some((char::from_u32(code).unwrap_or('\0'), i + 3))
        }
        'u' => {
            let code = ((hex_digit(cs[i + 1]) * 16 + hex_digit(cs[i + 2])) * 16
                + hex_digit(cs[i + 3]))
                * 16
                + hex_digit(cs[i + 4]);
            Some((char::from_u32(code).unwrap_or('\0'), i + 5))
        }
        _ => None,
    }
}
```

Rewrite `decode_string_literal`'s escape arm to call it, keeping the gap arm and the never-panic catch-all exactly as they are — the existing `decode_string_literal` tests are the gate that this factoring changed nothing.

Add:

```rust
/// oracle: `decodeCharLit` (`Init/Meta/Defs.lean:1177-1183`).
pub(crate) fn decode_char_literal(raw: &str) -> Option<char> {
    let cs: Vec<char> = raw.chars().collect();
    if cs.len() < 3 {
        return None;
    }
    if cs[1] == '\\' {
        decode_quoted_char(&cs, 2).map(|(c, _)| c)
    } else {
        Some(cs[1])
    }
}

/// oracle: `decodeScientificLitVal?` (`Init/Meta/Defs.lean:1008-1071`),
/// transcribed as a single pass over the token rather than the
/// oracle's four mutually-recursive `where` bindings. The states
/// correspond one-to-one: `decode` (integer part), `decodeAfterDot`,
/// `decodeExp`, `decodeAfterExp`.
///
/// Returns `(mantissa, exponentIsNegative, exponent)`. The final
/// combination (`:1018-1024`) is the subtle part: with a positive
/// written exponent `e` and `d` digits after the dot, the result is
/// `(m, false, e - d)` when `e >= d` and `(m, true, d - e)` otherwise;
/// with a negative written exponent it is always `(m, true, d + e)`.
pub(crate) fn decode_scientific_literal(raw: &str) -> Option<(u64, bool, u64)> {
    let cs: Vec<char> = raw.chars().collect();
    let mut i = 0usize;
    let mut mantissa: u64 = 0;
    let mut dot_digits: u64 = 0;
    if cs.is_empty() || !cs[0].is_ascii_digit() {
        return None;
    }
    // `decode`: the integer part.
    while i < cs.len() && (cs[i].is_ascii_digit() || cs[i] == '_') {
        if cs[i] != '_' {
            mantissa = mantissa.checked_mul(10)?.checked_add(cs[i] as u64 - '0' as u64)?;
        }
        i += 1;
    }
    let mut saw_dot = false;
    if i < cs.len() && cs[i] == '.' {
        saw_dot = true;
        i += 1;
        // `decodeAfterDot`.
        while i < cs.len() && (cs[i].is_ascii_digit() || cs[i] == '_') {
            if cs[i] != '_' {
                mantissa = mantissa.checked_mul(10)?.checked_add(cs[i] as u64 - '0' as u64)?;
                dot_digits += 1;
            }
            i += 1;
        }
        if i == cs.len() {
            return Some((mantissa, true, dot_digits));
        }
    }
    if i >= cs.len() || (cs[i] != 'e' && cs[i] != 'E') {
        // No exponent and no dot: this is a plain `num` token, which
        // the oracle's `decode` rejects by falling through to `none`.
        return if saw_dot { None } else { None };
    }
    i += 1;
    // `decodeExp`: an optional sign.
    let mut written_negative = false;
    if i < cs.len() && (cs[i] == '-' || cs[i] == '+') {
        written_negative = cs[i] == '-';
        i += 1;
    }
    // `decodeAfterExp`.
    let mut exp: u64 = 0;
    while i < cs.len() {
        if cs[i] == '_' {
            i += 1;
            continue;
        }
        if !cs[i].is_ascii_digit() {
            return None;
        }
        exp = exp.checked_mul(10)?.checked_add(cs[i] as u64 - '0' as u64)?;
        i += 1;
    }
    // oracle: `:1018-1024`, with the oracle's `e` = `dot_digits` and
    // its `exp` = the written exponent.
    if written_negative {
        Some((mantissa, true, exp + dot_digits))
    } else if exp >= dot_digits {
        Some((mantissa, false, exp - dot_digits))
    } else {
        Some((mantissa, true, dot_digits - exp))
    }
}
```

- [ ] **Step 4: Write the two elaborators**

In `lit/mod.rs`:

```rust
/// oracle: `elabCharLit` (`BuiltinTerm.lean:248-252`) —
/// `Char.ofNat (rawNatLit c)`. No instance, no expected type, no
/// universe level: the constant is monomorphic. `Char`'s own shape is
/// never consulted, which is why the fixture may carry an opaque
/// carrier (design spec § P3; plan § Measured facts, item 8).
pub fn elab_char(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    _kinds: &KindInterner,
    _expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let raw = node.text().to_string();
    let Some(c) = decode::decode_char_literal(&raw) else {
        return Err(ElabError::IllFormedLiteral(format!(
            "character literal `{raw}` is not a Char literal"
        )));
    };
    let lit = mk_raw_nat_lit(elab, c as u64)?;
    let cname = crate::app::head::intern_dotted(elab, "Char.ofNat")?;
    let resolved = crate::resolve::resolve_global(&elab.view, cname, "Char.ofNat")?;
    let base = elab.view.store;
    let levels = elab
        .mctx
        .store_mut()
        .intern_level_list(None, &[])
        .map_err(leanr_meta::MetaError::from)?;
    let f = elab
        .mctx
        .store_mut()
        .expr_const(Some(base), Some(resolved), levels)
        .map_err(leanr_meta::MetaError::from)?;
    app_n(elab, f, &[lit])
}

/// oracle: `elabScientificLit` (`BuiltinTerm.lean:235-246`) —
/// `@OfScientific.ofScientific.{u} ?α ?inst (rawNatLit m) sign
/// (rawNatLit e)`.
///
/// Note the ARGUMENT ORDER differs from `elabNumLit`'s: the instance
/// comes SECOND here (right after the carrier type), not last, and
/// there is no `getDecLevel` failure recovery — the oracle lets the
/// level error propagate (`:241`, a bare `getDecLevel`, no `try`).
/// Both are transcribed as written rather than harmonized with `num`.
pub fn elab_scientific(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    _kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let raw = node.text().to_string();
    let Some((m, sign, e)) = decode::decode_scientific_literal(&raw) else {
        return Err(ElabError::IllFormedLiteral(format!(
            "scientific literal `{raw}` is not a scientific literal \
             (or a component exceeds u64 — M4b-3 P3 seam)"
        )));
    };
    let type_mvar = mk_fresh_type_mvar_for(elab, expected)?;
    let u = elab.mctx.get_dec_level(type_mvar)?;
    let of_sci = const_with_level(elab, "OfScientific", u)?;
    let goal = app_n(elab, of_sci, &[type_mvar])?;
    let inst = elab.mk_inst_mvar(goal, SynElem::Node(node.clone()))?;
    let m_lit = mk_raw_nat_lit(elab, m)?;
    let e_lit = mk_raw_nat_lit(elab, e)?;
    let sign_expr = bool_const(elab, sign)?;
    let f = const_with_level(elab, "OfScientific.ofScientific", u)?;
    let r = app_n(elab, f, &[type_mvar, inst, m_lit, sign_expr, e_lit])?;
    if let Node::MVar { id: Some(n) } = {
        let base = elab.view.store;
        elab.mctx.store().expr_node(Some(base), inst)
    } {
        elab.register_mvar_error_implicit_arg_info(MVarId(n), SynElem::Node(node.clone()), r);
    }
    Ok(r)
}

/// oracle: `toExpr (b : Bool)` — `Bool.true` / `Bool.false`, a
/// zero-universe constant either way.
fn bool_const(elab: &mut TermElabM, b: bool) -> Result<ExprId, ElabError> {
    let name = if b { "Bool.true" } else { "Bool.false" };
    let cname = crate::app::head::intern_dotted(elab, name)?;
    let resolved = crate::resolve::resolve_global(&elab.view, cname, name)?;
    let base = elab.view.store;
    let levels = elab
        .mctx
        .store_mut()
        .intern_level_list(None, &[])
        .map_err(leanr_meta::MetaError::from)?;
    elab.mctx
        .store_mut()
        .expr_const(Some(base), Some(resolved), levels)
        .map_err(|e| ElabError::from(leanr_meta::MetaError::from(e)))
}
```

- [ ] **Step 5: Register both dispatch arms**

In `dispatch.rs`, add `"char" => Some("char"),` and `"scientific" => Some("scientific"),` to `elaborator_name_for`, plus:

```rust
        ("char", NodeOrToken::Node(node)) => {
            crate::builtin::lit::elab_char(elab, node, kinds, expected)
        }
        ("scientific", NodeOrToken::Node(node)) => {
            crate::builtin::lit::elab_scientific(elab, node, kinds, expected)
        }
```

Delete the `num / char literals (OfNat / Char.ofNat) ... M4b-3 P3` line from the deferral table entirely, and delete the trailing paragraph that explains why `num`/`char` are seams. Task 8 re-audits the whole doc.

- [ ] **Step 6: Run the tests to verify they pass**

Run: `cargo test --package leanr_elab`
Expected: PASS, including the pre-existing `decode_string_literal` tests — those are the gate on the `decode_quoted_char` factoring.

- [ ] **Step 7: Add the corpus records and regenerate**

In `dump_elab.lean`:

```lean
/-- M4b-3 P3 task 7: `char` and `scientific`.

`char/*` pins `elabCharLit`'s two decode paths (plain and escaped);
the elaborated shape is `Char.ofNat` applied to a raw literal in every
case, with no instance and no expected type, so the discrimination is
entirely in the decoded code point.

`sci/*` pins `decodeScientificLitVal?`'s three exponent combinations —
dot only, positive written exponent, negative written exponent — since
those are what decide the emitted `sign`/`exponent` pair. Every record
is ascribed to `Tag`: `OfScientific` has exactly one instance in the
fixture and no default instance, so an unascribed scientific literal is
a stuck typeclass problem the dumper would drop. -/
def charQueries : List (String × String) :=
  [ ("char/plain",   "'a'")
  , ("char/newline", "'\\n'")
  , ("char/hex",     "'\\x41'")
  , ("char/unicode", "'\\u00e9'")
  ]

def scientificQueries : List (String × String) :=
  [ ("sci/dot",       "(1.5 : Tag)")
  , ("sci/dotTwo",    "(1.25 : Tag)")
  , ("sci/expPos",    "(121e100 : Tag)")
  , ("sci/expNeg",    "(1e-3 : Tag)")
  , ("sci/dotExpPos", "(1.5e2 : Tag)")
  , ("sci/dotExpNeg", "(1.5e-2 : Tag)")
  ]
```

Wire `numQueries ++ charQueries ++ scientificQueries` into `main`'s concatenation, then:

```bash
cd /workspace
mise run fixtures:regen-elab
git diff --stat -- tests/fixtures/elab/elab-queries.jsonl
cargo test --release --package leanr_elab --test oracle_elab
```

Expected: ten new records, no existing record changes, gate green.

- [ ] **Step 8: Commit**

```bash
cd /workspace
mise run fmt && mise run lint && mise run test
git add crates/leanr_elab tests/fixtures/elab
git commit -m "feat(elab): char and scientific literals

elabCharLit emits Char.ofNat applied to a raw literal -- no instance, no
expected type, and Char's shape never consulted, which is what lets the
fixture carry an opaque carrier. elabScientificLit goes through
OfScientific with the instance argument SECOND (not last, unlike
elabNumLit) and no getDecLevel recovery, both transcribed as written
rather than harmonized.

decode_quoted_char is factored out of decode_string_literal and shared;
the existing string tests gate that factoring. decode_scientific_literal
transcribes decodeScientificLitVal?'s four states, including the
exponent/dot-digit combination at :1018-1024.

Ten corpus records covering both char decode paths and all three
exponent combinations."
```

---

## Task 8: Seam audit, deferral ledgers, and the retired-label gate

The final reconciliation: every claim the crate makes about what is and is not implemented is re-checked against what P3 actually shipped.

**Files:**
- Modify: `crates/leanr_elab/src/lib.rs` (deferral ledger)
- Modify: `crates/leanr_elab/src/dispatch.rs` (deferral table, re-audited)
- Modify: `crates/leanr_elab/src/synthetic/mod.rs` (module doc)
- Modify: `crates/leanr_elab/src/app/mod.rs` (seam index)
- Modify: `crates/leanr_elab/tests/seam_audit.rs`
- Test: `crates/leanr_elab/tests/seam_audit.rs`

**Interfaces:**
- Consumes: everything Tasks 1-7 shipped.
- Produces: no new API.

- [ ] **Step 1: Write the failing tests**

Append to `crates/leanr_elab/tests/seam_audit.rs`:

```rust
/// P3 RETIRED the rung-3 default-instance seam rather than retargeting
/// it. A source tree that still mentions the old label is a stale
/// claim about what is implemented.
///
/// Mirrors `no_seam_points_at_the_retired_p2_label` (M4b-3 P2a task 10),
/// which does the same for P1's "M4b-3 P2" labels.
#[test]
fn no_seam_points_at_the_retired_p3_default_instance_label() {
    let needle = "requires synthesizeUsingDefault";
    let mut offenders = Vec::new();
    for path in walk_rs_files("crates/leanr_elab/src") {
        let text = std::fs::read_to_string(&path).expect("readable source");
        if text.contains(needle) {
            offenders.push(path.display().to_string());
        }
    }
    assert!(
        offenders.is_empty(),
        "P3 retired the rung-3 seam; stale label in {offenders:?}"
    );
}

/// The three literal kinds are REGISTERED, so they must no longer
/// appear in `dispatch`'s deferral table or land on its catch-all.
#[test]
fn literal_kinds_are_registered_not_deferred() {
    for kind in ["num", "char", "scientific", "str"] {
        assert!(
            leanr_elab::dispatch::elaborator_name_for(kind).is_some(),
            "{kind} must be registered after M4b-3 P3"
        );
    }
    let doc = std::fs::read_to_string("crates/leanr_elab/src/dispatch.rs")
        .expect("dispatch.rs is readable");
    assert!(
        !doc.contains("num / char literals"),
        "dispatch's deferral table still defers num/char"
    );
}

/// Every seam message in the crate names a slice that still OWNS
/// something. P3 shipped rung 3 and the three literals, so no message
/// may name "M4b-3 P3" any more.
#[test]
fn no_seam_message_names_the_completed_p3_slice() {
    let mut offenders = Vec::new();
    for path in walk_rs_files("crates/leanr_elab/src") {
        let text = std::fs::read_to_string(&path).expect("readable source");
        for (i, line) in text.lines().enumerate() {
            // Doc comments may cite P3 historically; only a seam
            // MESSAGE (a string literal handed to UnsupportedSyntax) is
            // a live claim.
            if line.contains("M4b-3 P3") && !line.trim_start().starts_with("//") {
                offenders.push(format!("{}:{}", path.display(), i + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "P3 is complete; live seam claiming it at {offenders:?}"
    );
}
```

Delete `seam_audit.rs`'s assertions that `num`/`char` reach `UnsupportedSyntax` — grep for `"num"` and `"char"` inside `deferred_constructs_are_named_seams` and `unregistered_kinds_are_named_by_kind` and remove those cases, since the constructs are now implemented.

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test --package leanr_elab --test seam_audit`
Expected: FAIL — `no_seam_message_names_the_completed_p3_slice` reports the `u64`-overflow seam messages Tasks 6 and 7 wrote, which contain the literal text `M4b-3 P3`.

- [ ] **Step 3: Reconcile the seam labels**

The overflow seams are real and must stay, but "M4b-3 P3" is now a completed slice, so they need an owner that still exists. Retarget both messages (in `decode_nat_literal`'s call site in `elab_num` and in `elab_scientific`) to name the condition rather than a slice:

```rust
             "numeric literal `{raw}` is not a Nat literal \
              (or exceeds u64 — arbitrary-precision literals are \
              unreached by any committed corpus record; the slice that \
              first needs one owns widening this)"
```

Adjust `no_seam_message_names_the_completed_p3_slice` if a doc-comment citation trips it — the test deliberately only inspects non-comment lines, so a `/// oracle: … M4b-3 P3 …` citation is fine and should stay.

- [ ] **Step 4: Update the three deferral ledgers**

`crates/leanr_elab/src/lib.rs` — the module-doc ledger currently records P2a's gaps and names `num`/`char` and the `classExtension` work. Rewrite the P3-affected entries:

- delete the "num / char literals" deferral;
- change the rung-3 entry from "P2a supplies a shape-guarded seam, P3 replaces the body" to a statement that P3 shipped it, naming `synthetic/default_inst.rs`;
- **keep** the local-instance outParam entry, retargeting its "M4b-3 P2b" owner note to say that P2b now runs *after* P3 (design spec § Amendment 2);
- **keep** the `IsDefEqStuck` / mctx-depth gap verbatim — P3 does not close it, and it is the crate's own record of P2a's unreachable stuck path.

`crates/leanr_elab/src/dispatch.rs` — remove `num`/`char` from the deferred list; the remaining entries (`letI`/`haveI`/…, local-instance outParam, coercions, optParam/autoParam, implicit lambda, the M4b-4 group, macro expansion, `open`/alias resolution) are unchanged.

`crates/leanr_elab/src/synthetic/mod.rs` — update the layout block Task 1 wrote so `default_inst.rs`'s line reads "rung 3's real body (P3 task 5)" without the "P3 task 5" forward-looking framing.

`crates/leanr_elab/src/app/mod.rs` — its seam index lists `local-instance outParam result type .......... P2b args.rs, finalize.rs`. That line stays exactly as it is; P3 changed nothing in `app/`. Confirm by grep rather than by editing.

- [ ] **Step 5: Run the whole suite and both gates**

```bash
cd /workspace
cargo test --package leanr_elab
cargo test --package leanr_meta
mise run elab:fast
mise run meta:fast
```

Expected: PASS, all four.

- [ ] **Step 6: Final full-branch verification**

```bash
cd /workspace
mise run ci
git diff --stat main...HEAD
```

Expected: `mise run ci` green (it gates `cargo fmt --check`, clippy and the test suite). Read the diffstat and confirm it touches only the files this plan's § File Structure names — an unexpected file is a scope leak to explain, not to wave through.

- [ ] **Step 7: Commit**

```bash
cd /workspace
mise run fmt && mise run lint && mise run test
git add crates/leanr_elab
git commit -m "docs(elab): reconcile deferral ledgers and seam audit for P3

num/char/scientific are registered, not deferred; rung 3 is implemented,
not seamed. Three new gates: no source may still carry the retired
'requires synthesizeUsingDefault' label, the four literal kinds must all
be registered, and no live (non-comment) seam message may name the now
completed M4b-3 P3 slice. The u64-overflow literal seams stay but are
retargeted to name their condition rather than a finished slice.

The IsDefEqStuck / mctx-depth gap is kept verbatim: P3 does not close it.
The local-instance outParam entry is kept and retargeted to note that
P2b now runs after P3 (design spec § Amendment 2)."
```

---

## Self-Review

**1. Spec coverage.** Walking § P3 and § Amendment 2 of the design spec:

| Spec requirement | Task |
|---|---|
| `num` — `mkFreshTypeMVarFor`, `getDecLevel`, `OfNat` instance mvar, `registerMVarErrorImplicitArgInfo`, both failure branches distinct | 6 |
| `char` — `@Char.ofNat (rawNatLit c)`, no instance, no expected type | 7 |
| `scientific` — the `num` shape against `OfScientific` | 7 |
| `rawNatLit` excluded (no leanr parser producer) | not registered in Task 6/7's dispatch arms; gated by Task 8's `literal_kinds_are_registered_not_deferred`, which lists exactly four kinds |
| `synthesizeUsingDefault` — descending priority set, reverse-creation-order walk, queue rebuild | 5 |
| Nested fixpoint (`synthesizePending` → `synthesizeUsingInstances` → `synthesizeSomeUsingDefault?`) | 5 |
| `withAssignableSyntheticOpaque` as a `MetaCtx` config toggle | 4 (field + scope), 5 (use) |
| Module structure — `synthetic.rs` split, `lit.rs` split | 1, 6 |
| `Term.mkInstMVar` distinct from `ElabAppArgs`'s | 5 |
| Fixture growth — verbatim `Bool`/`OfNat`/`instOfNatNat`/`OfScientific`, opaque `Char`, `Tag` for `Int`, three priorities | 3 |
| The `natVal`-against-fixture-`Nat` risk, measured not assumed | 3 |
| Accessor ledger, including the `synth.rs` generalization and the `isClass?` fusion | 4 |
| Verification tiers 1/2/3 | 6+7 (corpus), 5 (orderings), 8 (seam audit) |
| Second instances per fixture class, as task 2 | 2 |
| `synthetic.rs` split *before* `default_inst.rs` | 1, ordered before 5 |

No gaps.

**2. Placeholder scan.** No "TBD", "TODO", "similar to Task N", or "add appropriate error handling". Two places delegate a decision to the implementer with explicit criteria rather than leaving it open: Task 4 Step 3's `is_prop` naming (grep, then take the simpler of two named options) and Task 5 Step 3's `restore` closure shape (two named options, with `RefCell` explicitly ruled out). Both are borrow-checker mechanics with a stated preferred outcome, not unspecified design.

**3. Type consistency.** Checked across tasks: `synthesize_using_default` gains `kinds: &KindInterner` in Task 5 and every caller (`ladder.rs`'s rung 3, `synthetic_smoke.rs`'s three tests, `support::visit_order_of_default_walk`) passes it. `mk_inst_mvar(ty, stx)` is defined in Task 5 and called in Tasks 6 and 7 with the same argument order. `const_with_level(elab, name, u)`, `mk_raw_nat_lit(elab, v)` and `app_n(elab, f, args)` are defined in Task 6 and used unchanged in Task 7. `forall_meta_telescope_reducing` returns `(Vec<ExprId>, Vec<BinderInfo>, ExprId)` in Task 4 and is destructured that way in both Task 4's `get_subgoals` and Task 5's `synthesize_using_default_instance`. `fixture_const`/`fixture_declares` are defined in Task 3 and reused by Task 5's `dflt_of_fresh_mvar`. `ElabError::{NumeralIsNotData, IllFormedLiteral}` are added in Task 6 and used in Task 7.

One deliberate asymmetry, flagged so it is not "fixed" during implementation: `elab_num` recovers from a `get_dec_level` failure and `elab_scientific` does not. That mirrors the oracle exactly — `BuiltinTerm.lean:216` wraps `getDecLevel` in `try`, `:241` does not.

---

## Execution Handoff

**Plan complete and saved to `docs/superpowers/plans/2026-07-28-m4b3-p3-literals-defaults.md`. Two execution options:**

**1. Subagent-Driven (recommended)** — I dispatch a fresh subagent per task, review between tasks, fast iteration

**2. Inline Execution** — Execute tasks in this session using executing-plans, batch execution with checkpoints

**Which approach?**
