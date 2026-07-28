# M4b-3 Plan 2a — Synthetic-MVar Ladder and Instance Arguments Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the `synthesizeSyntheticMVars` fixpoint and instance-implicit argument insertion so that typeclass applications elaborate byte-for-byte identically to the pinned Lean oracle, and so every synthetic metavariable leanr creates is either solved, resumed, or reported stuck — never silently dropped.

**Architecture:** A new `leanr_elab/src/synthetic.rs` transliterates `Lean/Elab/SyntheticMVars.lean`'s scheduler. The ladder's state (`pending_mvars`, `synthetic_mvars`, `mvar_error_infos`, `may_postpone`) lives directly on `TermElabM`, mirroring the oracle's `Term.State`/`Term.Context` one-to-one, with the `impl` block in `synthetic.rs` so `elab.rs` does not grow. `app/args.rs`'s `InstImplicit` arm and the three `inst_mvars` guards P1 left behind become real code driven by `synthesizeInstMVarCore`. The `classExtension` decode and `resultTypeOutParam?` support are **not** in this plan — they are M4b-3 P2b.

**Tech Stack:** Rust (workspace crates `leanr_elab`, `leanr_meta`, `leanr_kernel`, `leanr_syntax`), `cargo test`, mise tasks, Lean 4 `v4.33.0-rc1` as the differential oracle (dumper: `tests/fixtures/elab/dump_elab.lean`).

**Spec:** `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` (§ Amendment; § P2a — the synthetic-mvar ladder, the fixpoint, and instance arguments).

## Global Constraints

- **Pinned oracle:** `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`). Every oracle citation below is against `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`. **Never bump the pin.**
- **`leanr_kernel` is byte-untouched.** It depends on no workspace crate; no existing kernel function is modified, and no new one is added.
- **`leanr_meta/src` additions are additive, TCB-neutral, behavior-neutral accessors only.** This plan adds exactly two: `MetaCtx::process_postponed_levels` and `MetaCtx::default_instances_of` (Task 1). Nothing else in `leanr_meta` changes.
- **`leanr_olean` is untouched by this plan.** The `classExtension` decode is P2b's.
- **Named-seam discipline.** Every unimplemented construct returns `ElabError::UnsupportedSyntax` carrying a message that names the owning slice — never a panic, never a wrong `ExprId`, never a silent fall-through that emits a different term.
- **Oracle discipline.** Correctness is byte-for-byte agreement with the oracle's canonical `Expr` via `crates/leanr_elab/tests/oracle_elab.rs`. **Never hand-write an `exp` value in `elab-queries.jsonl`** — always regenerate with `mise run fixtures:regen-elab` and commit what the oracle emits.
- **Before every commit:** `mise run fmt`, then `mise run lint`, then `mise run test` (or `mise run ci`, which gates all three plus `cargo fmt --check`). Test gates do not cover formatting; CI does.
- **Regeneration needs the elan toolchain** (`mise run elan:bootstrap` once). It never runs in CI.

### Measured facts this plan is built on

These were established by a throwaway probe against the pinned oracle (a class-scaffolded copy of `Elab0`, never committed). They are **not** assumptions — do not re-derive them, but do let a contradiction stop you:

1. **Instance arguments resolve eagerly, without the ladder.** `synthesizeAppInstMVars` → `synthesizeInstMVarCore` succeeds at `finalize` time for ordinary typeclass applications. `useWrap Nat.zero`, `@useWrap Nat _ Nat.zero`, `usePair Nat.zero Nat.zero` all produce identical terms with and without `synthesizeSyntheticMVarsNoPostponing`. **Consequence:** instance-argument records can land in the corpus (Task 7) *before* the entry-point change (Task 9).
2. **Every ladder-exercising term in P2a's grammar ends in an error.** `useWrap` (bare) is a stuck typeclass problem; `fun f => f Nat.zero` postpones and then fails to resume. `dump_elab.lean` drops a throwing query (`IO.eprintln`, no record emitted), so **the ladder's coverage is Rust-side negative tests, not JSONL records.**
3. **`resumePostponed`'s success path has no P2a producer.** Every `tryPostpone*` site in `Lean/Elab` was enumerated: within P2a's grammar the only producer is `App.lean:1367`'s `tryPostponeIfMVar fType`, and every shape it reaches ends stuck. The others belong to M4b-4 (`resolveLValLoop` `App.lean:1680`, `resolveDottedIdentFn` `App.lean:1988`/`:2020`), P3 (`elabNum`, `BuiltinTerm.lean:163`), P5 (autoParam), and later M4 (`by`, `StructInst.lean`, `Match.lean`, `Extra.lean`). This is a **named coverage gap**, recorded in Task 10 — the first differential coverage for a successful resume arrives with P3's numerals.
4. **`(fun f => f Nat.zero : (Nat -> Nat) -> Nat)` diverges today and still will after this plan.** The oracle succeeds (it propagates the expected type into the binder domain, so `fType` is never an mvar); leanr hits `args.rs`'s "too many arguments" seam because M4b-2's `fun` uses a fresh type mvar domain. Task 8 re-labels that seam; it does **not** fix it. The fix is expected-type propagation into `fun` binders, which belongs to the slice that grows binder breadth (P5).

---

## File Structure

**Created:**

| File | Responsibility |
|---|---|
| `crates/leanr_elab/src/synthetic.rs` | the whole scheduler: `PostponeBehavior`, `SavedContext`, `SyntheticMVarKind`, `SyntheticMVarDecl`, `MVarErrorInfo`/`MVarErrorKind`, registration helpers, `synthesize_synthetic_mvar`, `synthesize_synthetic_mvars_step`, the escalation ladder, `report_stuck_synthetic_mvars`, `with_synthesize` |
| `crates/leanr_elab/tests/synthetic_smoke.rs` | Rust-level unit tests for the orderings and stuck paths the oracle corpus cannot express |

**Modified:**

| File | Change |
|---|---|
| `crates/leanr_meta/src/metactx.rs` | add `process_postponed_levels`, `postponed_len`, `default_instances_of` (Task 1) |
| `crates/leanr_elab/src/elab.rs` | ladder state fields on `TermElabM`; `mk_fresh_expr_mvar_of_kind`; `elab_term_and_synthesize` entry point (Tasks 2, 9) |
| `crates/leanr_elab/src/lib.rs` | `pub mod synthetic;` + update the deferral ledger in the module doc (Tasks 2, 10) |
| `crates/leanr_elab/src/error.rs` | new variants (Tasks 4, 5, 8) |
| `crates/leanr_elab/src/builtin/ascription.rs` | rewire both arms through `with_synthesize` (Task 6) |
| `crates/leanr_elab/src/builtin/binder.rs` | `let`/`have` type elaboration through `with_synthesize(.partial)` (Task 6) |
| `crates/leanr_elab/src/app/args.rs` | real `process_inst_implicit_arg`; `synthesize_pending_and_normalize_fun_type` (Tasks 7, 8) |
| `crates/leanr_elab/src/app/finalize.rs` | replace two `inst_mvars` guards with `try_synthesize_app_inst_mvars` / `synthesize_app_inst_mvars` (Task 7) |
| `crates/leanr_elab/src/app/propagate.rs` | replace the third `inst_mvars` guard (Task 7) |
| `crates/leanr_elab/src/app/mod.rs` | update the seam index in the module doc (Task 10) |
| `crates/leanr_elab/src/dispatch.rs` | update the deferral table (Task 10) |
| `crates/leanr_elab/tests/seam_audit.rs` | retarget P2 seam messages; add the stuck-path assertions (Task 10) |
| `tests/fixtures/elab/Elab0.lean` | the class/instance scaffold (Task 7) |
| `tests/fixtures/elab/dump_elab.lean` | new query lists (Task 7); the entry-point change (Task 9) |
| `tests/fixtures/elab/elab-queries.jsonl` | regenerated (never hand-edited) |
| `tests/fixtures/elab/Elab0.olean` | rebuilt when `Elab0.lean` changes |
| `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` | accessor-ledger correction (Task 1) |

---

## Task 1: `leanr_meta` accessors — postponed level constraints and default instances

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs`
- Modify: `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` (§ Accessor ledger)
- Test: `crates/leanr_meta/src/metactx.rs` (`#[cfg(test)] mod tests`, the module's existing convention)

**Interfaces:**
- Produces:
  - `MetaCtx::process_postponed_levels(&mut self) -> Result<bool, MetaError>`
  - `MetaCtx::postponed_len(&self) -> usize`
  - `MetaCtx::default_instances_of(&self, class: NameId) -> Vec<(NameId, usize)>`

**Spec-ledger correction to make in this task.** § Accessor ledger lists `with_assignable_synthetic_opaque` on P2a's row. It does not belong there: the oracle uses `withAssignableSyntheticOpaque` in exactly one place, `synthesizeUsingDefaultPrio` (`SyntheticMVars.lean:164`), which is P3's. Move that entry to the P3 row in the same commit. (`grep -rn "withAssignableSyntheticOpaque" ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/Lean/` confirms the single call site plus its `Meta/Basic.lean:1312` definition.)

- [ ] **Step 1: Write the failing tests**

Append to `crates/leanr_meta/src/metactx.rs`'s existing `#[cfg(test)] mod tests`:

```rust
    #[test]
    fn process_postponed_levels_drains_an_empty_queue() {
        with_test_ctx(|ctx| {
            assert_eq!(ctx.postponed_len(), 0);
            // An empty queue is vacuously solvable: the oracle's
            // `processPostponed` returns `true` when there is nothing
            // left to solve (`level.rs::process_postponed`'s own
            // contract), which is what makes the ladder's final
            // `process_postponed_universe_constraints` a no-op on every
            // term that never postponed a level constraint.
            assert!(ctx.process_postponed_levels().expect("no error"));
            assert_eq!(ctx.postponed_len(), 0);
        });
    }

    #[test]
    fn default_instances_of_reads_the_default_instance_table() {
        // Mirrors `default_instances_finds_the_default_instance`
        // (instances.rs) through the new public accessor: the same
        // fixture, the same class, the same expected entry — proving the
        // accessor forwards rather than reimplementing.
        with_default_instance_ctx(|ctx, class, expected_name| {
            let found = ctx.default_instances_of(class);
            assert_eq!(found.len(), 1, "one default instance for the class");
            assert_eq!(found[0].0, expected_name);
        });
    }
```

`with_test_ctx` and `with_default_instance_ctx` are this module's existing test-context builders. Read `crates/leanr_meta/src/instances.rs:581`'s `default_instances_finds_the_default_instance` first and reuse **its** construction verbatim rather than inventing one — if it builds its context inline instead of through a helper, do the same here and drop `with_default_instance_ctx`.

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_meta metactx::tests::process_postponed_levels -- --nocapture`
Expected: FAIL — `no method named process_postponed_levels found for struct MetaCtx`.

- [ ] **Step 3: Write the accessors**

In `crates/leanr_meta/src/metactx.rs`, alongside the other `pub fn` accessors (after `matcher_of`, `metactx.rs:773`):

```rust
    /// oracle: `processPostponed (mayPostpone := false)`
    /// (`Lean/Meta/LevelDefEq.lean`), reached from
    /// `Lean.Elab.Term.processPostponedUniverseConstraints`
    /// (`SyntheticMVars.lean:409-411`) — the ladder's final step when
    /// `postpone == .no`.
    ///
    /// Additive and behavior-neutral: a thin `pub` forwarder to the
    /// existing `pub(crate)` `level::process_postponed`
    /// (`level.rs:741`), which `defeq.rs:102` already calls on the same
    /// queue. No new logic, no TCB surface — `leanr_elab` simply cannot
    /// reach a `pub(crate)` item from another crate.
    ///
    /// Returns `true` when every postponed constraint was solved.
    /// leanr does NOT model the oracle's `exceptionOnFailure` parameter:
    /// that flag exists to guarantee `throwStuckAtUniverseCnstr`'s
    /// "entries is not empty" precondition, and leanr's caller reports
    /// stuck constraints from the `false` verdict instead of from a
    /// thrown exception (`synthetic.rs`'s
    /// `process_postponed_universe_constraints`).
    pub fn process_postponed_levels(&mut self) -> Result<bool, MetaError> {
        self.process_postponed()
    }

    /// The number of postponed level constraints. The oracle's
    /// `getNumPostponed` (`Lean/Meta/Basic.lean`), used by
    /// `defeq.rs:173`'s own postponed-count guard and, from P2a on, by
    /// the ladder's checkpoint bookkeeping.
    pub fn postponed_len(&self) -> usize {
        self.postponed.len()
    }

    /// oracle: `getDefaultInstances` (`Lean/Meta/Instances.lean`),
    /// consumed by `synthesizeSomeUsingDefaultPrio`
    /// (`SyntheticMVars.lean:213-221`).
    ///
    /// Additive: a `pub` forwarder to the existing `pub(crate)`
    /// `InstanceTable::default_instances` (`instances.rs:520`). P2a uses
    /// it only to shape-guard the `synthesize_using_default` seam — "are
    /// there default instances that WOULD apply here?" — so that P3 can
    /// replace the seam body without the guard having lied in the
    /// meantime. Each entry is `(instance name, priority)`.
    pub fn default_instances_of(&self, class: NameId) -> Vec<(NameId, usize)> {
        self.instances.default_instances(class)
    }
```

Adjust the two field paths (`self.postponed`, `self.instances`) to whatever `MetaCtx` actually names them — read `metactx.rs:261`'s `new` and `defeq.rs:99-107`'s use of `self.postponed` first. Do not add fields.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p leanr_meta metactx::tests::`
Expected: PASS, and no other `leanr_meta` test changes status.

- [ ] **Step 5: Amend the spec's accessor ledger**

In `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` § Accessor ledger, edit the P2a row to name the accessors as built and move `with_assignable_synthetic_opaque` to the P3 row:

```markdown
| P2a | `process_postponed_levels` + `postponed_len`, `default_instances_of` (forwarding the `pub(crate)` `instances.rs:520` — needed by rung 3's guarded seam) |
| P3 | `get_dec_level`, `mk_raw_nat_lit`, `with_assignable_synthetic_opaque` (used only by `synthesizeUsingDefaultPrio`, `SyntheticMVars.lean:164` — moved here from P2a, whose ladder never reaches it) |
```

- [ ] **Step 6: Commit**

```bash
mise run fmt && mise run lint && mise run test
git add crates/leanr_meta/src/metactx.rs docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md
git commit -m "M4b-3 P2a task 1: process_postponed_levels/default_instances_of accessors + ledger fix"
```

---

## Task 2: Ladder state, types, and registration

**Files:**
- Create: `crates/leanr_elab/src/synthetic.rs`
- Create: `crates/leanr_elab/tests/synthetic_smoke.rs`
- Modify: `crates/leanr_elab/src/elab.rs`, `crates/leanr_elab/src/lib.rs`

**Interfaces:**
- Consumes: `TermElabM` (`elab.rs:15`), `MVarId`/`MVarKind`/`MVarDecl` (`leanr_meta::mvar_ctx`), `SynElem` (`dispatch.rs:39`).
- Produces:
  - `synthetic::{PostponeBehavior, SavedContext, SyntheticMVarKind, SyntheticMVarDecl, MVarErrorKind, MVarErrorInfo}`
  - `TermElabM` fields `pending_mvars: Vec<MVarId>`, `synthetic_mvars: HashMap<MVarId, SyntheticMVarDecl>`, `mvar_error_infos: Vec<MVarErrorInfo>`, `may_postpone: bool`
  - `TermElabM::{register_synthetic_mvar, register_mvar_error_implicit_arg_info, register_mvar_error_hole_info, mark_as_resolved, synthetic_mvar_decl, save_context, without_postponing, mk_fresh_expr_mvar_of_kind}`

**Design note — storing the syntax reference.** The oracle's `SyntheticMVarDecl.stx` is a `Syntax`. leanr's equivalent is `SynElem` (`rowan::NodeOrToken<SyntaxNode, SyntaxToken>`), which is an **owned**, `Clone` handle into an Rc-backed green tree — so it can be stored in the table without a lifetime parameter. The `KindInterner` cannot: `TermElabM`'s module doc pins that it is "passed to `elab_term`, never stored". So every fixpoint entry point takes `kinds: &KindInterner`, exactly as `elab_term` does. One elaboration uses one tree, so one interner is always the right one; assert that contract in the doc comment rather than trying to store per-decl interners.

- [ ] **Step 1: Write the failing test**

Create `crates/leanr_elab/tests/synthetic_smoke.rs`:

```rust
//! M4b-3 P2a: Rust-level tests for the scheduler's state and orderings.
//! These live here, not in `oracle_elab.rs`, because every term that
//! exercises the ladder ends in an ERROR in the oracle too, and
//! `dump_elab.lean` drops a throwing query rather than recording it
//! (plan § Measured facts, item 2).

mod support;

use leanr_elab::synthetic::{PostponeBehavior, SyntheticMVarKind};

#[test]
fn registering_a_synthetic_mvar_makes_it_pending_and_findable() {
    support::with_app_harness("Nat.zero", |app| {
        let ty = app.st.f_type;
        let (_e, mvar_id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(ty, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        assert!(app.elab.pending_mvars.is_empty(), "nothing pending yet");

        let stx = support::any_syn_elem();
        app.elab
            .register_synthetic_mvar(stx, mvar_id, SyntheticMVarKind::TypeClass);

        // oracle: `registerSyntheticMVar` (`TermElabM.lean:864-865`) —
        // inserts into `syntheticMVars` AND conses onto `pendingMVars`,
        // head-is-most-recent.
        assert_eq!(app.elab.pending_mvars, vec![mvar_id]);
        assert!(app.elab.synthetic_mvar_decl(mvar_id).is_some());

        // oracle: `markAsResolved` (`SyntheticMVars.lean:417-418`) erases
        // from `syntheticMVars` only — `pendingMVars` is managed by the
        // step's own filter, not here.
        app.elab.mark_as_resolved(mvar_id);
        assert!(app.elab.synthetic_mvar_decl(mvar_id).is_none());
        assert_eq!(app.elab.pending_mvars, vec![mvar_id]);
    });
}

#[test]
fn without_postponing_restores_the_flag_on_both_paths() {
    support::with_app_harness("Nat.zero", |app| {
        // oracle: `withoutPostponing` (`TermElabM.lean:1049-1050`) is a
        // READER modification — `mayPostpone := false` for the duration,
        // restored afterwards. leanr's is a field, so the restore is
        // explicit and must survive an early return.
        app.elab.may_postpone = true;
        let ok: Result<u8, leanr_elab::ElabError> =
            app.elab.without_postponing(|e| {
                assert!(!e.may_postpone);
                Ok(1)
            });
        assert_eq!(ok.expect("ok path"), 1);
        assert!(app.elab.may_postpone, "restored after the ok path");

        let err: Result<u8, leanr_elab::ElabError> =
            app.elab.without_postponing(|e| {
                assert!(!e.may_postpone);
                Err(leanr_elab::ElabError::UnsupportedSyntax("probe".into()))
            });
        assert!(err.is_err());
        assert!(app.elab.may_postpone, "restored after the error path");
    });
}

#[test]
fn postpone_behavior_is_three_valued() {
    // oracle: `inductive PostponeBehavior` (`SyntheticMVars.lean:423-441`)
    // — `yes` / `no` / `partial`. The third value is not decorative:
    // `let`'s type elaboration uses it (`Binders.lean:775`), and the
    // ladder's rungs 2-5 are gated on `postpone != .yes`, which is a
    // DIFFERENT test from `postpone == .no`.
    assert_ne!(PostponeBehavior::Partial, PostponeBehavior::Yes);
    assert_ne!(PostponeBehavior::Partial, PostponeBehavior::No);
}
```

Add `any_syn_elem()` to `crates/leanr_elab/tests/support/mod.rs` — a helper that parses `"Nat.zero"` and returns the owned term child, for tests that need *a* syntax reference and do not care which:

```rust
/// A syntax reference for tests that need one but do not care which.
/// `SynElem` is an owned rowan handle, so the parse tree it points into
/// stays alive through the returned value.
pub fn any_syn_elem() -> leanr_elab::dispatch::SynElem {
    use leanr_syntax::{builtin, parse_term};
    let snap = builtin::snapshot();
    let parsed = parse_term("Nat.zero", &snap);
    assert!(parsed.errors.is_empty());
    parsed
        .tree
        .root()
        .first_child_or_token()
        .expect("term child")
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_elab --test synthetic_smoke`
Expected: FAIL to compile — `unresolved import leanr_elab::synthetic`.

- [ ] **Step 3: Create `synthetic.rs` with the types and registration**

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

use std::collections::HashMap;

use leanr_kernel::bank::{ExprId, NameId};
use leanr_meta::MVarId;

use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `inductive PostponeBehavior` (`SyntheticMVars.lean:423-441`).
///
/// Three-valued, not a `bool`: `Partial` means "typeclass problems may
/// be postponed, everything else may not" and is what `let`'s type
/// elaboration uses (`Binders.lean:775`). The ladder gates rungs 2-5 on
/// `!= Yes` and the stuck report on `== No` — two different tests that a
/// boolean would collapse.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PostponeBehavior {
    Yes,
    No,
    Partial,
}

/// oracle: `structure SavedContext` (`TermElabM.lean:45-53`).
///
/// The oracle saves seven fields; leanr models the two that exist here.
/// `declName?`, `options`, `openDecls`, `macroStack` and
/// `fixedTermElabs` have no leanr counterpart yet — there is no command
/// layer, no options plumbing, no `open` resolution (`resolve.rs`'s own
/// deferral) and no macro stack (`dispatch.rs` never expands a macro).
/// Each arrives with the slice that adds the concept; adding empty
/// placeholders now would be speculative surface.
#[derive(Debug, Clone)]
pub struct SavedContext {
    pub level_names: Vec<NameId>,
    pub may_postpone: bool,
}

/// oracle: `inductive SyntheticMVarKind` (`TermElabM.lean:65-92`).
///
/// **All four variants exist from P2a**, even though P2a produces only
/// `TypeClass` and `Postponed`: the oracle's control flow branches on
/// the kind in places far from where it is set, and a missing variant is
/// a silent fidelity hole where a missing *arm* is a named seam. P4
/// produces `Coe`; P5 registers `Tactic`.
///
/// The oracle's message-carrying payloads (`extraErrorMsg?`,
/// `mkErrorMsg?`, `header?`) are omitted: leanr defers the prose layer
/// (design spec § Amendment, item 2). `Coe` keeps the two payloads that
/// are `Expr`s rather than messages, because P4's arm computes with
/// them.
#[derive(Debug, Clone)]
pub enum SyntheticMVarKind {
    TypeClass,
    Coe { expected_type: ExprId, e: ExprId },
    Tactic,
    Postponed { ctx: SavedContext },
}

/// oracle: `structure SyntheticMVarDecl` (`TermElabM.lean:105-108`).
///
/// `stx` is a `SynElem` — an OWNED rowan handle (`rowan::SyntaxNode` is
/// Rc-backed), so the table needs no lifetime parameter. The matching
/// `KindInterner` is NOT stored: `TermElabM`'s module doc pins that it
/// is passed per call, so every fixpoint entry point takes `kinds`
/// instead. One elaboration uses one tree, so one interner is always the
/// right one.
#[derive(Debug, Clone)]
pub struct SyntheticMVarDecl {
    pub stx: SynElem,
    pub kind: SyntheticMVarKind,
}

/// oracle: `inductive MVarErrorKind` (`TermElabM.lean:116-124`).
#[derive(Debug, Clone)]
pub enum MVarErrorKind {
    /// oracle: `.implicitArg (lctx) (ctx)` — the parent application.
    /// leanr stores only the application: the oracle's `lctx` exists for
    /// the named-argument eta feature's error rendering, which is prose.
    ImplicitArg { app: ExprId },
    Hole,
}

/// oracle: `structure MVarErrorInfo` (`TermElabM.lean:135-139`).
/// Registered here, rendered by whichever slice grows a diagnostics
/// layer (design spec § Amendment, item 2).
#[derive(Debug, Clone)]
pub struct MVarErrorInfo {
    pub mvar_id: MVarId,
    pub stx: SynElem,
    pub kind: MVarErrorKind,
}

impl<'e> TermElabM<'e> {
    /// oracle: `registerSyntheticMVar` (`TermElabM.lean:864-865`).
    /// `pending_mvars` is a list whose **head is the most recent** — the
    /// oracle conses, so leanr inserts at 0. Every ordering in this
    /// module depends on that invariant.
    pub fn register_synthetic_mvar(
        &mut self,
        stx: SynElem,
        mvar_id: MVarId,
        kind: SyntheticMVarKind,
    ) {
        self.synthetic_mvars
            .insert(mvar_id, SyntheticMVarDecl { stx, kind });
        self.pending_mvars.insert(0, mvar_id);
    }

    /// oracle: `getSyntheticMVarDecl?` (`TermElabM.lean:1455-1456`).
    pub fn synthetic_mvar_decl(&self, mvar_id: MVarId) -> Option<&SyntheticMVarDecl> {
        self.synthetic_mvars.get(&mvar_id)
    }

    /// oracle: `markAsResolved` (`SyntheticMVars.lean:417-418`) — erases
    /// from `syntheticMVars` ONLY. `pending_mvars` is managed by the
    /// step's own filter; removing it here too would double-remove and
    /// break the step's progress count.
    pub fn mark_as_resolved(&mut self, mvar_id: MVarId) {
        self.synthetic_mvars.remove(&mvar_id);
    }

    /// oracle: `registerMVarErrorImplicitArgInfo` (`TermElabM.lean:876-877`).
    pub fn register_mvar_error_implicit_arg_info(
        &mut self,
        mvar_id: MVarId,
        stx: SynElem,
        app: ExprId,
    ) {
        self.mvar_error_infos.push(MVarErrorInfo {
            mvar_id,
            stx,
            kind: MVarErrorKind::ImplicitArg { app },
        });
    }

    /// oracle: `registerMVarErrorHoleInfo` (`TermElabM.lean:873-874`).
    pub fn register_mvar_error_hole_info(&mut self, mvar_id: MVarId, stx: SynElem) {
        self.mvar_error_infos.push(MVarErrorInfo {
            mvar_id,
            stx,
            kind: MVarErrorKind::Hole,
        });
    }

    /// oracle: `saveContext` (`TermElabM.lean:1420-1428`), restricted to
    /// the fields leanr has (see `SavedContext`).
    pub fn save_context(&self) -> SavedContext {
        SavedContext {
            level_names: self.level_names.clone(),
            may_postpone: self.may_postpone,
        }
    }

    /// oracle: `withSavedContext` (`TermElabM.lean:1434-1442`).
    /// Restores on BOTH paths — the oracle gets that from `withReader`'s
    /// scoping; leanr's is a field, so the restore is explicit.
    pub fn with_saved_context<R>(
        &mut self,
        saved: &SavedContext,
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let prev_levels = std::mem::replace(&mut self.level_names, saved.level_names.clone());
        let prev_postpone = std::mem::replace(&mut self.may_postpone, saved.may_postpone);
        let out = k(self);
        self.level_names = prev_levels;
        self.may_postpone = prev_postpone;
        out
    }

    /// oracle: `withoutPostponing` (`TermElabM.lean:1049-1050`).
    pub fn without_postponing<R>(
        &mut self,
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let prev = std::mem::replace(&mut self.may_postpone, false);
        let out = k(self);
        self.may_postpone = prev;
        out
    }
}
```

- [ ] **Step 4: Add the state to `TermElabM`**

In `crates/leanr_elab/src/elab.rs`, add to the struct (after `binder_name_gen`):

```rust
    /// oracle: `Term.State.pendingMVars` (`TermElabM.lean:180`). **Head
    /// is the most recent** — the oracle conses. Every ordering in
    /// `synthetic.rs` depends on that invariant.
    pub pending_mvars: Vec<MVarId>,
    /// oracle: `Term.State.syntheticMVars` (`TermElabM.lean:183`).
    pub synthetic_mvars: HashMap<MVarId, crate::synthetic::SyntheticMVarDecl>,
    /// oracle: `Term.State.mvarErrorInfos` (`TermElabM.lean:185`).
    /// Registered by P2a, rendered by whichever slice grows a
    /// diagnostics layer (design spec § Amendment, item 2).
    pub mvar_error_infos: Vec<crate::synthetic::MVarErrorInfo>,
    /// oracle: `Term.Context.mayPostpone` — a READER field there, a
    /// plain field here, saved/restored by `without_postponing` and
    /// `with_saved_context`. Defaults to `true`, matching `elabTerm`'s
    /// own `catchExPostpone := true` default (`TermElabM.lean:1879`).
    pub may_postpone: bool,
```

Initialize in `new`: `pending_mvars: Vec::new(), synthetic_mvars: HashMap::new(), mvar_error_infos: Vec::new(), may_postpone: true,` and add `use std::collections::HashMap;`.

Add the kind-taking mvar constructor next to `mk_fresh_expr_mvar`. Do **not** change `mk_fresh_expr_mvar`'s signature — P1 has ten call sites:

```rust
    /// oracle: `mkFreshExprMVar ty kind` — as `mk_fresh_expr_mvar`, but
    /// with the caller choosing `MVarKind` and receiving the `MVarId`
    /// alongside the `ExprId`.
    ///
    /// P2a needs both: an instance-implicit argument is minted
    /// `MetavarKind.synthetic` (`App.lean:919`, so `isDefEq` may assign
    /// it — unlike `syntheticOpaque`), and the caller must keep its
    /// `MVarId` to push onto `instMVars`. `mk_fresh_expr_mvar` stays the
    /// `Natural` + `ExprId`-only path P1's callers use.
    pub fn mk_fresh_expr_mvar_of_kind(
        &mut self,
        ty: ExprId,
        kind: MVarKind,
    ) -> Result<(ExprId, MVarId), ElabError> {
        // Body: `mk_fresh_expr_mvar`'s, verbatim, with `kind` threaded
        // into the `MVarDecl` and `(mvar_id, id)` returned. Then rewrite
        // `mk_fresh_expr_mvar` to delegate:
        //     self.mk_fresh_expr_mvar_of_kind(ty, MVarKind::Natural)
        //         .map(|(e, _)| e)
        // so the id-minting convention (`base = None`, the three
        // counters) lives in exactly one place.
        todo!("move mk_fresh_expr_mvar's body here; this todo must not survive this step")
    }
```

Register the module in `lib.rs`: `pub mod synthetic; // M4b-3 P2a`.

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p leanr_elab --test synthetic_smoke`
Expected: PASS, 3 tests.

Run: `cargo test -p leanr_elab`
Expected: every pre-existing test still passes — in particular `oracle_elab::oracle_elab_gate`, which must be unaffected: nothing added here is called yet.

- [ ] **Step 6: Commit**

```bash
mise run fmt && mise run lint && mise run test
git add crates/leanr_elab/src/synthetic.rs crates/leanr_elab/src/elab.rs crates/leanr_elab/src/lib.rs crates/leanr_elab/tests/synthetic_smoke.rs crates/leanr_elab/tests/support/mod.rs
git commit -m "M4b-3 P2a task 2: ladder state, synthetic-mvar types, registration helpers"
```

---

## Task 3: `synthesizeSyntheticMVarsStep` and its two orderings

**Files:**
- Modify: `crates/leanr_elab/src/synthetic.rs`
- Test: `crates/leanr_elab/tests/synthetic_smoke.rs`

**Interfaces:**
- Consumes: Task 2's state and types.
- Produces:
  - `TermElabM::synthesize_synthetic_mvar(&mut self, mvar_id, postpone_on_error: bool, run_tactics: bool, kinds: &KindInterner) -> Result<bool, ElabError>`
  - `TermElabM::synthesize_synthetic_mvars_step(&mut self, postpone_on_error: bool, run_tactics: bool, kinds: &KindInterner) -> Result<bool, ElabError>`

**Why this task is its own gate.** Two orderings inside the step are fidelity-critical and *invisible* on any corpus term: a version that gets them backwards still terminates and still looks green, then diverges on nested applications. Both are pinned by direct unit tests here, constructing the queue state by hand.

The oracle (`SyntheticMVars.lean:573-602`), stated precisely:

1. snapshot `pendingMVars` and record its length;
2. **clear** `pendingMVars` — new mvars created during the step land in a fresh list;
3. walk the snapshot with `filterRevM`, keeping the ones that did **not** succeed;
4. re-merge as `s.pendingMVars ++ remainingPendingMVars`, i.e. **new-pending first, then still-unsolved**;
5. progress is `numSyntheticMVars != remainingPendingMVars.length`.

`filterRevM` (`Init/Data/List/Control.lean:180-181`) is `filterAuxM p as.reverse []`: it visits **right-to-left** and, because `filterAuxM` prepends, returns survivors in the **original list order**. Since `pending_mvars` is head-is-most-recent, right-to-left is **oldest-first — creation order**, which is exactly why the oracle uses `filterRevM` and not `filterM`.

- [ ] **Step 1: Write the failing tests**

Append to `crates/leanr_elab/tests/synthetic_smoke.rs`:

```rust
/// The step visits pending mvars in CREATION order, not list order.
///
/// `pending_mvars` is head-is-most-recent, and the oracle walks it with
/// `filterRevM` (`SyntheticMVars.lean:596`), which visits right-to-left
/// — oldest first. `filterM` would visit newest first and still
/// terminate, which is why this needs a direct test.
#[test]
fn step_processes_pending_mvars_in_creation_order() {
    support::with_app_harness("Nat.zero", |app| {
        let ids = support::register_n_typeclass_mvars(app, 3);
        // Registered oldest..newest, so the list is newest..oldest.
        assert_eq!(
            app.elab.pending_mvars,
            vec![ids[2], ids[1], ids[0]],
            "head is most recent"
        );

        let seen = support::step_recording_visit_order(app);
        assert_eq!(
            seen,
            vec![ids[0], ids[1], ids[2]],
            "visited oldest-first (creation order)"
        );
    });
}

/// Survivors keep their ORIGINAL order (head still most recent), and
/// mvars created DURING the step land BEFORE them.
///
/// oracle: `pendingMVars := s.pendingMVars ++ remainingPendingMVars`
/// (`SyntheticMVars.lean:601`). Reversing that merge still terminates
/// and still looks green on simple terms, then diverges on nested
/// applications.
#[test]
fn step_merges_new_pending_before_still_unsolved() {
    support::with_app_harness("Nat.zero", |app| {
        let old = support::register_n_typeclass_mvars(app, 2);
        let fresh = support::step_creating_one_mvar_solving_none(app);
        assert_eq!(
            app.elab.pending_mvars,
            vec![fresh, old[1], old[0]],
            "new pending first, then still-unsolved in original order"
        );
    });
}

/// Progress is a COUNT comparison, not "any succeeded".
///
/// oracle: `return numSyntheticMVars != remainingPendingMVars.length`
/// (`SyntheticMVars.lean:602`). The comparison is SNAPSHOT length vs
/// SURVIVOR count — never the post-merge list — so mvars created during
/// the step can never mask progress. Two pending with one solved is
/// `2 != 1`, progress, however many new ones the step created.
#[test]
fn step_reports_progress_by_snapshot_count() {
    support::with_app_harness("Nat.zero", |app| {
        support::register_n_typeclass_mvars(app, 2);
        let progress = support::step_solving_exactly_one(app);
        assert!(progress, "2 pending, 1 solved -> progress");

        support::register_n_typeclass_mvars(app, 1);
        let progress = support::step_solving_none(app);
        assert!(!progress, "nothing solved -> no progress");
    });
}
```

Add these four helpers to `crates/leanr_elab/tests/support/mod.rs`. They construct queue state directly and drive the step with a stubbed per-mvar outcome, so the ordering assertions do not depend on real synthesis:

```rust
/// Register `n` `TypeClass` synthetic mvars, oldest first, returning
/// their ids in creation order.
pub fn register_n_typeclass_mvars(
    app: &mut leanr_elab::app::state::AppElab,
    n: usize,
) -> Vec<leanr_meta::MVarId> {
    use leanr_elab::synthetic::SyntheticMVarKind;
    let ty = app.st.f_type;
    let mut ids = Vec::new();
    for _ in 0..n {
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(ty, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        app.elab
            .register_synthetic_mvar(any_syn_elem(), id, SyntheticMVarKind::TypeClass);
        ids.push(id);
    }
    ids
}
```

`step_recording_visit_order`, `step_creating_one_mvar_solving_none`, `step_solving_exactly_one` and `step_solving_none` each need the step to run with a **caller-supplied outcome** rather than real synthesis. Implement that by giving `synthesize_synthetic_mvars_step` a sibling that takes a closure — `step_with(&mut self, f: impl FnMut(&mut Self, MVarId) -> Result<bool, ElabError>)` — with the real `synthesize_synthetic_mvars_step` delegating to it via `synthesize_synthetic_mvar`. That keeps the ordering logic in exactly one place and makes it testable without a class fixture. Write `step_with` in Step 3; write these helpers as thin wrappers over it.

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_elab --test synthetic_smoke step_`
Expected: FAIL to compile — `step_with` and the four helpers do not exist.

- [ ] **Step 3: Implement the step**

Append to `crates/leanr_elab/src/synthetic.rs`'s `impl TermElabM`:

```rust
    /// The ordering core of `synthesizeSyntheticMVarsStep`
    /// (`SyntheticMVars.lean:585-602`), with the per-mvar outcome
    /// supplied by the caller.
    ///
    /// Split out so the two fidelity-critical orderings can be tested
    /// without a class fixture (see `tests/synthetic_smoke.rs`): the real
    /// step passes `synthesize_synthetic_mvar`, tests pass a stub.
    pub fn step_with(
        &mut self,
        mut f: impl FnMut(&mut Self, MVarId) -> Result<bool, ElabError>,
    ) -> Result<bool, ElabError> {
        // oracle: `let pendingMVars := (← get).pendingMVars` then
        // `modify fun s => { s with pendingMVars := [] }` (:589-591) —
        // snapshot AND clear, so mvars created during the walk
        // accumulate in a fresh list.
        let pending = std::mem::take(&mut self.pending_mvars);
        let num_synthetic = pending.len();

        // oracle: `pendingMVars.filterRevM ..` (:596). `filterRevM` is
        // `filterAuxM p as.reverse []`
        // (`Init/Data/List/Control.lean:180-181`): it visits
        // RIGHT-TO-LEFT and, because `filterAuxM` prepends, returns the
        // survivors in the ORIGINAL list order. `pending_mvars` is
        // head-is-most-recent, so right-to-left is OLDEST-FIRST, i.e.
        // creation order — the oracle's own stated reason for using
        // `filterRevM` rather than `filterM`.
        let mut remaining = Vec::new();
        for mvar_id in pending.iter().rev().copied() {
            let succeeded = f(self, mvar_id)?;
            if succeeded {
                self.mark_as_resolved(mvar_id);
            } else {
                remaining.push(mvar_id);
            }
        }
        // Collected oldest-first; restore head-is-most-recent.
        remaining.reverse();

        // oracle: `pendingMVars := s.pendingMVars ++ remainingPendingMVars`
        // (:601) — `s.pendingMVars` here is what the walk CREATED, so
        // new-pending comes FIRST and still-unsolved after.
        let mut merged = std::mem::take(&mut self.pending_mvars);
        merged.extend(remaining.iter().copied());
        self.pending_mvars = merged;

        // oracle: `return numSyntheticMVars != remainingPendingMVars.length`
        // (:602) — against the SNAPSHOT length, not the merged list, so
        // newly created mvars can never mask progress.
        Ok(num_synthetic != remaining.len())
    }

    /// oracle: `synthesizeSyntheticMVarsStep` (`SyntheticMVars.lean:585-602`).
    pub fn synthesize_synthetic_mvars_step(
        &mut self,
        postpone_on_error: bool,
        run_tactics: bool,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        self.step_with(|elab, mvar_id| {
            elab.synthesize_synthetic_mvar(mvar_id, postpone_on_error, run_tactics, kinds)
        })
    }

    /// oracle: `synthesizeSyntheticMVar` (`SyntheticMVars.lean:539-571`).
    ///
    /// Returns `true` when the mvar was synthesized, `false` for "not
    /// ready yet". An mvar with no decl returns `true` — the oracle's
    /// `| return true -- The metavariable has already been synthesized`.
    pub fn synthesize_synthetic_mvar(
        &mut self,
        mvar_id: MVarId,
        postpone_on_error: bool,
        run_tactics: bool,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        let Some(decl) = self.synthetic_mvar_decl(mvar_id).cloned() else {
            return Ok(true);
        };
        match decl.kind {
            SyntheticMVarKind::TypeClass => self.synthesize_pending_inst_mvar(mvar_id),
            SyntheticMVarKind::Postponed { ref ctx } => {
                self.resume_postponed(ctx, &decl.stx, mvar_id, postpone_on_error, kinds)
            }
            SyntheticMVarKind::Coe { .. } => Err(ElabError::UnsupportedSyntax(
                "coercion synthetic mvars require coercion insertion — M4b-3 P4".to_string(),
            )),
            SyntheticMVarKind::Tactic => {
                // oracle: the `.tactic` arm runs the tactic only when
                // `runTactics` (`SyntheticMVars.lean:566-571`), and
                // returns `false` otherwise. Rung 5 is the only caller
                // that passes `run_tactics: true`, so this seam is
                // reachable ONLY there — a silent `false` here would make
                // the ladder report "stuck" for a reason the user cannot
                // see.
                if run_tactics {
                    Err(ElabError::UnsupportedSyntax(
                        "autoParam tactic execution requires the `by` elaborator — later M4"
                            .to_string(),
                    ))
                } else {
                    Ok(false)
                }
            }
        }
    }
```

`synthesize_pending_inst_mvar` is Task 4 and `resume_postponed` is Task 5. To keep this task's tests runnable, add both as temporary stubs returning `Ok(false)` with a `// Task 4` / `// Task 5` marker, and delete the markers in those tasks. Add `use leanr_syntax::kind::KindInterner;`.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p leanr_elab --test synthetic_smoke`
Expected: PASS, 6 tests.

- [ ] **Step 5: Commit**

```bash
mise run fmt && mise run lint && mise run test
git add crates/leanr_elab/src/synthetic.rs crates/leanr_elab/tests/synthetic_smoke.rs crates/leanr_elab/tests/support/mod.rs
git commit -m "M4b-3 P2a task 3: synthesizeSyntheticMVarsStep + creation-order/merge-order gates"
```

---

## Task 4: `synthesizeInstMVarCore` — the typeclass rung

**Files:**
- Modify: `crates/leanr_elab/src/synthetic.rs`, `crates/leanr_elab/src/error.rs`
- Test: `crates/leanr_elab/tests/synthetic_smoke.rs`

**Interfaces:**
- Consumes: `MetaCtx::synth_instance` (`synth.rs:1593`), `MetaCtx::{instantiate_mvars, infer_type, is_def_eq}`, `MetavarContext::{is_assigned, assignment, assign}`.
- Produces: `TermElabM::{synthesize_inst_mvar_core, synthesize_pending_inst_mvar}`.

**The trichotomy is the whole mechanism.** `trySynthInstance` returns `LOption` — `some` / `undef` / `none` — and leanr's `synth_instance` already mirrors it: `Ok(Some(e))` is `.some`, `Err(MetaError::IsDefEqStuck)` is `.undef` ("not ready yet"), `Ok(None)` is `.none` (a real failure). Collapsing `undef` into failure is what would break postponement; collapsing it into success would loop.

- [ ] **Step 1: Write the failing tests**

```rust
/// `Err(IsDefEqStuck)` from synthesis means POSTPONE, never fail.
///
/// oracle: `trySynthInstance`'s `.undef` -> `return false -- we will try
/// later` (`TermElabM.lean:1273`). This is the distinction the whole
/// postponement scheme rests on: `Ok(None)` is a real failure that
/// throws, `Err(IsDefEqStuck)` is "not ready yet" that survives to the
/// next rung.
#[test]
fn stuck_synthesis_is_not_ready_rather_than_failure() {
    support::with_app_harness("Nat.zero", |app| {
        // `Wrap ?m` — a class goal whose type argument is an unassigned
        // mvar, which is exactly what `synth_instance` reports stuck.
        let goal = support::wrap_of_fresh_mvar(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        let ready = app
            .elab
            .synthesize_inst_mvar_core(id)
            .expect("stuck is not an error");
        assert!(!ready, "stuck -> not ready yet");
        assert!(
            !app.elab.mctx.mctx().is_assigned(id),
            "a stuck goal assigns nothing"
        );
    });
}

/// A solvable goal is synthesized and ASSIGNED.
#[test]
fn solvable_instance_is_synthesized_and_assigned() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::wrap_of_nat(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        assert!(app.elab.synthesize_inst_mvar_core(id).expect("no error"));
        assert!(app.elab.mctx.mctx().is_assigned(id));
    });
}

/// A class with no instance is a real failure, not a postponement.
///
/// oracle: `trySynthInstance`'s `.none` arm throws
/// (`TermElabM.lean:1274+`).
#[test]
fn unsolvable_instance_is_a_synthesis_failure() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::no_inst_of_nat(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        assert!(matches!(
            app.elab.synthesize_inst_mvar_core(id),
            Err(leanr_elab::ElabError::InstanceSynthesisFailed { .. })
        ));
    });
}
```

`wrap_of_nat`, `wrap_of_fresh_mvar` and `no_inst_of_nat` build `Wrap Nat`, `Wrap ?m` and `NoInst Nat` as `ExprId`s against the fixture environment. They depend on Task 7's `Elab0.lean` scaffold — so **write these three tests now and mark them `#[ignore]` with the reason `"needs the Elab0 class scaffold (Task 7)"`, then remove the `#[ignore]` in Task 7 Step 6.** Do not weaken them into mvar-free stubs; the point is the trichotomy against real synthesis.

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_elab --test synthetic_smoke -- --ignored`
Expected: FAIL to compile — `synthesize_inst_mvar_core` and `ElabError::InstanceSynthesisFailed` do not exist.

- [ ] **Step 3: Add the error variant**

In `crates/leanr_elab/src/error.rs`:

```rust
    /// oracle: `synthesizeInstMVarCore`'s `.none` arm — "failed to
    /// synthesize" (`TermElabM.lean:1274+`). Carries the goal type; the
    /// oracle's `extraErrorMsg?` prose is deferred (design spec
    /// § Amendment, item 2).
    InstanceSynthesisFailed { goal: ExprId },
    /// oracle: `reportStuckSyntheticMVar`'s `.typeClass` arm —
    /// "typeclass instance problem is stuck"
    /// (`SyntheticMVars.lean:296-303`). Carries the goal type; the note
    /// and hint prose are deferred.
    StuckSyntheticMVar { goal: ExprId },
    /// oracle: `synthesizeInstMVarCore`'s two assignment-mismatch throws
    /// (`TermElabM.lean:1265-1271`) — the synthesized instance is not
    /// defeq to the one typing already inferred.
    InstanceMismatch { synthesized: ExprId, inferred: ExprId },
```

- [ ] **Step 4: Implement the rung**

```rust
    /// oracle: `synthesizeInstMVarCore` (`TermElabM.lean:1232-1275`).
    ///
    /// Returns `true` when the instance was synthesized, `false` when it
    /// is blocked by unassigned mvars ("try again later"), and errors
    /// when resolution or assignment irrevocably fails.
    pub fn synthesize_inst_mvar_core(&mut self, inst_mvar: MVarId) -> Result<bool, ElabError> {
        let ty = self
            .mctx
            .mctx()
            .decl(inst_mvar)
            .expect("instance mvar is declared")
            .ty;
        let ty = self.mctx.instantiate_mvars(ty)?;
        // The trichotomy: `Ok(Some)` = `.some`, `Err(IsDefEqStuck)` =
        // `.undef`, `Ok(None)` = `.none`. Preserving `undef` as "not
        // ready yet" rather than failure is the whole reason
        // postponement works.
        let val = match self.mctx.synth_instance(ty) {
            Ok(Some(val)) => val,
            Ok(None) => return Err(ElabError::InstanceSynthesisFailed { goal: ty }),
            Err(leanr_meta::MetaError::IsDefEqStuck) => return Ok(false),
            Err(e) => return Err(ElabError::from(e)),
        };
        if self.mctx.mctx().is_assigned(inst_mvar) {
            // oracle: :1240-1271 — the mvar may already carry a value
            // inferred by typing. Reconcile rather than overwrite.
            let old_val = self
                .mctx
                .mctx()
                .assignment(inst_mvar)
                .expect("just checked assigned");
            let old_val = self.mctx.instantiate_mvars(old_val)?;
            if !self.mctx.is_def_eq(old_val, val)? {
                // oracle: :1246-1249 — if EITHER side still mentions a
                // pending mvar, the mismatch is not yet grounded: return
                // `false` and retry later rather than throwing. Dropping
                // this branch turns a resolvable dependency between
                // postponed mvars into a hard error.
                if self.contains_pending_mvar(old_val)? || self.contains_pending_mvar(val)? {
                    return Ok(false);
                }
                let inferred = self.mctx.infer_type(old_val)?;
                return Err(ElabError::InstanceMismatch {
                    synthesized: val,
                    inferred,
                });
            }
        } else {
            // oracle: :1272-1273 — assign via `isDefEq`, not a raw
            // assign: the mvar's type may still need unification.
            if !self.mctx.is_def_eq_mvar_value(inst_mvar, val)? {
                return Err(ElabError::InstanceMismatch {
                    synthesized: val,
                    inferred: ty,
                });
            }
        }
        Ok(true)
    }

    /// oracle: `synthesizePendingInstMVar` (`SyntheticMVars.lean:79-85`)
    /// — `synthesizeInstMVarCore` with errors LOGGED rather than
    /// propagated, returning `true` so the mvar leaves the pending list.
    ///
    /// leanr has no message log, so a synthesis failure propagates as an
    /// `ElabError` instead of being logged and swallowed. That is the
    /// deliberate difference: the oracle keeps elaborating to collect
    /// more errors, leanr stops at the first. Recorded rather than
    /// hidden — the slice that adds a diagnostics layer revisits it.
    pub fn synthesize_pending_inst_mvar(&mut self, inst_mvar: MVarId) -> Result<bool, ElabError> {
        self.synthesize_inst_mvar_core(inst_mvar)
    }

    /// oracle: `containsPendingMVar` — does `e` mention an mvar that is
    /// still on the pending list?
    fn contains_pending_mvar(&mut self, e: ExprId) -> Result<bool, ElabError> {
        // Walk `e` collecting mvar ids and test membership in
        // `pending_mvars`. Use the same traversal idiom
        // `app/finalize.rs`'s `update_binder_names` uses (`app.node(e)`
        // over `Node`), not a new visitor abstraction.
        todo!("implement the walk; this todo must not survive this step")
    }
```

`is_def_eq_mvar_value` is not an existing `MetaCtx` method — build the `Expr.mvar` node for `inst_mvar` and call `is_def_eq` on it, exactly as `mk_fresh_expr_mvar` builds its own mvar node (`elab.rs`, `store.expr_mvar(None, Some(name))`). Do **not** add a `leanr_meta` accessor for it; the global constraint allows only Task 1's two.

- [ ] **Step 5: Run tests to verify they still fail for the right reason**

Run: `cargo test -p leanr_elab --test synthetic_smoke -- --ignored`
Expected: the three tests are `ignored` (not failing) — they light up in Task 7. `cargo test -p leanr_elab` must compile and stay green.

- [ ] **Step 6: Commit**

```bash
mise run fmt && mise run lint && mise run test
git add crates/leanr_elab/src/synthetic.rs crates/leanr_elab/src/error.rs crates/leanr_elab/tests/synthetic_smoke.rs
git commit -m "M4b-3 P2a task 4: synthesizeInstMVarCore + the some/undef/none trichotomy"
```

---

## Task 5: The escalation ladder, `resumePostponed`, and stuck reporting

**Files:**
- Modify: `crates/leanr_elab/src/synthetic.rs`
- Test: `crates/leanr_elab/tests/synthetic_smoke.rs`

**Interfaces:**
- Produces:
  - `TermElabM::synthesize_synthetic_mvars(&mut self, postpone: PostponeBehavior, kinds: &KindInterner) -> Result<(), ElabError>`
  - `TermElabM::synthesize_synthetic_mvars_no_postponing(&mut self, kinds: &KindInterner)`
  - `TermElabM::{resume_postponed, synthesize_using_default, report_stuck_synthetic_mvars, process_postponed_universe_constraints}`

The oracle's loop (`SyntheticMVars.lean:611-648`), stated exactly — note that the stuck report is the **last `else if` inside the loop body**, not a step after it, and that only `processPostponedUniverseConstraints` runs after `loop ()`:

```text
loop:
  unless pendingMVars.isEmpty:
    if step(postponeOnError := false, runTactics := false)      -> loop
    else if postpone != .yes:
      if withoutPostponing (step(postponeOnError := true,  runTactics := false)) -> loop
      else if synthesizeUsingDefault                             -> loop
      else if withoutPostponing (step(postponeOnError := false, runTactics := false)) -> loop
      else if step(postponeOnError := false, runTactics := true) -> loop
      else if postpone == .no: reportStuckSyntheticMVars
loop ()
if postpone == .no: processPostponedUniverseConstraints
```

- [ ] **Step 1: Write the failing tests**

```rust
/// The ladder terminates and reports a stuck typeclass problem.
///
/// Measured against the pinned oracle (plan § Measured facts, item 2):
/// `useWrap` with no expected type leaves `Wrap ?m` stuck, and the
/// oracle's own `synthesizeSyntheticMVarsNoPostponing` throws
/// "typeclass instance problem is stuck". leanr must do the same rather
/// than emitting a term with a dangling mvar.
#[test]
#[ignore = "needs the Elab0 class scaffold (Task 7)"]
fn bare_typeclass_application_is_reported_stuck() {
    let err = support::elab_and_synthesize("useWrap").expect_err("stuck");
    assert!(matches!(
        err,
        leanr_elab::ElabError::StuckSyntheticMVar { .. }
    ));
}

/// `postpone == .yes` does NOT report stuck — it leaves the mvar
/// pending for an outer scheduler.
///
/// oracle: rungs 2-5 and the stuck report are all under
/// `else if postpone != .yes` / `else if postpone == .no`
/// (`SyntheticMVars.lean:617,646`).
#[test]
#[ignore = "needs the Elab0 class scaffold (Task 7)"]
fn postpone_yes_leaves_the_mvar_pending() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::wrap_of_fresh_mvar(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        app.elab.register_synthetic_mvar(
            support::any_syn_elem(),
            id,
            leanr_elab::synthetic::SyntheticMVarKind::TypeClass,
        );
        let kinds = support::any_kinds();
        app.elab
            .synthesize_synthetic_mvars(leanr_elab::synthetic::PostponeBehavior::Yes, &kinds)
            .expect("postpone := .yes never reports stuck");
        assert_eq!(app.elab.pending_mvars, vec![id], "still pending");
    });
}

/// The default-instance seam fires only when default instances could
/// actually apply.
///
/// Rung 3 is P3's `synthesizeUsingDefault`. P2a supplies a SHAPE-GUARDED
/// stand-in: it errors when a pending `TypeClass` mvar's class has
/// default instances registered — the state in which the real rung would
/// have done something — and reports no progress otherwise. A blanket
/// `false` would silently skip a rung the oracle runs.
#[test]
fn synthesize_using_default_is_a_shape_guarded_seam() {
    support::with_app_harness("Nat.zero", |app| {
        // No pending mvars at all: no-op, no progress, no error.
        assert!(!app
            .elab
            .synthesize_using_default()
            .expect("no pending mvars -> no-op"));
    });
}

/// The stuck report drains `pending_mvars` before reporting.
///
/// oracle: `let pendingMVars ← modifyGet fun s => (s.pendingMVars,
/// { s with pendingMVars := [] })` (`SyntheticMVars.lean:323`).
#[test]
#[ignore = "needs the Elab0 class scaffold (Task 7)"]
fn stuck_report_drains_the_pending_list() {
    support::with_app_harness("Nat.zero", |app| {
        let goal = support::wrap_of_fresh_mvar(app);
        let (_e, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(goal, leanr_meta::MVarKind::Synthetic)
            .expect("fresh mvar");
        app.elab.register_synthetic_mvar(
            support::any_syn_elem(),
            id,
            leanr_elab::synthetic::SyntheticMVarKind::TypeClass,
        );
        let _ = app.elab.report_stuck_synthetic_mvars();
        assert!(app.elab.pending_mvars.is_empty(), "drained before reporting");
    });
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_elab --test synthetic_smoke synthesize_using_default`
Expected: FAIL to compile — the methods do not exist.

- [ ] **Step 3: Implement the ladder**

```rust
    /// oracle: `synthesizeSyntheticMVars` (`SyntheticMVars.lean:611-648`).
    ///
    /// Transliterated structurally, including two things easy to get
    /// subtly wrong: the stuck report is the LAST `else if` INSIDE the
    /// loop body (not a step after it), and only
    /// `processPostponedUniverseConstraints` runs after the loop.
    ///
    /// leanr drops the oracle's `ignoreStuckTC` parameter: its only
    /// caller is `simp` argument elaboration, which no leanr slice has.
    pub fn synthesize_synthetic_mvars(
        &mut self,
        postpone: PostponeBehavior,
        kinds: &KindInterner,
    ) -> Result<(), ElabError> {
        loop {
            if self.pending_mvars.is_empty() {
                break;
            }
            if self.synthesize_synthetic_mvars_step(false, false, kinds)? {
                continue;
            }
            if postpone == PostponeBehavior::Yes {
                break;
            }
            // Rung 2: postponement disabled, elaboration errors
            // postponed. The oracle's own worked example
            // (:618-635) is why `postponeOnError` and `mayPostpone` are
            // separate knobs.
            if self.without_postponing(|e| e.synthesize_synthetic_mvars_step(true, false, kinds))? {
                continue;
            }
            // Rung 3: default instances (P3; shape-guarded seam here).
            if self.synthesize_using_default()? {
                continue;
            }
            // Rung 4: postponement disabled, errors NOT postponed —
            // force a commitment.
            if self.without_postponing(|e| e.synthesize_synthetic_mvars_step(false, false, kinds))? {
                continue;
            }
            // Rung 5: run tactics.
            if self.synthesize_synthetic_mvars_step(false, true, kinds)? {
                continue;
            }
            if postpone == PostponeBehavior::No {
                self.report_stuck_synthetic_mvars()?;
            }
            break;
        }
        if postpone == PostponeBehavior::No {
            self.process_postponed_universe_constraints()?;
        }
        Ok(())
    }

    /// oracle: `synthesizeSyntheticMVarsNoPostponing`
    /// (`SyntheticMVars.lean:650-651`).
    pub fn synthesize_synthetic_mvars_no_postponing(
        &mut self,
        kinds: &KindInterner,
    ) -> Result<(), ElabError> {
        self.synthesize_synthetic_mvars(PostponeBehavior::No, kinds)
    }

    /// oracle: `resumePostponed` (`SyntheticMVars.lean:88-144`) —
    /// re-elaborate the postponed syntax under its saved context, ensure
    /// it has the mvar's type, and assign.
    ///
    /// The oracle's `occursCheck` guard before assigning is preserved:
    /// a resumed result may mention `mvarId` itself when it contains
    /// synthetic `sorry`s.
    fn resume_postponed(
        &mut self,
        ctx: &SavedContext,
        stx: &SynElem,
        mvar_id: MVarId,
        postpone_on_error: bool,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        let expected = self
            .mctx
            .mctx()
            .decl(mvar_id)
            .expect("postponed mvar is declared")
            .ty;
        let expected = self.mctx.instantiate_mvars(expected)?;
        let stx = stx.clone();
        let result = self.with_saved_context(ctx, |elab| {
            elab.elab_term_ensuring_type(&stx, kinds, Some(expected))
        });
        match result {
            Ok(e) => {
                self.mctx.mctx_mut().assign(mvar_id, e)?;
                Ok(true)
            }
            // oracle: :137-144 — on an ERROR, `postponeOnError` decides
            // between "restore and try again later" (`false`) and "log
            // it and consider the mvar done" (`true`). leanr has no
            // message log, so the `true` branch propagates.
            Err(e) if postpone_on_error => {
                let _ = e;
                Ok(false)
            }
            Err(e) => Err(e),
        }
    }

    /// Rung 3's stand-in. P3 replaces the body with
    /// `synthesizeUsingDefault` / `synthesizeSomeUsingDefaultPrio`
    /// (`SyntheticMVars.lean:150-230`).
    ///
    /// Shape-guarded rather than a blanket `false`: it errors when a
    /// pending `TypeClass` mvar's class has default instances
    /// registered — the exact state in which the real rung would have
    /// done something — and reports "no progress" otherwise. That keeps
    /// the seam from silently skipping a rung the oracle runs, without
    /// building P3's reverse-creation-order walk here.
    pub fn synthesize_using_default(&mut self) -> Result<bool, ElabError> {
        for mvar_id in self.pending_mvars.clone() {
            if !matches!(
                self.synthetic_mvar_decl(mvar_id).map(|d| &d.kind),
                Some(SyntheticMVarKind::TypeClass)
            ) {
                continue;
            }
            let Some(class) = self.pending_class_name(mvar_id)? else {
                continue;
            };
            if !self.mctx.default_instances_of(class).is_empty() {
                return Err(ElabError::UnsupportedSyntax(
                    "default instances for a pending typeclass mvar require \
                     synthesizeUsingDefault — M4b-3 P3"
                        .to_string(),
                ));
            }
        }
        Ok(false)
    }

    /// The head constant of a pending typeclass goal, if it has one.
    /// `Wrap ?m` -> `Wrap`; a goal whose head is not a constant has no
    /// class name and cannot have default instances.
    fn pending_class_name(&mut self, mvar_id: MVarId) -> Result<Option<NameId>, ElabError> {
        todo!("instantiate the mvar's type, take the app fn, return its const name; \
               this todo must not survive this step")
    }

    /// oracle: `reportStuckSyntheticMVars` (`SyntheticMVars.lean:322-362`)
    /// and `reportStuckSyntheticMVar` (`:292-320`).
    ///
    /// Drains `pending_mvars`, sorts by the oracle's priority order, and
    /// raises on the first entry. The sort is ported (it picks the
    /// reported mvar deterministically); the note/hint prose is not
    /// (design spec § Amendment, item 2).
    pub fn report_stuck_synthetic_mvars(&mut self) -> Result<(), ElabError> {
        let pending = std::mem::take(&mut self.pending_mvars);
        let mut problems: Vec<(MVarId, SyntheticMVarDecl)> = pending
            .into_iter()
            .filter_map(|id| self.synthetic_mvar_decl(id).cloned().map(|d| (id, d)))
            .collect();
        // oracle: :348-360 — non-typeclass problems come FIRST; among
        // typeclass problems, the SMALLER syntactic range wins (an inner
        // `LT ?m` is more informative than the enclosing
        // `Decidable (x < x)`), ties broken by start offset.
        problems.sort_by(|(_, a), (_, b)| {
            use std::cmp::Ordering;
            let tc = |d: &SyntheticMVarDecl| matches!(d.kind, SyntheticMVarKind::TypeClass);
            match (tc(a), tc(b)) {
                (true, true) => {
                    let ra = a.stx.text_range();
                    let rb = b.stx.text_range();
                    if ra.len() != rb.len() {
                        ra.len().cmp(&rb.len())
                    } else {
                        ra.start().cmp(&rb.start())
                    }
                }
                (true, false) => Ordering::Greater,
                (false, true) => Ordering::Less,
                (false, false) => Ordering::Equal,
            }
        });
        let Some((mvar_id, decl)) = problems.into_iter().next() else {
            return Ok(());
        };
        match decl.kind {
            SyntheticMVarKind::TypeClass => {
                let goal = self
                    .mctx
                    .mctx()
                    .decl(mvar_id)
                    .expect("declared")
                    .ty;
                let goal = self.mctx.instantiate_mvars(goal)?;
                Err(ElabError::StuckSyntheticMVar { goal })
            }
            SyntheticMVarKind::Coe { .. } => Err(ElabError::UnsupportedSyntax(
                "stuck coercion reporting requires coercion insertion — M4b-3 P4".to_string(),
            )),
            SyntheticMVarKind::Tactic => Err(ElabError::UnsupportedSyntax(
                "stuck tactic reporting requires the `by` elaborator — later M4".to_string(),
            )),
            // oracle: `| _ => unreachable!` (:320) — `.postponed` never
            // reaches the reporter, because a postponed mvar that could
            // not be resumed has already raised from `resume_postponed`.
            SyntheticMVarKind::Postponed { .. } => Err(ElabError::UnsupportedSyntax(
                "a postponed mvar reached the stuck reporter — M4b-3 P2a invariant".to_string(),
            )),
        }
    }

    /// oracle: `processPostponedUniverseConstraints`
    /// (`SyntheticMVars.lean:407-411`).
    fn process_postponed_universe_constraints(&mut self) -> Result<(), ElabError> {
        if self.mctx.process_postponed_levels()? {
            return Ok(());
        }
        // oracle: `throwStuckAtUniverseCnstr` (:374-388) renders the
        // unique constraint pairs. leanr reports the count; the prose is
        // deferred with the rest (design spec § Amendment, item 2).
        Err(ElabError::UnsupportedSyntax(format!(
            "stuck universe constraints ({} postponed) — diagnostics layer not built",
            self.mctx.postponed_len()
        )))
    }
```

`SynElem::text_range()` is rowan's — available on both `NodeOrToken` variants. Confirm the exact method name against `rowan`'s API before relying on it; if `NodeOrToken` needs a match, write the two-arm match rather than a helper trait.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p leanr_elab --test synthetic_smoke`
Expected: PASS; the four class-fixture tests remain `ignored`.

- [ ] **Step 5: Commit**

```bash
mise run fmt && mise run lint && mise run test
git add crates/leanr_elab/src/synthetic.rs crates/leanr_elab/tests/synthetic_smoke.rs
git commit -m "M4b-3 P2a task 5: escalation ladder, resumePostponed, stuck reporting"
```

---

## Task 6: `withSynthesize` and the ascription / let-have rewires

**Files:**
- Modify: `crates/leanr_elab/src/synthetic.rs`, `crates/leanr_elab/src/builtin/ascription.rs`, `crates/leanr_elab/src/builtin/binder.rs`
- Test: `crates/leanr_elab/tests/oracle_elab.rs` (the existing gate — this task must not change a single record)

**Interfaces:**
- Produces: `TermElabM::{with_synthesize, with_synthesize_light}`.

**Why this lands here and not later.** `builtin/ascription.rs:39-42` records that both `elabTypeAscription` arms are degenerate *because* `withSynthesize` did not exist. That seam goes live the moment the ladder lands, and it is on the hot path: ascription is how the corpus induces expected types. With the ladder present but ascription unrewired, instance mvars created inside the ascribed **type** would drain at the top-level fixpoint instead of before the body is elaborated — reordering assignments and potentially changing the emitted term.

`let`/`have` need the same treatment: `elabLetDeclAux` elaborates its type under `withSynthesize (postpone := .partial)` (`Binders.lean:775`), with the oracle's own comment explaining why (issue #4051: unresolved synthetic-opaque mvars in the type make the value's defeq check waste enormous time and then insert a postponed coercion).

- [ ] **Step 1: Write the failing test**

The gate for this task is that **no committed record changes**. Add to `crates/leanr_elab/tests/synthetic_smoke.rs`:

```rust
/// `with_synthesize` restores the caller's pending list by APPENDING,
/// on both the ok and the error path.
///
/// oracle: `withSynthesizeImp` (`SyntheticMVars.lean:662-676`) — save,
/// clear, run, synthesize, then `finally` restore as
/// `s.pendingMVars ++ pendingMVarsSaved`. The `finally` is why leanr's
/// restore must survive an early return.
#[test]
fn with_synthesize_saves_clears_and_restores_pending() {
    support::with_app_harness("Nat.zero", |app| {
        let outer = support::register_n_typeclass_mvars(app, 1);
        let kinds = support::any_kinds();
        let inner_seen = std::cell::Cell::new(usize::MAX);
        let _ = app.elab.with_synthesize(
            leanr_elab::synthetic::PostponeBehavior::Yes,
            &kinds,
            |e| {
                // The caller's pending mvars are invisible inside.
                inner_seen.set(e.pending_mvars.len());
                Ok(())
            },
        );
        assert_eq!(inner_seen.get(), 0, "cleared for the duration");
        assert_eq!(app.elab.pending_mvars, outer, "restored afterwards");

        let _ = app.elab.with_synthesize(
            leanr_elab::synthetic::PostponeBehavior::Yes,
            &kinds,
            |_e| Err(leanr_elab::ElabError::UnsupportedSyntax("probe".into())),
        );
        assert_eq!(app.elab.pending_mvars, outer, "restored on the error path too");
    });
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p leanr_elab --test synthetic_smoke with_synthesize`
Expected: FAIL to compile — `with_synthesize` does not exist.

- [ ] **Step 3: Implement `with_synthesize`**

```rust
    /// oracle: `withSynthesizeImp` (`SyntheticMVars.lean:662-676`).
    ///
    /// Save the caller's pending mvars, clear, run `k`, synthesize what
    /// `k` created, then restore by APPENDING the saved list after
    /// whatever is left. The oracle's `finally` means the restore
    /// happens on the error path too.
    ///
    /// The oracle also runs `synthesizeUsingDefaultLoop` when
    /// `postpone == .yes`; that loop is P3's, and P2a's guarded
    /// `synthesize_using_default` stands in for it (design spec
    /// § Amendment, item 3).
    pub fn with_synthesize<R>(
        &mut self,
        postpone: PostponeBehavior,
        kinds: &KindInterner,
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let saved = std::mem::take(&mut self.pending_mvars);
        // Every exit path below must run `self.pending_mvars.extend(saved)`
        // exactly once — that is the oracle's `finally`. Written as
        // straight-line code with one `saved` consumer per branch rather
        // than a closure, because a closure taking `saved` by value
        // cannot be called on two paths.
        let out = match k(self) {
            Ok(v) => v,
            Err(e) => {
                self.pending_mvars.extend(saved);
                return Err(e);
            }
        };
        let mut synth = self.synthesize_synthetic_mvars(postpone, kinds);
        if synth.is_ok() && postpone == PostponeBehavior::Yes {
            // oracle: `synthesizeUsingDefaultLoop` (:668). P3 owns the
            // real loop; the guarded seam stands in.
            synth = self.synthesize_using_default().map(|_| ());
        }
        self.pending_mvars.extend(saved);
        synth?;
        Ok(out)
    }

    /// oracle: `withSynthesizeLightImp` (`SyntheticMVars.lean:681-691`)
    /// — as `with_synthesize` with `postpone := .yes` and NO default
    /// loop. No P2a caller; present because the ladder's callers arrive
    /// in later plans and a missing sibling reads as an oversight.
    pub fn with_synthesize_light<R>(
        &mut self,
        kinds: &KindInterner,
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        self.with_synthesize(PostponeBehavior::Yes, kinds, k)
    }
```

- [ ] **Step 4: Rewire ascription**

In `crates/leanr_elab/src/builtin/ascription.rs`, wrap the type elaboration of the `(e : T)` arm in `with_synthesize(PostponeBehavior::Yes, ..)` and the `(e :)` arm's term elaboration in `with_synthesize(PostponeBehavior::No, ..)`, matching `BuiltinNotation.lean:410-434`. Then **rewrite the module doc's fourth paragraph** — the one beginning "`withSynthesize`'s postponement scaffolding does not exist in this slice" — to record that P2a supplied it and both arms now take their real shape. Leaving that paragraph in place would be a false statement in the file that most needs to be trustworthy.

- [ ] **Step 5: Rewire `let`/`have`**

In `crates/leanr_elab/src/builtin/binder.rs`, wrap the `let`/`have` **type** elaboration in `with_synthesize(PostponeBehavior::Partial, ..)`, citing `Binders.lean:775` and the oracle's own #4051 rationale. Only the type — the value and body keep their current, direct shape (`config.postponeValue` is false for every form leanr parses).

- [ ] **Step 6: Prove no record changed**

```bash
mise run elan:bootstrap   # once per machine
mise run fixtures:regen-elab
git diff --exit-code tests/fixtures/elab/elab-queries.jsonl
```
Expected: **empty diff, exit 0.** The rewire changes elaboration ORDER; it must not change any emitted term, because no committed record involves a typeclass. If a record does change, stop and run it down — that is a finding about ordering, not a fixture to update.

Run: `cargo test -p leanr_elab`
Expected: all green, including `oracle_elab::oracle_elab_gate`.

- [ ] **Step 7: Commit**

```bash
mise run fmt && mise run lint && mise run test
git add crates/leanr_elab/src/synthetic.rs crates/leanr_elab/src/builtin/ascription.rs crates/leanr_elab/src/builtin/binder.rs crates/leanr_elab/tests/synthetic_smoke.rs
git commit -m "M4b-3 P2a task 6: withSynthesize + ascription and let/have rewires (no record changes)"
```

---

## Task 7: Instance-implicit arguments end-to-end

**Files:**
- Modify: `crates/leanr_elab/src/app/args.rs`, `crates/leanr_elab/src/app/finalize.rs`, `crates/leanr_elab/src/app/propagate.rs`
- Modify: `tests/fixtures/elab/Elab0.lean`, `tests/fixtures/elab/dump_elab.lean`
- Regenerate: `tests/fixtures/elab/Elab0.olean`, `tests/fixtures/elab/elab-queries.jsonl`
- Test: `crates/leanr_elab/tests/oracle_elab.rs` (new records), `crates/leanr_elab/tests/synthetic_smoke.rs` (un-ignore Tasks 4/5)

**Interfaces:**
- Consumes: Task 4's `synthesize_inst_mvar_core`, Task 2's registration helpers.
- Produces: `app::args::process_inst_implicit_arg`, `AppElab::{add_inst_mvar, try_synthesize_app_inst_mvars, synthesize_app_inst_mvars}`.

- [ ] **Step 1: Add the fixture scaffold**

Append to `tests/fixtures/elab/Elab0.lean`. This exact scaffold was compiled against the pinned toolchain in prelude mode during planning — classes, instances and the three `def`s all elaborate with no additional prelude:

```lean
-- === M4b-3 P2a corpus: classes, instances, instance-implicit args ===
--
-- Modelled on tests/fixtures/meta/Synth0.lean:86-136 (leanr_meta's own
-- synthesis corpus) but deliberately NOT a copy: only the shapes P2a's
-- records discriminate.
--
--   * `Wrap` — one parameter, one concrete instance. The minimal shape
--     that makes `processInstImplicitArg` observable.
--   * `Pair` — TWO parameters, so an instance goal with more than one
--     argument exercises `getArgExpectedType` past the first.
--   * `NoInst` — a class with NO instance, so `synthesizeInstMVarCore`'s
--     `.none` (real failure) arm is reachable and distinguishable from
--     its `.undef` (stuck) arm, which `useWrap` with no expected type
--     reaches instead. Both are error paths, so neither appears in the
--     JSONL: the dumper drops a throwing query. They are asserted in
--     crates/leanr_elab/tests/synthetic_smoke.rs.
class Wrap (a : Type) where
  wrap : a -> a

instance instWrapNat : Wrap Nat where
  wrap := fun n => n

class Pair (a : Type) (b : Type) where
  mk2 : a -> b -> a

instance instPairNatNat : Pair Nat Nat where
  mk2 := fun x _ => x

class NoInst (a : Type) where
  nope : a

def useWrap {a : Type} [Wrap a] (x : a) : a := Wrap.wrap x
def usePair {a : Type} {b : Type} [Pair a b] (x : a) (y : b) : a := Pair.mk2 x y
def useNoInst {a : Type} [NoInst a] (x : a) : a := x
```

- [ ] **Step 2: Add the corpus queries**

In `tests/fixtures/elab/dump_elab.lean`, add a query list and append it to `main`'s concatenation:

```lean
/-- M4b-3 P2a: instance-implicit arguments. Every term here SUCCEEDS in
the oracle under the current entry point — instance synthesis runs
eagerly in `synthesizeAppInstMVars` at `finalize`, not in the fixpoint
(measured during planning) — so these records land before the
entry-point change and stay byte-identical across it.

  * `tc/useWrapNat` — the base shape: one instance-implicit parameter
    solved from the explicit argument's type.
  * `tc/useWrapAscribed` — the same under an induced expected type, so
    `propagateExpectedType`'s `trySynthesizeAppInstMVars` call runs
    before the unification rather than after.
  * `tc/atUseWrap` — `@` with the instance supplied POSITIONALLY, the
    `processInstImplicitArg` branch that does NOT synthesize.
  * `tc/atUseWrapHole` — `@` with `_` in the instance position, which
    the oracle still resolves by synthesis (`nextArgHole?`,
    App.lean:905-911). The two `@` records together are the only
    coverage of that arm's split.
  * `tc/atWrapImplicit` — `@` with `_` in the ordinary IMPLICIT position
    too, so the explicit-mode arm is exercised for both binder kinds.
  * `tc/pairBoth` — a two-parameter class.
  * `tc/wrapWrap` — nested, so an instance goal is solved while another
    application is mid-flight.
  * `tc/wrapUnderFun`, `tc/funWrapElided`, `tc/letWrapElided` — an
    instance argument under each binder form M4b-2 shipped, so the
    Task 6 rewires are exercised by real records rather than by
    inspection. -/
def instImplicitQueries : List (String × String) :=
  [ ("tc/useWrapNat",      "useWrap Nat.zero")
  , ("tc/useWrapAscribed", "(useWrap Nat.zero : Nat)")
  , ("tc/atUseWrap",       "@useWrap Nat instWrapNat Nat.zero")
  , ("tc/atUseWrapHole",   "@useWrap Nat _ Nat.zero")
  , ("tc/atWrapImplicit",  "@useWrap _ instWrapNat Nat.zero")
  , ("tc/pairBoth",        "usePair Nat.zero Nat.zero")
  , ("tc/wrapWrap",        "useWrap (useWrap Nat.zero)")
  , ("tc/wrapUnderFun",    "fun (n : Nat) => useWrap n")
  , ("tc/funWrapElided",   "(fun x => useWrap x : Nat -> Nat)")
  , ("tc/letWrapElided",   "let x := useWrap Nat.zero; x")
  ]
```

- [ ] **Step 3: Regenerate and watch the gate go red**

```bash
mise run fixtures:regen        # rebuilds Elab0.olean (Elab0.lean changed)
mise run fixtures:regen-elab   # re-runs the dumper
git diff --stat tests/fixtures/elab/
```
Expected: `Elab0.olean` rebuilt, `elab-queries.jsonl` gains exactly 10 records, **no existing record changes**.

Run: `cargo test -p leanr_elab --test oracle_elab`
Expected: FAIL — the 10 new records hit `UnsupportedSyntax("instance-implicit arguments require typeclass synthesis and the synthetic-mvar fixpoint — M4b-3 P2")`.

- [ ] **Step 4: Implement `processInstImplicitArg`**

Replace the `BinderInfo::InstImplicit` arm in `crates/leanr_elab/src/app/args.rs` (currently the seam at `args.rs:89-115`) with both halves of `App.lean:903-923`:

```rust
                BinderInfo::InstImplicit => {
                    if !process_inst_implicit_arg(app, kinds, binder_name)? {
                        return crate::app::finalize::finalize(app);
                    }
                }
```

and add:

```rust
/// oracle: `processInstImplicitArg` (`App.lean:903-923`).
///
/// Both halves, per the seam attribution P1 left here: under `@` an
/// instance-implicit parameter is filled POSITIONALLY, except that a
/// literal `_` is STILL synthesized (`nextArgHole?`, :905-911) — the
/// oracle's own comment: "We still use typeclass resolution for `_`
/// arguments."
fn process_inst_implicit_arg(
    app: &mut AppElab,
    kinds: &KindInterner,
    binder_name: Option<NameId>,
) -> Result<bool, ElabError> {
    if app.ctx.explicit {
        if let Some(_hole) = next_arg_hole(app)? {
            let ty = app.get_arg_expected_type()?;
            mk_inst_mvar(app, ty, binder_name)?;
            // oracle: `modify fun s => { s with args := s.args.tail! }`
            // — the hole is CONSUMED even though it was not elaborated.
            app.st.args.remove(0);
            return Ok(true);
        }
        return process_explicit_arg(app, kinds, binder_name);
    }
    let ty = app.get_arg_expected_type()?;
    mk_inst_mvar(app, ty, binder_name)?;
    Ok(true)
}

/// oracle: `mkInstMVar` (`App.lean:919-923`).
///
/// `MVarKind::Synthetic`, NOT `SyntheticOpaque`: an instance mvar must
/// remain assignable by `isDefEq` (that is precisely what
/// `PostponeBehavior::Partial` relies on — "this kind of metavariable
/// are not synthetic opaque", `SyntheticMVars.lean:436-437`).
fn mk_inst_mvar(
    app: &mut AppElab,
    ty: ExprId,
    binder_name: Option<NameId>,
) -> Result<ExprId, ElabError> {
    let (arg, mvar_id) = app
        .elab
        .mk_fresh_expr_mvar_of_kind(ty, MVarKind::Synthetic)?;
    app.st.inst_mvars.push(mvar_id);
    let _ = binder_name; // oracle passes it to `addNewArg`; see below
    add_new_arg(app, arg)?;
    Ok(arg)
}
```

`next_arg_hole` is the oracle's `nextArgHole?` (`App.lean:~860`): peek `s.args[0]` and return it when it is a `Arg::Stx` whose syntax is a `Lean.Parser.Term.hole`. Read that definition in the pinned source before writing it — in particular whether it consumes or only peeks.

- [ ] **Step 5: Replace the three `inst_mvars` guards**

In `crates/leanr_elab/src/app/state.rs` (or `app/mod.rs`, wherever `AppElab`'s methods live), add:

```rust
    /// oracle: `trySynthesizeAppInstMVars` (`App.lean:355-362`) — try
    /// each pending instance mvar, KEEP the ones that are not ready.
    /// Runs before expected-type propagation and before the final
    /// unification, so those see whatever assignments succeeded.
    ///
    /// The oracle guards each attempt with
    /// `unless (← instantiateMVars (← inferType (.mvar instMVar))).isMVar`
    /// — do not synthesize when the goal's own type is still an mvar —
    /// and swallows errors (`try .. catch _ => pure ()`), because this
    /// is the opportunistic pass; the committing pass is
    /// `synthesize_app_inst_mvars`.
    pub fn try_synthesize_app_inst_mvars(&mut self) -> Result<(), ElabError> {
        let mut kept = Vec::new();
        for mvar_id in std::mem::take(&mut self.st.inst_mvars) {
            let ty = self.elab.mctx.mctx().decl(mvar_id).expect("declared").ty;
            let ty = self.elab.mctx.infer_type(ty)?;
            let ty = self.elab.mctx.instantiate_mvars(ty)?;
            let goal_is_mvar = matches!(self.node(ty), Node::MVar { .. });
            if !goal_is_mvar {
                match self.elab.synthesize_inst_mvar_core(mvar_id) {
                    Ok(true) => continue,
                    Ok(false) | Err(_) => {}
                }
            }
            kept.push(mvar_id);
        }
        self.st.inst_mvars = kept;
        Ok(())
    }

    /// oracle: `synthesizeAppInstMVars` (`App.lean:368-370` ->
    /// `Term.synthesizeAppInstMVars`, `:75-79`) — the COMMITTING pass on
    /// every exit path. Each mvar that is still not ready is registered
    /// as a pending `.typeClass` synthetic mvar for the fixpoint, with
    /// an `MVarErrorInfo` attributing it to this application.
    pub fn synthesize_app_inst_mvars(&mut self, stx: &SynElem) -> Result<(), ElabError> {
        let app_expr = self.st.f;
        for mvar_id in std::mem::take(&mut self.st.inst_mvars) {
            if self.elab.synthesize_inst_mvar_core(mvar_id)? {
                continue;
            }
            self.elab
                .register_synthetic_mvar(stx.clone(), mvar_id, SyntheticMVarKind::TypeClass);
            self.elab
                .register_mvar_error_implicit_arg_info(mvar_id, stx.clone(), app_expr);
        }
        Ok(())
    }
```

Then replace the guard at `app/propagate.rs:88` with `app.try_synthesize_app_inst_mvars()?;`, and the two guards at `app/finalize.rs:67` and `:85` with `try_synthesize_app_inst_mvars` and `synthesize_app_inst_mvars` respectively — each exactly where the guard stood, since P1 placed the guards at the oracle's own call sites.

`finalize` needs a `SynElem` for the registration. Thread the application's own syntax through `AppElab` (a `stx: SynElem` field on `Context`, set in `elab_app_aux`) rather than passing it down through `main` — the oracle uses `getRef`, which is ambient, and a `Context` field is leanr's closest equivalent.

- [ ] **Step 6: Run tests to verify they pass; un-ignore Tasks 4/5 tests**

Remove the four `#[ignore = "needs the Elab0 class scaffold (Task 7)"]` attributes and implement the `wrap_of_nat`, `wrap_of_fresh_mvar`, `no_inst_of_nat`, `elab_and_synthesize`, `any_kinds` helpers in `tests/support/mod.rs`.

Run: `cargo test -p leanr_elab`
Expected: PASS — 10 new oracle records green, and the Task 4/5 tests now running rather than ignored.

- [ ] **Step 7: Commit**

```bash
mise run fmt && mise run lint && mise run test
git add crates/leanr_elab/src crates/leanr_elab/tests tests/fixtures/elab
git commit -m "M4b-3 P2a task 7: instance-implicit arguments end-to-end + Elab0 class scaffold"
```

---

## Task 8: `synthesizePendingAndNormalizeFunType`

**Files:**
- Modify: `crates/leanr_elab/src/app/args.rs`, `crates/leanr_elab/src/error.rs`
- Test: `crates/leanr_elab/tests/seam_audit.rs`

**Interfaces:**
- Produces: `app::args::synthesize_pending_and_normalize_fun_type`.

This closes the last P2-labelled seam in `app/`: `args.rs:126`'s "too many arguments" branch. The oracle (`App.lean:372-404`) is `trySynthesizeAppInstMVars`, then the **fixpoint** (`synthesizeSyntheticMVars`, default `postpone := .yes`), then re-check `fTypeIsForall`; if it is still not a forall, try `coerceToFunction?` (P4) and otherwise report "function expected".

**Read this before starting.** `(fun f => f Nat.zero : (Nat -> Nat) -> Nat)` hits this path in leanr and **succeeds in the oracle**. That is a *pre-existing* divergence: the oracle propagates the expected type into the `fun` binder's domain so `fType` is never an mvar, while M4b-2's `fun` uses a fresh type mvar. This task **re-labels** the seam; it does not fix it. Do not add a corpus record of that shape, and do not "fix" it by special-casing mvar function types — the fix is expected-type propagation into binders, which belongs to the slice that grows binder breadth (P5).

- [ ] **Step 1: Write the failing test**

In `crates/leanr_elab/tests/seam_audit.rs`:

```rust
/// An over-applied function reaches `synthesizePendingAndNormalizeFunType`
/// and, when the type is genuinely not a function, reports it as such
/// rather than as a pending-synthesis seam.
#[test]
fn over_application_reports_function_expected() {
    let err = elab_src("Nat.zero Nat.zero").expect_err("Nat is not a function");
    assert!(
        matches!(err, leanr_elab::ElabError::FunctionExpected { .. }),
        "got {err:?}"
    );
}

/// A function type that is still an unassigned mvar after the fixpoint
/// is a named P4/P5 seam, NOT a wrong term.
///
/// This shape diverges from the oracle today and will keep diverging
/// until expected types propagate into `fun` binder domains (plan
/// § Measured facts, item 4). The assertion pins that it stays an
/// ERROR naming its owner — the failure mode this discipline exists to
/// prevent is emitting a different term silently.
#[test]
fn mvar_function_type_is_a_named_seam() {
    let err = elab_src("(fun f => f Nat.zero : (Nat -> Nat) -> Nat)")
        .expect_err("leanr cannot elaborate this yet");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("M4b-3 P4") || msg.contains("M4b-3 P5"),
        "seam must name its owner, got {msg}"
    );
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_elab --test seam_audit over_application mvar_function_type`
Expected: FAIL — both currently produce the "too many arguments … M4b-3 P2" message and `ElabError::FunctionExpected` does not exist.

- [ ] **Step 3: Add the error variant**

```rust
    /// oracle: `"Function expected at .. but this term has type .."`
    /// (`App.lean:404-408`). Carries the head and its type; the oracle's
    /// `.note` hint about indentation mishaps is prose (deferred).
    FunctionExpected { f: ExprId, f_type: ExprId },
```

- [ ] **Step 4: Implement it**

Replace the `else if app.has_args_to_process()` seam in `args.rs` with a call to:

```rust
/// oracle: `synthesizePendingAndNormalizeFunType` (`App.lean:372-404`).
/// "fType may become a forallE after we synthesize pending metavariables."
fn synthesize_pending_and_normalize_fun_type(
    app: &mut AppElab,
    kinds: &KindInterner,
) -> Result<(), ElabError> {
    app.try_synthesize_app_inst_mvars()?;
    // oracle: `synthesizeSyntheticMVars` with its DEFAULT
    // `postpone := .yes` (:375) — this is a normalization attempt, not a
    // commitment point, so a still-stuck mvar must stay pending rather
    // than be reported.
    app.elab
        .synthesize_synthetic_mvars(PostponeBehavior::Yes, kinds)?;
    if app.f_type_is_forall()? {
        return Ok(());
    }
    // oracle: `coerceToFunction? s.f` (:378) — M4b-3 P4.
    // The oracle's remaining arms are diagnostics: a deprecated-argument
    // linter, `throwInvalidNamedArg` (which needs `foundNamedArgs`
    // rendering leanr does not do), and the "Function expected" error.
    // Only the last changes control flow, so only it is ported.
    let f_type = app.st.f_type;
    if app.st.f_type_is_mvar_after_instantiation()? {
        return Err(ElabError::UnsupportedSyntax(
            "function type is still an unassigned metavariable after synthesis: needs \
             CoeFun (M4b-3 P4), or expected-type propagation into `fun` binder domains \
             (M4b-3 P5) for the M4b-2 `fun` shape"
                .to_string(),
        ));
    }
    Err(ElabError::FunctionExpected {
        f: app.st.f,
        f_type,
    })
}
```

`f_type_is_mvar_after_instantiation` is a small `AppElab` helper: `instantiate_mvars(self.st.f_type)` then `matches!(self.node(..), Node::MVar { .. })`. Splitting the message this way is deliberate — an mvar function type and a genuinely non-function type are different failures with different owners, and collapsing them would send a P5 bug to P4.

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p leanr_elab`
Expected: PASS, including the unchanged `oracle_elab` gate.

- [ ] **Step 6: Commit**

```bash
mise run fmt && mise run lint && mise run test
git add crates/leanr_elab/src/app/args.rs crates/leanr_elab/src/error.rs crates/leanr_elab/tests/seam_audit.rs
git commit -m "M4b-3 P2a task 8: synthesizePendingAndNormalizeFunType closes the over-application seam"
```

---

## Task 9: The entry-point change and the empty-diff gate

**Files:**
- Modify: `crates/leanr_elab/src/elab.rs`, `tests/fixtures/elab/dump_elab.lean`
- Regenerate: `tests/fixtures/elab/elab-queries.jsonl`

**Interfaces:**
- Produces: `TermElabM::elab_term_and_synthesize(&mut self, elem, kinds, expected) -> Result<ExprId, ElabError>`.

The design spec's § The entry-point pipeline: `elab_term → synthesize_synthetic_mvars(.no) → instantiate_mvars`, matching the oracle's `elabTermAndSynthesize` (`SyntheticMVars.lean:694-696`, which is `withSynthesize` at its default `postpone := .no` — identical at the top level, where the saved pending list is empty).

- [ ] **Step 1: Write the failing test**

```rust
/// The top-level entry point runs the fixpoint before instantiating.
///
/// Without it, a term whose instance argument is only solvable by the
/// ladder would emit a dangling mvar instead of erroring or resolving.
#[test]
fn entry_point_runs_the_fixpoint() {
    // `useWrap` (bare) elaborates to a term with a stuck instance mvar.
    // Under `elab_term` alone it succeeds; under the real entry point it
    // must be reported stuck (measured against the oracle: plan
    // § Measured facts, item 2).
    let plain = support::elab_only("useWrap");
    assert!(plain.is_ok(), "elab_term alone does not report stuck");

    let full = support::elab_and_synthesize("useWrap");
    assert!(
        matches!(full, Err(leanr_elab::ElabError::StuckSyntheticMVar { .. })),
        "the entry point must report the stuck instance, got {full:?}"
    );
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p leanr_elab --test synthetic_smoke entry_point`
Expected: FAIL — `elab_term_and_synthesize` does not exist.

- [ ] **Step 3: Implement the entry point**

In `crates/leanr_elab/src/elab.rs`:

```rust
    /// oracle: `elabTermAndSynthesize` (`SyntheticMVars.lean:694-696`) —
    /// `instantiateMVars (← withSynthesize <| elabTerm stx expectedType?)`
    /// with `withSynthesize`'s default `postpone := .no`.
    ///
    /// At the top level `withSynthesize`'s save/restore is a no-op (the
    /// saved pending list is empty), so this is exactly
    /// `elab_term` -> `synthesize_synthetic_mvars(.no)` ->
    /// `instantiate_mvars`, the pipeline the design spec pins.
    ///
    /// `elab_term_ensuring_type` is unchanged and remains the INNER
    /// entry point every elaborator uses; this is the outermost one.
    pub fn elab_term_and_synthesize(
        &mut self,
        elem: &SynElem,
        kinds: &KindInterner,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        let e = self.elab_term(elem, kinds, expected)?;
        self.synthesize_synthetic_mvars_no_postponing(kinds)?;
        self.mctx.instantiate_mvars(e).map_err(ElabError::from)
    }
```

- [ ] **Step 4: Change the dumper to match**

In `tests/fixtures/elab/dump_elab.lean`, replace the elaboration step in `main`:

```lean
          -- M4b-3 P2a: the entry point now matches
          -- `crates/leanr_elab`'s `elab_term_and_synthesize` —
          -- elabTerm, then the fixpoint, then instantiateMVars. The
          -- fixpoint is what forces stuck typeclass problems to be
          -- reported rather than emitted as dangling mvars.
          let e ← (do
            let e ← Lean.Elab.Term.elabTerm stx none
            Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e).run'
```

and rewrite the module doc's "**Slice 1 does NO postponement**" paragraph to describe the new pipeline. That paragraph explicitly pins the old entry point as deliberate; leaving it would make the file lie about itself.

- [ ] **Step 5: Regenerate and prove the no-op**

```bash
mise run fixtures:regen-elab
git diff --exit-code tests/fixtures/elab/elab-queries.jsonl
```
Expected: **empty diff, exit 0.**

This is the plan's central piece of evidence, so state what it does and does not prove. It proves the fixpoint is a no-op on all 81 committed records — including `hole/bare`, whose `{"k":"mvar","i":0}` survives because a bare `_` is a **natural**, not synthetic, mvar and `reportStuckSyntheticMVars` never sees it. It does **not** prove the fixpoint is a no-op in general: `useWrap` and `fun f => f Nat.zero` both change from a term to an error, which is exactly why neither is a record. If any committed record changes, stop and run it down.

- [ ] **Step 6: Run the full suite**

Run: `mise run test`
Expected: all green.

- [ ] **Step 7: Commit**

```bash
mise run fmt && mise run lint && mise run test
git add crates/leanr_elab/src/elab.rs crates/leanr_elab/tests tests/fixtures/elab
git commit -m "M4b-3 P2a task 9: entry point runs the fixpoint; empty-diff gate over the corpus"
```

---

## Task 10: Seam audit, deferral ledgers, and the recorded coverage gap

**Files:**
- Modify: `crates/leanr_elab/tests/seam_audit.rs`, `crates/leanr_elab/src/lib.rs`, `crates/leanr_elab/src/app/mod.rs`, `crates/leanr_elab/src/dispatch.rs`

- [ ] **Step 1: Write the failing test**

Add to `crates/leanr_elab/tests/seam_audit.rs`:

```rust
/// No seam message in `leanr_elab` still points at "M4b-3 P2".
///
/// P2 split into P2a (this plan) and P2b (classExtension + outParam), so
/// an unqualified "P2" is now ambiguous. Every remaining seam must name
/// P2b, P3, P4, P5, M4b-4, or later M4.
#[test]
fn no_seam_points_at_the_retired_p2_label() {
    let src_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    let mut offenders = Vec::new();
    for entry in walk_rs_files(src_dir) {
        let text = std::fs::read_to_string(&entry).expect("read source");
        for (n, line) in text.lines().enumerate() {
            // Match the seam label, not prose mentioning the plan.
            if line.contains("M4b-3 P2\"") || line.contains("M4b-3 P2 ") {
                offenders.push(format!("{}:{}", entry.display(), n + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "seams still labelled with the retired `M4b-3 P2`: {offenders:?}"
    );
}
```

`walk_rs_files` is a small recursive helper over `src/`; if `seam_audit.rs` already has one for `fixture_declares_no_undecoded_elab_attributes`, reuse it.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p leanr_elab --test seam_audit no_seam_points_at`
Expected: FAIL, listing the surviving `M4b-3 P2` labels (`app/mod.rs`'s doc index and any comment Tasks 7-8 did not touch).

- [ ] **Step 3: Retarget every label and ledger**

- `crates/leanr_elab/src/app/mod.rs` — rewrite the seam index: the instance-implicit arm and the three `inst_mvars` guards are **gone** (implemented); the local-instance outParam seam is **P2b**; the "normalizing a non-forall fType" entry is now split P4/P5 per Task 8.
- `crates/leanr_elab/src/lib.rs` — replace the "instance-implicit arguments and the synthetic-mvar fixpoint — M4b-3 P2" bullet with what is now true: the fixpoint and instance arguments shipped in P2a; `classExtension` + `resultTypeOutParam?` are P2b. Add a bullet for the **recorded coverage gap**:

```rust
//! - **`resumePostponed`'s success path has no differential coverage
//!   yet.** P2a builds the whole ladder, and its stuck paths are
//!   asserted in `tests/synthetic_smoke.rs` — but every term in P2a's
//!   grammar that postpones also ends stuck (the only producer is
//!   `App.lean:1367`'s `tryPostponeIfMVar fType`; every other
//!   `tryPostpone*` site belongs to M4b-4, P3, P5 or later M4). The
//!   first term that postpones and then RESUMES into a term arrives
//!   with P3's numerals. Recorded rather than papered over: the corpus
//!   does not cover this path today.
```

- `crates/leanr_elab/src/dispatch.rs` — update the deferral table row.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p leanr_elab --test seam_audit`
Expected: PASS, including the pre-existing seam assertions with their retargeted messages.

- [ ] **Step 5: Final full gate**

Run: `mise run ci`
Expected: all green — `cargo fmt --check`, clippy, and the full test suite.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_elab
git commit -m "M4b-3 P2a task 10: seam audit retargeted to P2b/P3/P4/P5; coverage gap recorded"
```

---

## Self-Review

**Spec coverage (§ P2a, and § Amendment items 1-3):**

| Spec requirement | Task |
|---|---|
| ladder state on `TermElabM`, `impl` in `synthetic.rs` | 2 |
| all four `SyntheticMVarKind` variants from the start | 2 |
| `synthesizeSyntheticMVarsStep`, creation order, merge order, count-based progress | 3 |
| `synthesizeInstMVarCore` whole, incl. `containsPendingMVar` re-try and both mismatch throws | 4 |
| the five-rung escalation, `PostponeBehavior` three-valued | 5 |
| `resumePostponed` + `SavedContext` | 5 |
| `synthesize_using_default` as a shape-guarded seam (Amendment item 3) | 5 |
| `reportStuckSyntheticMVars` incl. the priority sort; prose deferred (Amendment item 2) | 5 |
| `mvarErrorInfos` table + registration sites; prose deferred | 2, 7 |
| `process_postponed_universe_constraints` | 1, 5 |
| `mayPostpone` / `withoutPostponing` | 2 |
| `withSynthesize` + ascription rewire (Amendment item 3) | 6 |
| `let`/`have` `.partial` rewire | 6 |
| `processInstImplicitArg` both halves | 7 |
| `trySynthesizeAppInstMVars` / `synthesizeAppInstMVars` replacing P1's three guards | 7 |
| `synthesizePendingAndNormalizeFunType` | 8 |
| the entry-point pipeline change + empty-diff gate | 9 |
| `Elab0.lean` class scaffold modelled on `Synth0.lean:86-136` | 7 |
| ordering unit tests (spec § Verification tier 2) | 3 |
| seam audit per plan (tier 3) | 10 |
| accessor ledger = `process_postponed` + `default_instances` | 1 |
| P2b explicitly not in this plan (`classExtension`, `resultTypeOutParam?`) | Global Constraints; 10 |

**Deviations from the spec, each deliberate and recorded in-plan:**

1. § Accessor ledger's `with_assignable_synthetic_opaque` moves to P3 — its only oracle caller is `synthesizeUsingDefaultPrio` (Task 1 Step 5, with the spec edited in the same commit).
2. § P2a says "M4b-2 plan 2's `fun` postponement seam becomes live code". Measured: `elabFun` does not call `tryPostpone` at all, and leanr's `fun` never postpones. The real P2a postpone producer is `App.lean:1367`, and every shape it reaches ends stuck — recorded as a coverage gap in Task 10 rather than claimed as coverage.

**Placeholder scan:** three `todo!()`s (Task 2 Step 4's `mk_fresh_expr_mvar_of_kind` body-move, Task 4's `contains_pending_mvar` walk, Task 5's `pending_class_name`), each carrying "this todo must not survive this step" and naming the idiom to copy. Two deliberately-`#[ignore]`d test groups (Task 4's three, Task 5's three) with the un-ignore step named explicitly (Task 7 Step 6). No "TBD", no "add error handling", no "similar to Task N".

**Type consistency:** `synthesize_synthetic_mvars_step`, `synthesize_synthetic_mvar`, `step_with`, `synthesize_inst_mvar_core`, `synthesize_pending_inst_mvar`, `with_synthesize`, `try_synthesize_app_inst_mvars` and `synthesize_app_inst_mvars` keep one signature across Tasks 3-9. `kinds: &KindInterner` is threaded through every fixpoint entry point (Task 2's design note), consistently with `elab_term`'s existing convention. `mk_fresh_expr_mvar_of_kind` returns `(ExprId, MVarId)` and `mk_fresh_expr_mvar` delegates to it, so P1's ten existing call sites are untouched.

**Three places where a task's own step is expected to correct this plan** — each names what to read first rather than asserting the answer: `nextArgHole?`'s consume-vs-peek semantics (Task 7 Step 4), `MetaCtx`'s field names for the Task 1 forwarders, and `rowan`'s `text_range` on `NodeOrToken` (Task 5 Step 3).

---

## Execution Handoff

Plan complete and saved to `docs/superpowers/plans/2026-07-27-m4b3-p2a-ladder-instance-args.md`. Two execution options:

1. **Subagent-Driven (recommended)** — a fresh subagent per task, review between tasks, fast iteration.
2. **Inline Execution** — execute tasks in this session using executing-plans, batch execution with checkpoints.
