# M4b-4a P2 — term-level postponement Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** An elaborator that meets a term whose type is not yet known postpones it, and the fixpoint resumes it once unification has filled the type in, exactly as the pinned oracle does. `(fun x => x.1) (Prod.mk Nat.zero Nat.zero)` and `(fun f => f Nat.zero) Nat.succ` elaborate. `fun x => x.1` is rejected with the oracle's error, not a seam.

**Architecture:**
- `ElabError::Postpone` is the oracle's internal `postponeExceptionId`. It is a variant, not an error.
- A new `postpone.rs` holds the producers (`try_postpone` family, exact `isMVarApp`, `postpone_elab_term`).
- `elab.rs` grows `elab_using_elab_fns`, the oracle's catch: restore the saved state, then register a `.postponed` synthetic mvar. `elab_term_core` threads `catch_ex_postpone`.
- `resume_postponed` becomes faithful: it elaborates with the catch off and rolls state back on every non-success.
- Three producers go live: `useImplicitLambda`'s `.postpone` arm, `resolveLValLoop`'s `tryPostponeIfMVar` and `elabAppArgs`' `tryPostponeIfMVar fType`.

**Tech Stack:** Rust (`leanr_elab`, one additive `leanr_meta` visibility change), Lean 4 `v4.33.0-rc1` as the differential oracle, `mise` tasks.

**Spec:** `docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md`. Read § P2, § Errors, § Testing and § Landed › P1 before starting any task.

## Spec deviations (found while planning, all measured)

The plan departs from spec § P2 in four places. Task 5 records each one in the spec as a P2 amendment.

1. **A third producer: `elabAppArgs`' `tryPostponeIfMVar fType`** (`App.lean:1366-1367`). The spec lists only the LVal and implicit-lambda producers.
   - leanr skips this call today. Pinned oracle: `(fun f => f Nat.zero) Nat.succ` elaborates. leanr raises `FunctionExpected`.
   - That is a silent divergence with no seam. It is also the reason `(fun x f => f x.1) … Nat.succ` fails in leanr.
   - It lives in the same control flow P2 builds, so it is in scope (Task 4).
2. **`synthetic/report.rs`'s `Postponed` arm is not a seam.** It is the oracle's `| _ => unreachable!` (`SyntheticMVars.lean:316`).
   - It stays an internal-invariant error.
   - Task 5 re-verifies that nothing can reach it and rewrites its doc. The only route is `check_occurs` failing, which needs a synthetic `sorry`, and leanr mints none.
3. **"the existing `with_synthesize` scopes setting `may_postpone`"**: the oracle's `withSynthesize` never touches `mayPostpone`. Only `withoutPostponing` does (`TermElabM.lean:1049-1050`), and the ladder's rungs 2 and 4 already use it. There is nothing to change.
4. **`is_mvar_app` becomes exact (`whnfR`).** § Landed › P1 carried this forward as P2's to fix. It needs `MetaCtx::whnf_r` widened from `pub(crate)` to `pub`, an additive change covered by the elab→meta accessor precedent.

## Global Constraints

- Oracle is `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`). Never bump it.
- Every oracle `file:line` citation written into code or tests is opened against `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/Lean/...` first. Every citation in this plan was opened while writing it. Re-open any you copy anyway: citations in this repo drift by 1-2 lines.
- `leanr_meta` changes are additive and TCB-neutral. This plan's whole allowance is `whnf_r`'s `pub(crate)` → `pub`. `leanr_kernel` is untouched.
- No new dependencies.
- Named-seam discipline:
  - A construct owned by a later slice raises `ElabError::UnsupportedSyntax` naming the owner.
  - A genuine oracle error gets a typed variant.
  - `ElabError::Postpone` is neither of these. It must never reach a caller of `elab_term_and_synthesize`.
- Every committed `elab-queries.jsonl` record stays byte-identical except those this plan adds. Check with `git diff tests/fixtures/elab/elab-queries.jsonl | grep '^-[^-]'`, which must print nothing.
- **Every new test is shown to discriminate.** The implementer applies the mutation named in the task, watches the test go red, reverts, and records the command and its output in the task report.
  - This repo's plans have repeatedly named mutations their tests do not kill: nine times across the last two slices. Treat every "Mutation:" line below as a hypothesis until you have run it.
  - If a mutation survives, strengthen the test. Never delete the mutation.
- Before every push: `mise run ci`, blocking, to completion (fmt, clippy, full suite). A subagent must not background it. Run it in the foreground and wait for the exit status.
- Fixture regeneration (never `mise run fixtures:regen`, which also touches Mathlib):
  `cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_elab.lean > elab-queries.jsonl`
  No task changes `Elab0.lean`, so `Elab0.olean` is not rebuilt.
- Oracle rejections are checked with a prelude-mode scratch file (in the scratchpad, never committed):
  ```
  prelude
  import Elab0
  #check <term>
  ```
  run as `cd tests/fixtures/elab && LEAN_PATH=$PWD lean /path/to/Chk.lean`. Quote the oracle's message beside the assertion.

## Review Focus

These are the five failure modes most likely to bite a user that no task's happy path exercises. Each has a test, added in the owning task.

1. **A resumed term that postpones again must not spawn a new postponed mvar.** If the resume catches its own postpone (`catchExPostpone` left on), each rung-1 pass "succeeds" by assigning the old mvar to a new one. The fixpoint then reports progress forever. Test in Task 2 (`resuming_does_not_catch_its_own_postpone`).
2. **`ElabError::Postpone` must never escape the public entry point.** A term that stays unresolvable through every rung reports the oracle's error: `fun x => x.1` and `(_ : _).1` give `InvalidProjection { TypeUnknown }`, and `fun x => (x).fst` gives `InvalidField { TypeUnknown }`. Tests in Task 3.
3. **A postponed term under binders resumes in its own local context and is abstracted out of the lambda** (`elimMVarDeps` over a `syntheticOpaque` mvar). Corpus records `p2/lval-in-arg` and `p2/lval-two-binders` in Task 3.
4. **A postponement inside a nested `(e :)` scope resolves or fails inside that scope** (`withSynthesize (postpone := .no)`, `BuiltinNotation.lean:433-435`). It must not leak out to the enclosing fixpoint. Corpus `p2/lval-nested-synthesize` and rejection `fun x => (x.1 :)` in Task 3.
5. **An application with no arguments never postpones on its head's type** (`unless namedArgs.isEmpty && args.isEmpty`, `App.lean:1366`). Without the guard, every mvar-typed local (`fun x => x`) is postponed for nothing. Test in Task 4.

---

## File Structure

| File | Responsibility | Task |
|---|---|---|
| `crates/leanr_meta/src/whnf.rs` | `whnf_r` → `pub` | 1 |
| `crates/leanr_elab/src/error.rs` | `ElabError::Postpone` | 1 |
| `crates/leanr_elab/src/postpone.rs` (new) | `try_postpone`, `is_mvar_app`, `try_postpone_if_mvar`, `try_postpone_if_none_or_mvar`, `postpone_elab_term` | 1 |
| `crates/leanr_elab/src/lib.rs` | `mod postpone;`; ledger rewrite | 1, 5 |
| `crates/leanr_elab/src/elab.rs` | `mk_fresh_type_mvar`; old `is_mvar_app` removed; `elab_using_elab_fns`, `resume_elab_term`, `catch_ex_postpone` threading, `.postpone` arm | 1, 2 |
| `crates/leanr_elab/src/builtin/hole.rs` | uses `mk_fresh_type_mvar` | 1 |
| `crates/leanr_elab/src/app/lval.rs` | `is_retryable` excludes `Postpone`; the real `tryPostponeIfMVar` | 1, 3 |
| `crates/leanr_elab/src/synthetic/state.rs` | `SavedTermState`, `save_term_state` and `restore_term_state` → `pub(crate)` | 2 |
| `crates/leanr_elab/src/synthetic/ladder.rs` | `resume_postponed` rewritten | 2 |
| `crates/leanr_elab/src/app/mod.rs` | `elab_app_args`' `tryPostponeIfMVar fType`; seam index | 4, 5 |
| `crates/leanr_elab/src/app/args.rs` | stale `FunctionExpected` comment | 4 |
| `crates/leanr_elab/src/app/head.rs` | generic arm's `catchPostpone` comment | 3 |
| `crates/leanr_elab/src/synthetic/report.rs`, `synthetic/default_inst.rs`, `dispatch.rs` | docs and deferral table | 5 |
| `crates/leanr_elab/tests/support/mod.rs` | `with_elab` helper | 1 |
| `crates/leanr_elab/tests/postpone_smoke.rs` (new) | mechanics tests | 1-4 |
| `crates/leanr_elab/tests/lval_smoke.rs`, `tests/seam_audit.rs` | flipped seams, needle | 2, 3, 5 |
| `tests/fixtures/elab/dump_elab.lean`, `elab-queries.jsonl` | `p2Queries` | 2, 3, 4 |
| spec § Landed + P2 amendment | record | 5 |

---

### Task 1: The postpone outcome and its producers (no producer wired yet)

**Files:**
- Modify: `crates/leanr_meta/src/whnf.rs:1888-1894`
- Modify: `crates/leanr_elab/src/error.rs` (new variant after `Internal`)
- Create: `crates/leanr_elab/src/postpone.rs`
- Modify: `crates/leanr_elab/src/lib.rs:283-290` (module list)
- Modify: `crates/leanr_elab/src/elab.rs` (add `mk_fresh_type_mvar`; delete the free fn `is_mvar_app` at `:548-575`; `use_implicit_lambda` calls the method)
- Modify: `crates/leanr_elab/src/builtin/hole.rs:57-70`
- Modify: `crates/leanr_elab/src/app/lval.rs:305-315` (`is_retryable`) and `:338` (the call site of the old free fn)
- Modify: `crates/leanr_elab/tests/support/mod.rs` (add `with_elab`)
- Create: `crates/leanr_elab/tests/postpone_smoke.rs`

**Interfaces:**
- Produces (all `pub`, on `TermElabM`):
  - `fn try_postpone(&self) -> Result<(), ElabError>`
  - `fn is_mvar_app(&mut self, e: ExprId) -> Result<bool, ElabError>`
  - `fn try_postpone_if_mvar(&mut self, e: ExprId) -> Result<(), ElabError>`
  - `fn try_postpone_if_none_or_mvar(&mut self, e: Option<ExprId>) -> Result<(), ElabError>`
  - `fn postpone_elab_term(&mut self, stx: &SynElem, expected: Option<ExprId>) -> Result<ExprId, ElabError>`
  - `fn mk_fresh_type_mvar(&mut self) -> Result<ExprId, ElabError>`
- Produces: `ElabError::Postpone` (unit variant).
- Produces (tests): `support::with_elab(src, |elab, term, kinds| …)`.
- `leanr_meta`: `MetaCtx::whnf_r` is now `pub`.

- [ ] **Step 1: Add the `with_elab` test helper**

Append to `crates/leanr_elab/tests/support/mod.rs`, after `elab_and_synthesize_doctored`:

```rust
/// Replay `Elab0`, parse `src`, and hand `k` a fresh `TermElabM` with
/// the parsed term — for tests that drive the elaborator step by step
/// (elaborate, then inspect `pending_mvars`, then run one fixpoint
/// step) rather than through a single entry point.
pub fn with_elab<R>(
    src: &str,
    k: impl FnOnce(
        &mut leanr_elab::TermElabM,
        &leanr_elab::dispatch::SynElem,
        &leanr_syntax::kind::KindInterner,
    ) -> R,
) -> R {
    with_elab_harness("with_elab", src, k)
}
```

- [ ] **Step 2: Write the failing tests**

Create `crates/leanr_elab/tests/postpone_smoke.rs`:

```rust
//! M4b-4a P2: term-level postponement mechanics — the producers
//! (`postpone.rs`), the catch (`elab.rs`'s `elab_using_elab_fns`) and
//! the resume (`synthetic/ladder.rs`'s `resume_postponed`). The corpus
//! (`oracle_elab.rs`, `p2/*` records) pins the TERMS postponement
//! produces; this file pins the state transitions the corpus cannot
//! see.

mod support;

use leanr_elab::synthetic::SyntheticMVarKind;
use leanr_elab::{ElabError, TermElabM};
use leanr_meta::{MVarId, MVarKind};

/// Pending synthetic mvars of kind `.postponed`, head-is-most-recent.
fn postponed_ids(elab: &TermElabM) -> Vec<MVarId> {
    elab.pending_mvars
        .iter()
        .copied()
        .filter(|id| {
            matches!(
                elab.synthetic_mvar_decl(*id).map(|d| &d.kind),
                Some(SyntheticMVarKind::Postponed { .. })
            )
        })
        .collect()
}

/// oracle: `tryPostpone` (`TermElabM.lean:1370-1372`) throws only
/// while `mayPostpone` holds, and `withoutPostponing` (`:1049-1050`)
/// clears it. `tryPostponeIfNoneOrMVar none` is plain `tryPostpone`
/// (`:1384-1387`).
#[test]
fn try_postpone_reads_may_postpone() {
    support::with_elab("Nat.zero", |elab, _, _| {
        assert!(matches!(elab.try_postpone(), Err(ElabError::Postpone)));
        assert!(matches!(
            elab.try_postpone_if_none_or_mvar(None),
            Err(ElabError::Postpone)
        ));
        assert!(elab.without_postponing(|e| e.try_postpone()).is_ok());
        assert!(elab
            .without_postponing(|e| e.try_postpone_if_none_or_mvar(None))
            .is_ok());
    });
}

/// oracle: `isMVarApp` is `(← whnfR e).getAppFn.isMVar`
/// (`TermElabM.lean:1375-1376`). `outParam` is `@[reducible]`
/// (`Elab0.lean:341`), so `outParam ?m` whnfR-reduces to `?m` — an
/// instantiate-then-spine-walk (leanr's pre-P2 approximation) sees the
/// constant `outParam` instead.
#[test]
fn is_mvar_app_sees_through_reducible_definitions() {
    support::with_elab("outParam _", |elab, term, kinds| {
        let e = elab.elab_term(term, kinds, None).expect("outParam _ elaborates");
        assert!(elab.is_mvar_app(e).unwrap(), "outParam ?m whnfR-reduces to ?m");
        assert!(matches!(
            elab.try_postpone_if_mvar(e),
            Err(ElabError::Postpone)
        ));
        assert!(elab.without_postponing(|el| el.try_postpone_if_mvar(e)).is_ok());
    });
    support::with_elab("Prod Nat _", |elab, term, kinds| {
        let e = elab.elab_term(term, kinds, None).expect("Prod Nat _ elaborates");
        assert!(!elab.is_mvar_app(e).unwrap(), "the head is the constant Prod");
        assert!(elab.try_postpone_if_mvar(e).is_ok());
    });
}

/// `whnfR` instantiates an ASSIGNED head mvar, so an mvar that has been
/// solved no longer counts.
#[test]
fn is_mvar_app_instantiates_an_assigned_head() {
    support::with_elab("Nat", |elab, term, kinds| {
        let nat = elab.elab_term(term, kinds, None).unwrap();
        let ty = elab.mctx.infer_type(nat).unwrap();
        let (m, id) = elab.mk_fresh_expr_mvar_of_kind(ty, MVarKind::Natural).unwrap();
        assert!(elab.is_mvar_app(m).unwrap());
        elab.mctx.mctx_mut().assign(id, nat).unwrap();
        assert!(!elab.is_mvar_app(m).unwrap());
    });
}

/// oracle: `postponeElabTermCore` (`TermElabM.lean:1449-1453`) —
/// `mkFreshExprMVar expectedType? .syntheticOpaque`, registered
/// `.postponed (← saveContext)`. With no expected type,
/// `mkFreshExprMVarImpl`'s `none` arm (`Meta/Basic.lean:872-875`)
/// mints a fresh type mvar first.
#[test]
fn postpone_elab_term_registers_a_synthetic_opaque_postponed_mvar() {
    support::with_elab("Nat.zero", |elab, term, _| {
        let before = elab.pending_mvars.len();
        elab.postpone_elab_term(term, None).unwrap();
        assert_eq!(elab.pending_mvars.len(), before + 1);
        let id = elab.pending_mvars[0];
        assert!(matches!(
            elab.synthetic_mvar_decl(id).unwrap().kind,
            SyntheticMVarKind::Postponed { .. }
        ));
        let decl = elab.mctx.mctx().decl(id).unwrap();
        assert_eq!(decl.kind, MVarKind::SyntheticOpaque);
        let ty = decl.ty;
        assert!(elab.is_mvar_app(ty).unwrap(), "no expected type: a fresh type mvar");
        assert_eq!(postponed_ids(elab), vec![id]);
    });
}
```

Also add, at the end of `crates/leanr_elab/src/app/lval.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    /// `resolveLValLoop` retries on `.error` only and rethrows internal
    /// exceptions (`App.lean:1688-1694`). A postponement is internal.
    #[test]
    fn postpone_is_not_retryable() {
        assert!(!is_retryable(&ElabError::Postpone));
        assert!(is_retryable(&ElabError::PlaceholderAsFunction));
    }
}
```

- [ ] **Step 3: Run them to verify they fail**

Run: `cargo test -p leanr_elab --test postpone_smoke` and `cargo test -p leanr_elab --lib lval::tests`
Expected: compile errors (`try_postpone`, `ElabError::Postpone`, `postpone_elab_term` do not exist).

- [ ] **Step 4: Widen `whnf_r`**

In `crates/leanr_meta/src/whnf.rs`, change `pub(crate) fn whnf_r` to `pub fn whnf_r`, and replace its doc's last sentence ("Composed here rather than exported: …") with:

```rust
    /// oracle: `whnfR` (`Basic.lean:2113-2114`) — `withTransparency
    /// .reducible <| whnf e`. In-crate consumers: `coe.rs`'s `isTypeApp?`
    /// and `coerceCollectingNames?`. `pub` since M4b-4a P2 for
    /// `leanr_elab`'s `isMVarApp` (`TermElabM.lean:1375-1376`) — the
    /// elab→meta accessor precedent: additive, no behaviour change.
```

- [ ] **Step 5: Add `ElabError::Postpone`**

In `crates/leanr_elab/src/error.rs`, after the `Internal(String)` variant:

```rust
    /// oracle: `Exception.internal postponeExceptionId`
    /// (`Elab/Exception.lean:15`, thrown by `throwPostpone`, `:22-23`) —
    /// "not ready yet: retry once more is known". An internal exception,
    /// never a user-facing error. Raised only while `may_postpone` holds,
    /// by the `try_postpone` family (`postpone.rs`) and `elab.rs`'s
    /// `useImplicitLambda` `.postpone` arm.
    ///
    /// Caught in exactly two places: `elab.rs`'s `elab_using_elab_fns`
    /// (`elabUsingElabFnsAux`, `TermElabM.lean:1635-1651`) and
    /// `synthetic/ladder.rs`'s `resume_postponed`
    /// (`SyntheticMVars.lean:60-65`). A catch site that retries or
    /// swallows ERRORS must let it through: `app/lval.rs`'s
    /// `is_retryable` (`App.lean:1688-1694`). `commit_when` and
    /// `with_synthesize_impl` restore and rethrow every `Err`, which is
    /// the oracle's treatment of it too.
    Postpone,
```

- [ ] **Step 6: `mk_fresh_type_mvar` in `elab.rs`, used by `hole.rs`**

In `crates/leanr_elab/src/elab.rs`, after `mk_fresh_expr_mvar_of_kind`:

```rust
    /// oracle: `mkFreshTypeMVar` (`Meta/Basic.lean:880-882`) — a fresh
    /// level mvar `u`, then a fresh NATURAL mvar of type `Sort u`. Also
    /// `mkFreshExprMVarImpl`'s `none` arm (`:872-875`), which builds the
    /// same type before minting the requested mvar of it.
    pub fn mk_fresh_type_mvar(&mut self) -> Result<ExprId, ElabError> {
        let u = self.mk_fresh_level_mvar()?;
        let sort = self
            .mctx
            .store_mut()
            .expr_sort(None, u)
            .map_err(leanr_meta::MetaError::from)?;
        self.mk_fresh_expr_mvar(sort)
    }
```

In `crates/leanr_elab/src/builtin/hole.rs`, replace the `None => { … }` arm of the `let ty = match expected` with `None => elab.mk_fresh_type_mvar()?,`, keeping the `mkFreshTypeMVar` comment as a one-liner above it.

- [ ] **Step 7: Create `postpone.rs`**

Create `crates/leanr_elab/src/postpone.rs`:

```rust
//! Term-level postponement, the PRODUCER side. Oracle:
//! `Lean/Elab/Term/TermElabM.lean`'s `tryPostpone` family
//! (`:1369-1387`) and `postponeElabTermCore` (`:1449-1453`).
//!
//! The three places postponement lives:
//! - here: the producers, and `postpone_elab_term`, which turns a term
//!   into a `.postponed` synthetic mvar;
//! - `elab.rs`'s `elab_using_elab_fns`: the catch
//!   (`elabUsingElabFnsAux`, `:1635-1651`);
//! - `synthetic/ladder.rs`'s `resume_postponed`: the resume
//!   (`resumePostponed`, `SyntheticMVars.lean:32-74`).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_meta::MVarKind;

use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::synthetic::SyntheticMVarKind;

impl<'e> TermElabM<'e> {
    /// oracle: `tryPostpone` (`TermElabM.lean:1370-1372`).
    pub fn try_postpone(&self) -> Result<(), ElabError> {
        if self.may_postpone {
            Err(ElabError::Postpone)
        } else {
            Ok(())
        }
    }

    /// oracle: `isMVarApp` (`TermElabM.lean:1375-1376`) —
    /// `(← whnfR e).getAppFn.isMVar`. `whnf_r` both unfolds reducible
    /// heads (`outParam ?m` is `?m`) and instantiates an assigned head
    /// mvar, so this is exact, not the instantiate-then-spine-walk
    /// approximation P1 carried.
    pub fn is_mvar_app(&mut self, e: ExprId) -> Result<bool, ElabError> {
        let r = self.mctx.whnf_r(e)?;
        let base = self.view.store;
        let mut cur = r;
        while let Node::App { f, .. } = self.mctx.store().expr_node(Some(base), cur) {
            cur = f;
        }
        Ok(matches!(
            self.mctx.store().expr_node(Some(base), cur),
            Node::MVar { .. }
        ))
    }

    /// oracle: `tryPostponeIfMVar` (`TermElabM.lean:1379-1381`).
    pub fn try_postpone_if_mvar(&mut self, e: ExprId) -> Result<(), ElabError> {
        if self.is_mvar_app(e)? {
            self.try_postpone()?;
        }
        Ok(())
    }

    /// oracle: `tryPostponeIfNoneOrMVar` (`TermElabM.lean:1384-1387`).
    /// The spec's P2 surface; its first production caller is P4's
    /// `resolveDottedIdentFn` (`App.lean:1988`).
    pub fn try_postpone_if_none_or_mvar(&mut self, e: Option<ExprId>) -> Result<(), ElabError> {
        match e {
            Some(e) => self.try_postpone_if_mvar(e),
            None => self.try_postpone(),
        }
    }

    /// oracle: `postponeElabTermCore` (`TermElabM.lean:1449-1453`), also
    /// `postponeElabTerm` (`:1608-1610`), whose only addition is the
    /// info-tree context (UI-only, not ported).
    ///
    /// `mkFreshExprMVar expectedType? .syntheticOpaque`: opaque, so no
    /// `is_def_eq` can assign it — only `resume_postponed` does, through
    /// a direct `assign`. With no expected type the mvar's type is a
    /// fresh type mvar (`mkFreshExprMVarImpl`'s `none` arm,
    /// `Meta/Basic.lean:872-875`).
    pub fn postpone_elab_term(
        &mut self,
        stx: &SynElem,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        let ty = match expected {
            Some(t) => t,
            None => self.mk_fresh_type_mvar()?,
        };
        let (mvar, mvar_id) = self.mk_fresh_expr_mvar_of_kind(ty, MVarKind::SyntheticOpaque)?;
        let ctx = self.save_context();
        self.register_synthetic_mvar(stx.clone(), mvar_id, SyntheticMVarKind::Postponed { ctx });
        Ok(mvar)
    }
}
```

Add `mod postpone; // M4b-4a P2` to `lib.rs`'s module list (private: its methods live on the public `TermElabM`).

- [ ] **Step 8: Retire the old `is_mvar_app` and exclude `Postpone` from the retry**

- `elab.rs`: delete the free function `pub(crate) fn is_mvar_app` (with its doc, `:548-575`). In `use_implicit_lambda`, change `if is_mvar_app(elab, x_ty)? {` to `if elab.is_mvar_app(x_ty)? {`.
- `app/lval.rs`: change `crate::elab::is_mvar_app(elab, e_type)?` to `elab.is_mvar_app(e_type)?`. Leave the seam around it alone; Task 3 replaces it.
- In `is_retryable`, add `| ElabError::Postpone` to the `matches!`, and extend its doc: "`Postpone` is the oracle's internal `postponeExceptionId`, which the `.internal` arm rethrows."
- Delete the sentence in `lval.rs`'s seam comment that says `is_mvar_app` is an approximation P2 owns: it is exact now.

- [ ] **Step 9: Run the tests to verify they pass**

Run: `cargo test -p leanr_elab --test postpone_smoke && cargo test -p leanr_elab --lib lval::tests && cargo test -p leanr_elab --test oracle_elab`
Expected: PASS. The corpus gate stays green (Task 1 has no producer wired; `is_mvar_app` exactness is behaviour-neutral on every committed record).

- [ ] **Step 10: Run the mutations**

Apply each, run the named test, see it fail, revert. Record each in the report.
- `try_postpone` always `Ok(())` → `try_postpone_reads_may_postpone` fails on the first assert.
- `try_postpone` ignores `may_postpone` (always `Err`) → fails on the `without_postponing` assert.
- `is_mvar_app` back to P1's shape (`instantiate_mvars` then spine walk, no `whnf_r`) → `is_mvar_app_sees_through_reducible_definitions` fails.
- `is_mvar_app` reads `expr_node` of `e` directly (no `whnf_r`, no instantiate) → `is_mvar_app_instantiates_an_assigned_head` fails.
- `postpone_elab_term` mints `MVarKind::Natural` → the kind assert fails.
- `is_retryable` without the `Postpone` arm → `postpone_is_not_retryable` fails.

- [ ] **Step 11: Commit**

```bash
cargo fmt --all
git add crates/leanr_meta/src/whnf.rs crates/leanr_elab/src crates/leanr_elab/tests/support/mod.rs crates/leanr_elab/tests/postpone_smoke.rs
git commit -m "M4b-4a P2: the postpone outcome and its producers"
```

---

### Task 2: The catch, the resume, and the implicit-lambda producer

**Files:**
- Modify: `crates/leanr_elab/src/synthetic/state.rs:131-141`, `:318-333` (visibility)
- Modify: `crates/leanr_elab/src/elab.rs` (`elab_term`, `elab_term_without_implicit_lambda`, `elab_term_core`, new `elab_using_elab_fns` and `resume_elab_term`, `elab_implicit_lambda`, and the `UseImplicitLambda` docs)
- Modify: `crates/leanr_elab/src/synthetic/ladder.rs:437-489` (`resume_postponed`)
- Modify: `crates/leanr_elab/tests/seam_audit.rs:860-885` (`implicit_lambda_postpone_is_a_named_seam`) and the module doc paragraph at `:70-83`
- Modify: `tests/fixtures/elab/dump_elab.lean`, `elab-queries.jsonl`
- Test: `crates/leanr_elab/tests/postpone_smoke.rs`

**Interfaces:**
- Consumes: Task 1's `postpone_elab_term`, `ElabError::Postpone`, `with_elab`.
- Produces:
  - `TermElabM::resume_elab_term(&mut self, elem: &SynElem, kinds: &KindInterner, expected: ExprId) -> Result<ExprId, ElabError>`, `pub(crate)`.
  - `TermElabM::elab_using_elab_fns(&mut self, elem: &SynElem, kinds: &KindInterner, expected: Option<ExprId>, catch_ex_postpone: bool) -> Result<ExprId, ElabError>`, private to `elab.rs`.
  - `save_term_state` / `restore_term_state` / `SavedTermState` are now `pub(crate)`.
  - `dump_elab.lean`'s `p2Queries` list. Tasks 3-4 append to it.

- [ ] **Step 1: Add the corpus record**

In `tests/fixtures/elab/dump_elab.lean`, before `def emit`, add:

```lean
/- M4b-4a P2: term-level postponement. Every record here elaborates
only because a subterm is POSTPONED (`Exception.postpone`, caught by
`elabUsingElabFnsAux`, TermElabM.lean:1635-1651) and RESUMED by the
fixpoint once its type is known. -/
def p2Queries : List (String × String) :=
  -- `useImplicitLambda` returns `.postpone` for `x` (a local of type
  -- `?α`, expected `{a : Type} → Nat`, TermElabM.lean:1753-1778). The
  -- resume at rung 1 postpones again; rung 2's `withoutPostponing`
  -- elaborates `x` WITHOUT the implicit lambda (`:1853-1854`) and
  -- `ensureHasType` assigns `?α`. Result: `fun x => x`, no wrap.
  [ ("p2/implicit-lambda-postpone", "fun x => (x : {a : Type} -> Nat)")
  ]
```

and append `++ p2Queries` to the query concatenation in `main`. Regenerate:
`cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_elab.lean > elab-queries.jsonl`.
Check that the diff is exactly one added line: `git diff --stat tests/fixtures/elab/elab-queries.jsonl` and `git diff tests/fixtures/elab/elab-queries.jsonl | grep '^-[^-]'` (must print nothing).

- [ ] **Step 2: Write the failing mechanics tests**

Append to `crates/leanr_elab/tests/postpone_smoke.rs`:

```rust
/// oracle: `elabUsingElabFnsAux` (`TermElabM.lean:1635-1651`) catches
/// `Exception.postpone` when `catchExPostpone` and registers the term
/// as a `.postponed` synthetic mvar. The postponed syntax is `x` — the
/// local whose implicit-lambda treatment is postponed — not the
/// enclosing ascription.
#[test]
fn elab_term_catches_a_postpone_and_registers_the_term() {
    support::with_elab("fun x => (x : {a : Type} -> Nat)", |elab, term, kinds| {
        elab.elab_term(term, kinds, None)
            .expect("the catch turns the postponement into an mvar");
        let ids = postponed_ids(elab);
        assert_eq!(ids.len(), 1, "exactly the one postponed `x`");
        let decl = elab.synthetic_mvar_decl(ids[0]).unwrap();
        assert_eq!(kinds.name(decl.stx.kind()), "<ident>");
    });
}

/// oracle: `.postpone` with `mayPostpone == false` elaborates WITHOUT
/// implicit lambdas (`TermElabM.lean:1853-1854`) — no postponement.
#[test]
fn without_postponing_the_implicit_lambda_arm_elaborates_directly() {
    support::with_elab("fun x => (x : {a : Type} -> Nat)", |elab, term, kinds| {
        elab.without_postponing(|e| e.elab_term(term, kinds, None))
            .expect("elaborates without the wrap");
        assert!(postponed_ids(elab).is_empty());
    });
}

/// Review Focus 1. oracle: `resumeElabTerm` elaborates with
/// `catchExPostpone := false` (`SyntheticMVars.lean:23-26`), and
/// `resumePostponed` turns a postponement into "not ready yet"
/// (`:60-65`). At rung 1 `x`'s type is still unknown, so the resume
/// postpones again: the step makes NO progress and the SAME mvar stays
/// pending. Catching it instead would assign the old mvar to a fresh
/// one — "progress" the fixpoint would chase forever.
#[test]
fn resuming_does_not_catch_its_own_postpone() {
    support::with_elab("fun x => (x : {a : Type} -> Nat)", |elab, term, kinds| {
        elab.elab_term(term, kinds, None).unwrap();
        let before = postponed_ids(elab);
        let progressed = elab
            .synthesize_synthetic_mvars_step(false, false, kinds)
            .unwrap();
        assert!(!progressed, "a re-postponed resume is not progress");
        assert_eq!(postponed_ids(elab), before);
    });
}

/// oracle: `resumePostponed`'s `.error` arm with `postponeOnError`
/// restores the saved state (`SyntheticMVars.lean:66-69`). `(_ : Nat).1`
/// registers a hole (`registerMVarErrorHoleInfo`,
/// `BuiltinTerm.lean:67`), then fails: `#check (_ : Nat).1` on the
/// pinned oracle reports "Invalid projection: Projections extract
/// constructor fields for one-constructor inductive types. The
/// expression ?m.1 has type `Nat` which is not a one-constructor
/// inductive type."
#[test]
fn a_failed_resume_under_postpone_on_error_rolls_its_state_back() {
    support::with_elab("(_ : Nat).1", |elab, term, kinds| {
        elab.postpone_elab_term(term, None).unwrap();
        let id = elab.pending_mvars[0];
        let infos = elab.mvar_error_infos.len();
        let r = elab.without_postponing(|e| e.synthesize_synthetic_mvar(id, true, false, kinds));
        assert!(matches!(r, Ok(false)), "{r:?}");
        assert_eq!(elab.mvar_error_infos.len(), infos, "the hole's registration is rolled back");
        let r = elab.without_postponing(|e| e.synthesize_synthetic_mvar(id, false, false, kinds));
        assert!(
            matches!(
                r,
                Err(ElabError::InvalidProjection {
                    reason: leanr_elab::InvalidProjectionReason::NotOneCtor,
                    ..
                })
            ),
            "{r:?}"
        );
    });
}
```

- [ ] **Step 3: Flip the seam_audit test**

In `crates/leanr_elab/tests/seam_audit.rs`, replace `implicit_lambda_postpone_is_a_named_seam` (doc and body) with:

```rust
/// M4b-3 P5 Task 6 seamed `useImplicitLambda`'s `.postpone` arm
/// (`TermElabM.lean:1753-1778`); M4b-4a P2 closed it. The same source
/// now ELABORATES — the success shape is the corpus record
/// `p2/implicit-lambda-postpone` — so what stays pinned here is that it
/// is no longer a seam.
#[test]
fn implicit_lambda_postpone_is_no_longer_a_seam() {
    let src = "fun x => (x : {a : Type} -> Nat)";
    assert!(
        elab_and_synthesize(src).is_ok(),
        "{src:?} must elaborate since M4b-4a P2"
    );
}
```

Rewrite the module-doc paragraph starting "**The implicit-lambda `.postpone` arm**" (`:70-83`) to say it was seamed by M4b-3 P5 Task 6 and closed by M4b-4a P2. Point to the new test and the corpus record.

- [ ] **Step 4: Run them to verify they fail**

Run: `cargo test -p leanr_elab --test postpone_smoke --test seam_audit --test oracle_elab`
Expected: the four new mechanics tests fail. The first three hit the `UnsupportedSyntax` seam. `a_failed_resume…` returns `Ok(false)` but with `infos + 1`, because today's `resume_postponed` never restores. `implicit_lambda_postpone_is_no_longer_a_seam` and `oracle_elab_gate` (record `p2/implicit-lambda-postpone`) fail too.

- [ ] **Step 5: Make the saved-state pair crate-visible**

In `synthetic/state.rs`, make `struct SavedTermState`, `fn save_term_state` and `fn restore_term_state` `pub(crate)`. Append to `commit_when`'s doc paragraph naming its callers: "`elab.rs`'s `elab_using_elab_fns` and `ladder.rs`'s `resume_postponed` use the same pair since M4b-4a P2."

- [ ] **Step 6: Thread `catch_ex_postpone` through `elab.rs`**

Replace `elab_term`, `elab_term_without_implicit_lambda` and `elab_term_core` with the following. Keep `elab_term_core`'s existing paren-loop comment verbatim where marked.

```rust
    pub fn elab_term(
        &mut self,
        elem: &SynElem,
        kinds: &KindInterner,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        self.elab_term_core(elem, kinds, expected, true, true)
    }

    // (`elab_term_without_implicit_lambda`: body becomes
    // `self.elab_term_core(elem, kinds, expected, true, false)`; doc unchanged.)

    /// oracle: `resumeElabTerm` (`SyntheticMVars.lean:23-26`) —
    /// `elabTerm stx expectedType? (catchExPostpone := false)`, so a
    /// resumed term that postpones again throws to `resume_postponed`
    /// instead of minting a second postponed mvar. The `errToSorry`
    /// narrowing there is not modelled (leanr has no `errToSorry`).
    pub(crate) fn resume_elab_term(
        &mut self,
        elem: &SynElem,
        kinds: &KindInterner,
        expected: ExprId,
    ) -> Result<ExprId, ElabError> {
        self.elab_term_core(elem, kinds, Some(expected), false, true)
    }

    /// oracle: `elabTermAux` (`TermElabM.lean:1823-1856`).
    fn elab_term_core(
        &mut self,
        elem: &SynElem,
        kinds: &KindInterner,
        expected: Option<ExprId>,
        catch_ex_postpone: bool,
        implicit_lambda: bool,
    ) -> Result<ExprId, ElabError> {
        if !implicit_lambda {
            // … existing paren-stripping comment and loop, unchanged …
            return self.elab_using_elab_fns(&cur, kinds, expected, catch_ex_postpone);
        }
        // oracle: `useImplicitLambda` runs BEFORE `elabUsingElabFns`
        // (`:1839-1841`); `.yes` short-circuits dispatch entirely.
        match use_implicit_lambda(self, elem, kinds, expected)? {
            UseImplicitLambda::Yes(ty) => {
                elab_implicit_lambda(self, elem, kinds, catch_ex_postpone, ty)
            }
            UseImplicitLambda::No => {
                self.elab_using_elab_fns(elem, kinds, expected, catch_ex_postpone)
            }
            // oracle: `:1843-1854` — postpone if we still may; once we
            // may not, elaborate WITHOUT implicit lambdas. With the catch
            // off (a resume), the postponement is thrown to the resumer.
            UseImplicitLambda::Postpone => {
                if self.may_postpone {
                    if catch_ex_postpone {
                        self.postpone_elab_term(elem, expected)
                    } else {
                        Err(ElabError::Postpone)
                    }
                } else {
                    self.elab_using_elab_fns(elem, kinds, expected, catch_ex_postpone)
                }
            }
        }
    }

    /// oracle: `elabUsingElabFns` (`TermElabM.lean:1663-1668`), which
    /// saves the state, and `elabUsingElabFnsAux`'s postpone handler
    /// (`:1635-1651`): on `Exception.postpone`, with `catchExPostpone`,
    /// RESTORE the saved state — discarding whatever the failed attempt
    /// registered (the oracle's own example: in `((f.x a1).x a2).x a3`
    /// the inner postponed mvars are dead once the outer one is
    /// postponed) — then `postponeElabTermCore`.
    ///
    /// leanr has one elaborator per kind, so the oracle's walk over
    /// several `elabFns` (and its `unsupportedSyntax` fall-through) has
    /// no counterpart.
    ///
    /// The `lctx` is restored too. The oracle gets that for free: its
    /// local context is a reader field, never part of the saved state.
    /// leanr's `lctx` lives in `MetaCtx`, and every telescope bracket
    /// already restores on `Err`, so this is the same guarantee made
    /// explicit at the one place a postponement is swallowed.
    ///
    /// Cost: `save_term_state` clones the three `Term.State` tables and
    /// the mctx assignment maps on EVERY caught elaboration, where the
    /// oracle's persistent structures make `saveState` O(1). Recorded in
    /// the spec's § Landed as a known cost.
    fn elab_using_elab_fns(
        &mut self,
        elem: &SynElem,
        kinds: &KindInterner,
        expected: Option<ExprId>,
        catch_ex_postpone: bool,
    ) -> Result<ExprId, ElabError> {
        if !catch_ex_postpone {
            return dispatch::dispatch(self, elem, kinds, expected);
        }
        let saved = self.save_term_state();
        let lctx = self.mctx.lctx_checkpoint();
        match dispatch::dispatch(self, elem, kinds, expected) {
            Err(ElabError::Postpone) => {
                self.restore_term_state(saved);
                self.mctx.lctx_restore(lctx);
                self.postpone_elab_term(elem, expected)
            }
            other => other,
        }
    }
```

Change `elab_implicit_lambda`'s signature to take `catch_ex_postpone: bool` before `ty`. Replace its body line `let e = elab.elab_term_ensuring_type(elem, kinds, Some(ty))?;` with:

```rust
        // oracle: `elabImplicitLambdaAux` (`:1796-1799`) —
        // `elabUsingElabFns stx expectedType catchExPostpone`, then
        // `ensureHasType`. The catch flag is the caller's: a resumed
        // term's postponement must reach `resume_postponed` even from
        // inside the wrap.
        let body = elab.elab_using_elab_fns(elem, kinds, Some(ty), catch_ex_postpone)?;
        let e = elab.ensure_has_type(elem, Some(ty), body)?;
```

In that function's doc, delete the first bullet ("the oracle elaborates the residual body with `elabUsingElabFns` … reviewer-verified behaviourally equivalent"). It is now a literal port.

In the `UseImplicitLambda::Postpone` variant doc and `use_implicit_lambda`'s doc, replace every "named seam … M4b-4a P2" sentence with: "`elab_term_core` handles it: postpone, throw to the resumer, or (with postponement off) elaborate without the wrap, `TermElabM.lean:1843-1854`."

- [ ] **Step 7: Rewrite `resume_postponed`**

Replace the body of `synthetic/ladder.rs`'s `resume_postponed` (doc included) with:

```rust
    /// oracle: `resumePostponed` (`SyntheticMVars.lean:32-74`) —
    /// re-elaborate the postponed syntax under its saved context, ensure
    /// it has the mvar's type, and assign.
    ///
    /// - The elaboration is `resume_elab_term` (catch OFF): a term that
    ///   postpones again is "not ready yet", never a fresh mvar.
    /// - `saveState` is taken inside the mvar's context (the caller,
    ///   `synthesize_synthetic_mvar`, installs it). EVERY non-success
    ///   restores it: a postponement (`:61-65`) and, under
    ///   `postponeOnError`, an error (`:66-69`).
    /// - Without `postponeOnError` the oracle logs the error and reports
    ///   the mvar done (`:70-72`). leanr has no message log, so the error
    ///   propagates (the same narrowing `synthesize_pending_inst_mvar`
    ///   records).
    /// - The `occursCheck` guard (`:56-58`) is kept: a result containing
    ///   `mvar_id` itself is "not ready", not an error.
    fn resume_postponed(
        &mut self,
        ctx: &SavedContext,
        stx: &SynElem,
        mvar_id: MVarId,
        postpone_on_error: bool,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        let saved = self.save_term_state();
        let stx = stx.clone();
        let result = self.with_saved_context(ctx, |elab| {
            let expected = elab
                .mctx
                .mctx()
                .decl(mvar_id)
                .expect("postponed mvar is declared")
                .ty;
            let expected = elab.mctx.instantiate_mvars(expected)?;
            let e = elab.resume_elab_term(&stx, kinds, expected)?;
            // oracle: `:52-53` — the postponing method never saw the
            // result, so its type is checked here.
            let e = elab.ensure_has_type(&stx, Some(expected), e)?;
            if elab.mctx.check_occurs(mvar_id, e)? {
                elab.mctx.mctx_mut().assign(mvar_id, e)?;
                Ok(true)
            } else {
                Ok(false)
            }
        });
        match result {
            Ok(done) => Ok(done),
            Err(ElabError::Postpone) => {
                self.restore_term_state(saved);
                Ok(false)
            }
            Err(_) if postpone_on_error => {
                self.restore_term_state(saved);
                Ok(false)
            }
            Err(e) => Err(e),
        }
    }
```

(`ensure_has_type` is `pub(crate)` in `coe.rs`, callable from `ladder.rs`.)

- [ ] **Step 8: Run the tests to verify they pass**

Run: `cargo test -p leanr_elab`
Expected: PASS, including every existing corpus record and `p2/implicit-lambda-postpone`.

Existing tests that assert the P2 seam still fail at this point. They belong to Task 3; mark each `#[ignore = "M4b-4a P2 Task 3"]` rather than editing it:
- `lval_smoke.rs`'s `p2_p3_p4_constructs_are_named_seams`, whose `fun x => x.1` is still seamed at `resolve_lval_loop`. It should in fact still pass until Task 3. Only ignore a test that actually fails, and list it in the report.

- [ ] **Step 9: Run the mutations**

- In `elab_using_elab_fns`, drop the `Err(Postpone)` arm (return `other` for everything) → `elab_term_catches_a_postpone_and_registers_the_term` fails with `Err(Postpone)`.
- In the `.postpone` arm, take the `may_postpone` branch unconditionally → `without_postponing_the_implicit_lambda_arm_elaborates_directly` fails (one postponed id).
- In the `.postpone` arm's `!catch_ex_postpone` branch, call `postpone_elab_term` instead of `Err(Postpone)`. Or make `resume_elab_term` pass `true`. → `resuming_does_not_catch_its_own_postpone` fails (`progressed == true`, a different id pending).
- In `resume_postponed`, drop the `restore_term_state` in the `postpone_on_error` arm → `a_failed_resume_under_postpone_on_error_rolls_its_state_back` fails (`infos + 1`).
- Restore the old seam in the `.postpone` arm → `oracle_elab_gate` fails on `p2/implicit-lambda-postpone`.

The `restore_term_state` in `resume_postponed`'s `Err(Postpone)` arm and in `elab_using_elab_fns` get their discriminating tests in Task 3. They need the LVal producer, which postpones AFTER state has changed; this task's only producer postpones before any change. Say so in the report; do not invent a test here.

- [ ] **Step 10: Commit**

```bash
cargo fmt --all
git add crates/leanr_elab tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -m "M4b-4a P2: catch and resume postponed terms; implicit-lambda .postpone"
```

---

### Task 3: `resolveLValLoop` postpones

**Files:**
- Modify: `crates/leanr_elab/src/app/lval.rs:326-348` (`resolve_lval_loop`)
- Modify: `crates/leanr_elab/src/app/head.rs:155-163` (generic-arm comment)
- Modify: `crates/leanr_elab/tests/lval_smoke.rs:120-128`
- Modify: `tests/fixtures/elab/dump_elab.lean` (`p2Queries`), `elab-queries.jsonl`
- Test: `crates/leanr_elab/tests/postpone_smoke.rs`

**Interfaces:**
- Consumes: `try_postpone_if_mvar`, `is_mvar_app` (Task 1), and the catch and resume (Task 2).
- Produces: nothing new. `resolve_lval_loop`'s signature is unchanged.

- [ ] **Step 1: Add the corpus records**

Append to `p2Queries` (every one checked on the pinned oracle while writing this plan):

```lean
  -- `resolveLValLoop`'s `tryPostponeIfMVar eType` (App.lean:1680): `x`'s
  -- type is `?α` until the application unifies it with `Prod Nat Nat`.
  , ("p2/lval-idx-applied",        "(fun x => x.1) (Prod.mk Nat.zero Nat.zero)")
  , ("p2/lval-name-applied",       "(fun x => (x).fst) (Prod.mk Nat.zero Nat.zero)")
  -- The inner `x.1` is postponed, then the outer `.1` postpones on the
  -- inner mvar's type: the catch RESTORES (dropping the inner mvar) and
  -- postpones the whole `(x.1).1` (TermElabM.lean:1636-1650).
  , ("p2/lval-chain",              "(fun x => (x.1).1) (Prod.mk (Prod.mk Nat.zero Nat.zero) Nat.zero)")
  -- Postponed as an ARGUMENT, resumed under `x`'s binder (Review Focus 3).
  , ("p2/lval-in-arg",             "(fun x => Nat.succ x.1) (Prod.mk Nat.zero Nat.zero)")
  , ("p2/lval-two-binders",        "(fun x y => Prod.mk x.2 y.1) (Prod.mk Nat.zero Nat.zero) (Prod.mk Nat.zero Nat.zero)")
  -- `(e :)` drains its own postponements (`withSynthesize (postpone :=
  -- .no)`, BuiltinNotation.lean:433-435) — Review Focus 4.
  , ("p2/lval-nested-synthesize",  "((fun x => x.1) (Prod.mk Nat.zero Nat.zero) :)")
  -- `outParam` is reducible: `isMVarApp (outParam ?m)` is true only
  -- through `whnfR` (TermElabM.lean:1375-1376).
  , ("p2/lval-reducible-alias",    "(fun (x : outParam _) => x.1) (Prod.mk Nat.zero Nat.zero)")
```

Regenerate, and check the diff adds exactly seven lines and removes none.

- [ ] **Step 2: Write the failing mechanics tests**

Append to `postpone_smoke.rs`:

```rust
/// oracle: the catch restores the saved state before postponing
/// (`TermElabM.lean:1636-1650`). Elaborating `(x.1).1` postpones the
/// inner `x.1` first (a registered mvar `?m`), then the outer `.1`
/// postpones on `?m`'s unknown type; the restore drops `?m`, so exactly
/// ONE postponed mvar — the whole `(x.1).1` — is pending.
#[test]
fn a_postpone_discards_what_the_failed_attempt_registered() {
    support::with_elab("fun x => (x.1).1", |elab, term, kinds| {
        elab.elab_term(term, kinds, None).unwrap();
        let ids = postponed_ids(elab);
        assert_eq!(ids.len(), 1, "the inner postponement is discarded");
        let decl = elab.synthetic_mvar_decl(ids[0]).unwrap();
        assert_eq!(
            u32::from(decl.stx.text_range().len()),
            "(x.1).1".len() as u32,
            "the postponed syntax is the whole projection chain"
        );
    });
}

/// oracle: a resume that postpones again restores its saved state
/// (`SyntheticMVars.lean:61-65`). `(_ : _).1`'s head registers two holes
/// (the type and the value), THEN `.1` postpones on `?T`.
#[test]
fn a_resume_that_postpones_again_rolls_its_state_back() {
    support::with_elab("(_ : _).1", |elab, term, kinds| {
        elab.postpone_elab_term(term, None).unwrap();
        let id = elab.pending_mvars[0];
        let infos = elab.mvar_error_infos.len();
        let pending = elab.pending_mvars.clone();
        let r = elab.synthesize_synthetic_mvar(id, false, false, kinds);
        assert!(matches!(r, Ok(false)), "{r:?}");
        assert_eq!(elab.mvar_error_infos.len(), infos, "both holes rolled back");
        assert_eq!(elab.pending_mvars, pending);
    });
}
```

- [ ] **Step 3: Turn the P2 seam assertion into oracle rejections**

In `lval_smoke.rs`'s `p2_p3_p4_constructs_are_named_seams`, delete the `tryPostponeIfMVar … seam("fun x => x.1")` assertion and its comment. Remove the `#[ignore]` if Task 2 added one. Add a new test:

```rust
/// Review Focus 2: a postponed projection whose type never becomes
/// known is reported at the last rung with the oracle's error — never
/// as `ElabError::Postpone`, never as a seam. Each message is the
/// pinned oracle's (`#check`, prelude file importing `Elab0`).
#[test]
fn postponed_projections_on_an_unknown_type_report_the_oracle_error() {
    // "Invalid projection: Type of x is not known; cannot resolve projection `1`"
    assert_eq!(proj_reason("fun x => x.1"), InvalidProjectionReason::TypeUnknown);
    // Same message, raised inside `(e :)`'s own `withSynthesize (postpone := .no)`.
    assert_eq!(proj_reason("fun x => (x.1 :)"), InvalidProjectionReason::TypeUnknown);
    // Same message through a reducible alias (`outParam ?m`).
    assert_eq!(
        proj_reason("fun (x : outParam _) => x.1"),
        InvalidProjectionReason::TypeUnknown
    );
    // "Invalid projection: Type of ?m.4 is not known; cannot resolve projection `1`"
    assert_eq!(proj_reason("(_ : _).1"), InvalidProjectionReason::TypeUnknown);
    // "Invalid field notation: Type of x is not known; cannot resolve field `fst`"
    match support::elab_and_synthesize("fun x => (x).fst") {
        Err(ElabError::InvalidField { reason: InvalidFieldReason::TypeUnknown, .. }) => {}
        other => panic!("expected InvalidField TypeUnknown, got {other:?}"),
    }
}
```

- [ ] **Step 4: Run them to verify they fail**

Run: `cargo test -p leanr_elab --test postpone_smoke --test lval_smoke --test oracle_elab`
Expected: the two new mechanics tests, the rejection test and the seven `p2/lval-*` records fail on the P2 seam (`UnsupportedSyntax(… M4b-4a P2)`).

- [ ] **Step 5: Replace the seam with the oracle's call**

In `resolve_lval_loop`, replace everything from the `// \`tryPostponeIfMVar eType\` then …` comment through the closing `}` of the `if … is_mvar_app` block with:

```rust
    // oracle: `tryPostponeIfMVar eType` (`App.lean:1680`), then, when
    // postponement is off (ladder rungs 2 and 4, or a resume below
    // them), `if (← isMVarApp eType) then
    // synthesizeSyntheticMVarsUsingDefault` (`:1681-1683`) — try default
    // instances to unblock the type before resolving.
    elab.try_postpone_if_mvar(e_type)?;
    if elab.is_mvar_app(e_type)? {
        elab.synthesize_synthetic_mvars_using_default(kinds)?;
    }
```

In `app/head.rs`'s generic arm comment (`:155-163`), replace "The `catchPostpone`/`overloaded` distinction (`:2121-2129`, `:2137`) is P2's and the overloading slice's: leanr cannot postpone yet, and `overloaded` is always false until `choice` is routed." with:

"`catchPostpone := !overloaded` (`:2121`) is always `true` here, since `overloaded` is false until `choice` is routed (overloading slice), so `elab_term`'s catch applies. `observing`'s restore-and-rethrow of a postponement (`TermElabM.lean:586-589`) is subsumed by the enclosing `elab_term`'s own restore, which rolls back to an earlier state."

- [ ] **Step 6: Run the tests to verify they pass**

Run: `cargo test -p leanr_elab`
Expected: PASS. If any `p2/lval-*` record differs, diff the encodings (`oracle_elab.rs` prints both) before changing code. The likely suspects are the resume's local context and `elimMVarDeps` over the `syntheticOpaque` mvar. Report the diff.

- [ ] **Step 7: Run the mutations**

- Replace `elab.try_postpone_if_mvar(e_type)?;` with nothing → the seven `p2/lval-*` records fail (TypeUnknown), and `a_postpone_discards…` fails.
- Revert `is_mvar_app` to P1's shape (instantiate + spine walk) → `p2/lval-reducible-alias` fails. If it survives, record why: leanr may already expose `?m` before `resolve_lval_loop` reads it. Then add the mutation's output to the report and rely on Task 1's unit test.
- In `elab_using_elab_fns`, drop `self.restore_term_state(saved);` → `a_postpone_discards_what_the_failed_attempt_registered` fails (2 postponed ids).
- In `resume_postponed`, drop the `restore_term_state` in the `Err(Postpone)` arm → `a_resume_that_postpones_again_rolls_its_state_back` fails.
- Make `is_retryable(&Postpone)` true → nothing in the corpus notices, because the postpone is raised outside the retried `match`. That is why Task 1's unit test exists. Record it.

- [ ] **Step 8: Commit**

```bash
cargo fmt --all
git add crates/leanr_elab tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -m "M4b-4a P2: field notation postpones on an unknown type"
```

---

### Task 4: `elabAppArgs` postpones on an mvar-typed head

**Files:**
- Modify: `crates/leanr_elab/src/app/mod.rs:460-477` (`elab_app_args`)
- Modify: `crates/leanr_elab/src/app/args.rs:139-146` (comment above `FunctionExpected`)
- Modify: `tests/fixtures/elab/dump_elab.lean` (`p2Queries`), `elab-queries.jsonl`
- Test: `crates/leanr_elab/tests/postpone_smoke.rs`, `crates/leanr_elab/tests/app_smoke.rs`

**Interfaces:**
- Consumes: `try_postpone_if_mvar` (Task 1), the catch and resume (Task 2), the LVal producer (Task 3, for `p2/app-fn-after-lval`).

- [ ] **Step 1: Add the corpus records**

Append to `p2Queries`:

```lean
  -- `elabAppArgs`' `unless namedArgs.isEmpty && args.isEmpty do
  -- tryPostponeIfMVar fType` (App.lean:1366-1367): `f : ?α` is applied
  -- before the outer application assigns `?α := Nat → Nat`.
  , ("p2/app-fn-applied",          "(fun f => f Nat.zero) Nat.succ")
  , ("p2/app-fn-two-args",         "(fun f x => f x) Nat.succ Nat.zero")
  , ("p2/app-fn-after-lval",       "(fun x f => f x.1) (Prod.mk Nat.zero Nat.zero) Nat.succ")
```

Regenerate, and check the diff adds exactly three lines and removes none.

- [ ] **Step 2: Write the failing tests**

Append to `postpone_smoke.rs`:

```rust
/// Review Focus 5. oracle: `elabAppArgs` postpones on an mvar-typed
/// head only when there is something to apply (`unless namedArgs.isEmpty
/// && args.isEmpty`, `App.lean:1366`). A bare local of unknown type is
/// elaborated as is.
#[test]
fn an_application_with_no_arguments_does_not_postpone_on_its_head_type() {
    support::with_elab("fun x => x", |elab, term, kinds| {
        elab.elab_term(term, kinds, None).unwrap();
        assert!(postponed_ids(elab).is_empty());
    });
}

/// …and with an argument, it does: the body `f Nat.zero` is postponed
/// whole.
#[test]
fn an_application_of_an_mvar_typed_head_is_postponed() {
    support::with_elab("fun f => f Nat.zero", |elab, term, kinds| {
        elab.elab_term(term, kinds, None).unwrap();
        assert_eq!(postponed_ids(elab).len(), 1);
    });
}
```

Append to `app_smoke.rs`, next to the other `FunctionExpected` tests:

```rust
/// Nothing ever pins `f`'s type: postponed, resumed at rung 4 without
/// postponement, and reported. `#check fun f => f Nat.zero` on the
/// pinned oracle: "Function expected at f but this term has type ?m.1".
#[test]
fn an_unpinned_function_head_is_reported_after_postponement() {
    match support::elab_and_synthesize("fun f => f Nat.zero") {
        Err(leanr_elab::ElabError::FunctionExpected { .. }) => {}
        other => panic!("expected FunctionExpected, got {other:?}"),
    }
}
```

(The last one passes today and after, a regression pin. Say so in the report; its discriminating partners are the corpus records.)

- [ ] **Step 3: Run them to verify they fail**

Run: `cargo test -p leanr_elab --test postpone_smoke --test oracle_elab`
Expected: `an_application_of_an_mvar_typed_head_is_postponed` fails (0 postponed), and the three `p2/app-fn-*` records fail with `FunctionExpected`.

- [ ] **Step 4: Add the call**

In `app/mod.rs`'s `elab_app_args`, directly after `let f_type = elab.mctx.instantiate_mvars(f_type)?;`:

```rust
    // oracle: `unless namedArgs.isEmpty && args.isEmpty do
    // tryPostponeIfMVar fType` (`App.lean:1366-1367`) — an mvar-typed
    // head with something to apply waits for its type. With
    // postponement off it falls through to `main`, whose
    // `synthesize_pending_and_normalize_fun_type` reports
    // `FunctionExpected`.
    if !(named_args.is_empty() && args.is_empty()) {
        elab.try_postpone_if_mvar(f_type)?;
    }
```

In `app/args.rs`, update the comment above `Err(ElabError::FunctionExpected { … })` ("M4b-3 P5 task 4 closed the mvar-fType seam …"). Say that an `fType` still an unassigned mvar here is reached only with postponement off, because `elab_app_args` postpones it first while `may_postpone` holds (`App.lean:1366-1367`). The oracle then falls straight through to "Function expected" (`:395-411`).

- [ ] **Step 5: Run the tests to verify they pass**

Run: `cargo test -p leanr_elab`
Expected: PASS, including every earlier record.

- [ ] **Step 6: Run the mutations**

- Delete the `try_postpone_if_mvar` call → the three `p2/app-fn-*` records and `an_application_of_an_mvar_typed_head_is_postponed` fail.
- Drop the guard (postpone unconditionally) → `an_application_with_no_arguments_does_not_postpone_on_its_head_type` fails. If it survives, `x` does not reach `elab_app_args`. Confirm by tracing `dispatch` → `app::elab_atom` → `head::elab_app_fn` for an `<ident>`, and swap the source to `fun x => @x`. If that survives as well, report it. Do not keep an undiscriminating test.

- [ ] **Step 7: Commit**

```bash
cargo fmt --all
git add crates/leanr_elab tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -m "M4b-4a P2: elabAppArgs postpones on an mvar-typed head"
```

---

### Task 5: Reconciliation, the landed record, and the spec amendment

**Files:**
- Modify: `crates/leanr_elab/src/lib.rs` (§ Recorded coverage gaps, the two postponement entries; the `:116` and `:135` mentions)
- Modify: `crates/leanr_elab/src/dispatch.rs:166` (deferral table)
- Modify: `crates/leanr_elab/src/app/mod.rs:67` (seam index)
- Modify: `crates/leanr_elab/src/synthetic/default_inst.rs:100-130` (doc)
- Modify: `crates/leanr_elab/src/synthetic/report.rs:520-538` (`Postponed` arm doc)
- Modify: `crates/leanr_elab/tests/seam_audit.rs:756-775` (needle)
- Modify: `docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md` (§ P2 amendment, § Landed › P2)

- [ ] **Step 1: Add the needle (failing)**

In `seam_audit.rs`'s `no_seam_message_names_a_completed_slice`, add `"M4b-4a P2"` to `needles` and update the assert message to "M4b-3 P3, P4, P5 and M4b-4a P1, P2 are complete". Run `cargo test -p leanr_elab --test seam_audit no_seam_message`. It should PASS already, since Tasks 2-4 removed every live P2 seam. If it fails, the offender list is the remaining work.

Then check the needle is not vacuous: temporarily add `let _ = "M4b-4a P2";` to any `src` function, see the test fail, and revert.

- [ ] **Step 2: Sweep every remaining mention**

Run: `grep -rn "M4b-4a P2\|no term-level postponement\|cannot postpone\|postpone_elab_term. has no\|leanr has no term-level" crates/leanr_elab/src crates/leanr_elab/tests`

Rewrite each hit so it says what is true now. Specifically:
- `lib.rs` § Recorded coverage gaps:
  - Replace the "`SyntheticMVarKind::Postponed` has no producer" entry with a short history. Its producers since M4b-4a P2 are `postpone_elab_term`, via `elab_using_elab_fns`'s catch and `useImplicitLambda`'s `.postpone` arm. The corpus covers resume through the `p2/*` records.
  - Replace the "`may_postpone` has exactly one production reader" entry the same way. Its readers are the `try_postpone` family and the `.postpone` arm. Rungs 2 and 4 are now behaviourally distinct from rung 1: `resuming_does_not_catch_its_own_postpone` and `p2/implicit-lambda-postpone` both depend on it.
  - Fix the `:116` and `:135` mentions to say closed.
- `dispatch.rs` deferral table: delete the "field notation on an mvar-typed term (postponement) … M4b-4a P2" row. Add "Reconciled a TENTH time by M4b-4a P2" to the paragraph above it.
- `app/mod.rs:67` seam index: delete the postponement row.
- `default_inst.rs:100-130`: the "`.postponed` justification is STILL speculative" paragraph. P2's producer went through `elab_using_elab_fns`, not this fixpoint. The rung-3 walk still skips every non-`.typeClass` kind, so the parameter's justification stays the ladder convention alone. Say that in one sentence and cut the speculation.
- `report.rs`'s `Postponed` arm: keep the error. Replace the doc with what is true now. The oracle's `| _ => unreachable!` (`SyntheticMVars.lean:316`) holds in leanr too:
  - `resume_postponed` either assigns the mvar, returns "not ready", or propagates an error.
  - At rung 4 (postponement off) no producer fires, so a postponed mvar can only still be pending when `check_occurs` failed.
  - That needs a synthetic `sorry` inside the result, and leanr mints none.
  - Cite `ladder.rs`'s `resume_postponed`.

- [ ] **Step 3: Amend the spec**

In `docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md`:
1. Under § P2, append a "**P2 amendments (found while planning, measured)**" list with the four items from this plan's § Spec deviations, one bullet each, with their citations.
2. Under § Landed, add `### P2 — term-level postponement (PR #<n>)`, bullets:
   - `ElabError::Postpone` (internal exception); `postpone.rs`; `elab_using_elab_fns` (catch with state and `lctx` restore); `resume_elab_term` / `resume_postponed` (catch off, restore on postpone and on `postponeOnError`).
   - Producers: `useImplicitLambda` `.postpone`, `resolveLValLoop`, and `elabAppArgs`. The last was missing from the spec; `(fun f => f Nat.zero) Nat.succ` had been a silent `FunctionExpected`.
   - `is_mvar_app` is exact (`whnf_r` is `pub`).
   - Corpus: the `p2/*` records (list the count). Rejections: `lval_smoke.rs`, `app_smoke.rs`. Mechanics: `postpone_smoke.rs`.
   - **Known cost:** `elab_using_elab_fns` clones the `Term.State` tables and mctx assignment maps on every caught elaboration, where the oracle's `saveState` is O(1). The owner is whichever slice first measures elaboration throughput. It is not a correctness seam.
   - The `.postpone` seam test in `seam_audit.rs` and P1's LVal postponement seam are closed. `tryPostponeIfNoneOrMVar` has no production caller until P4.

- [ ] **Step 4: Full CI, blocking**

Run: `mise run ci` in the foreground and wait for its exit status. Expected: exit 0. fmt, clippy (`-D warnings`) and the full suite are all green.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_elab docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md
git commit -m "M4b-4a P2: reconcile seams, ledgers and the landed record"
```
