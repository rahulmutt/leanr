# M4c-2b-ii — overloaded elaboration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Elaborate an identifier (or `.x`) with two or more `resolveGlobalName` candidates the way the oracle does: try each under `observing`, filter with `getSuccesses`, then return the one survivor, `Ambiguous term`, or `overloaded, errors`. Also port the plain-throw ambiguity errors whose text needs no delaborator.

**Architecture:** `TermElabM` gains `observing` / `apply_result` over the existing value snapshot (`SavedTermState`). `head::elab_app_fn` returns an `AppFn`: either `Done(e)` for one resolution, or `Candidates(results)` for two or more. `app/overload.rs` owns the selection (`get_successes`, `Ambiguous term`, `mergeFailures`). Non-oracle errors (seams) are never captured, so they stop the elaboration instead of counting as a candidate's failure.

**Tech Stack:** Rust (`crates/leanr_elab`), the Lean oracle `leanprover/lean4:v4.33.0-rc1` (dumpers under `tests/fixtures/elab/`), `mise` tasks.

**Spec:** `docs/superpowers/specs/2026-10-04-m4c2b-ii-overloaded-elab-design.md`. Its § Plan amendments section is written in Task 5. The amendments are listed under "Plan-time oracle facts" below.

## Global Constraints

- Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. Every citation below was opened against `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/Lean`.
- `leanr_meta/src` and the kernel stay untouched. `MetaSnapshot` is already `Clone` and `pub`, so nothing in `leanr_meta` is needed.
- Every committed corpus stays byte-identical, except for:
  - the appended `file-queries.jsonl` rows;
  - one appended `elim.jsonl` record (`instCoeListNatInt`, Task 2).
- `CORPUS_FLOOR` in `crates/leanr_elab/tests/oracle_file.rs` is raised per task: 122 after Task 2, 126 after Task 3, 131 after Task 4.
- **Stop rule:** if a corpus row fails for a reason that is not overloading (a coercion, default-instance or codegen gap, say), STOP and report it as a finding. Do not special-case the row or delete it.
- Build and test only under `/workspace` (never `/tmp`: a 20Gi EmptyDir).
- `mise run ci` gates on `cargo fmt --check` and clippy. Run it, blocking, before every commit that ends a task. Never background it and end the turn.
- After Task 5, no source or test text contains `M4c-2b-ii`.
- Oracle first lines are compared byte for byte: `overloaded, errors ` and `failed to open, errors ` each END WITH ONE SPACE.

## Plan-time oracle facts (all probed 2026-10-04)

Probe scratch is in `target/m4c2biiprobe/`. `elab0/` holds the appended `Elab0` and `elab0/file-final.jsonl` is the full expected `file-queries.jsonl`: 131 lines, whose first 89 are byte-identical to the committed file.

- **Candidate order:**
  - For an identifier, the overloaded fold sees `B` before `A`, given `open A B`. That shows in the `Ambiguous term` listing and the `mergeFailures` nesting, both after line 1.
  - `findMethod?`'s list is `` `A.S1.g`, `B.S1.g` `` (open order).
  - `resolveUniqueNamespace`'s list is `[B.X, A.X]`.
  - Only the last two reach a first line. Each is pinned by a row.
- **`mkConst` runs before the fold** (`resolveName'` → `mkConsts`).
  - `overload/explicitUniv` errors with ``too many explicit universe levels for `B.u` ``.
  - That is the RESOLVED name. leanr currently passes the source text (`u`), and `TooManyUniverseLevels` has no `oracle_first_line`. This is a latent bug, fixed in Task 2.
- **Nested namespaces never overload.** Inside `namespace A.B`, `h` resolves to `A.B.h` alone. The spec's `overload/nestedNs` rows are dropped.
- **`.x` overloads only when the root name is absent.** `resolveExact` wins otherwise, so the `.x` rows use two OPENED candidates.
- **`getSuccesses` stages have source-level discriminators:**
  - `overload/stage3`: without stage 3, the result is `Ambiguous term`.
  - `overload/delayedCoeStage2`: without stage 2, the result is `Ambiguous term`, because stage 3's defaulting resolves `A.g`'s delayed coercion (control: `overload/delayedCoeControl`). This row needs an `Elab0` append: `instance instCoeListNatInt : Coe (List Nat) Int`. leanr has no `instance` command.
  - The append is inert: rebuilt in scratch, every Elab0-reading dump is byte-identical except `elim.jsonl` (+1 record).
- **Rule 1 has a source-level discriminator.** In `def Nat.t : Nat := f .t`, the oracle answers `Ambiguous term`:
  - `B.f .t` reaches leanr's recursion seam;
  - `A.f .t` succeeds;
  - so a leanr that counted the seam as a failure would silently emit `A.f Bool.t`.
- **Counters stay monotonic.** `Core.SavedState.restore` (`CoreM.lean:407-410`) rewinds only `env`, `messages`, `infoState` and `snapshotTasks`, never the name generator or macro scopes. So `binder_name_gen` (like the mvar generators) is NOT part of `SavedTermState`.
- **`open`'s "ambiguous identifier" throws render `Expr` lists.**
  - `Open.lean:75`: `{result.map mkConst}`.
  - `ResolveName.lean:376`: `{cs.map mkConst}`.
  - Both go through the delaborator, so they become `— delab name rendering` seams, not ported errors. The spec's `AmbiguousOpenIdent` variant is dropped.
- **`failed to open` is portable.** `throwErrorWithNestedErrors "failed to open"` (`Open.lean:66`) has the same shape as `mergeFailures`, so its first line `failed to open, errors ` is ported as `FailedToOpen`.

## Review Focus

These input classes are the most likely to bite, and only the rows named below exercise them:
1. **An overload nested in an argument, or in a binder type.** `pick (f Nat.zero) …` picks `A.f`; `Eq c Nat.zero` is `Ambiguous term`. Rows `overload/nestedArg`, `overload/argExpected`, `overload/inType` (Task 2).
2. **Two overloads in one application** (`f c`): `Ambiguous term`. Row `overload/twoOverloads` (Task 2).
3. **An overload under `fun` against a known function type** picks by the binder's type. Row `overload/underFun` (Task 2).
4. **A seam inside one candidate** stops the command with that seam. Test `a_seam_in_one_candidate_stops_the_overload` (Task 2).
5. **A local binder that shadows an overloaded global** is a single local resolution, with no fan-out. Row `overload/localShadows` (Task 2).

---

### Task 1: `observing`, `apply_result`, and the two selection errors

**Files:**
- Modify: `crates/leanr_elab/src/synthetic/state.rs` (`SavedTermState` gets `#[derive(Clone)]`; add `TermElabResult`, `observing`, `apply_result`; add a `#[cfg(test)] mod tests`)
- Modify: `crates/leanr_elab/src/synthetic/mod.rs` (add `pub(crate) use state::{SavedTermState, TermElabResult};` beside the existing `pub use state::{…}`)
- Modify: `crates/leanr_elab/src/error.rs` (variants `AmbiguousTerm`, `Overloaded(Vec<ElabError>)`, with first lines and tests)

**Interfaces:**
- Produces:
  - `pub(crate) enum TermElabResult { Ok(ExprId, SavedTermState), Err(ElabError, SavedTermState) }`
  - `TermElabM::observing(&mut self, f: impl FnOnce(&mut Self) -> Result<ExprId, ElabError>) -> Result<TermElabResult, ElabError>`
  - `TermElabM::apply_result(&mut self, r: TermElabResult) -> Result<ExprId, ElabError>`
  - `ElabError::AmbiguousTerm`
  - `ElabError::Overloaded(Vec<ElabError>)`
  - `SavedTermState: Clone`

- [ ] **Step 1: Write the failing tests.** Append to `crates/leanr_elab/src/synthetic/state.rs`:

```rust
#[cfg(test)]
mod tests {
    use leanr_kernel::bank::terms::Node;
    use leanr_kernel::bank::Store;
    use leanr_kernel::{AxiomVal, ConstantInfo, ConstantVal, Environment};
    use leanr_meta::{Config, EnvExtensions, MetaCtx};

    use super::TermElabResult;
    use crate::elab::TermElabM;
    use crate::ElabError;

    /// One axiom `Foo : Prop` (the `app::head::tests::env_with_foo` shape).
    fn env_with_foo() -> Environment {
        let mut env = Environment::default();
        let prop = {
            let store = env.store_mut();
            let zero = store.level_zero(None).unwrap();
            store.expr_sort(None, zero).unwrap()
        };
        let foo = {
            let store = env.store_mut();
            let s = store.intern_str(None, "Foo").unwrap();
            store.name_str(None, None, s).unwrap()
        };
        env.admit_unchecked(ConstantInfo::Axiom(AxiomVal {
            val: ConstantVal { name: foo, level_params: vec![], ty: prop },
            is_unsafe: false,
        }))
        .unwrap();
        env
    }

    /// Runs `k` with a fresh elaborator, an unassigned mvar `?m : Prop`
    /// (its id) and the constant `Foo`.
    fn with_mvar(k: impl FnOnce(&mut TermElabM, leanr_meta::MVarId, leanr_kernel::bank::ExprId)) {
        let env = env_with_foo();
        let view = env.view();
        let mut scratch = Store::scratch();
        let mctx = MetaCtx::new(view, &mut scratch, Config::default(), EnvExtensions::default());
        let mut elab = TermElabM::new(mctx, view);
        let foo = crate::builtin::op::mk_const_named(&mut elab, "Foo").unwrap();
        let prop = elab.mctx.infer_type(foo).unwrap();
        let m = elab.mk_fresh_expr_mvar(prop).unwrap();
        let Node::MVar { id: Some(id) } = crate::app::lval::node(&elab, m) else {
            panic!("mk_fresh_expr_mvar returned a non-mvar")
        };
        k(&mut elab, id, foo);
    }

    /// oracle `observing` (`TermElabM.lean:574-580`): the candidate's state
    /// is captured, the state before it is restored; `applyResult`
    /// (`:592-596`) restores the captured state.
    #[test]
    fn observing_restores_before_and_apply_result_restores_after() {
        with_mvar(|elab, id, foo| {
            let r = elab
                .observing(|elab| {
                    elab.mctx.mctx_mut().assign(id, foo)?;
                    Ok(foo)
                })
                .unwrap();
            assert!(matches!(r, TermElabResult::Ok(..)));
            assert!(!elab.mctx.mctx().is_assigned(id), "before-state restored");
            assert_eq!(elab.apply_result(r).unwrap(), foo);
            assert!(elab.mctx.mctx().is_assigned(id), "after-state restored");
        });
    }

    /// `:582-585`: an oracle error is captured with its state; `applyResult`
    /// restores that state and rethrows.
    #[test]
    fn observing_captures_an_oracle_error_with_its_state() {
        with_mvar(|elab, id, foo| {
            let r = elab
                .observing(|elab| {
                    elab.mctx.mctx_mut().assign(id, foo)?;
                    Err(ElabError::UnknownIdent("x".into()))
                })
                .unwrap();
            assert!(matches!(r, TermElabResult::Err(ElabError::UnknownIdent(_), _)));
            assert!(!elab.mctx.mctx().is_assigned(id));
            assert!(matches!(elab.apply_result(r), Err(ElabError::UnknownIdent(_))));
            assert!(elab.mctx.mctx().is_assigned(id));
        });
    }

    /// `:586-590`: postponement restores the before-state and is rethrown.
    #[test]
    fn observing_rethrows_postpone_after_restoring() {
        with_mvar(|elab, id, foo| {
            let r = elab.observing(|elab| {
                elab.mctx.mctx_mut().assign(id, foo)?;
                Err(ElabError::Postpone)
            });
            assert!(matches!(r, Err(ElabError::Postpone)));
            assert!(!elab.mctx.mctx().is_assigned(id));
        });
    }

    /// Spec § Rule 1: a seam is never captured as a candidate's failure.
    #[test]
    fn observing_rethrows_a_seam() {
        with_mvar(|elab, _, _| {
            let r = elab.observing(|_| Err(ElabError::UnsupportedSyntax("x — later".into())));
            assert!(matches!(r, Err(ElabError::UnsupportedSyntax(_))));
        });
    }
}
```

In `error.rs`'s test module, next to `declaration_error_first_lines_are_the_oracles`, add:

```rust
    #[test]
    fn overload_first_lines_are_the_oracles() {
        // `App.lean:2217`: the term starts the next line (`indentD`).
        assert_eq!(ElabError::AmbiguousTerm.oracle_first_line().as_deref(), Some("Ambiguous term"));
        // `Util.lean:262-263` + `Message.lean:859-860`: the list is an
        // `indentD`, so line 1 ends with the space before it.
        assert_eq!(
            ElabError::Overloaded(vec![]).oracle_first_line().as_deref(),
            Some("overloaded, errors ")
        );
        assert!(ElabError::AmbiguousTerm.is_oracle_error());
        assert!(ElabError::Overloaded(vec![]).is_oracle_error());
    }
```

- [ ] **Step 2: Run them and confirm they fail to compile.**

Run: `cargo test -p leanr_elab --lib observing overload_first_lines 2>&1 | tail -20`
Expected: compile errors for `observing`, `apply_result`, `TermElabResult`, `AmbiguousTerm` and `Overloaded`. If `crate::builtin::op::mk_const_named` or `crate::app::lval::node` is not visible from `synthetic::state`, widen its visibility to `pub(crate)` (both are already crate-reachable today).

- [ ] **Step 3: Implement.** Make `SavedTermState` `#[derive(Clone)]`. Every field is already `Clone`, and `MetaSnapshot` derives `Clone` (`leanr_meta/src/metactx.rs:2063`). Then add to `state.rs`:

```rust
/// oracle: `TermElabResult` (`TermElabM.lean:565`,
/// `EStateM.Result Exception SavedState α`): a candidate's value or error
/// together with the state it left behind. Produced by
/// [`TermElabM::observing`]; consumed by [`TermElabM::apply_result`].
/// Only oracle errors are ever captured (see `observing`).
pub(crate) enum TermElabResult {
    Ok(ExprId, SavedTermState),
    Err(ElabError, SavedTermState),
}

impl<'e> TermElabM<'e> {
    /// oracle: `observing` (`TermElabM.lean:574-590`). Saves the state, runs
    /// `f`, captures the state `f` left, and restores the saved one.
    ///
    /// An ORACLE error is captured, as the oracle captures `.error`. Every
    /// other error is rethrown: `Postpone` after restoring
    /// (`postponeExceptionId`, `:587-589`), a seam (or `Meta`/`Internal`)
    /// as is. A seam stands for behaviour leanr does not model, so it
    /// cannot count as this candidate failing: the oracle might accept the
    /// candidate (spec § Rule 1). Rethrowing stops the whole overloaded
    /// elaboration at the first such error, in candidate order.
    ///
    /// The id generators are not part of [`SavedTermState`] and are never
    /// rewound, as the oracle's `Core.SavedState.restore` (`CoreM.lean:407-410`)
    /// rewinds neither `ngen` nor the macro scope.
    pub(crate) fn observing(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<ExprId, ElabError>,
    ) -> Result<TermElabResult, ElabError> {
        let before = self.save_term_state();
        match f(self) {
            Ok(e) => {
                let after = self.save_term_state();
                self.restore_term_state(before);
                Ok(TermElabResult::Ok(e, after))
            }
            Err(err) if err.is_oracle_error() => {
                let after = self.save_term_state();
                self.restore_term_state(before);
                Ok(TermElabResult::Err(err, after))
            }
            Err(ElabError::Postpone) => {
                self.restore_term_state(before);
                Err(ElabError::Postpone)
            }
            Err(err) => Err(err),
        }
    }

    /// oracle: `applyResult` (`TermElabM.lean:592-596`): restore the
    /// captured state, then return the value or rethrow the error.
    pub(crate) fn apply_result(&mut self, r: TermElabResult) -> Result<ExprId, ElabError> {
        match r {
            TermElabResult::Ok(e, s) => {
                self.restore_term_state(s);
                Ok(e)
            }
            TermElabResult::Err(err, s) => {
                self.restore_term_state(s);
                Err(err)
            }
        }
    }
}
```

In `error.rs`, add the variants beside `UnknownIdent`:

```rust
    /// oracle: `elabAppAux`'s `throwErrorAt f "Ambiguous term{indentD f}…"`
    /// (`App.lean:2217`): two or more overloaded candidates survived
    /// `getSuccesses`.
    AmbiguousTerm,
    /// oracle: `mergeFailures` (`App.lean:2190-2200`):
    /// `throwErrorWithNestedErrors "overloaded" exs`. Every candidate
    /// failed. The nested errors are kept in candidate order, for tests.
    Overloaded(Vec<ElabError>),
```

Add `oracle_first_line` arms:

```rust
            Self::AmbiguousTerm => Some("Ambiguous term".into()),
            Self::Overloaded(_) => Some("overloaded, errors ".into()),
```

`is_oracle_error` already returns `true` for every variant it doesn't list, so nothing changes there.

- [ ] **Step 4: Run the tests.**

Run: `cargo test -p leanr_elab --lib observing overload_first_lines`
Expected: 5 passed.

- [ ] **Step 5: Mutation check.** These tests guard primitives that later tasks depend on, so check them now. For each mutation, apply it, rerun Step 4, confirm the named test FAILS, then revert:
  - drop `self.restore_term_state(before)` from the `Ok` arm → `observing_restores_before_and_apply_result_restores_after`;
  - capture every error (remove the `if err.is_oracle_error()` guard) → `observing_rethrows_a_seam` and `observing_rethrows_postpone_after_restoring`;
  - in `apply_result`, skip `restore_term_state(s)` on `Ok` → `observing_restores_before_and_apply_result_restores_after`.

Record the three results in the commit message body.

- [ ] **Step 6: Gate and commit.**

```bash
mise run ci   # blocking; must end green
git add crates/leanr_elab/src/synthetic crates/leanr_elab/src/error.rs
git commit -m "leanr_elab: observing/applyResult and the overload selection errors (M4c-2b-ii)"
```

---

### Task 2: Overloaded identifiers: fan-out, `getSuccesses`, selection

**Files:**
- Modify: `tests/fixtures/elab/Elab0.lean` (append), then regenerate `Elab0.olean` and `elim.jsonl`
- Modify: `crates/leanr_elab/src/app/head.rs` (`AppFn`, `Resolution`, `elab_app_fn_resolutions`, rewrite `elab_app_fn_id`, `mk_const` without `display`)
- Modify: `crates/leanr_elab/src/app/overload.rs` (replace `expect_single` with `select` / `get_successes`)
- Modify: `crates/leanr_elab/src/app/mod.rs` (`elab_app_aux`)
- Modify: `crates/leanr_elab/src/resolve.rs` (delete `expect_one` and adjust its two tests)
- Modify: `crates/leanr_elab/src/builtin/op/mod.rs` (`resolve_id`'s ≥2 seam relabel; `mk_const` call sites)
- Modify: the other `mk_const` callers: `app/dot_ident.rs:186`, `builtin/anon_ctor.rs:165`, `app/lval.rs:850`, `app/lval.rs:908`, `app/mod.rs:195`
- Modify: `crates/leanr_elab/src/error.rs` (`TooManyUniverseLevels` first line)
- Modify: `tests/fixtures/elab/dump_decls.lean` (33 rows) → `tests/fixtures/elab/file-queries.jsonl`
- Modify: `crates/leanr_elab/tests/oracle_file.rs` (`CORPUS_FLOOR = 122`), `crates/leanr_elab/tests/scopes.rs`

**Interfaces:**
- Consumes (Task 1): `TermElabResult`, `observing`, `apply_result`, `ElabError::{AmbiguousTerm, Overloaded}`.
- Produces:
  - `pub(crate) enum AppFn { Done(ExprId), Candidates(Vec<TermElabResult>) }`
  - `pub(crate) struct Resolution { pub f: ExprId, pub fields: Vec<LVal> }`
  - `pub(crate) fn elab_app_fn_resolutions(elab, fns: Vec<Resolution>, lvals: Vec<LVal>, call: AppCall, kinds: &KindInterner) -> Result<AppFn, ElabError>`
  - `pub(crate) fn elab_app_fn(...) -> Result<AppFn, ElabError>` (was `pub fn … -> Result<Vec<ExprId>, _>`)
  - `pub(crate) fn mk_const(elab, cname: NameId, explicit_levels: &[LevelId]) -> Result<ExprId, ElabError>` (no `display`)
  - `overload::select(elab, cands: Vec<TermElabResult>, kinds) -> Result<ExprId, ElabError>`
  - `AppCall: Clone`

- [ ] **Step 1: Append to `Elab0`** at the end of `tests/fixtures/elab/Elab0.lean`:

```lean

-- M4c-2b-ii: a coercion whose source carries a type argument, so an
-- overloaded candidate of type `List ?a` against `Int` leaves a DELAYED
-- coercion that default instances later resolve (`getSuccesses` stage 2,
-- spec `docs/superpowers/specs/2026-10-04-m4c2b-ii-overloaded-elab-design.md`).
-- Appended last, so no earlier constant changes.
instance instCoeListNatInt : Coe (List Nat) Int := ⟨fun _ => Int.ofNat Nat.zero⟩
```

Then rebuild:

```bash
cd tests/fixtures/elab && lean Elab0.lean -o Elab0.olean && cd -
mise run fixtures:regen-elab
mise run fixtures:regen-decls
git status --short tests/fixtures
```

Expected: exactly `Elab0.lean`, `Elab0.olean` and `elim.jsonl` are modified. `git diff tests/fixtures/elab/elim.jsonl | grep -c '^+{'` prints 1, and that record names `instCoeListNatInt`. `fixtures:regen-elab` prints `dump_elab: elaboration failed for p5/propagate-short: internal exception #3` on stderr; that line is pre-existing. If ANY other committed fixture changed, STOP and report it.

Then run `cargo test -p leanr_elab -p leanr_meta` and expect it green (the append is inert).

- [ ] **Step 2: Add the corpus rows.** In `tests/fixtures/elab/dump_decls.lean`'s `fileQueries`:
  - add a comma after the last row, `("err/inScoped", …)`;
  - append these 33 rows, then the closing `]` (the last row has no trailing comma).

```lean
  ("overload/argType", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := f Nat.zero"),
  ("overload/argBool", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := f Bool.true"),
  ("overload/argNumeral", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := f 0"),
  ("overload/expectedType", "namespace A\ndef c : Nat := Nat.zero\nend A\nnamespace B\ndef c : Bool := Bool.true\nend B\nopen A B\ndef t : Bool := c"),
  ("overload/coe", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t : Int := f Nat.zero"),
  ("overload/coeBoth", "namespace A\ndef g : Nat := Nat.zero\nend A\nnamespace B\ndef g : Int := Int.ofNat Nat.zero\nend B\nopen A B\ndef t : Int := g"),
  ("overload/ambiguous", "namespace A\ndef g : Nat := Nat.zero\nend A\nnamespace B\ndef g : Nat := pick Nat.zero Nat.zero\nend B\nopen A B\ndef t : Nat := g"),
  ("overload/ambiguousNoType", "namespace A\ndef g : Nat := Nat.zero\nend A\nnamespace B\ndef g : Nat := pick Nat.zero Nat.zero\nend B\nopen A B\ndef t := g"),
  ("overload/binderNames", "namespace A\ndef k (n : Nat) : Nat := n\nend A\nnamespace B\ndef k (b : Bool) : Bool := b\nend B\nopen A B\ndef t := fun y => k y"),
  ("overload/allFail", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := f Unit.unit"),
  ("overload/binder", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t (x : Nat) := f x"),
  ("overload/binderBool", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t (x : Bool) := f x"),
  ("overload/localShadows", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t (f : Nat) := f"),
  ("overload/fields", "def Nat.dbl (n : Nat) : Nat := n\nnamespace A\ndef n : Nat := Nat.zero\nend A\nnamespace B\ndef n : Bool := Bool.true\nend B\nopen A B\ndef t := n.dbl"),
  ("overload/lvals", "def Nat.dbl (n : Nat) : Nat := n\nnamespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := (f Nat.zero).dbl"),
  ("overload/pipeLvals", "def Nat.dbl (n : Nat) : Nat := n\nnamespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := f Nat.zero |>.dbl"),
  ("overload/explicitAt", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := @f Nat.zero"),
  ("overload/namedArg", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := f (n := Nat.zero)"),
  ("overload/explicitUniv", "namespace A\ndef u.{w} (a : Sort w) : Sort w := a\nend A\nnamespace B\ndef u (b : Bool) : Bool := b\nend B\nopen A B\ndef t := u.{1} Nat"),
  ("overload/delayedCoeStuck", "namespace A\ndef g {a : Type} : List a := List.nil\nend A\nnamespace B\ndef g : Int := Int.ofNat Nat.zero\nend B\nopen A B\ndef t : Int := g"),
  ("overload/delayedCoeArg", "namespace A\ndef g {a : Type} (x : a) : List a := List.nil\nend A\nnamespace B\ndef g (n : Nat) : Int := Int.ofNat n\nend B\nopen A B\ndef t (x : Nat) : Int := g x"),
  ("overload/delayedCoeStage2", "namespace A\ndef g {a : Type} [Dflt a] : List a := List.nil\nend A\nnamespace B\ndef g : Int := Int.ofNat Nat.zero\nend B\nopen A B\ndef t : Int := g"),
  ("overload/delayedCoeControl", "namespace A\ndef g {a : Type} [Dflt a] : List a := List.nil\nend A\ndef t : Int := A.g"),
  ("overload/stage3", "namespace A\ndef h {a : Type} [NoInst a] : Nat := Nat.zero\nend A\nnamespace B\ndef h : Nat := Nat.zero\nend B\nopen A B\ndef t : Nat := h"),
  ("overload/stage3Default", "namespace A\ndef h {a : Type} [Dflt a] : Nat := Nat.zero\nend A\nnamespace B\ndef h : Nat := Nat.zero\nend B\nopen A B\ndef t : Nat := h"),
  ("overload/pendingInst", "namespace A\ndef w {a : Type} [Wrap a] (x : a) : a := x\nend A\nnamespace B\ndef w {a : Type} [NoInst a] (x : a) : a := x\nend B\nopen A B\ndef t := w Nat.zero"),
  ("overload/rootAndOpen", "def shown : Nat := Nat.zero\nopen Scope0\ndef f : Nat := shown"),
  ("overload/exportAlias", "def Scope0.ex : Nat := Nat.zero\nopen Scope0\ndef f : Nat := ex"),
  ("overload/nestedArg", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := pick (f Nat.zero) Nat.zero"),
  ("overload/argExpected", "namespace A\ndef c : Nat := Nat.zero\nend A\nnamespace B\ndef c : Bool := Bool.true\nend B\nopen A B\ndef t := pick c Nat.zero"),
  ("overload/underFun", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t : Nat → Nat := fun x => f x"),
  ("overload/inType", "namespace A\ndef c : Nat := Nat.zero\nend A\nnamespace B\ndef c : Bool := Bool.true\nend B\nopen A B\ndef t (h : Eq c Nat.zero) : Nat := Nat.zero"),
  ("overload/twoOverloads", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\nnamespace A\ndef c : Nat := Nat.zero\nend A\nnamespace B\ndef c : Bool := Bool.true\nend B\nopen A B\ndef t := f c")
```

Regenerate with `mise run fixtures:regen-decls` and check it:
- `wc -l tests/fixtures/elab/file-queries.jsonl` prints 122;
- `head -122 target/m4c2biiprobe/elab0/file-final.jsonl | cmp - tests/fixtures/elab/file-queries.jsonl` succeeds (when the scratch file exists);
- `git diff tests/fixtures/elab/decl-queries.jsonl` is empty.

Expected oracle outcomes (the last command of each row):

| Row | Oracle |
|---|---|
| `argType`, `explicitAt`, `namedArg` | `t := A.f Nat.zero` |
| `argBool` | `t := B.f Bool.true` |
| `argNumeral` | `t := A.f (OfNat.ofNat Nat 0 (instOfNatNat 0))` |
| `expectedType` | `t := B.c` |
| `coe` | `t := Int.ofNat (A.f Nat.zero)` |
| `coeBoth`, `ambiguous`, `ambiguousNoType`, `binderNames`, `delayedCoeArg`, `stage3Default`, `rootAndOpen`, `exportAlias`, `inType`, `twoOverloads` | `Ambiguous term` |
| `allFail` | `overloaded, errors ` |
| `binder` / `binderBool` / `underFun` | `fun x => A.f x` / `fun x => B.f x` / `fun x => A.f x` |
| `localShadows` | `fun f => f` |
| `fields` | `Nat.dbl A.n` |
| `lvals`, `pipeLvals` | `Nat.dbl (A.f Nat.zero)` |
| `explicitUniv` | ``too many explicit universe levels for `B.u` `` |
| `delayedCoeStuck`, `delayedCoeStage2` | `t := B.g` |
| `delayedCoeControl` | `t := Int.ofNat Nat.zero` |
| `stage3` | `t := B.h` |
| `pendingInst` | `t := A.w Nat instWrapNat Nat.zero` |
| `nestedArg` / `argExpected` | `pick (A.f Nat.zero) Nat.zero` / `pick A.c Nat.zero` |

Raise `CORPUS_FLOOR` to 122 in `crates/leanr_elab/tests/oracle_file.rs`.

- [ ] **Step 3: Update `scopes.rs`, and add the Rule 1 test.** Replace `ambiguous_identifiers_seam_end_to_end` with:

```rust
/// M4c-2b-ii: two or more candidates are elaborated, not seamed. All three
/// are oracle-probed `Ambiguous term` (rows `overload/rootAndOpen`,
/// `overload/exportAlias`; `A.k`/`B.k`).
#[test]
fn ambiguous_identifiers_are_ambiguous_terms() {
    for src in [
        "def shown : Nat := Nat.zero\nopen Scope0\ndef f : Nat := shown",
        "def Scope0.ex : Nat := Nat.zero\nopen Scope0\ndef f : Nat := ex",
        "namespace A\ndef k : Nat := Nat.zero\nend A\nnamespace B\ndef k : Nat := Nat.zero\nend B\nopen A B\ndef f : Nat := k",
    ] {
        let (_, stop) = run(src);
        assert_eq!(stop.expect("stops").1, "Ambiguous term", "{src:?}");
    }
}

/// Spec § Rule 1 (plan Review Focus 4). `B.f .t` reaches the recursion
/// seam (`.t` against `Nat` is the declaration's own aux local, M4c-2b-i);
/// `A.f .t` succeeds with `Bool.t`. The oracle reports `Ambiguous term`
/// (plan-time probe), so selecting `A.f` would be a silent wrong Ok.
#[test]
fn a_seam_in_one_candidate_stops_the_overload() {
    let src = "def Bool.t : Bool := Bool.true\nnamespace A\ndef f (b : Bool) : Nat := Nat.zero\nend A\nnamespace B\ndef f (n : Nat) : Nat := n\nend B\nopen A B\ndef Nat.t : Nat := f .t";
    let (_, stop) = run(src);
    let (at, m) = stop.expect("stops");
    assert_eq!(at, 8, "{m}");
    assert!(m.starts_with("SEAM ") && m.contains("recursive reference to"), "{m}");
}
```

- [ ] **Step 4: Run the gates and confirm they fail.**

Run: `cargo test -p leanr_elab --test oracle_file --test scopes 2>&1 | tail -40`
Expected: `oracle_file_gate` lists divergences for the new rows (leanr stops with `… — M4c-2b-ii` seams), and both new `scopes.rs` tests fail.

- [ ] **Step 5: `mk_const` renders the resolved name.** In `app/head.rs`:
  - drop the `display` parameter;
  - build the error from `cname`, as the oracle's ``too many explicit universe levels for `{constName}` `` does (`TermElabM.lean:2131`);
  - fix every caller listed under Files by deleting its last argument;
  - delete any `display`/`name` local that is now unused.

```rust
/// oracle: `mkConst` (`TermElabM.lean:2127-2135`).
///
/// An undeclared `cname` is `UnknownConstant` (the full name), as the
/// oracle's `getConstInfo` throws. `resolve_global_name` can return one:
/// alias targets and an explicit `open`'s declaration are not checked
/// against the environment (`ResolveName.lean:85-92`, `:175-176`).
pub(crate) fn mk_const(
    elab: &mut TermElabM,
    cname: NameId,
    explicit_levels: &[LevelId],
) -> Result<ExprId, ElabError> {
    let render = |elab: &TermElabM| {
        crate::names::render(elab.mctx.store(), Some(elab.view.store), Some(cname))
    };
    let Some(info) = elab.view.get(cname) else {
        return Err(ElabError::UnknownConstant(render(elab)));
    };
    let n_params = info.constant_val().level_params.len();
    // oracle: `mkConst` errors when the user wrote MORE explicit levels
    // than the constant has parameters (the RESOLVED name: row
    // `overload/explicitUniv`), rather than truncating.
    if explicit_levels.len() > n_params {
        return Err(ElabError::TooManyUniverseLevels(render(elab)));
    }
    // … the rest of the body is unchanged …
}
```

In `error.rs`, give it a first line:

```rust
            Self::TooManyUniverseLevels(n) => {
                Some(format!("too many explicit universe levels for `{n}`"))
            }
```

Also add an assertion to `overload_first_lines_are_the_oracles`:

```rust
        assert_eq!(
            ElabError::TooManyUniverseLevels("B.u".into()).oracle_first_line().as_deref(),
            Some("too many explicit universe levels for `B.u`") // overload/explicitUniv
        );
```

- [ ] **Step 6: Fan out in `head.rs`.** Add `#[derive(Clone)]` to `AppCall` in `app/mod.rs`; `Arg`, `NamedArg` and `SynElem` are already `Clone`. Then, in `head.rs`:

```rust
/// What `elabAppFn` (`App.lean:2059-2138`) produced.
///
/// The oracle always returns a `TermElabResult` array and `elabAppAux`
/// `applyResult`s a lone candidate (`:2204-2206`). leanr returns one
/// resolution as `Done` and never brackets it: with a single candidate,
/// observing and then applying is the identity. It also skips a state
/// snapshot on every application.
pub(crate) enum AppFn {
    Done(ExprId),
    /// Two or more resolutions, each under `observing`.
    /// `app::overload::select` picks.
    Candidates(Vec<TermElabResult>),
}

/// One entry of `resolveName'`'s output (`TermElabM.lean:2201-2208`): the
/// head, plus the `LVal`s its split-off field components become.
pub(crate) struct Resolution {
    pub f: ExprId,
    pub fields: Vec<LVal>,
}

/// oracle: `elabAppFnResolutions` (`App.lean:1925-1950`). With more than
/// one resolution the application is `overloaded` (`:1930`): each
/// resolution is elaborated under `observing`, and its result must have
/// the expected type (`ensureHasType`, `:1943`), since the expected type
/// is what tells the candidates apart (row `overload/expectedType`).
///
/// The oracle's incoming `overloaded` flag is only ever `true` under a
/// `choice` node (`:2062-2065`), which is out of scope (`head.rs`'s
/// `choice` arm). So here `overloaded` is exactly `fns.len() > 1`.
/// `errToSorry := false` (`:1932`) is leanr's only mode: it stops at
/// the first error.
pub(crate) fn elab_app_fn_resolutions(
    elab: &mut TermElabM,
    fns: Vec<Resolution>,
    lvals: Vec<LVal>,
    call: AppCall,
    kinds: &KindInterner,
) -> Result<AppFn, ElabError> {
    if fns.len() == 1 {
        let Resolution { f, mut fields } = fns.into_iter().next().expect("len == 1");
        fields.extend(lvals);
        return Ok(AppFn::Done(crate::app::lval::elab_app_lvals(
            elab, f, fields, call, kinds,
        )?));
    }
    let mut out = Vec::with_capacity(fns.len());
    for Resolution { f, mut fields } in fns {
        fields.extend(lvals.iter().cloned());
        let call = call.clone();
        out.push(elab.observing(|elab| {
            let (stx, expected) = (call.stx.clone(), call.expected);
            let e = crate::app::lval::elab_app_lvals(elab, f, fields, call, kinds)?;
            elab.ensure_has_type(&stx, expected, e)
        })?);
    }
    Ok(AppFn::Candidates(out))
}
```

Rewrite `elab_app_fn_id` so it builds the resolutions and delegates. Keep its existing doc comment, and add a paragraph on `mkConsts`:

```rust
fn elab_app_fn_id(
    elab: &mut TermElabM,
    elem: &SynElem,
    raw: &str,
    explicit_levels: &[LevelId],
    lvals: Vec<LVal>,
    call: AppCall,
    kinds: &KindInterner,
) -> Result<AppFn, ElabError> {
    let (comps, prefixes) = ident_prefixes(elab, raw)?;
    let parts: Vec<&str> = comps.iter().map(String::as_str).collect();
    // `resolveName`: every local prefix before any global (`:2180-2181`).
    // (Keep the existing M4b-2 comment on locals shadowing globals here.)
    let fns = if let Some((fvar, n_fields)) = resolve_local_name(elab, &prefixes)? {
        // `processLocal` (`:2172-2179`).
        if n_fields == 0 && !explicit_levels.is_empty() {
            return Err(ElabError::InvalidExplicitUniversesForLocal(fvar));
        }
        let fields = field_name_lvals(elem, &parts, n_fields, explicit_levels);
        vec![Resolution { f: fvar, fields }]
    } else {
        let cands = elab.resolve_global(&prefixes)?;
        if cands.is_empty() {
            // `elabAppFnId`'s `throwUnknownIdWithSuggestions` (`App.lean:1956`).
            return Err(ElabError::UnknownIdent(raw.to_string()));
        }
        // `mkConsts` (`:2145-2158`) builds EVERY candidate's constant before
        // `elabAppFnResolutions` tries any. Its fresh level mvars live
        // outside the `observing` brackets, and a `mkConst` error is thrown
        // before any candidate runs (row `overload/explicitUniv`). With
        // fields, the explicit levels belong to the last field and the
        // constant gets fresh ones.
        let mut fns = Vec::with_capacity(cands.len());
        for (cname, n_fields) in cands {
            let (const_levels, proj_levels): (&[LevelId], &[LevelId]) = if n_fields == 0 {
                (explicit_levels, &[])
            } else {
                (&[], explicit_levels)
            };
            let f = mk_const(elab, cname, const_levels)?;
            let fields = field_name_lvals(elem, &parts, n_fields, proj_levels);
            fns.push(Resolution { f, fields });
        }
        fns
    };
    elab_app_fn_resolutions(elab, fns, lvals, call, kinds)
}

/// `elabAppFnResolutions`' field `LVal`s (`App.lean:1933-1938`): the last
/// `n_fields` components of the identifier. `levels` go to the last one,
/// and the first carries the composite `suffix?`.
fn field_name_lvals(elem: &SynElem, parts: &[&str], n_fields: usize, levels: &[LevelId]) -> Vec<LVal> {
    let fields = &parts[parts.len() - n_fields..];
    let suffix = (!fields.is_empty()).then(|| fields.join("."));
    fields
        .iter()
        .enumerate()
        .map(|(i, c)| LVal::FieldName {
            r#ref: elem.clone(),
            name: (*c).to_string(),
            levels: if i + 1 == n_fields { levels.to_vec() } else { Vec::new() },
            suffix: if i == 0 { suffix.clone() } else { None },
        })
        .collect()
}
```

This replaces the old body from `let (f, n_fields, proj_levels) = …` through its final `elab_app_lvals` call. Check that the old `display`/`proj_levels` handling for a LOCAL hit (which passed `explicit_levels` as the projection levels) is preserved: `field_name_lvals(…, explicit_levels)` above.

Then update `elab_app_fn`:
- its return type becomes `Result<AppFn, ElabError>` and it is `pub(crate)`;
- the `<ident>` arm returns `elab_app_fn_id(…)` directly;
- the `dotIdent` arm wraps its single result: `Ok(AppFn::Done(crate::app::lval::elab_app_lvals(…)?))` (Task 3 fans it out);
- `elab_app_fn_generic` returns `Ok(AppFn::Done(…))` in both branches;
- the recursive arms already return the recursive call.

The two in-file tests (`head.rs` around `:712` and `:764`) match on `Err(…)` and need no change unless the compiler disagrees.

- [ ] **Step 7: Selection in `overload.rs`.** Replace the file's contents with:

```rust
//! Overloaded elaboration's selection. Oracle: `elabAppAux`
//! (`App.lean:2202-2217`) after `elabAppFn` returned two or more
//! results: `getSuccesses` (`:2140-2185`), then the single survivor
//! (`applyResult`), `Ambiguous term` (`:2217`), or `mergeFailures`
//! (`:2190-2200`).
//!
//! Every captured error is an oracle error. `TermElabM::observing`
//! rethrows seams and other non-oracle errors instead of capturing them,
//! because leanr cannot know whether the oracle accepts that candidate
//! (spec § Rule 1). The `catch _` inside stages 2 and 3 follows the same
//! rule.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;

use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::synthetic::{PostponeBehavior, SyntheticMVarKind, TermElabResult};

/// `elabAppAux`'s multi-candidate arm (`App.lean:2207-2217`).
pub(crate) fn select(
    elab: &mut TermElabM,
    cands: Vec<TermElabResult>,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let ok = get_successes(elab, &cands, kinds)?;
    match ok.as_slice() {
        [i] => {
            let r = cands.into_iter().nth(*i).expect("an index get_successes returned");
            elab.apply_result(r)
        }
        // `mergeFailures`: no success at all means every candidate failed.
        [] => Err(ElabError::Overloaded(
            cands
                .into_iter()
                .map(|r| match r {
                    TermElabResult::Err(e, _) => e,
                    TermElabResult::Ok(..) => unreachable!("getSuccesses keeps every Ok in r₁"),
                })
                .collect(),
        )),
        _ => Err(ElabError::AmbiguousTerm),
    }
}

/// oracle: `getSuccesses` (`App.lean:2141-2185`), returning indices into
/// `cands`. Stages 2 and 3 each restore a success's state and synthesize.
/// Like the oracle, this leaves the elaborator in the last state it
/// restored; `select` either `apply_result`s the winner or throws.
fn get_successes(
    elab: &mut TermElabM,
    cands: &[TermElabResult],
    kinds: &KindInterner,
) -> Result<Vec<usize>, ElabError> {
    let oks: Vec<(usize, ExprId, &crate::synthetic::SavedTermState)> = cands
        .iter()
        .enumerate()
        .filter_map(|(i, r)| match r {
            TermElabResult::Ok(e, s) => Some((i, *e, s)),
            TermElabResult::Err(..) => None,
        })
        .collect();
    let r1: Vec<usize> = oks.iter().map(|&(i, _, _)| i).collect();
    if r1.len() <= 1 {
        return Ok(r1);
    }
    // Stage 2 (`:2145-2165`): drop a result that is still a delayed
    // coercion after `synthesizeSyntheticMVars` (default `postpone := .yes`).
    let mut r2 = Vec::new();
    for &(i, e, s) in &oks {
        if matches!(crate::app::lval::node(elab, e), Node::MVar { .. }) {
            elab.restore_term_state(s.clone());
            match elab.synthesize_synthetic_mvars(PostponeBehavior::Yes, kinds) {
                Ok(()) => {}
                // `catch _ => return false` (`:2161-2163`), oracle errors only.
                Err(err) if err.is_oracle_error() => continue,
                Err(err) => return Err(err),
            }
            let e = elab.mctx.instantiate_mvars(e)?;
            if let Node::MVar { id: Some(m) } = crate::app::lval::node(elab, e) {
                if matches!(
                    elab.synthetic_mvar_decl(m).map(|d| &d.kind),
                    Some(SyntheticMVarKind::Coe { .. })
                ) {
                    continue;
                }
            }
        }
        r2.push(i);
    }
    if r2.is_empty() {
        return Ok(r1);
    }
    if r2.len() == 1 {
        return Ok(r2);
    }
    // Stage 3 (`:2172-2185`): over ALL successes again (`candidates.filterM`,
    // not `r₂`), keep those whose pending work synthesizes with
    // `postpone := .no`.
    let mut r3 = Vec::new();
    for &(i, _, s) in &oks {
        elab.restore_term_state(s.clone());
        match elab.synthesize_synthetic_mvars(PostponeBehavior::No, kinds) {
            Ok(()) => r3.push(i),
            Err(err) if err.is_oracle_error() => {}
            Err(err) => return Err(err),
        }
    }
    Ok(if r3.is_empty() { r1 } else { r3 })
}
```

`SyntheticMVarKind` is already re-exported from `crate::synthetic`; `SavedTermState` and `TermElabResult` are re-exported by Task 1. If `synthetic_mvar_decl`'s field is not `kind`, read `SyntheticMVarDecl` (`synthetic/state.rs:36`) and adjust.

In `app/mod.rs`, `elab_app_aux` ends:

```rust
    match head::elab_app_fn(elab, &head, kinds, &explicit_levels, Vec::new(), call)? {
        head::AppFn::Done(e) => Ok(e),
        head::AppFn::Candidates(cands) => overload::select(elab, cands, kinds),
    }
```

Also update `elab_app_aux`'s doc to name the overload selection rather than the `choice` seam.

- [ ] **Step 8: Retire `expect_one`.** Delete `resolve::expect_one` (`resolve.rs:355-370`). In `resolve.rs`'s tests:
  - `unknown_ident_when_not_declared` keeps `assert!(cands.is_empty());` and drops the `expect_one` match. Its doc becomes "An undeclared name has no candidates (`elab_app_fn_id` turns that into `UnknownIdent`)".
  - `two_candidates_are_returned_and_expect_one_seams` is renamed `two_candidates_are_returned`. It keeps only the `assert_eq!(cands.len(), 2, …)` line, after the resolve call.
  - Remove `expect_one` from the test module's `use super::{…}`.

In `builtin/op/mod.rs`'s `resolve_id`, replace the `expect_one` line with:

```rust
    let cname = match fs.as_slice() {
        [(c, _)] => *c,
        // oracle: `resolveId?`'s throw (`TermElabM.lean:2223`) renders the
        // candidates as a `List Expr` through the delaborator.
        _ => {
            return Err(ElabError::UnsupportedSyntax(format!(
                "ambiguous term `{raw}` ({} candidates; `resolveId?`'s message renders a \
                 `List Expr`) — delab name rendering",
                fs.len()
            )))
        }
    };
    Ok(Some(crate::app::head::mk_const(elab, cname, &[])?))
```

Update that function's doc, which mentions `expect_one`'s M4c-2b-ii text, to say "leanr seams it (`— delab name rendering`)".

- [ ] **Step 9: Run the gates.**

Run: `cargo test -p leanr_elab 2>&1 | tail -40`
Expected: all green, including `oracle_file_gate` (122 checked) and the two new `scopes.rs` tests. If a row diverges, compare it with the table in Step 2. Apply the Global Constraints stop rule to any non-overload cause.

- [ ] **Step 10: Mutation check.** For each mutation, apply it, run `cargo test -p leanr_elab --test oracle_file --test scopes`, confirm the named row or test FAILS, then revert. Record every result, including any surprise, in the commit body.
  1. Remove the `ensure_has_type` call in `elab_app_fn_resolutions` (return `e`) → `overload/expectedType`, `overload/coe`.
  2. In `observing`, capture every error (drop the `is_oracle_error()` guard) → `a_seam_in_one_candidate_stops_the_overload`.
  3. Skip stage 2 (start with `let r2 = r1.clone();`) → `overload/delayedCoeStage2`.
  4. Skip stage 3 (return `r2` after stage 2) → `overload/stage3`.
  5. Build each constant lazily inside the `observing` closure instead of up front → `overload/explicitUniv`.
  6. `TooManyUniverseLevels` from the source text again → `overload/explicitUniv`.
  7. Do not restore the before-state in `observing`'s `Ok` arm → `overload/binderNames`. If that row does not catch it, record it: Task 1's unit test pins this mutation.

- [ ] **Step 11: Gate and commit.**

```bash
mise run ci   # blocking; must end green
git add tests/fixtures/elab crates/leanr_elab
git commit -m "leanr_elab: overloaded identifiers — observing fan-out, getSuccesses, Ambiguous term / mergeFailures (M4c-2b-ii)"
```

---

### Task 3: `.x` with several candidates

**Files:**
- Modify: `crates/leanr_elab/src/app/dot_ident.rs` (`resolve_dotted_ident_fn`, `go` and `resolve_against` return `Vec<ExprId>`; module doc)
- Modify: `crates/leanr_elab/src/app/head.rs` (`dotIdent` arm → `elab_app_fn_resolutions`)
- Modify: `tests/fixtures/elab/dump_decls.lean` (4 rows), `file-queries.jsonl`, `oracle_file.rs` (`CORPUS_FLOOR = 126`), `crates/leanr_elab/tests/scopes.rs`

**Interfaces:**
- Consumes (Task 2): `Resolution`, `elab_app_fn_resolutions`, `AppFn`, `mk_const(elab, cname, levels)`.
- Produces: `resolve_dotted_ident_fn(elab, raw, explicit_levels, expected) -> Result<Vec<ExprId>, ElabError>` (non-empty).

- [ ] **Step 1: Add the rows** after Task 2's last row (put a comma after it):

```lean
  ("overload/dotIdentPick", "namespace A\ndef Nat.two : Nat := Nat.zero\nend A\nnamespace B\ndef Nat.two (b : Bool) : Nat := Nat.zero\nend B\nopen A B\ndef t : Nat := .two"),
  ("overload/dotIdentArgs", "namespace A\ndef Nat.two : Nat := Nat.zero\nend A\nnamespace B\ndef Nat.two (b : Bool) : Nat := Nat.zero\nend B\nopen A B\ndef t : Nat := .two Bool.true"),
  ("overload/dotIdentAmbig", "namespace A\ndef Nat.two : Nat := Nat.zero\nend A\nnamespace B\ndef Nat.two : Nat := pick Nat.zero Nat.zero\nend B\nopen A B\ndef t : Nat := .two"),
  ("overload/dotIdentAllFail", "namespace A\ndef Nat.two : Nat := Nat.zero\nend A\nnamespace B\ndef Nat.two (b : Bool) : Nat := Nat.zero\nend B\nopen A B\ndef t : Nat := .two Unit.unit")
```

The oracle gives, in order:
- `t := A.Nat.two`;
- `t := B.Nat.two Bool.true`;
- `Ambiguous term`;
- `overloaded, errors `.

Regenerate with `mise run fixtures:regen-decls`. Then check that `wc -l` prints 126 and `head -126 target/m4c2biiprobe/elab0/file-final.jsonl | cmp - tests/fixtures/elab/file-queries.jsonl` succeeds. Set `CORPUS_FLOOR = 126`.

In `scopes.rs`, the two-opened-candidates loop (the one with `Foo.S1.g`/`Bar.S1.g` and `Foo.Nat.two`/`Bar.Nat.two`) becomes two separate assertions. Task 3 owns the `.two` source:

```rust
    // Two opened `.two` candidates: oracle `Ambiguous term` (probed).
    let (_, stop) = run("def Foo.Nat.two : Nat := Nat.zero\ndef Bar.Nat.two : Nat := Nat.zero\nopen Foo Bar\ndef x : Nat := .two");
    assert_eq!(stop.expect("stops"), (3, "Ambiguous term".to_string()));
```

Leave the `S1.g` source in its old seam assertion, with a `// Task 4` comment; Task 4 replaces it.

- [ ] **Step 2: Run and confirm the failure.**

Run: `cargo test -p leanr_elab --test oracle_file --test scopes 2>&1 | tail -20`
Expected: the four `dotIdent*` rows and the `.two` assertion fail on the `overloaded identifier `.two` … — M4c-2b-ii` seam.

- [ ] **Step 3: Implement.** In `dot_ident.rs`:
  - `resolve_dotted_ident_fn`, `go` and `resolve_against` return `Result<Vec<ExprId>, ElabError>`;
  - `go`'s `Ok(e) => Ok(e)` passes the vector through;
  - the local and unknown arms wrap their single result in `vec![…]`.

Replace the candidate match in `resolve_against` with:

```rust
            // `resolveGlobalName Name.anonymous (← getOpenDecls) fullName
            // |>.filter (·.2.isEmpty)` (`:2029-2031`), then `mkConst` each
            // (`:2032-2033`). Every candidate is a resolution for
            // `elabAppFnResolutions` (`:2082`), overloaded when two or more.
            let cands = crate::resolve::resolve_global_name_at_root(elab, full)?;
            if !cands.is_empty() {
                return cands
                    .into_iter()
                    .map(|c| mk_const(elab, c, explicit_levels))
                    .collect();
            }
```

Update the module doc's "Not ported" list: delete the overloaded-candidates bullet, and add a line saying overloaded candidates go through `head::elab_app_fn_resolutions`. In `head.rs`, the `dotIdent` arm becomes:

```rust
        ("Lean.Parser.Term.dotIdent", _) => {
            let raw = dot_ident_text(elem)?;
            let fs = crate::app::dot_ident::resolve_dotted_ident_fn(
                elab,
                &raw,
                explicit_levels,
                call.expected,
            )?;
            let fns = fs.into_iter().map(|f| Resolution { f, fields: Vec::new() }).collect();
            elab_app_fn_resolutions(elab, fns, lvals, call, kinds)
        }
```

- [ ] **Step 4: Run the gates.**

Run: `cargo test -p leanr_elab 2>&1 | tail -30`
Expected: green, with 126 checked.

- [ ] **Step 5: Mutation check.** Keep only the first candidate (`cands.into_iter().take(1)`) → `overload/dotIdentAmbig` and `overload/dotIdentArgs` fail. Revert, and record the result in the commit body.

- [ ] **Step 6: Gate and commit.**

```bash
mise run ci   # blocking; must end green
git add tests/fixtures/elab crates/leanr_elab
git commit -m "leanr_elab: overloaded .x candidates through elabAppFnResolutions (M4c-2b-ii)"
```

---

### Task 4: Plain-throw ambiguity errors

**Files:**
- Modify: `crates/leanr_elab/src/error.rs` (`AmbiguousFieldName`, `AmbiguousNamespace`, `FailedToOpen`)
- Modify: `crates/leanr_elab/src/app/lval.rs:250-262` (`findMethod?`'s ambiguity)
- Modify: `crates/leanr_elab/src/command/scope.rs:108-111`, `:162-170`, `:175-202`, `:206-241`
- Modify: `tests/fixtures/elab/dump_decls.lean` (5 rows), `file-queries.jsonl`, `oracle_file.rs` (`CORPUS_FLOOR = 131`), `crates/leanr_elab/tests/scopes.rs`

**Interfaces:**
- Produces:
  - `ElabError::AmbiguousFieldName { field: String, full: String, cands: Vec<String> }`
  - `ElabError::AmbiguousNamespace { id: String, cands: Vec<String> }`
  - `ElabError::FailedToOpen(Vec<ElabError>)`

- [ ] **Step 1: Add the rows** after Task 3's last row (put a comma after it):

```lean
  ("ambig/fieldName", "namespace A\ndef S1.g (s : S1) : Nat := Nat.zero\nend A\nnamespace B\ndef S1.g (s : S1) : Nat := Nat.zero\nend B\nopen A B\ndef t (s : S1) : Nat := s.g"),
  ("ambig/openHiding", "namespace A.X\ndef p : Nat := Nat.zero\nend A.X\nnamespace B.X\ndef p : Nat := Nat.zero\nend B.X\nopen A B\nopen X hiding p"),
  ("ambig/openRenaming", "namespace A.X\ndef p : Nat := Nat.zero\nend A.X\nnamespace B.X\ndef p : Nat := Nat.zero\nend B.X\nopen A B\nopen X renaming p → q"),
  ("ambig/openFailed", "namespace A.X\ndef p : Nat := Nat.zero\nend A.X\nnamespace B.X\ndef p : Nat := Nat.zero\nend B.X\nopen A B\nopen X (r)"),
  ("ambig/openFailedOne", "namespace A.X\ndef p : Nat := Nat.zero\nend A.X\nopen A\nopen X (r)")
```

Oracle first lines, in order:
1. ``Field name `g` is ambiguous: `S1.g` has possible interpretations `A.S1.g`, `B.S1.g` ``
2. ``ambiguous namespace `X`, possible interpretations: `[B.X, A.X]` ``
3. ``ambiguous namespace `X`, possible interpretations: `[B.X, A.X]` ``
4. `failed to open, errors ` (trailing space)
5. ``Unknown constant `A.X.r` ``

Regenerate. Check that `wc -l` prints 131 and that `target/m4c2biiprobe/elab0/file-final.jsonl` `cmp`s equal to the whole file. Set `CORPUS_FLOOR = 131`.

In `scopes.rs`, replace Task 3's `// Task 4` `S1.g` seam assertion with:

```rust
    // Two opened `S1.g`: `findMethod?`'s throw (probed).
    let (_, stop) = run("def Foo.S1.g (_s : S1) : Nat := Nat.zero\ndef Bar.S1.g (_s : S1) : Nat := Nat.zero\nopen Foo Bar\ndef y (s : S1) : Nat := s.g");
    assert_eq!(
        stop.expect("stops"),
        (3, "Field name `g` is ambiguous: `S1.g` has possible interpretations `Foo.S1.g`, `Bar.S1.g`".to_string())
    );
```

Add this test:

```rust
/// `open X (p)` with `X` naming two namespaces: the oracle's "ambiguous
/// identifier `p`, possible interpretations: [B.X.p, A.X.p]"
/// (`Open.lean:75`) renders `mkConst`s, an `Expr` list, through the
/// delaborator, so leanr seams it.
#[test]
fn open_explicit_ambiguity_is_a_delab_seam() {
    let src = "namespace A.X\ndef p : Nat := Nat.zero\nend A.X\nnamespace B.X\ndef p : Nat := Nat.zero\nend B.X\nopen A B\nopen X (p)";
    let (_, stop) = run(src);
    let (at, m) = stop.expect("stops");
    assert_eq!(at, 7, "{m}");
    assert!(m.starts_with("SEAM ") && m.ends_with(" — delab name rendering"), "{m}");
}
```

- [ ] **Step 2: Run and confirm the failure.**

Run: `cargo test -p leanr_elab --test oracle_file --test scopes 2>&1 | tail -20`
Expected: the five rows and the two `scopes.rs` assertions fail, on M4c-2b-ii seams.

- [ ] **Step 3: Implement the errors.** In `error.rs`:

```rust
    /// oracle: `findMethod?`'s throw (`App.lean:1466-1468`). `cands` are
    /// full names in `resolveGlobalName` order.
    AmbiguousFieldName { field: String, full: String, cands: Vec<String> },
    /// oracle: `resolveUniqueNamespace` (`ResolveName.lean:353-356`),
    /// ``s!"ambiguous namespace `{id}`, possible interpretations: `{nss}`"``.
    /// `{nss}` is `List Name`'s `toString`.
    AmbiguousNamespace { id: String, cands: Vec<String> },
    /// oracle: `resolveNameUsingNamespacesCore`'s
    /// `throwErrorWithNestedErrors "failed to open" exs` (`Open.lean:63-66`).
    FailedToOpen(Vec<ElabError>),
```

```rust
            Self::AmbiguousFieldName { field, full, cands } => Some(format!(
                "Field name `{field}` is ambiguous: `{full}` has possible interpretations {}",
                cands.iter().map(|c| format!("`{c}`")).collect::<Vec<_>>().join(", ")
            )),
            Self::AmbiguousNamespace { id, cands } => Some(format!(
                "ambiguous namespace `{id}`, possible interpretations: `[{}]`",
                cands.join(", ")
            )),
            Self::FailedToOpen(_) => Some("failed to open, errors ".into()),
```

Add first-line assertions for the three variants to `overload_first_lines_are_the_oracles`, using the row strings above.

In `lval.rs`, the `cs =>` arm becomes:

```rust
        cs => Err(ElabError::AmbiguousFieldName {
            field: field.to_string(),
            full: render(elab, full),
            cands: cs.iter().map(|&c| render(elab, c)).collect(),
        }),
```

In `scope.rs`:
- **`resolve_unique_namespace`.** Its `_ =>` arm returns `Err(ElabError::AmbiguousNamespace { id: comps.join("."), cands: nss.iter().map(|&n| self.render(n)).collect() })`. Bind the slice as `nss` first. Keep the `[] → UnknownNamespace` arm, which `resolve_namespace` already raises before this point.
- **Both "ambiguous identifier" arms** (`resolve_id`'s, and `resolve_name_using_namespaces`'s final one) become:

```rust
            _ => Err(ElabError::UnsupportedSyntax(format!(
                "ambiguous identifier `{}` in `open` (the oracle's message renders a \
                 `List Expr` of `mkConst`s, `Open.lean:75` / `ResolveName.lean:376`) \
                 — delab name rendering",
                …the same name expression each arm already renders…
            ))),
```

- **`resolve_name_using_namespaces`'s all-failed branch.** With more than one error it returns `Err(ElabError::FailedToOpen(errs))`.
- **The catch arm stays as it is:** `is_oracle_error() || UnsupportedSyntax`. Rewrite its comment: the `UnsupportedSyntax` it admits is `resolve_id`'s delab seam, which stands for an oracle `throwError` that the `try … catch ex` would catch. `FailedToOpen`'s first line does not depend on its nested errors.
- **The `ambiguous` helper** (`:108-111`) is now unused: delete it.

- [ ] **Step 4: Run the gates.**

Run: `cargo test -p leanr_elab 2>&1 | tail -30`
Expected: green, with 131 checked. If the namespace order comes out `[A.X, B.X]`, leanr's `resolve_namespace` order diverges from the oracle's. Fix the order at its source in `resolve.rs` (the oracle prepends each open hit, `ResolveName.lean:232-239`), not by reversing in the error.

- [ ] **Step 5: Mutation check.** For each mutation, apply it, rerun, confirm the named row fails, then revert:
  - reverse `AmbiguousNamespace`'s `cands` → `ambig/openHiding`;
  - reverse `AmbiguousFieldName`'s `cands` → `ambig/fieldName`;
  - return `errs.remove(0)` instead of `FailedToOpen` → `ambig/openFailed`.

Record the results in the commit body.

- [ ] **Step 6: Gate and commit.**

```bash
mise run ci   # blocking; must end green
git add tests/fixtures/elab crates/leanr_elab
git commit -m "leanr_elab: findMethod?/open ambiguity errors; open's Expr-list throws seam on the delaborator (M4c-2b-ii)"
```

---

### Task 5: Retire the `M4c-2b-ii` label; docs; spec § Landed

**Files:**
- Modify: `crates/leanr_elab/src/app/head.rs:153-157` (the `choice` seam text), `app/mod.rs` (module index rows at `:63`, `:69`; `elab_app_aux` doc), `dispatch.rs:186`, `:195`, `lib.rs:119`, `:134`, `:151`, `command/scope.rs:109` (doc), `resolve.rs:20`, `:358` (docs), `builtin/op/mod.rs:164` (doc)
- Modify: `crates/leanr_elab/tests/seam_audit.rs` (retired-label gate)
- Modify: `docs/superpowers/specs/2026-10-04-m4c2b-ii-overloaded-elab-design.md` (§ Plan amendments, § Landed)

- [ ] **Step 1: Write the gate.** Append to `seam_audit.rs`. It mirrors `no_seam_points_at_the_retired_p2b_ii_label`:

```rust
/// M4c-2b-ii RETIRED its own label. Overloaded identifiers and `.x` are
/// elaborated (`app/overload.rs`). `findMethod?`'s and
/// `resolveUniqueNamespace`'s ambiguity, and `failed to open`, are real
/// errors. `choice` heads now seam as `— choice-node parsing`, and the
/// `List Expr` ambiguity messages as `— delab name rendering`. A textual
/// floor, like the gates above.
#[test]
fn no_seam_points_at_the_retired_m4c2b_ii_label() {
    let src_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    let mut offenders = Vec::new();
    for path in walk_rs_files(src_dir) {
        let text = std::fs::read_to_string(&path).expect("readable source");
        for (n, line) in text.lines().enumerate() {
            if line.contains("M4c-2b-ii") || line.contains("overloading slice") {
                offenders.push(format!("{}:{}", path.display(), n + 1));
            }
        }
    }
    assert!(offenders.is_empty(), "M4c-2b-ii landed; stale label at {offenders:?}");
}
```

Run `cargo test -p leanr_elab --test seam_audit no_seam_points_at_the_retired_m4c2b_ii_label` and expect it to FAIL, listing the doc and `choice` sites.

- [ ] **Step 2: Relabel.**
  - `head.rs`'s `choice` arm message becomes: `"application head `choice` needs `elabAppFn`'s `choiceKind` fan-out (App.lean:2062-2065); leanr's parser never builds `choice` (longestMatch ties are first-wins) — choice-node parsing"`.
  - Its neighbouring comment ("`overloaded` is false until `choice` is routed (overloading slice)") becomes "… until `choice` is routed (choice-node parsing)".
  - `app/mod.rs`'s index: the overload row reads `overload resolution (candidates > 1) ........ M4c-2b-ii (landed) overload.rs, head.rs`; rephrase it so it does not contain the label, e.g. `overload resolution (candidates > 1) ......... landed  overload.rs, head.rs`. The `choice` row reads `choice-node parsing`.
  - Rewrite `dispatch.rs`'s two rows and `lib.rs`'s three bullets the same way.
  - Every doc that names `expect_one`'s M4c-2b-ii seam now names `head::elab_app_fn_resolutions` / `overload::select`.

Then run:

```bash
grep -rn "M4c-2b-ii\|overloading slice" crates/ ; echo "exit=$?"
```

Expected: no hits in `crates/leanr_elab/src` (`exit=1` once tests are also clean). Any hit left in `crates/leanr_elab/tests` must be a comment: rewrite it.

- [ ] **Step 3: Spec amendments and § Landed.** Append to the spec:

```markdown
## Plan amendments (plan-time oracle probes, 2026-10-04)

- `elab_app_fn` returns `AppFn::{Done, Candidates}` instead of threading
  an accumulator, and takes no `overloaded` flag: the oracle sets the
  incoming flag only under `choice` (out of scope), so `overloaded` is
  `fns.len() > 1` inside `elab_app_fn_resolutions`.
- Rule 1 lives in `observing`: non-oracle errors are rethrown, never
  captured, so `select` only ever sees oracle errors.
- `open`'s two "ambiguous identifier" throws render `Expr` lists: they are
  `— delab name rendering` seams, and `AmbiguousOpenIdent` is dropped.
  `failed to open, errors ` is ported (`FailedToOpen`).
- Nested namespaces never overload (the inner shadows), so the
  `overload/nestedNs` rows are dropped.
- `binder_name_gen` stays monotonic: `Core.SavedState.restore` rewinds
  neither the name generator nor the macro scope.
- `Elab0` gains `instCoeListNatInt : Coe (List Nat) Int`, to give
  `getSuccesses` stage 2 a source-level discriminator. It is inert:
  only `elim.jsonl` gains its record.
- `mk_const` renders the resolved constant in
  ``too many explicit universe levels for `B.u` `` (it rendered the source
  text before, and the variant had no first line).

## Landed

(Fill in the actual PR number and head commit, the corpus count (131),
and the mutation results recorded in each task's commit body. Also list
any surprises, and the open seams: `choice` nodes (choice-node parsing),
`resolveId?` and `open`'s `Expr`-list ambiguity (delab name rendering).)
```

Replace the `## Landed` placeholder paragraph with the real facts before committing. It must contain no "Fill in".

- [ ] **Step 4: Full gate and commit.**

```bash
mise run ci   # blocking; must end green
git add crates/leanr_elab docs/superpowers/specs/2026-10-04-m4c2b-ii-overloaded-elab-design.md
git commit -m "leanr_elab: retire the M4c-2b-ii label; spec amendments and Landed (M4c-2b-ii)"
```

---

## Self-review notes

- **Spec coverage:**
  - State: Task 1.
  - Fan-out, selection, Rule 1, Rule 2 and identifiers: Task 2.
  - `.x`: Task 3.
  - Errors table and plain throws: Task 4.
  - Seam relabelling: Tasks 2, 4 and 5.
  - Testing and mutation evidence: each task's mutation step.
  - Gates: each task's `mise run ci`.
- **Spec items changed by probes:** listed in Task 5 Step 3 (`AmbiguousOpenIdent` dropped, `FailedToOpen` added, the nested-namespace rows dropped, accumulator → `AppFn`).
- **Not given a dedicated mutation:** stage 3 running over `r₂` instead of all successes. No probed row separates the two, and the code cites the oracle line.
