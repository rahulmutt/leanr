# Synthesis onto real mctx depth — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Run typeclass synthesis under the real mctx-depth model (`with_new_mctx_depth` + `isDefEqStuckEx`) instead of a checkpoint/rollback stand-in, so "stuck" is detected dynamically and the syntactic pre-test in `try_synth_instance` can be deleted.

**Architecture:** `leanr_meta::synth` swaps its rollback boundary for `MetaCtx::with_new_mctx_depth(true, …)` and sets `Config::is_def_eq_stuck_ex`; its four table-key/abstraction walks start treating lower-depth mvars as constants, as the oracle does. `synth_pending` (`whnf.rs`) ports the oracle's catch of `isDefEqStuck`. Then `try_synth_instance` becomes a one-to-one port of `trySynthInstance`, and new oracle rows pin the two residues the pre-test got wrong.

**Tech Stack:** Rust (workspace crates `leanr_meta`, `leanr_elab`), mise tasks, the pinned Lean oracle `leanprover/lean4:v4.33.0-rc1` for fixture regeneration.

**Spec:** `docs/superpowers/specs/2026-10-02-synth-real-depth-design.md` (read § Amendment 1 — it corrects the task boundaries below).

## Global Constraints

- Branch: `synth-real-depth` (already created; the spec is committed on it).
- Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. Never bump `lean-toolchain`. When `lean` complains "no default toolchain", invoke `lean +leanprover/lean4:v4.33.0-rc1 …`.
- Oracle probes and fixture dumps run in prelude mode against the committed fixture only (`LEAN_PATH=$PWD` inside `tests/fixtures/elab` or `tests/fixtures/meta`). Never probe with stock Init.
- Every oracle `file:line` you write into a comment must be opened against `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/` first. Citations in this plan were verified while writing it; re-verify any you change.
- `IsDefEqStuck` must never be collapsed to `false` inside `is_def_eq`. The only new catch sites are the oracle's own: `trySynthInstance` (already ported) and `synthPendingImp` (Task 2).
- No new dependencies.
- Build only under `/workspace` (never `/tmp`: 20Gi EmptyDir, the pod gets evicted).
- `mise run ci` gates on `cargo fmt --check` and clippy. Run `cargo fmt --all` before every commit. Run `mise run ci` blocking, in-turn (never backgrounded and abandoned), before pushing.
- Every test a task adds must be shown to fail under the stated mutation. Run the mutation, observe the failure, revert. Record each result for § Landed.

## Review Focus

1. **A caller's level mvar inside the search.** `allow_level_assignments = true` keeps outer level mvars ASSIGNABLE, but `normLevel`/`AbstractMVars` still treat them as constants (depth ≠ current). A reviewer should check Task 1's level arms compare against `mctx.depth()`, not `level_assign_depth()`. Pinned by Task 1's `table_key_keeps_a_lower_depth_level_mvar` and `abstract_mvars_keeps_lower_depth_mvars`.
2. **Undeclared mvars.** `decode_expr` and some tests intern mvar nodes without declaring them. `expr_mvar_depth` returns `None` for them; they must stay constants (today's behaviour), not panic and not be renamed. Pinned by the existing `oracle_synth_gate` records (all declare) plus Task 1's same-depth controls; the `None ≠ Some(depth)` comparison is the code-level guarantee.
3. **An error inside the depth block.** `with_new_mctx_depth` must restore depth and roll back on the `Err` path too (it does: it rolls back unconditionally after `f`). Pinned by Task 1's `pi_goal_with_mvar_body_is_stuck`, which asserts `?a` is unassigned after an `Err`.
4. **`synth_pending` re-entered while the outer search is stuck.** The catch must map ONLY `IsDefEqStuck`; budget/depth errors must still propagate. Pinned by Task 2's mutation (b).
5. **A goal whose only mvar is in an out-param position.** It must still be answered and assign the caller's mvar AFTER the depth block (`assign_out_params` outside). Pinned by the existing `try_synth_instance_is_three_valued` `Op N N ?c` arm and Synth0's `outParam/synth/0`, which must stay green through every task.

---

### Task 1: Real depth in the synthesis driver and its walks

**Files:**
- Modify: `crates/leanr_meta/src/synth.rs` — `KeyNormalizer::norm_level_body` (≈:515), `KeyNormalizer::norm_expr_body` mvar arm (≈:600-625), `MVarAbstractor::level_body` (≈:1219), `MVarAbstractor::expr_body` (≈:1272-1300), `synth_instance_main` (≈:2238-2318), `synth_instance_preprocessed` (≈:2320-2343); module doc ≈:95-120; doc comments of `synth_instance_body`, `assign_out_params`, `apply_abstract_result`; unit tests in the `tests` module.
- Modify: `crates/leanr_meta/tests/oracle_synth.rs` — `SEAM_EXCLUSIONS` (:39-60), the gate's `exc` comment (:92-114), `compared` assertion (:466), delete `seam_excluded_mvar_goal_is_incompleteness_not_an_error` (≈:480-558), rewrite `exc_record_stuck_synth_0_pins_leanrs_current_divergent_answer` (≈:568-696).

**Interfaces:**
- Consumes (already exist): `MetaCtx::with_new_mctx_depth<R>(&mut self, allow_level_assignments: bool, f: impl FnOnce(&mut Self) -> R) -> R` (`metactx.rs:547`); `MetavarContext::depth() -> u32`, `expr_mvar_depth(MVarId) -> Option<u32>`, `level_mvar_depth(LMVarId) -> u32` (`mvar_ctx.rs:164-183`); `Config::is_def_eq_stuck_ex: bool` (`config.rs:167`); `MetaError::IsDefEqStuck`.
- Produces: `synth_instance(&mut self, ty) -> Result<Option<ExprId>, MetaError>` now returns `Err(MetaError::IsDefEqStuck)` when the search tries to assign a caller's expr mvar. In `oracle_synth.rs`: `fn with_synth0_record<R>(id: &str, f: impl FnOnce(&mut MetaCtx<'_>, &serde_json::Value, ExprId, MVarId) -> R) -> R` (Task 3 reuses it).

- [ ] **Step 1: Write the failing walk tests** (in `synth.rs`'s `tests` module, next to `assigned_level_mvar_resolves_without_consuming_a_counter_index`)

```rust
    // -----------------------------------------------------------------
    // synth-real-depth Task 1: the four depth-only checks
    // -----------------------------------------------------------------

    /// oracle `MkTableKey.normExpr` (`SynthInstance.lean:145`):
    /// `if !(← mvarId.isAssignable) then return e`, and `isAssignable`
    /// (`MetavarContext.lean:483-486`) is `decl.depth == mctx.depth`. A
    /// caller's mvar seen from inside a new depth is a CONSTANT in the
    /// key; at its own depth it is renamed (the control).
    #[test]
    fn table_key_keeps_a_lower_depth_expr_mvar() {
        with_instances_ctx(|ctx| {
            let ty = type_sort(ctx);
            let (a, _) = fresh_mvar(ctx, ty);
            let add = const_named(ctx, "Add");
            let base = Some(ctx.view.store);
            let goal = ctx.scratch.expr_app(base, add, a).expect("Add ?a");
            let inner = ctx
                .with_new_mctx_depth(true, |c| c.normalize_goal_key(goal))
                .unwrap();
            assert_eq!(inner, GoalKey(goal), "?a must stay a constant");
            let same_depth = ctx.normalize_goal_key(goal).unwrap();
            assert_ne!(same_depth, GoalKey(goal), "control: renamed to _tc.0");
        });
    }

    /// oracle `MkTableKey.normLevel` (`SynthInstance.lean:120`):
    /// `if getLevelDepth mvarId != mctx.depth then return u`. Compared
    /// against `depth`, NOT `levelAssignDepth`: under
    /// `allowLevelAssignments := true` the caller's level mvar is still
    /// assignable, but it is not renamed.
    #[test]
    fn table_key_keeps_a_lower_depth_level_mvar() {
        with_instances_ctx(|ctx| {
            let u = fresh_level_mvar_for_test(ctx);
            let base = Some(ctx.view.store);
            let goal = ctx.scratch.expr_sort(base, u).expect("Sort ?u");
            let inner = ctx
                .with_new_mctx_depth(true, |c| c.normalize_goal_key(goal))
                .unwrap();
            assert_eq!(inner, GoalKey(goal), "?u must stay a constant");
            let same_depth = ctx.normalize_goal_key(goal).unwrap();
            assert_ne!(same_depth, GoalKey(goal), "control: renamed to _tc.0");
        });
    }

    /// oracle `AbstractMVars` (`AbstractMVars.lean:56-60` level,
    /// `:89-93` expr): "metavariables from lower depths are treated as
    /// constants". This is what lets `wake_up`'s root check
    /// (`num_mvars() == 0`) accept an answer that mentions the caller's
    /// mvar (Synth0 `mvarGoal/synth/0`, oracle `instOfNN ?n`).
    #[test]
    fn abstract_mvars_keeps_lower_depth_mvars() {
        with_instances_ctx(|ctx| {
            let ty = type_sort(ctx);
            let (a, _) = fresh_mvar(ctx, ty);
            let u = fresh_level_mvar_for_test(ctx);
            let base = Some(ctx.view.store);
            let sort_u = ctx.scratch.expr_sort(base, u).expect("Sort ?u");
            let e = ctx.scratch.expr_app(base, sort_u, a).expect("app");
            let inner = ctx
                .with_new_mctx_depth(true, |c| c.abstract_mvars(e))
                .unwrap();
            assert_eq!(inner.num_mvars(), 0);
            assert!(inner.param_names.is_empty());
            assert_eq!(inner.expr, e);
            let same_depth = ctx.abstract_mvars(e).unwrap();
            assert_eq!(same_depth.num_mvars(), 1, "control");
            assert_eq!(same_depth.param_names.len(), 1, "control");
        });
    }
```

- [ ] **Step 2: Flip `pi_goal_with_mvar_body_does_not_error` to the oracle's answer**

Replace the whole test (doc comment included; it sits right after the `pi_goal_*` tests, ≈:3935-4005) with:

```rust
    /// `N → Add ?a` with `?a` minted OUTSIDE the search. The oracle runs
    /// the search under `withNewMCtxDepth` with `isDefEqStuckEx := true`
    /// (`SynthInstance.lean:963`, `:978`), so `?a` is read-only;
    /// `getUnify` keys it `.star` (`DiscrTree/Main.lean:395-411`) and
    /// `Add N =?= Add ?a` throws `isDefEqStuck`
    /// (`ExprDefEq.lean:1952-1956`). leanr now does the same: `Err`, and
    /// `?a` stays unassigned because the depth block rolls back on the
    /// error path too. `trySynthInstance` reports it as `.undef`
    /// (`:1014-1017`).
    #[test]
    fn pi_goal_with_mvar_body_is_stuck() {
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let ty = type_sort(ctx);
            let (a, a_id) = fresh_mvar(ctx, ty);
            let add = const_named(ctx, "Add");
            let base = Some(ctx.view.store);
            let add_a = ctx.scratch.expr_app(base, add, a).expect("Add ?a");
            let pi = mk_arrow_for_test(ctx, n, add_a);
            assert_eq!(ctx.synth_instance(pi), Err(MetaError::IsDefEqStuck));
            assert!(!ctx.mctx.is_assigned(a_id), "rolled back on Err");
            assert_eq!(
                ctx.try_synth_instance(pi).expect("no error"),
                LOption::Undef,
                "the oracle's trySynthInstance answer"
            );
        });
    }
```

If `MetaError` or `LOption` is not in scope in the tests module, add `use crate::{MetaError, LOption};` at the top of the module's existing `use` block (≈:3070).

- [ ] **Step 3: Flip the two Synth0 pins in `oracle_synth.rs`**

(a) Replace the `SEAM_EXCLUSIONS` value (keep the doc comment above it, it describes the mechanism) with an empty list plus a note:

```rust
// `mvarGoal/synth/0` (`OfN ?n N`) was the one entry. It closed in
// synth-real-depth Task 1: under real depth `abstract_mvars` leaves the
// caller's lower-depth `?n` alone (`AbstractMVars.lean:89-93`), so the
// answer `instOfNN ?n` passes `wake_up`'s root check, as in the oracle.
const SEAM_EXCLUSIONS: &[(&str, &str)] = &[];
```

(b) Raise the gate's count: `compared, 37,` → `compared, 38,`, and change the message's preamble to `"expected 38 compared synthesis records (37 -> 38: synth-real-depth Task 1 closed the mvarGoal/synth/0 seam exclusion; skipped `exc`: …`. Keep the rest of the message as it is.

(c) Rewrite the `exc` comment in `oracle_synth_gate` (≈:100-114, the paragraph starting "The one such record today is `stuck/synth/0`") to:

```rust
        // The one such record today is `stuck/synth/0` (`Add ?a`, `?a`
        // minted OUTSIDE the search): the oracle's search runs under
        // `withNewMCtxDepth` with `isDefEqStuckEx := true`
        // (`SynthInstance.lean:963`, `:978`) and its first unification
        // throws `isDefEqStuck`. leanr now throws `IsDefEqStuck` there
        // too — `exc_record_stuck_synth_0_is_stuck_in_leanr_too` pins it.
```

(d) Delete `seam_excluded_mvar_goal_is_incompleteness_not_an_error` entirely (doc comment and body). The gate now compares that record.

(e) Add the helper and replace `exc_record_stuck_synth_0_pins_leanrs_current_divergent_answer` (doc + body) with:

```rust
/// Replays `Synth0.olean`, finds the committed record `id`, decodes its
/// `goal`, and DECLARES its first goal mvar at depth 0 before handing the
/// context to `f` (`decode_expr` interns mvar nodes without declaring
/// them, and an undeclared mvar is not one the search can reason about).
fn with_synth0_record<R>(
    id: &str,
    f: impl FnOnce(&mut MetaCtx<'_>, &serde_json::Value, ExprId, MVarId) -> R,
) -> R {
    let support::Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
        classes,
        coe_decls,
        aux_recs,
        elab_as_elim,
        structures: _,
    } = replay_fixture("Synth0.olean");
    let queries =
        std::fs::read_to_string(fixture("synth-queries.jsonl")).expect("committed queries");
    let q: serde_json::Value = queries
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str::<serde_json::Value>(l).expect("valid JSONL"))
        .find(|q| q["id"].as_str() == Some(id))
        .unwrap_or_else(|| panic!("{id} must be present in the corpus"));
    let view: EnvView = env.view();
    let base = Some(view.store);
    let mut scratch = Store::scratch();
    let mut fv = HashMap::new();
    let mut mv: HashMap<u64, NameId> = HashMap::new();
    let goal = decode_expr(&mut scratch, base, &q["goal"], &mut fv, &mut mv);
    let ty = decode_expr(&mut scratch, base, &q["mvars"][0]["t"], &mut fv, &mut mv);
    let nid = mv[&q["mvars"][0]["i"].as_u64().expect("mvars[0].i")];
    let mut ctx = MetaCtx::new(
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
            aux_recs: &aux_recs,
            elab_as_elim: &elab_as_elim,
            structures: &[],
        },
    );
    ctx.mctx_mut().declare(
        MVarId(nid),
        MVarDecl {
            user_name: None,
            ty,
            lctx: LocalCtxSnapshot::empty(),
            kind: MVarKind::Natural,
        },
    );
    f(&mut ctx, &q, goal, MVarId(nid))
}

/// `stuck/synth/0` (`Add ?a`, `?a : Type` minted OUTSIDE the search) is
/// an `exc` record: the oracle throws `isDefEqStuck`
/// (`SynthInstance.lean:963` sets `isDefEqStuckEx`; the throw is
/// `ExprDefEq.lean:1952-1956`). The gate skips `exc` records, so this
/// test is what pins leanr's side: the same `IsDefEqStuck`, with `?a`
/// left unassigned.
#[test]
fn exc_record_stuck_synth_0_is_stuck_in_leanr_too() {
    with_synth0_record("stuck/synth/0", |ctx, q, goal, a| {
        assert_eq!(q["q"].as_str(), Some("exc"));
        assert_eq!(q["msg"].as_str(), Some("internal exception #7"));
        assert_eq!(ctx.synth_instance(goal), Err(MetaError::IsDefEqStuck));
        assert!(!ctx.mctx().is_assigned(a));
    });
}
```

Add `MetaError` to the `use leanr_meta::{…}` line (:24). Remove imports that become unused (`encode_expr`/`EncSt` only if nothing else uses them; let `cargo clippy` tell you).

- [ ] **Step 4: Run the new and flipped tests; confirm they fail**

Run: `cargo test -p leanr_meta --lib -- table_key_keeps abstract_mvars_keeps pi_goal_with_mvar_body_is_stuck` then `cargo test -p leanr_meta --test oracle_synth`
Expected: the three walk tests FAIL on the `inner` assertion (the walks rename `?a`/`?u`); `pi_goal_with_mvar_body_is_stuck` FAILS (`Ok(Some(fun _ => instAddN))`); `oracle_synth_gate` FAILS on `mvarGoal/synth/0` (leanr `None` vs oracle `instOfNN ?n`); `exc_record_stuck_synth_0_is_stuck_in_leanr_too` FAILS (`Ok(Some(instAddN))`).

- [ ] **Step 5: Port the four depth checks**

(a) `KeyNormalizer::norm_expr_body`, mvar arm: replace the comment block that starts `// oracle: \`if !(← mvarId.isAssignable) then return e\`` and the line `let assignable = self.ctx.mctx.decl(mid).is_some();` with:

```rust
                // oracle: `if !(← mvarId.isAssignable) then return e`
                // (:145). `MVarId.isAssignable`
                // (`MetavarContext.lean:483-486`) is DEPTH-ONLY,
                // `decl.depth == mctx.depth`: kind plays no role, so a
                // syntheticOpaque mvar at the current depth IS renamed.
                // Not `assign.rs::unassigned_mvar_id`'s
                // `isReadOnlyOrSyntheticOpaque` (a different oracle
                // question; see the module doc). Undeclared → no depth →
                // a constant (the oracle's `getDecl` would panic).
                let assignable =
                    self.ctx.mctx.expr_mvar_depth(mid) == Some(self.ctx.mctx.depth());
```

(b) `KeyNormalizer::norm_level_body`, `LevelRow::MVar` arm: right after the `if let Some(v) = self.ctx.mctx.level_assignment(lid) { return self.norm_level(v); }` block, insert:

```rust
                // oracle: `if getLevelDepth mvarId != mctx.depth then
                // return u` (:120). Depth, NOT `levelAssignDepth`: a
                // caller's level mvar stays assignable under
                // `allowLevelAssignments := true` but is still a constant
                // in the key.
                if self.ctx.mctx.level_mvar_depth(lid) != self.ctx.mctx.depth() {
                    return Ok(l);
                }
```

(c) `MVarAbstractor::level_body`, `LevelRow::MVar` arm: after its `level_assignment` block, insert:

```rust
                // oracle: `AbstractMVars.lean:56-60` — "metavariables
                // from lower depths are treated as constants".
                if self.ctx.mctx.level_mvar_depth(lid) != self.ctx.mctx.depth() {
                    return Ok(l);
                }
```

(d) `MVarAbstractor::expr_body`, `Node::MVar { id: Some(id) }` arm: replace the comment `// oracle: \`if decl.depth != mctx.depth then return e\` … no type to abstract by either.` with:

```rust
                // oracle: `if decl.depth != mctx.depth then return e`
                // (`AbstractMVars.lean:89-93`): a lower-depth mvar is a
                // constant. Undeclared → no depth → a constant too.
                if self.ctx.mctx.expr_mvar_depth(mid) != Some(self.ctx.mctx.depth()) {
                    return Ok(e);
                }
```

Keep the following `let Some(decl_ty) = … else { return Ok(e); };` line (now unreachable for a declared mvar, still the safe answer).

- [ ] **Step 6: Run the walk tests; confirm they pass**

Run: `cargo test -p leanr_meta --lib -- table_key_keeps abstract_mvars_keeps`
Expected: PASS (3 tests). The pi/Synth0 tests still fail; the driver is next.

- [ ] **Step 7: Swap the driver onto real depth**

(a) In `synth_instance_main`, add after `self.cfg.univ_approx = false;`:

```rust
        self.cfg.is_def_eq_stuck_ex = true;
```

and rewrite the comment bullets `isDefEqStuckEx := true -- NAMED SEAM …` and `withNewMCtxDepth (allowLevelAssignments := true) -- NAMED SEAM …` into one bullet:

```rust
        //  - `isDefEqStuckEx := true` -- set below. Together with
        //    `synth_instance_preprocessed`'s `with_new_mctx_depth(true, ..)`
        //    (`SynthInstance.lean:978`) it makes the caller's mvars
        //    read-only during the search: an attempt to assign one
        //    throws `MetaError::IsDefEqStuck` (#59's read-only arms in
        //    `assign.rs`/`level.rs`), which `try_synth_instance` and
        //    `synth_pending` report as "not now".
```

Also rewrite the `ctxApprox := true` bullet's sentences from "The restriction's depth guard … WEAKER here …" through "… not a separate one." to: `The restriction's depth guard (\`expr_mvar_depth(id) != mctx.depth()\`) is exact here: the caller's mvars sit below the search's depth, so they are never restricted mid-search.`

(b) Replace `synth_instance_preprocessed`'s body with:

```rust
    fn synth_instance_preprocessed(&mut self, ty: ExprId) -> Result<Option<ExprId>, MetaError> {
        let PreprocessResult { ty, kind } = self.preprocess(ty)?;
        // oracle: `withNewMCtxDepth (allowLevelAssignments := true)`
        // (`SynthInstance.lean:978-1002`). `with_new_mctx_depth` restores
        // the caller's mctx wholesale on BOTH paths, like
        // `withNewMCtxDepthImp`'s `finally` (`Basic.lean:1974-1980`). The
        // answer survives because `mk_answer` already abstracted it. Only
        // `.mvarsNoOutputParams` skips `preprocessOutParam`; `.noMVars`
        // runs it too, deliberately (the `OrderDual` note, `:981-999`).
        let abst = self.with_new_mctx_depth(true, |ctx| {
            let searched = match kind {
                PreprocessKind::MVarsNoOutputParams => Ok(ty),
                PreprocessKind::NoMVars | PreprocessKind::MVarsOutputParams => {
                    ctx.preprocess_out_param(ty)
                }
            };
            searched.and_then(|t| ctx.synth_instance_body(t))
        })?;
        // oracle: `applyAbstractResult?` (`:1003`), OUTSIDE the depth
        // block, so `assign_out_params` assigns the caller's mvars at
        // their own depth.
        self.apply_abstract_result(ty, abst)
    }
```

Update the doc comment above it: "run the search under this crate's `withNewMCtxDepth` stand-in (the `checkpoint`/`rollback` pair)" → "run the search under `with_new_mctx_depth(true, ..)`".

(c) Comment hygiene. Grep `synth.rs` for `rollback`, `stand-in`, `flat-depth`, `withNewMCtxDepth` and rewrite each prose mention that describes the old stand-in. Known sites: the module doc ≈:108-120 (replace "This crate has per-mvar depth bookkeeping … for every declared mvar, KIND INCLUDED:" through "… than this one does." with a short paragraph: both walks compare the mvar's recorded depth against `mctx.depth()`; a lower-depth or undeclared mvar is a constant; kind plays no role); `try_synth_instance`'s doc ("does not yet run under `with_new_mctx_depth`" — Task 3 rewrites the whole doc, so only fix sentences that become false now); `synth_instance_body`'s doc ("runs AFTER `synth_instance_preprocessed`'s `rollback`" → "after the depth block closes"); `assign_out_params`' doc ("OUTSIDE the search's `checkpoint`/`rollback` pair, which is this crate's stand-in for the oracle's `withNewMCtxDepth`" → "OUTSIDE the search's `with_new_mctx_depth` block"); `apply_abstract_result`. Leave `rollback`s that refer to other things (`with_mctx`, per-candidate rollbacks) alone.

- [ ] **Step 8: Run `leanr_meta`'s whole suite**

Run: `cargo test -p leanr_meta 2>&1 | tail -40`
Expected: all PASS, including `oracle_synth_gate` with `compared == 38` and `exc_record_stuck_synth_0_is_stuck_in_leanr_too`. If any OTHER test fails, stop and diagnose it before going on. A failure here is a depth bug or an unlisted pin. Do not re-baseline it; report it.

- [ ] **Step 9: Run the mutations; each must fail a named test, then revert**

| Mutation | Must fail |
|---|---|
| (a) `synth_instance_preprocessed` back to `checkpoint`/`rollback` (keep the flag) | `pi_goal_with_mvar_body_is_stuck`, `exc_record_stuck_synth_0_is_stuck_in_leanr_too` |
| (b) drop `self.cfg.is_def_eq_stuck_ex = true` | same two (leanr answers through a read-only mvar → `Ok(None)`/no throw) |
| (c) revert (a) of Step 5 (`decl(mid).is_some()`) | `table_key_keeps_a_lower_depth_expr_mvar` |
| (d) revert (b) of Step 5 | `table_key_keeps_a_lower_depth_level_mvar` |
| (e) revert (c) of Step 5 | `abstract_mvars_keeps_lower_depth_mvars` |
| (f) revert (d) of Step 5 | `abstract_mvars_keeps_lower_depth_mvars`, `oracle_synth_gate` (`mvarGoal/synth/0`) |
| (g) `with_new_mctx_depth(false, ..)` | record whatever fails; if nothing, it is a SURVIVOR — record it for § Landed, don't invent a test now |
| (h) in (b)/(c) of Step 5 compare against `level_assign_depth()` instead of `depth()` | `table_key_keeps_a_lower_depth_level_mvar` / `abstract_mvars_keeps_lower_depth_mvars` |

Run each with the narrowest `cargo test -p leanr_meta …` filter that covers its "must fail" list. Record the outcomes (killed / survived) in a scratch note for Task 4.

- [ ] **Step 10: Format, lint and commit**

```bash
cargo fmt --all
cargo clippy -p leanr_meta --all-targets -- -D warnings
git add crates/leanr_meta/src/synth.rs crates/leanr_meta/tests/oracle_synth.rs
git commit -m "leanr_meta: run typeclass synthesis under real mctx depth + isDefEqStuckEx"
```

---

### Task 2: `synth_pending` treats a stuck search as no progress

**Files:**
- Modify: `crates/leanr_meta/src/whnf.rs` — `synth_pending`'s body (the `match val? { … }` after `with_mvar_context`, ≈:1428-1440); its doc comment's `catchInternalId isDefEqStuckExceptionId (:1052) is NOT replicated here — NAMED SEAM …` paragraph (≈:1348-1362); the module doc's "Named seams" entry that cites it (grep `:1052` / `catchInternalId` in `whnf.rs`).
- Test: `crates/leanr_meta/src/whnf.rs` tests module, next to `synth_pending_depth_guard_refuses_without_assigning` (≈:3857).

**Interfaces:**
- Consumes: Task 1's `synth_instance` that returns `Err(MetaError::IsDefEqStuck)`.
- Produces: `synth_pending(&mut self, mvar: MVarId) -> Result<bool, MetaError>` returns `Ok(false)` (nothing assigned) when the search is stuck. All other errors still propagate.

- [ ] **Step 1: Write the failing test**

```rust
    /// synth-real-depth Task 2. oracle `synthPendingImp` wraps its
    /// `synthInstance?` in `catchInternalId isDefEqStuckExceptionId ..
    /// (fun _ => pure none)` (`SynthInstance.lean:1052`) and returns
    /// `false` on `none`. Goal `Add ?a` with `?a` minted OUTSIDE the
    /// search: `Add N =?= Add ?a` meets the read-only `?a` and throws.
    #[test]
    fn synth_pending_treats_a_stuck_search_as_no_progress() {
        use crate::test_support::{const_named, fresh_mvar, with_instances_ctx};
        with_instances_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("0");
            let one = ctx.scratch.level_succ(base, zero).expect("1");
            let type0 = ctx.scratch.expr_sort(base, one).expect("Type");
            let (a, a_id) = fresh_mvar(ctx, type0);
            let add = const_named(ctx, "Add");
            let add_a = ctx.mk_app_spine(add, &[a]).expect("Add ?a");
            let (_inst, inst_id) = fresh_mvar(ctx, add_a);
            assert_eq!(ctx.synth_pending(inst_id), Ok(false));
            assert!(!ctx.mctx().is_assigned(inst_id));
            assert!(!ctx.mctx().is_assigned(a_id));
        });
    }
```

- [ ] **Step 2: Run it; confirm it fails**

Run: `cargo test -p leanr_meta --lib -- synth_pending_treats_a_stuck_search`
Expected: FAIL with `left: Err(IsDefEqStuck)`, `right: Ok(false)`.

- [ ] **Step 3: Port the catch**

Replace `match val? {` and its `None => Ok(false),` arm with:

```rust
        // oracle: `catchInternalId isDefEqStuckExceptionId
        // (synthInstance? ..) (fun _ => pure none)` (:1052), then
        // `none => return false`. ONLY `IsDefEqStuck` is caught.
        match val {
            Ok(None) | Err(MetaError::IsDefEqStuck) => Ok(false),
            Err(e) => Err(e),
            Ok(Some(val)) => {
```

Keep the existing `Some(val)` body unchanged inside the new `Ok(Some(val))` arm. Then rewrite the doc paragraph `catchInternalId isDefEqStuckExceptionId (:1052) is NOT replicated here — NAMED SEAM …` to:

```rust
    /// `catchInternalId isDefEqStuckExceptionId` (:1052) is ported: a
    /// stuck search (the caller's mvars are read-only under synthesis's
    /// `withNewMCtxDepth`) is "no progress", `Ok(false)`, with nothing
    /// assigned. This is the oracle's OWN catch site, so it does not
    /// conflict with the crate rule that `is_def_eq` never collapses
    /// `IsDefEqStuck` to `false`. Every other error still propagates.
```

Update the module doc's named-seam entry for `:1052` to say it is closed (synth-real-depth Task 2).

- [ ] **Step 4: Run it; confirm it passes**

Run: `cargo test -p leanr_meta --lib -- synth_pending`
Expected: PASS (all `synth_pending*` tests).

- [ ] **Step 5: Mutations**

(a) Delete `| Err(MetaError::IsDefEqStuck)` from the arm → the new test fails with `Err(IsDefEqStuck)`. (b) Widen the catch to `Err(_) => Ok(false)` → `synth_pending_depth_guard_refuses_without_assigning` must still pass and the new test passes, so this mutation SURVIVES the unit tests. Then force a budget error to show the difference: in the new test temporarily call `ctx.set_step_budget(1)` before `synth_pending` with the ORIGINAL code and confirm `Err(MetaError::StepBudgetExhausted)` propagates. Then add this permanent test, which kills (b):

```rust
    /// Only `IsDefEqStuck` is caught: a budget error inside the pending
    /// search still propagates (oracle `catchInternalId` is id-specific).
    #[test]
    fn synth_pending_still_propagates_a_budget_error() {
        use crate::test_support::with_instances_ctx;
        with_instances_ctx(|ctx| {
            let (_goal, mvar) = stuck_mul_over_fresh_instance(ctx);
            ctx.set_step_budget(1);
            assert!(ctx.synth_pending(mvar).is_err());
            assert!(!ctx.mctx().is_assigned(mvar));
        });
    }
```

If `set_step_budget(1)` errors before reaching the search (e.g. in `synth_pending`'s own `step()`), that still pins "non-stuck errors propagate"; keep it and note in § Landed which call site raised it. Re-run (b) to confirm the new test kills it, then revert.

- [ ] **Step 6: The workspace byte-identical gate (spec Amendment 1 item 3)**

Run: `cargo test --workspace 2>&1 | grep -E "^test result|FAILED|panicked" | sort | uniq -c`
Expected: every suite passes. In particular `oracle_elab_gate` (floor 345) and `oracle_op_gate` (floor 99) pass against the UNCHANGED committed JSONL, which is the byte-identical check. The pre-test is still in place, so elab/op behaviour must not move. If anything fails, stop: classify it per Task 4's triage table before proceeding, and do not edit a corpus.

- [ ] **Step 7: Format, lint and commit**

```bash
cargo fmt --all
cargo clippy -p leanr_meta --all-targets -- -D warnings
git add crates/leanr_meta/src/whnf.rs
git commit -m "leanr_meta: synth_pending catches IsDefEqStuck (SynthInstance.lean:1052)"
```

---

### Task 3: Delete the syntactic pre-test; pin residues 2 and 3 with oracle rows

**Files:**
- Modify: `crates/leanr_meta/src/synth.rs` — `try_synth_instance` (doc ≈:1662-1788, body ≈:1789-1800), delete `has_mvar_outside_out_params` (≈:1802-1850); test `try_synth_instance_is_three_valued_and_positional` (≈:4424-4515).
- Modify: `crates/leanr_elab/src/lib.rs:68` (doc mentions `has_mvar_outside_out_params`), plus any other doc hit from `grep -rn "has_mvar_outside_out_params\|pre-test\|residue 2\|residue 3" crates`.
- Modify: `tests/fixtures/meta/dump_synth.lean` (curated list ≈:528 and the per-tag doc list ≈:345); regenerate `tests/fixtures/meta/synth-queries.jsonl`.
- Modify: `crates/leanr_meta/tests/oracle_synth.rs` (count 38 → 39; new test).
- Modify: `tests/fixtures/elab/Elab0.lean` (after `def useNoInst …`, ≈:233); regenerate `tests/fixtures/elab/Elab0.olean`.
- Modify: `tests/fixtures/elab/dump_elab.lean` (`instImplicitQueries`, ≈:434, plus its doc list ≈:413); regenerate `tests/fixtures/elab/elab-queries.jsonl`.
- Modify: `crates/leanr_elab/tests/oracle_elab.rs` (`CORPUS_FLOOR` 345 → 346 plus history comment).
- Modify: `crates/leanr_elab/tests/synthetic_smoke.rs` (new test after `bare_typeclass_application_is_reported_stuck`, ≈:332).

**Interfaces:**
- Consumes: Task 1's `with_synth0_record` (in `oracle_synth.rs`); Task 1/2 behaviour.
- Produces: `try_synth_instance(&mut self, ty) -> Result<LOption<ExprId>, MetaError>` = `instantiate_mvars` → `synth_instance` → `IsDefEqStuck ↦ Undef`. `has_mvar_outside_out_params` no longer exists.

- [ ] **Step 1: Add the Synth0 residue-3 query and regenerate**

In `dump_synth.lean`'s `synthQueries`, right after the `` (`stuck, …) `` line, add:

```lean
  , (`noInstMVar,  0, [], do pure (cls1 `NoInst (← mkFreshExprMVar type0)))
```

and in the per-tag doc list, after the `stuck` entry, add:

```
* `noInstMVar`  — `NoInst ?a`, `?a` minted OUTSIDE the search, ZERO
                  candidates. `synthInstance?` answers `none` cleanly:
                  no candidate means no unification, so nothing gets
                  stuck. Residue 3 of synth-real-depth: leanr's old
                  syntactic pre-test answered `.undef` here.
```

Regenerate (in-turn, blocking):

```bash
cd tests/fixtures/meta && LEAN_PATH=$PWD lean +leanprover/lean4:v4.33.0-rc1 --run dump_synth.lean > synth-queries.jsonl; cd /workspace
git diff --stat tests/fixtures/meta/synth-queries.jsonl
grep noInstMVar tests/fixtures/meta/synth-queries.jsonl
```

Expected: exactly one line added (`1 insertion`), with `"q":"synth"` and `"ok":false`. If any other line changed, stop and report.

- [ ] **Step 2: Add the Elab0 residue-2 support and query; regenerate**

Append after `def useNoInst … := x` in `Elab0.lean`:

```lean
-- `Any` — residue 2 of synth-real-depth: ONE instance, polymorphic in
-- the class argument. Synthesizing `Any ?a` assigns only search-local
-- mvars, so the oracle answers `.some` and leaves the caller's `?a`
-- alone (`useAny _` → `@useAny ?m (@instAnyAll ?m) ?x`). Like
-- `Wrap`/`Pair`/`NoInst`, it must NEVER gain a `@[default_instance]`.
class Any (a : Type) where
  any : a -> a

instance instAnyAll {a : Type} : Any a where
  any := fun x => x

def useAny {a : Type} [Any a] (x : a) : a := Any.any x
```

In `dump_elab.lean`'s `instImplicitQueries`, after the `tc/useWrapNat` line, add `  , ("tc/useAnyHole",      "useAny _")`, and in the doc list above it add:

```
  * `tc/useAnyHole` — `Any ?a` whose only candidate is polymorphic
    (synth-real-depth residue 2): answered, not postponed.
```

Regenerate (in-turn, blocking):

```bash
cd tests/fixtures/elab && lean +leanprover/lean4:v4.33.0-rc1 Elab0.lean -o Elab0.olean && LEAN_PATH=$PWD lean +leanprover/lean4:v4.33.0-rc1 --run dump_elab.lean > elab-queries.jsonl; cd /workspace
git diff --stat tests/fixtures/elab/elab-queries.jsonl
grep '"tc/useAnyHole"' tests/fixtures/elab/elab-queries.jsonl
wc -l tests/fixtures/elab/elab-queries.jsonl
```

Expected: one line added (346 lines), with the term `@useAny ?m (@instAnyAll ?m) ?x` (canonical mvar encoding). If any other line changed, stop and report. If `tc/useAnyHole` is MISSING (the dumper drops a throwing query), the oracle threw. Stop and report; don't substitute a variant without the controller.

- [ ] **Step 3: Write the failing tests**

(a) `oracle_synth.rs`: bump `compared, 38,` → `compared, 39,` (message: `38 -> 39: synth-real-depth Task 3 added noInstMVar/synth/0`), and add:

```rust
/// Residue 3 of synth-real-depth: `NoInst ?a` with ZERO candidates. The
/// oracle's `synthInstance?` answers `none` (`"ok":false` in the corpus):
/// with no candidate, no unification runs and nothing gets stuck. So
/// `trySynthInstance` (`SynthInstance.lean:1014-1017`) is `.none`, not
/// `.undef`. The old syntactic pre-test answered `Undef` here.
#[test]
fn no_inst_mvar_goal_is_none_not_undef() {
    with_synth0_record("noInstMVar/synth/0", |ctx, q, goal, _a| {
        assert_eq!(q["ok"].as_bool(), Some(false));
        assert_eq!(ctx.try_synth_instance(goal), Ok(LOption::None));
    });
}
```

Add `LOption` to the `use leanr_meta::{…}` line (it is re-exported at `leanr_meta/src/lib.rs:54` and derives `Debug, PartialEq`).

(b) `oracle_elab.rs`: `const CORPUS_FLOOR: usize = 345;` → `346`, appending to the history comment above it:

```rust
    //
    // 345 -> 346 (synth-real-depth task 3): `tc/useAnyHole`.
```

(c) `synthetic_smoke.rs`, after `bare_typeclass_application_is_reported_stuck`:

```rust
/// Residue 3 of synth-real-depth, end to end. `useNoInst _`: the goal
/// `NoInst ?a` has ZERO candidates, so the oracle's `trySynthInstance`
/// is `.none` and elaboration fails with "failed to synthesize instance
/// of type class NoInst ?m" (probed on Elab0). It is NOT a stuck
/// problem: the old syntactic pre-test postponed it and the ladder
/// reported `StuckSyntheticMVar`.
#[test]
fn hole_against_a_class_without_instances_is_a_synthesis_failure() {
    let err = support::elab_and_synthesize("useNoInst _").expect_err("fails");
    assert!(
        matches!(err, leanr_elab::ElabError::InstanceSynthesisFailed { .. }),
        "got {err:?}"
    );
}
```

- [ ] **Step 4: Run them; confirm they fail for the right reason**

Run: `cargo test -p leanr_meta --test oracle_synth; cargo test -p leanr_elab --test oracle_elab --test synthetic_smoke 2>&1 | tail -30`
Expected: `no_inst_mvar_goal_is_none_not_undef` FAILS (`Ok(Undef)`); `oracle_synth_gate` PASSES at 39 (leanr's bare `synth_instance` already answers `None`; the gate is the oracle evidence, the try-test is the discriminator); `oracle_elab_gate` FAILS on `tc/useAnyHole` (leanr: stuck error); the smoke test FAILS (`StuckSyntheticMVar`).

- [ ] **Step 5: Delete the pre-test**

Replace `try_synth_instance`'s doc comment and body with:

```rust
    /// oracle: `Lean.Meta.trySynthInstance` (`SynthInstance.lean:1014-1017`)
    /// — `synthInstance?` with `isDefEqStuckExceptionId` caught and
    /// reported as `.undef`.
    ///
    /// The `.undef` is DYNAMIC: `synth_instance` runs its search under
    /// `with_new_mctx_depth` with `is_def_eq_stuck_ex` set
    /// (`synth_instance_main`), so the caller's mvars are read-only and
    /// a candidate that needs one assigned throws
    /// `MetaError::IsDefEqStuck` (the read-only arms in
    /// `assign.rs`/`level.rs`). That replaced a syntactic pre-test that
    /// over-approximated: an all-polymorphic candidate set (`Any ?a`,
    /// `tc/useAnyHole`) and a class with zero candidates (`NoInst ?a`,
    /// `noInstMVar/synth/0`) both answer here, as in the oracle.
    /// Out-param mvars never get stuck: `preprocess_out_param` replaces
    /// them before the search and `assign_out_params` assigns them after
    /// it, at the caller's depth.
    ///
    /// LEVEL mvars cannot make it stuck: `allow_level_assignments =
    /// true` (`:978`) keeps the caller's level mvars assignable.
    pub fn try_synth_instance(&mut self, ty: ExprId) -> Result<LOption<ExprId>, MetaError> {
        // oracle: `let type ← instantiateMVars type` (:967).
        let ty = self.instantiate_mvars(ty)?;
        match self.synth_instance(ty) {
            Ok(Some(val)) => Ok(LOption::Some(val)),
            Ok(None) => Ok(LOption::None),
            Err(MetaError::IsDefEqStuck) => Ok(LOption::Undef),
            Err(e) => Err(e),
        }
    }
```

Before deleting `has_mvar_outside_out_params`, run `grep -rn "has_mvar_outside_out_params\|get_out_param_positions" crates --include=*.rs`. Delete the method. Keep `get_out_param_positions` if anything else still calls it; if nothing does, delete it too. Fix the `leanr_elab/src/lib.rs:68` doc bullet and any other doc hit so it describes the dynamic path in one or two sentences (no history essay). Leave `crates/leanr_elab/src/synthetic/ladder.rs`'s call alone; it consumes `LOption` and needs no change.

- [ ] **Step 6: Update `try_synth_instance_is_three_valued_and_positional`**

Rename it to `try_synth_instance_is_three_valued`. Change its doc's first sentence to: "`try_synth_instance` — the oracle's `trySynthInstance` (`SynthInstance.lean:1014-1017`) over `Instances.olean`." Replace "an mvar in a NON-output position postpones (`Get N ?i ?e` — the `GetElem` worked example depends on this)" with "an mvar in a NON-output position postpones (`Get N ?i ?e`: `instGetN`'s `Get N N N` meets the read-only `?i` and the search throws `IsDefEqStuck` — the `GetElem` worked example depends on this)". The assertions stay unchanged.

- [ ] **Step 7: Run everything; confirm green**

Run: `cargo test --workspace 2>&1 | grep -E "^test result|FAILED|panicked" | sort | uniq -c`
Expected: all PASS. In particular these must stay green with the pre-test gone (they are the evidence the dynamic path REPLACES it): `bare_typeclass_application_is_reported_stuck` (`useWrap`), `try_synth_instance_is_three_valued` (`Get N ?i ?e` → `Undef`), every `GetElem`/`pairW`/`coe` postponement row in the elab and op corpora. A failure here goes to Task 4's triage table. Do not edit expectations to match.

- [ ] **Step 8: Mutations**

| Mutation | Must fail |
|---|---|
| (1) restore the pre-test (`if self.has_mvar_outside_out_params(ty) { return Ok(LOption::Undef); }`, temporarily re-adding the method from `git show HEAD:crates/leanr_meta/src/synth.rs`) | `no_inst_mvar_goal_is_none_not_undef`, `oracle_elab_gate` (`tc/useAnyHole`), `hole_against_a_class_without_instances_is_a_synthesis_failure` |
| (2) drop `self.cfg.is_def_eq_stuck_ex = true` (Task 1's line) | `bare_typeclass_application_is_reported_stuck`, `try_synth_instance_is_three_valued` (`Get N ?i ?e`), plus whichever corpus rows depend on postponement. List them. |
| (3) map `IsDefEqStuck` to `LOption::None` instead of `Undef` | `bare_typeclass_application_is_reported_stuck` |

Revert each. Record the outcomes.

- [ ] **Step 9: Format, lint and commit**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/leanr_meta crates/leanr_elab tests/fixtures/meta/dump_synth.lean tests/fixtures/meta/synth-queries.jsonl tests/fixtures/elab/Elab0.lean tests/fixtures/elab/Elab0.olean tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -m "leanr_meta: try_synth_instance reads IsDefEqStuck dynamically; drop the syntactic pre-test"
```

---

### Task 4: Full gate, neighbour triage, housekeeping, PR

**Files:**
- Modify: `docs/superpowers/specs/2026-10-02-synth-real-depth-design.md` (§ Landed).
- Modify: `docs/superpowers/specs/2026-10-02-synth-pi-goals-design.md` (§ Landed, the Prod/Option bullet ≈:386-397, and the "Synthesis onto real depth" follow-up ≈:377).
- Modify: `docs/superpowers/specs/2026-10-01-macro-expansion-binop-design.md` (§ Landed P1 open follow-ups ≈:557-558).
- Possibly modify (only if triage forces it): `crates/leanr_meta/src/discr_tree.rs` / `discr_path.rs`.

**Interfaces:**
- Consumes: Tasks 1–3.
- Produces: a pushed branch and a PR.

- [ ] **Step 1: Run the full CI gate, blocking, in-turn**

```bash
mise run ci > /workspace/target/ci-synth-real-depth.log 2>&1; echo "CI_EXIT=$?"
tail -60 /workspace/target/ci-synth-real-depth.log
```

Expected: `CI_EXIT=0`. Do NOT background this and end the turn.

- [ ] **Step 2: Triage every failure, one at a time** (skip if `CI_EXIT=0` and Tasks 1–3 recorded no open failures)

For each failing row or test, reproduce it alone and probe the oracle on the same source (prelude + the fixture, as in Global Constraints). Then classify:

| Symptom | Classification | Action |
|---|---|---|
| leanr errors `IsDefEqStuck`/`StuckSyntheticMVar`; the oracle answers; the stuck mvar is a synthetic INSTANCE mvar the oracle would synthesize via `synthPending` | `unstuckMVar` forced (`ExprDefEq.lean:1985-2025`) | STOP. Report to the controller: per the spec, tasks 1–3 ship as PR 1 and `unstuckMVar` + `isDefEqOnFailure` become PR 2 with a spec addendum. Do not start porting it. |
| leanr returns a candidate or `None`; the oracle reports stuck/postpones; the goal has a reducible/matcher/recursor head applied to mvars | DiscrTree stuck cases forced (`DiscrTree/Main.lean:359-386`) | Port in this PR as a Task 4a: write the failing row/test first, port the `isDefEqStuckEx && e.hasExprMVar` throw for reducible heads (`:359-371`) and matcher/recursor heads (`:381-386`) exactly, run the mutation (delete the throw → the row fails), commit. |
| anything else | not forced | Record it in § Landed as a named seam with an owner. Do not widen the slice. |

- [ ] **Step 3: Correct the synth pi-goals spec**

In `2026-10-02-synth-pi-goals-design.md` § Landed, replace the Prod/Option bullet (the one starting "pi-subgoal rows):** `(inferInstance : Inhabited (Prod Nat Nat))`" through "Not root-caused in this slice.") with:

```markdown
  pi-subgoal rows):** ~~`Inhabited (Prod Nat Nat)`, `BEq (Prod Nat Nat)`
  and `BEq (Option Nat)` fail in leanr while the oracle answers.~~ NOT A
  BUG (corrected 2026-10-02, synth-real-depth spec § Housekeeping):
  `instInhabitedProd`, `instBEqProd` and `Option.instBEq` are not in
  `ElabOp.olean`, and the oracle on ElabOp (prelude + `import ElabOp`)
  fails all three too. The recorded answers came from stock Init.
```

(Keep the bullet's opening words as they are; replace only the claim.) Mark the "Synthesis onto real depth." follow-up line with `CLOSED by synth-real-depth (\`2026-10-02-synth-real-depth-design.md\`).`

- [ ] **Step 4: Close the macro/binop% follow-up**

In `2026-10-01-macro-expansion-binop-design.md` § Landed P1 "Open follow-ups", append to the "Synthesis onto real depth + `isDefEqStuckEx`" bullet: ` CLOSED by synth-real-depth (\`2026-10-02-synth-real-depth-design.md\`).`

- [ ] **Step 5: Fill in § Landed of the synth-real-depth spec**

Replace `(Filled in at merge: corrections, mutations run, seams left.)` with: the commit list (`git log --oneline main..HEAD`); every mutation from Tasks 1–3 with killed/survived; every citation corrected along the way; the triage outcome (which neighbours were forced, or "none"); corpus counts (synth compared 37 → 39, elab floor 345 → 346, op floor 99 unchanged); remaining open seams (`unstuckMVar`, the DiscrTree stuck cases unless ported, nondep R9, the synthesis cache, `checkMayHaveSideEffects`/`check result`, inner-scope declarations persisting with an inner depth stamp).

- [ ] **Step 6: Sweep the branch for citation drift**

```bash
git diff main..HEAD | grep -oE "[A-Za-z/]+\.lean:[0-9]+(-[0-9]+)?" | sort -u
```

Open each one against the pinned source and fix any that is off. Commit the docs:

```bash
cargo fmt --all
git add docs/ crates/
git commit -m "docs: synth-real-depth landed; close real-depth follow-ups; correct Prod/Option note"
```

- [ ] **Step 7: Re-run CI, push, open the PR**

```bash
mise run ci > /workspace/target/ci-synth-real-depth.log 2>&1; echo "CI_EXIT=$?"
git -c credential.https://github.com.helper= -c "credential.https://github.com.helper=!$(which gh) auth git-credential" push -u origin synth-real-depth
gh pr create --title "leanr_meta: synthesis onto real mctx depth + isDefEqStuckEx" --body-file <(cat <<'EOF'
Moves typeclass synthesis off its checkpoint/rollback stand-in and onto the real mctx-depth model (#59).

- The search runs under `with_new_mctx_depth(true, ..)` with `is_def_eq_stuck_ex`. The table-key and AbstractMVars walks treat lower-depth mvars as constants, as the oracle does.
- `synth_pending` catches `IsDefEqStuck`, as `SynthInstance.lean:1052` does.
- `try_synth_instance` is now a one-to-one port of `trySynthInstance`. The syntactic pre-test is gone.
- Oracle rows: `tc/useAnyHole` (residue 2) and `noInstMVar/synth/0` (residue 3). Synth0's `mvarGoal/synth/0` seam exclusion is closed.

Spec: docs/superpowers/specs/2026-10-02-synth-real-depth-design.md (see § Landed).
EOF
)
```

Then follow the standing merge workflow: wait for green CI on the PR, verify, merge, and delete the branch.
