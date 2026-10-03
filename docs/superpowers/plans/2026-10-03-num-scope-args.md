# `numScopeArgs` + `processConstApprox` prefix search — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Port the oracle's `MetavarDecl.numScopeArgs` and the two constant-approximation gates that read it, plus `processConstApprox`'s longest-prefix search, so leanr elaborates the scope-mvar terms the oracle accepts.

**Architecture:** `leanr_meta` only. `MVarDecl` gains `num_scope_args`. `mk_aux_mvar_at` takes it as a parameter. `elim_mvar` and the ctxApprox restriction produce it. `is_def_eq_mvar_self` and `process_const_approx` read it. `process_const_approx` becomes a 1:1 port of `ExprDefEq.lean:1271-1309`, with a new `instantiate_forall` helper. `leanr_elab` changes only in tests and the oracle corpus.

**Tech Stack:** Rust (workspace crates `leanr_meta`, `leanr_elab`), the pinned Lean oracle `leanprover/lean4:v4.33.0-rc1` for fixtures, mise tasks.

**Spec:** `docs/superpowers/specs/2026-10-03-num-scope-args-design.md` — read it first. § The oracle model has the oracle pseudo-code every task ports.

## Global Constraints

- Oracle pin: `leanprover/lean4:v4.33.0-rc1`. Cite oracle source from `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/Lean/` (NOT the v4.32 toolchain also present). Open every line you cite; plan/spec citations have been off by 1-2 lines before.
- Oracle probes: a scratch file under `/workspace/target/nsa-probe/` (never `/tmp`: it is a 20Gi EmptyDir and cargo builds there evict the pod), starting `prelude` / `import Elab0`, run from `/workspace` with `LEAN_PATH=tests/fixtures/elab lean <file>`.
- `leanr_meta` and `leanr_elab` source changes are limited to what the spec lists; no `leanr_elab/src` change.
- No new dependencies.
- Before every commit: `cargo fmt --all` (CI's `mise run ci` gates on `cargo fmt --check` and clippy).
- The final gate is `mise run ci`. Run it in the foreground and wait for the exit code; do not background it and end the turn.
- `mise run fixtures:regen-elab` also rewrites `elim.jsonl`/`structures.jsonl` (pre-existing drift from #65). Always `git checkout -- tests/fixtures/elab/elim.jsonl tests/fixtures/elab/structures.jsonl` after it; fixing that drift is NOT this slice.
- Every mutation listed in a task MUST actually be applied, run, and reverted. Record killed/survived, with the killing test's name, for § Landed. Do not trust this plan's prediction of which test kills it.

## Review Focus

1. **A twice-abstracted scope mvar** (a `fun` nested in a `fun`, both binders holes) must accumulate counts (`old + applied`), not reset them. Pinned by Task 1's `elim_mvar_scope_args_accumulate_across_nested_abstractions`.
2. **A genuine `let` among the reverted fvars** is not applied by `mkMVarApp`, so it must not be counted. Pinned by Task 1's `elim_mvar_does_not_count_a_skipped_let`.
3. **A `syntheticOpaque` (delayed-assigned) abstraction** must set the count too, since the oracle sets it before branching on the kind. Pinned by the assertion Task 1 adds to `elim_mvar_deps_delays_a_synthetic_opaque_metavariable`.
4. **An mvar whose args are genuine function args** (`num_scope_args == 0`, e.g. the oracle's `?m Prop =?= IO Bool` example) must still refuse constant approximation on the default profile. Pinned by Task 2's gate tests (the `n = 2` mismatch rows) and the existing `const_approx_*` tests (`n = 0`, flag off → `false`).
5. **Terms the oracle rejects must stay rejected.** Opening the gate must not turn an existing oracle-rejected smoke case into an acceptance. `synthetic_smoke.rs` `stuck_coercion_is_reported_by_the_coe_reporter_arm` and `binder_smoke.rs` `a_have_bound_variable_is_opaque_to_defeq` cover this. Task 2 Step 9 triages any movement against the oracle.

---

### Task 1: `num_scope_args` field and its producers

**Files:**
- Modify: `crates/leanr_meta/src/mvar_ctx.rs:46-60` (`MVarDecl`)
- Modify: `crates/leanr_meta/src/assign.rs:717-764` (`mk_aux_mvar`, `mk_aux_mvar_at`)
- Modify: `crates/leanr_meta/src/mk_binding.rs:265-289` (`mk_mvar_app`), `:624-712` (`elim_mvar`)
- Modify: `crates/leanr_meta/src/check_assignment.rs:329-362` (`check_mvar` restriction), `:442` (`ctx_approx_const_fun`)
- Modify (mechanical `num_scope_args: 0` / extra `0` arg): every other `MVarDecl {` literal and `mk_aux_mvar_at(` call. Exhaustive list from `grep -rn "MVarDecl {" crates/ --include=*.rs` and `grep -rn "mk_aux_mvar_at(" crates/ --include=*.rs`:
  - `crates/leanr_elab/src/elab.rs:427`
  - `crates/leanr_meta/src/mk_binding.rs:1673`
  - `crates/leanr_meta/src/infer.rs:1058`
  - `crates/leanr_meta/src/mvar_ctx.rs:324`
  - `crates/leanr_meta/src/test_support.rs:104`
  - `crates/leanr_meta/src/lazy_delta.rs:1120`
  - `crates/leanr_meta/src/assign.rs:1925`
  - `crates/leanr_meta/src/whnf.rs:3002`, `:3978`
  - `crates/leanr_meta/src/metactx.rs:2905`
  - `crates/leanr_meta/tests/oracle_synth.rs:276`, `:513`
  - `crates/leanr_meta/tests/oracle_fast.rs:179`
  - `mk_aux_mvar_at(` callers: 4 in `assign.rs`, 5 in `check_assignment.rs`, 9 in `mk_binding.rs`, 3 in `synth.rs`
- Test: `crates/leanr_meta/src/mk_binding.rs` (tests module, `use crate::test_support::{fresh_fvar, fresh_mvar, with_ctx};` at :920), `crates/leanr_meta/src/check_assignment.rs` (tests module)

**Interfaces:**
- Produces:
  - `pub struct MVarDecl { pub user_name, pub ty, pub lctx, pub kind, pub num_scope_args: usize }`
  - `pub(crate) fn mk_aux_mvar_at(&mut self, lctx: Arc<LocalCtxSnapshot>, ty: ExprId, kind: MVarKind, user_name: Option<NameId>, num_scope_args: usize) -> Result<(ExprId, MVarId), MetaError>`
  - `mk_aux_mvar(ty)` is unchanged in signature and passes `0`.
  - `fn mvar_app_skips(&self, x: ExprId, lctx: &LocalCtxSnapshot, kind: MVarKind) -> bool` (private to `mk_binding.rs`).

- [ ] **Step 1: Add the field and the parameter**

In `mvar_ctx.rs`, extend `MVarDecl`:

```rust
pub struct MVarDecl {
    pub user_name: Option<NameId>,
    pub ty: ExprId,
    pub lctx: Arc<LocalCtxSnapshot>,
    pub kind: MVarKind,
    /// oracle: `MetavarDecl.numScopeArgs` (`MetavarContext.lean:323`):
    /// how many of this mvar's arguments model a potential dependency on
    /// a binder (set by `elimMVar`, `:1208`) rather than a genuine
    /// function argument. `isDefEqMVarSelf` (`ExprDefEq.lean:1800`) and
    /// `processConstApprox` (`:1278`) allow constant approximation when
    /// it equals the argument count, even with `constApprox` off.
    pub num_scope_args: usize,
}
```

In `assign.rs`, add the parameter to `mk_aux_mvar_at` and pass it into the literal:

```rust
    pub(crate) fn mk_aux_mvar_at(
        &mut self,
        lctx: std::sync::Arc<crate::LocalCtxSnapshot>,
        ty: ExprId,
        kind: MVarKind,
        user_name: Option<leanr_kernel::bank::NameId>,
        num_scope_args: usize,
    ) -> Result<(ExprId, MVarId), MetaError> {
        // … unchanged id minting …
        self.mctx.declare(
            id,
            MVarDecl {
                user_name,
                ty,
                lctx,
                kind,
                num_scope_args,
            },
        );
```

Append to its doc comment: "`num_scope_args` is the oracle's `mkFreshExprMVarAt … numScopeArgs` (`Meta/Basic.lean:851-859`). Only `elim_mvar` and the ctxApprox restriction (`check_assignment.rs`) pass a non-zero value; every other oracle mint uses the default 0." `mk_aux_mvar` becomes `self.mk_aux_mvar_at(lctx, ty, MVarKind::Natural, None, 0)`.

- [ ] **Step 2: Fix every other construction site mechanically**

Add `num_scope_args: 0,` to every `MVarDecl {` literal in the Files list. Add a trailing `0` argument to every `mk_aux_mvar_at(` call EXCEPT `elim_mvar`'s and `check_mvar`'s restriction (Steps 5-6). Then:

Run: `cargo build -p leanr_meta -p leanr_elab --tests 2>&1 | grep -E "^error" | head`
Expected: only errors at the two sites Steps 5-6 rewrite (if you left them unfixed), or none.

- [ ] **Step 3: Write the failing `elim_mvar` tests**

In `mk_binding.rs`'s tests module, add a helper and three tests:

```rust
    /// The `num_scope_args` of the head of `?mid`'s assignment (`?new
    /// a…`), for a NON-opaque original, which `elim_mvar` assigns outright.
    fn assigned_head_scope_args(ctx: &mut MetaCtx, mid: crate::MVarId) -> usize {
        let assigned = ctx
            .mctx()
            .assignment(mid)
            .expect("a non-opaque original is assigned outright");
        let head = ctx.get_app_fn(assigned);
        let Node::MVar { id: Some(n) } = ctx.node(head) else {
            panic!("the assignment's head is the auxiliary metavariable");
        };
        ctx.mctx()
            .decl(crate::MVarId(n))
            .expect("declared")
            .num_scope_args
    }

    /// oracle `MetavarContext.lean:1207-1208`: the auxiliary mvar's
    /// `numScopeArgs` is the original's plus `result.getAppNumArgs`.
    /// Fresh original (0) abstracted over one fvar → 1.
    #[test]
    fn elim_mvar_counts_the_applied_reverted_fvars() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let lctx = ctx.current_lctx();
            let (m, mid) = ctx
                .mk_aux_mvar_at(lctx, sort0, crate::MVarKind::Natural, None, 0)
                .expect("mvar under the binder");
            let _ = ctx.elim_mvar_deps(&[a], m).expect("elim_mvar_deps");
            assert_eq!(assigned_head_scope_args(ctx, mid), 1);
            ctx.lctx_restore(cp);
        });
    }

    /// `mkMVarApp` (`:1093-1098`) skips a genuine let-bound fvar for a
    /// non-opaque mvar, so `getAppNumArgs` is 1, not `toRevert.size` = 2.
    #[test]
    fn elim_mvar_does_not_count_a_skipped_let() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let l = ctx.push_let_decl(None, sort0, a, false).expect("let");
            let lctx = ctx.current_lctx();
            let (m, mid) = ctx
                .mk_aux_mvar_at(lctx, sort0, crate::MVarKind::Natural, None, 0)
                .expect("mvar under the let");
            let _ = ctx.elim_mvar_deps(&[a, l], m).expect("elim_mvar_deps");
            assert_eq!(
                assigned_head_scope_args(ctx, mid),
                1,
                "the let is reverted but not applied, so it is not counted"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// A second abstraction adds to the count the first left (Review
    /// Focus 1): original at 2, abstracted over one more fvar → 3.
    #[test]
    fn elim_mvar_scope_args_accumulate_across_nested_abstractions() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let lctx = ctx.current_lctx();
            let (m, mid) = ctx
                .mk_aux_mvar_at(lctx, sort0, crate::MVarKind::Natural, None, 2)
                .expect("an already-abstracted mvar");
            let _ = ctx.elim_mvar_deps(&[a], m).expect("elim_mvar_deps");
            assert_eq!(assigned_head_scope_args(ctx, mid), 3);
            ctx.lctx_restore(cp);
        });
    }
```

In the existing `elim_mvar_deps_delays_a_synthetic_opaque_metavariable`, after `let new_id = crate::MVarId(n);`, add (Review Focus 3):

```rust
                    assert_eq!(
                        ctx.mctx().decl(new_id).expect("declared").num_scope_args,
                        1,
                        "the opaque branch sets numScopeArgs too (`:1208` runs before \
                         the kind split at `:1212`)"
                    );
```

- [ ] **Step 4: Run them to verify they fail**

Run: `cargo test -p leanr_meta --lib elim_mvar 2>&1 | tail -20`
Expected: the three new tests and the opaque test FAIL (`left: 0`).

- [ ] **Step 5: Implement the `elim_mvar` producer**

In `mk_binding.rs`, extract `mk_mvar_app`'s skip predicate and use it in both places:

```rust
    /// oracle `mkMVarApp` (`:1093-1098`): whether `x` is NOT applied.
    /// A syntheticOpaque mvar applies every fvar; otherwise a genuine
    /// let-bound fvar is skipped. `LocalDecl.isLet` is FALSE for a nondep
    /// ldecl, so a `have` is applied like a cdecl. (The oracle also skips
    /// non-fvar entries; leanr's `to_revert` holds fvars only, since
    /// `collect_forward_deps` reads lctx entries.)
    fn mvar_app_skips(&self, x: ExprId, lctx: &LocalCtxSnapshot, kind: crate::MVarKind) -> bool {
        kind != crate::MVarKind::SyntheticOpaque
            && self.fvar_id_of(x).is_some_and(|id| {
                lctx.lctx().get(id).is_some_and(|d| d.value.is_some())
                    && lctx.entry(id).is_some_and(|en| !en.nondep)
            })
    }

    pub(crate) fn mk_mvar_app(
        &mut self,
        mvar: ExprId,
        xs: &[ExprId],
        lctx: &LocalCtxSnapshot,
        kind: crate::MVarKind,
    ) -> Result<ExprId, MetaError> {
        let mut e = mvar;
        for x in xs {
            if self.mvar_app_skips(*x, lctx, kind) {
                continue;
            }
            e = self.scratch.expr_app(Some(self.view.store), e, *x)?;
        }
        Ok(e)
    }
```

In `elim_mvar`, capture the original's count next to `kind`/`decl_ty`, and mint with the sum:

```rust
        let kind = decl.kind;
        let decl_ty = decl.ty;
        let decl_scope_args = decl.num_scope_args;
        let mvar_lctx = Arc::clone(&decl.lctx);
        // …
        // oracle `:1207-1208`: `numScopeArgs := mvarDecl.numScopeArgs +
        // result.getAppNumArgs`. The count is what `mk_mvar_app` actually
        // applies, NOT `to_revert.len()`: it skips genuine lets.
        let applied = to_revert
            .iter()
            .filter(|x| !self.mvar_app_skips(**x, &mvar_lctx, kind))
            .count();
        let (new_mvar, new_id) =
            self.mk_aux_mvar_at(new_lctx, new_ty, kind, None, decl_scope_args + applied)?;
        let result = self.mk_mvar_app(new_mvar, &to_revert, &mvar_lctx, kind)?;
```

- [ ] **Step 6: Implement the ctxApprox pass-through**

In `check_assignment.rs` `check_mvar`, capture the count in the existing tuple and pass it on:

```rust
        let (inner_lctx, inner_ty, inner_kind, inner_scope_args) =
            (Arc::clone(&decl.lctx), decl.ty, decl.kind, decl.num_scope_args);
        // …
        // oracle `ExprDefEq.lean:936`: `mkAuxMVar lctx localInsts mvarType
        // mvarDecl.numScopeArgs` — the restricted mvar inherits the count.
        let (aux, _) =
            self.mk_aux_mvar_at(reduced, ty, MVarKind::Natural, None, inner_scope_args)?;
```

`ctx_approx_const_fun` (`:442`) passes `0`, with the comment `// oracle :978 passes no numScopeArgs (default 0).` Open `ExprDefEq.lean` and correct `:978` to the line holding `mkAuxMVar ctx.mvarDecl.lctx` if it differs.

- [ ] **Step 7: Write the failing ctxApprox test**

In `check_assignment.rs`'s tests, add:

```rust
    /// oracle `ExprDefEq.lean:936`: the restricted aux mvar inherits the
    /// inner mvar's `numScopeArgs`.
    #[test]
    fn check_mvar_restriction_inherits_num_scope_args() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let _x = fresh_fvar(ctx, n, "x");
            let lctx = ctx.current_lctx();
            let (i, _iid) = ctx
                .mk_aux_mvar_at(lctx, n, MVarKind::Natural, None, 3)
                .expect("inner");
            let out = ctx.check_assignment_aux(oid, &[], false, i).expect("check");
            let aux = out.expect("restricted, not refused");
            assert_eq!(
                ctx.mctx.decl(mvar_id(ctx, aux)).unwrap().num_scope_args,
                3
            );
            ctx.lctx_restore(cp);
        });
    }
```

Run: `cargo test -p leanr_meta --lib check_mvar_restriction_inherits 2>&1 | tail -5` with Step 6 temporarily reverted to `0` → FAIL; with Step 6 → PASS.

- [ ] **Step 8: Run the crate's tests**

Run: `cargo test -p leanr_meta 2>&1 | grep -E "test result|FAILED|panicked" | head -20`
Expected: all pass. The count does nothing observable yet, since no gate reads it.

- [ ] **Step 9: Mutations 1-3**

Apply each mutation, run `cargo test -p leanr_meta --lib 2>&1 | grep -E "FAILED|test result"`, record the result, and revert:
1. `elim_mvar`: `decl_scope_args + applied` → `applied`. Expect `elim_mvar_scope_args_accumulate_across_nested_abstractions` to fail.
2. `elim_mvar`: `applied` → `to_revert.len()`. Expect `elim_mvar_does_not_count_a_skipped_let` to fail.
3. `check_mvar`: `inner_scope_args` → `0`. Expect `check_mvar_restriction_inherits_num_scope_args` to fail.

- [ ] **Step 10: Commit**

```bash
cargo fmt --all
git add -A crates/
git commit -m "leanr_meta: MVarDecl.num_scope_args, set by elimMVar and the ctxApprox restriction"
```

---

### Task 2: the two gates read `num_scope_args`, plus the gate corpus rows

**Files:**
- Modify: `crates/leanr_meta/src/assign.rs:226-268` (`is_def_eq_mvar_self`), `:533-567` (`process_const_approx`)
- Test: `crates/leanr_meta/src/assign.rs` tests (next to `const_approx_gates_is_def_eq_mvar_self_fallback`, ~:1703)
- Modify: `tests/fixtures/elab/dump_elab.lean` (new `nsaQueries` list, the main `queries` concatenation at ~:1414, and the stale comments at ~:976-980 and ~:1007-1011)
- Regenerate: `tests/fixtures/elab/elab-queries.jsonl`
- Modify: `crates/leanr_elab/tests/oracle_elab.rs:72` (`CORPUS_FLOOR`)

**Interfaces:**
- Consumes: `MVarDecl::num_scope_args`, and `mk_aux_mvar_at(…, num_scope_args)` from Task 1.
- Produces: `process_const_approx(&mut self, mvar: ExprId, args: &[ExprId], pattern_var_prefix: usize, v: ExprId) -> Result<bool, MetaError>`, still going straight to `assign_const` after the gate. Task 3 replaces its body.

- [ ] **Step 1: Write the failing gate tests**

In `assign.rs`'s tests module (it already has `with_n_ctx_cfg`, `n_type`, `mk_const`, `mk_app`, `mk_forall`, `fresh_fvar`), add:

```rust
    /// An mvar minted at the EMPTY context with the given `num_scope_args`.
    fn fresh_scoped_mvar(ctx: &mut MetaCtx, ty: ExprId, n: usize) -> (ExprId, MVarId) {
        ctx.mk_aux_mvar_at(crate::LocalCtxSnapshot::empty(), ty, MVarKind::Natural, None, n)
            .expect("mvar")
    }

    /// oracle `processConstApprox` gate (`ExprDefEq.lean:1278`), default
    /// profile (`const_approx` off): `?m N.zero =?= N.succ` with `?m : Sort
    /// 0 -> Sort 0` is solved by constant approximation iff
    /// `numScopeArgs == 1` (the arg count).
    #[test]
    fn num_scope_args_gates_process_const_approx_on_the_default_profile() {
        for (n, expected) in [(1, true), (2, false), (0, false)] {
            with_n_ctx_cfg(Config::default(), |ctx| {
                let s0 = n_type(ctx);
                let mvar_ty = mk_forall(ctx, s0, s0);
                let (m_expr, m_id) = fresh_scoped_mvar(ctx, mvar_ty, n);
                let zero = mk_const(ctx, "N.zero");
                let succ = mk_const(ctx, "N.succ");
                let lhs = mk_app(ctx, m_expr, zero);
                assert_eq!(ctx.is_def_eq(lhs, succ).unwrap(), expected, "n={n}");
                assert_eq!(ctx.mctx.is_assigned(m_id), expected, "n={n}");
            });
        }
    }

    /// oracle `isDefEqMVarSelf` gate (`ExprDefEq.lean:1800`), default
    /// profile: `?m a =?= ?m b` (distinct `Sort 1` fvars, so pairwise
    /// unification fails; see `const_approx_gates_is_def_eq_mvar_self_fallback`
    /// for why `Sort 1`) falls back to constant approximation iff
    /// `numScopeArgs == 1`.
    #[test]
    fn num_scope_args_gates_is_def_eq_mvar_self_on_the_default_profile() {
        for (n, expected) in [(1, true), (2, false), (0, false)] {
            with_n_ctx_cfg(Config::default(), |ctx| {
                let z = ctx.scratch.level_zero(None).unwrap();
                let one = ctx.scratch.level_succ(None, z).unwrap();
                let sort1 = ctx.scratch.expr_sort(None, one).unwrap();
                let mvar_ty = mk_forall(ctx, sort1, sort1);
                let (m_expr, m_id) = fresh_scoped_mvar(ctx, mvar_ty, n);
                let a = fresh_fvar(ctx, sort1, "a");
                let b = fresh_fvar(ctx, sort1, "b");
                let lhs = mk_app(ctx, m_expr, a);
                let rhs = mk_app(ctx, m_expr, b);
                assert_eq!(ctx.is_def_eq(lhs, rhs).unwrap(), expected, "n={n}");
                assert_eq!(ctx.mctx.is_assigned(m_id), expected, "n={n}");
            });
        }
    }
```

- [ ] **Step 2: Run them to verify they fail**

Run: `cargo test -p leanr_meta --lib num_scope_args_gates 2>&1 | tail -10`
Expected: both FAIL at `n=1` (`left: false, right: true`).

- [ ] **Step 3: Implement gate 1**

In `is_def_eq_mvar_self`, replace the comment block and `if !self.cfg.const_approx { return Ok(false); }` (~:244-255) with:

```rust
        // oracle :1799-1800: `if mvarDecl.numScopeArgs == args₁.size ||
        // cfg.constApprox`. `num_scope_args` counts the args that model a
        // binder dependency (`elim_mvar`, mk_binding.rs).
        let num_scope_args = self.mctx.decl(mvar_id).map_or(0, |d| d.num_scope_args);
        if num_scope_args != args1.len() && !self.cfg.const_approx {
            return Ok(false);
        }
```

- [ ] **Step 4: Implement gate 2 (count check only)**

Replace `process_const_approx`'s doc and body (~:533-567) with the interim version below. Task 3 adds the prefix search:

```rust
    /// oracle: `processConstApprox` (ExprDefEq.lean:1271-1309). Gate
    /// (:1278): `numScopeArgs != numArgs && !cfg.constApprox` → `false`.
    /// The `patternVarPrefix > 0` search (:1282-1309) is Task 3 of the
    /// numScopeArgs plan; until then every caller goes to `defaultCase`.
    fn process_const_approx(
        &mut self,
        mvar: ExprId,
        args: &[ExprId],
        _pattern_var_prefix: usize,
        v: ExprId,
    ) -> Result<bool, MetaError> {
        let Node::MVar { id: Some(id) } = self.node(mvar) else {
            return Ok(false);
        };
        let num_scope_args = self.mctx.decl(MVarId(id)).map_or(0, |d| d.num_scope_args);
        if num_scope_args != args.len() && !self.cfg.const_approx {
            return Ok(false);
        }
        self.assign_const(mvar, args.len(), v)
    }
```

Also update `process_assignment`'s doc (~:357-367). It claims every `use_fo_approx` call returns `Ok(false)` on the default profile; that is no longer true. Replace the claim with: "on the default profile `use_fo_approx` can now succeed through `process_const_approx` when the mvar's `num_scope_args` equals the arg count".

- [ ] **Step 5: Run the gate tests and the crate**

Run: `cargo test -p leanr_meta 2>&1 | grep -E "test result|FAILED|panicked" | head -20`
Expected: the new tests pass. If an existing test fails, it is the gate firing for a scope mvar. Read the test, decide from the oracle model whether the new answer is the oracle's, and fix the test's expectation only with a citation in its doc comment.

- [ ] **Step 6: Add the gate corpus rows**

In `tests/fixtures/elab/dump_elab.lean`, add after `levelInstQueries`' definition:

```lean
/-- numScopeArgs slice (`docs/superpowers/specs/2026-10-03-num-scope-args-design.md`).
Each binder-type hole's body-type mvar is abstracted by `elimMVar`, which
sets the aux mvar's `numScopeArgs` (`MetavarContext.lean:1208`); the
application then needs constant approximation through the
`numScopeArgs == args.size` gate (`ExprDefEq.lean:1278`, `:1800`).
Probed on the pin 2026-10-03 with `#check` (all accepted). -/
def nsaQueries : List (String × String) :=
  [ ("nsa/two-binders-snd",          "(fun x y => y) Nat.zero Nat.zero")
  , ("nsa/two-binders-fst",          "(fun x y => x) Nat.zero Nat.zero")
  , ("nsa/fn-after-annotated",       "(fun (x : Nat) f => f) Nat.zero Nat.succ")
  -- Dropped in M4b-4a P2 for this gap (P2 § Landed).
  , ("p2/app-fn-after-lval",         "(fun x f => f x.1) (Prod.mk Nat.zero Nat.zero) Nat.succ")
  , ("nsa/lval-after-fn-binder",     "(fun f x => Nat.succ x.1) Nat.succ (Prod.mk Nat.zero Nat.zero)")
  -- `p2/lval-two-binders`'s source before P2 annotated `y` to dodge this gap.
  , ("p2/lval-two-binders-holes",    "(fun x y => Prod.mk x.2 y.1) (Prod.mk Nat.zero Nat.zero) (Prod.mk Nat.zero Nat.zero)")
  -- `?w Nat.zero Nat.zero =?= Eq Nat.zero Nat.zero`: first-order
  -- approximation wins before constant approximation (`useFOApprox`,
  -- :1319-1320), giving `(w : Eq x y)`.
  , ("nsa/fo-before-const",          "(fun x y w => w) Nat.zero Nat.zero (Eq.refl Nat.zero)")
  -- `n` is in `?w`'s own lctx, so `processAssignment` stops at arg 0
  -- (:1322-1323): pattern prefix 0 → `defaultCase`, giving `(w : Eq n n)`.
  , ("nsa/in-lctx-arg-default-case", "fun (n : Nat) => (fun x y w => w) n Nat.zero (Eq.refl n)")
  ]
```

Append `++ nsaQueries` after `++ elimQueries` in `main`'s `queries` concatenation (~:1414).

Fix the stale comments. In the `p2Queries` comment above `p2/lval-in-arg` (~:976-980), replace "with both binder types holes leanr fails `(fun x y => y) Nat.zero Nat.zero` too (a pre-existing gap on `y`'s `?Y x` type, not P2's)" with "the both-holes form is `nsaQueries`' `p2/lval-two-binders-holes`". Replace the trailing "Not recorded: …" comment (~:1007-1011) with "`(fun x f => f x.1) …` is recorded in `nsaQueries` (`p2/app-fn-after-lval`)."

- [ ] **Step 7: Regenerate the corpus**

```bash
mise run fixtures:regen-elab 2>&1 | grep -i "dump_elab:" ; \
git checkout -- tests/fixtures/elab/elim.jsonl tests/fixtures/elab/structures.jsonl ; \
git diff --stat tests/fixtures/elab/
```

Expected: no `dump_elab: … failed` / parse-error lines on stderr for any `nsa/*` or `p2/*` id. `elab-queries.jsonl` grows by exactly 8 lines (`git diff tests/fixtures/elab/elab-queries.jsonl | grep -c '^+{'` → 8) and changes no existing line (`grep -c '^-{'` → 0). If the dumper drops a row, read its stderr message and probe the term with `#check` (Global Constraints); a row the oracle rejects does not belong in this success corpus.

- [ ] **Step 8: Run the corpus gate; bump the floor**

In `oracle_elab.rs`, add a history line and bump the floor:

```rust
    // 350 -> 358 (numScopeArgs task 2): the 6 nsa/* gate records,
    // p2/app-fn-after-lval and p2/lval-two-binders-holes.
    const CORPUS_FLOOR: usize = 358;
```

Run: `cargo test -p leanr_elab --test oracle_elab 2>&1 | tail -15`
Expected: PASS. If an `nsa/*` record differs, print leanr's term against `exp` (the harness's failure message) and debug with superpowers:systematic-debugging. The spec's oracle model is the reference.

- [ ] **Step 9: Triage smoke-test movement**

Run: `cargo test -p leanr_elab 2>&1 | grep -E "test result|FAILED|panicked" | head -30`

For each newly failing test, BEFORE touching it, probe its source on the oracle (scratch file per Global Constraints, `#check <src>`).
- If the oracle now agrees with leanr's NEW behaviour, the old expectation encoded the gap (the #65 lesson). Update the expectation and say so in its doc comment, quoting the oracle's output.
- If the oracle disagrees, it is a regression. Stop and debug; do not edit the test.

Review Focus 5's two named tests must still pass unchanged.

- [ ] **Step 10: Mutations 4-5**

Apply each mutation, run `cargo test -p leanr_meta --lib num_scope_args_gates` plus `cargo test -p leanr_elab --test oracle_elab`, record the result, and revert:
4a. Gate 1 condition → never refuse (delete the `if`). 4b. Gate 1 → always refuse (`return Ok(false)` unconditionally when `!const_approx`).
5a. Gate 2 → never refuse. 5b. Gate 2 → always refuse when `!const_approx`.
5b must also turn the `nsa/*` corpus rows red.

- [ ] **Step 11: Commit**

```bash
cargo fmt --all
git add -A crates/ tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -m "leanr_meta: numScopeArgs opens the constApprox gates (isDefEqMVarSelf, processConstApprox)"
```

---

### Task 3: `instantiate_forall` and `processConstApprox`'s longest-prefix search

**Files:**
- Modify: `crates/leanr_meta/src/assign.rs` (`process_const_approx`; add `process_const_approx_prefix` and `instantiate_forall` next to `forall_bounded_telescope`, ~:635)
- Test: `crates/leanr_meta/src/assign.rs` tests
- Modify: `tests/fixtures/elab/dump_elab.lean` (`nsaQueries`), regenerate `elab-queries.jsonl`, `crates/leanr_elab/tests/oracle_elab.rs` floor

**Interfaces:**
- Consumes: Task 2's gated `process_const_approx`. Existing: `assign_const(mvar, num_args, v)`, `forall_bounded_telescope(ty, n) -> Result<Vec<ExprId>, _>` (returns FEWER on a short spine, and pushes local decls: callers bracket with `lctx_checkpoint`/`lctx_restore`), `mk_lambda_fvars_with_let_deps(xs, v) -> Result<Option<ExprId>, _>`, `check_assignment(mvar_id, fvars, v) -> Result<Option<ExprId>, _>`, `check_types_and_assign(mvar, v) -> Result<bool, _>`, `MetaCtx::is_type_correct(e) -> Result<bool, _>` (`check.rs:40`), `whnf(e)`, `leanr_kernel::instantiate(st, base, e, sub, guard)`.
- Produces: `pub(crate) fn instantiate_forall(&mut self, ty: ExprId, ps: &[ExprId]) -> Result<ExprId, MetaError>`.

- [ ] **Step 1: Write the failing `instantiate_forall` tests**

```rust
    /// oracle `instantiateForall` (`Meta/Basic.lean:2142-2153`) whnf's
    /// before each binder: `(fun _ => Sort 0 -> Sort 0) N.zero` is a
    /// beta-redex whose whnf is a pi.
    #[test]
    fn instantiate_forall_whnfs_to_find_the_binder() {
        with_n_ctx(|ctx| {
            let s0 = n_type(ctx);
            let pi = mk_forall(ctx, s0, s0);
            let lam = ctx
                .scratch
                .expr_lam(Some(ctx.view.store), None, s0, pi, leanr_kernel::BinderInfo::Default)
                .expect("lam");
            let zero = mk_const(ctx, "N.zero");
            let redex = mk_app(ctx, lam, zero);
            assert_eq!(ctx.instantiate_forall(redex, &[zero]).unwrap(), s0);
        });
    }

    /// Too many parameters is an error (`throwError "invalid
    /// instantiateForall, too many parameters"`), not a panic.
    #[test]
    fn instantiate_forall_rejects_too_many_parameters() {
        with_n_ctx(|ctx| {
            let s0 = n_type(ctx);
            let zero = mk_const(ctx, "N.zero");
            assert!(matches!(
                ctx.instantiate_forall(s0, &[zero]),
                Err(MetaError::Infer(_))
            ));
        });
    }
```

Run: `cargo test -p leanr_meta --lib instantiate_forall 2>&1 | tail -5`. Expected: compile error, no method `instantiate_forall`.

- [ ] **Step 2: Implement `instantiate_forall`**

Next to `forall_bounded_telescope`:

```rust
    /// oracle: `instantiateForall` (`Meta/Basic.lean:2142-2153`): for each
    /// `p`, `whnf` the type, require a `forallE`, and `instantiate1` its
    /// body with `p`.
    pub(crate) fn instantiate_forall(
        &mut self,
        ty: ExprId,
        ps: &[ExprId],
    ) -> Result<ExprId, MetaError> {
        let mut e = ty;
        for &p in ps {
            let t = self.whnf(e)?;
            let Node::Forall { body, .. } = self.node(t) else {
                return Err(MetaError::Infer(
                    "invalid instantiateForall, too many parameters".into(),
                ));
            };
            e = leanr_kernel::instantiate(
                self.scratch,
                Some(self.view.store),
                body,
                p,
                &mut self.guard,
            )?;
        }
        Ok(e)
    }
```

Run Step 1's tests → PASS.

- [ ] **Step 3: Write the failing prefix-search tests**

```rust
    /// oracle `processConstApprox` (`ExprDefEq.lean:1282-1309`), default
    /// profile: `?m a N.zero =?= N.f a`, `?m : Sort 0 -> Sort 0 -> Sort 0`
    /// minted at the EMPTY context with `numScopeArgs = 2`, `a` an ambient
    /// fvar. `a` is out of `?m`'s scope, so `processAssignment` reaches
    /// `N.zero` (arg 1) and calls `processConstApprox` with prefix 1. The
    /// prefix search assigns `?m := fun x _ => N.f x`. `defaultCase` alone
    /// would fail: `a` escapes `fun _ _ => N.f a`.
    #[test]
    fn prefix_search_abstracts_an_out_of_scope_pattern_prefix() {
        with_n_ctx_cfg(Config::default(), |ctx| {
            let s0 = n_type(ctx);
            let s0_s0 = mk_forall(ctx, s0, s0);
            let mvar_ty = mk_forall(ctx, s0, s0_s0);
            let (m, m_id) = fresh_scoped_mvar(ctx, mvar_ty, 2);
            let a = fresh_fvar(ctx, s0, "a");
            let zero = mk_const(ctx, "N.zero");
            let succ = mk_const(ctx, "N.succ");
            let f = mk_const(ctx, "N.f");
            let m_a = mk_app(ctx, m, a);
            let lhs = mk_app(ctx, m_a, zero);
            let rhs = mk_app(ctx, f, a);
            assert!(ctx.is_def_eq(lhs, rhs).unwrap());
            assert!(ctx.mctx.is_assigned(m_id));
            // `?m N.zero N.succ` ⇒ `N.f N.zero`: the first arg is abstracted.
            let m_z = mk_app(ctx, m, zero);
            let probe = mk_app(ctx, m_z, succ);
            let inst = ctx.instantiate_mvars(probe).unwrap();
            let got = ctx.head_beta(inst).unwrap();
            let want = mk_app(ctx, f, zero);
            assert_eq!(got, want);
        });
    }

    /// The prefix branch is tried BEFORE `defaultCase` and they disagree.
    /// `quasi_pattern_approx` on lets an fvar IN `?m`'s own lctx stay in
    /// the pattern prefix (:1322-1323), which then exercises the
    /// `isTypeCorrect` arm (:1303-1306). Prefix `[a]` gives `fun x _ => N.f
    /// x`; `defaultCase` would give `fun _ _ => N.f a`.
    #[test]
    fn prefix_search_prefers_the_prefix_over_the_default_case() {
        with_n_ctx_cfg(
            Config {
                quasi_pattern_approx: true,
                ..Config::default()
            },
            |ctx| {
                let s0 = n_type(ctx);
                let s0_s0 = mk_forall(ctx, s0, s0);
                let mvar_ty = mk_forall(ctx, s0, s0_s0);
                let a = fresh_fvar(ctx, s0, "a");
                let lctx = ctx.current_lctx();
                let (m, _m_id) = ctx
                    .mk_aux_mvar_at(lctx, mvar_ty, MVarKind::Natural, None, 2)
                    .expect("mvar seeing `a`");
                let zero = mk_const(ctx, "N.zero");
                let succ = mk_const(ctx, "N.succ");
                let f = mk_const(ctx, "N.f");
                let m_a = mk_app(ctx, m, a);
                let lhs = mk_app(ctx, m_a, zero);
                let rhs = mk_app(ctx, f, a);
                assert!(ctx.is_def_eq(lhs, rhs).unwrap());
                let m_z = mk_app(ctx, m, zero);
                let probe = mk_app(ctx, m_z, succ);
                let inst = ctx.instantiate_mvars(probe).unwrap();
                let got = ctx.head_beta(inst).unwrap();
                let want = mk_app(ctx, f, zero);
                assert_eq!(got, want, "prefix [a], not defaultCase's `N.f a`");
            },
        );
    }
```

Run: `cargo test -p leanr_meta --lib prefix_search 2>&1 | tail -10`
Expected: both FAIL. The first gives `is_def_eq` false; the second gives `got = N.f a` (defaultCase).

- [ ] **Step 4: Implement the prefix search**

Replace Task 2's interim `process_const_approx` with:

```rust
    /// oracle: `processConstApprox` (ExprDefEq.lean:1271-1309).
    ///
    /// Gate (:1278): `numScopeArgs != numArgs && !cfg.constApprox` →
    /// `false`. Prefix 0 → `defaultCase` (`assignConst mvar args.size v`,
    /// :1273, always over the ORIGINAL `v`). Otherwise
    /// `process_const_approx_prefix` searches for the longest valid
    /// prefix.
    fn process_const_approx(
        &mut self,
        mvar: ExprId,
        args: &[ExprId],
        pattern_var_prefix: usize,
        v: ExprId,
    ) -> Result<bool, MetaError> {
        let Node::MVar { id: Some(id) } = self.node(mvar) else {
            return Ok(false);
        };
        let mvar_id = MVarId(id);
        let Some(decl) = self.mctx.decl(mvar_id) else {
            return Ok(false);
        };
        let (num_scope_args, mvar_ty, decl_lctx) =
            (decl.num_scope_args, decl.ty, std::sync::Arc::clone(&decl.lctx));
        if num_scope_args != args.len() && !self.cfg.const_approx {
            return Ok(false);
        }
        if pattern_var_prefix == 0 {
            return self.assign_const(mvar, args.len(), v);
        }
        let checkpoint = self.lctx_checkpoint();
        let result = self.process_const_approx_prefix(
            mvar,
            mvar_id,
            mvar_ty,
            &decl_lctx,
            args,
            pattern_var_prefix,
            v,
        );
        self.lctx_restore(checkpoint);
        result
    }

    /// oracle :1282-1309, the `patternVarPrefix > 0` branch. The oracle's
    /// `go`/`cont` recursion is tail-recursive, so it is a loop here:
    /// each failed attempt abstracts the prefix's LAST arg into `v`, pops
    /// it, and retries; an empty prefix that fails goes to `defaultCase`.
    ///
    /// No checkpoint per attempt, deliberately: the oracle's `<||>` /
    /// `<&&>` are Bool combinators with no state rollback, and the
    /// enclosing `isDefEq` checkpoint is the only one. Do not add one.
    #[allow(clippy::too_many_arguments)]
    fn process_const_approx_prefix(
        &mut self,
        mvar: ExprId,
        mvar_id: MVarId,
        mvar_ty: ExprId,
        decl_lctx: &crate::LocalCtxSnapshot,
        args: &[ExprId],
        pattern_var_prefix: usize,
        v0: ExprId,
    ) -> Result<bool, MetaError> {
        let num_args = args.len();
        let mut args_prefix: Vec<ExprId> = args[..pattern_var_prefix].to_vec();
        // :1284-1286.
        let ty = self.instantiate_forall(mvar_ty, &args_prefix)?;
        let suffix_size = num_args - args_prefix.len();
        let xs = self.forall_bounded_telescope(ty, suffix_size)?;
        if xs.len() != suffix_size {
            return self.assign_const(mvar, num_args, v0); // :1288-1289
        }
        let Some(mut v) = self.mk_lambda_fvars_with_let_deps(&xs, v0)? else {
            return self.assign_const(mvar, num_args, v0); // :1291
        };
        loop {
            // `go` (:1292-1309).
            if let Some(v_new) = self.check_assignment(mvar_id, &args_prefix, v)? {
                if let Some(v_new) = self.mk_lambda_fvars_with_let_deps(&args_prefix, v_new)? {
                    let has_ctx_local = args_prefix.iter().any(|&a| {
                        matches!(self.node(a), Node::FVar { id: Some(fid) }
                            if decl_lctx.lctx().get(fid).is_some())
                    });
                    let assigned = if has_ctx_local {
                        // :1303-1306 (discussion A2).
                        self.is_type_correct(v_new)? && self.check_types_and_assign(mvar, v_new)?
                    } else {
                        self.check_types_and_assign(mvar, v_new)? // :1308
                    };
                    if assigned {
                        return Ok(true);
                    }
                }
            }
            // `cont` (:1294-1299).
            let Some(&last) = args_prefix.last() else {
                return self.assign_const(mvar, num_args, v0);
            };
            match self.mk_lambda_fvars_with_let_deps(&[last], v)? {
                None => return self.assign_const(mvar, num_args, v0),
                Some(v2) => {
                    v = v2;
                    args_prefix.pop();
                }
            }
        }
    }
```

Open `ExprDefEq.lean:1271-1309` and correct every `:NNNN` in the comments above to the real lines.

Delete the old "STRICTLY FEWER" seam paragraph if any of it survived Task 2.

- [ ] **Step 5: Run the tests**

Run: `cargo test -p leanr_meta 2>&1 | grep -E "test result|FAILED|panicked" | head -20`
Expected: all pass, including Step 3's two tests.

- [ ] **Step 6: Add the prefix-search corpus row**

Append to `nsaQueries` in `dump_elab.lean`:

```lean
  -- `f`'s `w`-type mvar was abstracted over `x y` BEFORE `n` existed, so
  -- `n` is out of its scope: `?w n Nat.zero =?= Eq n n` has pattern
  -- prefix 1. `processConstApprox`'s prefix search (:1282-1309) assigns
  -- `?w := fun x _ => Eq x x`, giving `(w : Eq x x)`; `defaultCase` would
  -- fail (`n` escapes). Probed on the pin 2026-10-03.
  , ("nsa/let-prefix-search",        "let f := fun x y w => w; fun (n : Nat) => f n Nat.zero (Eq.refl n)")
```

Regenerate exactly as Task 2 Step 7. Expect exactly 1 new line and 0 changed lines. Bump the floor:

```rust
    // 358 -> 359 (numScopeArgs task 3): nsa/let-prefix-search.
    const CORPUS_FLOOR: usize = 359;
```

Run: `cargo test -p leanr_elab --test oracle_elab 2>&1 | tail -10` → PASS. If leanr fails the row, first check that leanr elaborates the `let` itself (`let f := fun (x y : Nat) (w : Eq x x) => w; Nat.zero` via a scratch `support::elab_and_synthesize` probe test, deleted after) before blaming the prefix search.

- [ ] **Step 7: Mutations 6-9**

Apply each mutation, run `cargo test -p leanr_meta --lib` and `cargo test -p leanr_elab --test oracle_elab`, record the result, and revert:
6. `process_const_approx`: replace the prefix branch with `return self.assign_const(mvar, args.len(), v);` (always `defaultCase`). Expect both `prefix_search_*` tests and `nsa/let-prefix-search` to fail.
7. Drop `self.is_type_correct(v_new)? &&`. Prediction: may SURVIVE. When the check fails, `cont`'s next `go` over the shorter prefix re-derives the same abstraction and assigns it without a check (the empty prefix has no ctx-local), so the outcome often matches. If it survives, try to construct a unit test where `is_type_correct` is false AND the shorter-prefix retry differs. If you cannot within reason, record it as a named seam in § Landed with this explanation.
8. `cont`: replace the `match` with `return self.assign_const(mvar, num_args, v0);` (no retry on a shorter prefix). Prediction: may survive for the same reason. Treat it as in 7.
9. `instantiate_forall`: replace `let t = self.whnf(e)?;` with `let t = e;`. Expect `instantiate_forall_whnfs_to_find_the_binder` to fail.

- [ ] **Step 8: Commit**

```bash
cargo fmt --all
git add -A crates/ tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -m "leanr_meta: processConstApprox longest-prefix search + instantiateForall"
```

---

### Task 4: doc sweep, full CI, § Landed

**Files:**
- Modify: `crates/leanr_meta/src/assign.rs` (stale comments), `docs/superpowers/specs/2026-10-03-num-scope-args-design.md` (§ Landed), `docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md` (P2 § Landed pointer)

- [ ] **Step 1: Remove the stale "no numScopeArgs / no delayed assignment" claims**

Run: `grep -rn "numScopeArgs\|num_scope_args\|delayed-assignment concept\|no analogue" crates/leanr_meta/src crates/leanr_elab/src crates/leanr_elab/tests tests/fixtures/elab/dump_elab.lean`

Every hit that says leanr lacks `numScopeArgs` or delayed assignments is now false. Known sites:
- `assign.rs` `is_def_eq_mvar`'s doc (~:94-97, "this crate's `MetavarContext` has no delayed-assignment concept at all"). Delayed assignments landed in #62. Rewrite the sentence to say `expandDelayedAssigned?` (:1706-1725) is not ported. Do NOT port it here.
- Any leftover in `is_def_eq_mvar_self` / `process_const_approx` docs.
- `crates/leanr_elab/tests/*` comments naming this gap (e.g. `oracle_op.rs`, `lval_smoke.rs`). Update or delete each.

- [ ] **Step 2: Verify every new oracle citation**

For each `:NNNN` / `File.lean:NNNN` this branch added (`git diff main -- crates/ tests/fixtures/elab/dump_elab.lean | grep -oE "[A-Za-z/]*\.lean:[0-9-]+|:[0-9]{3,4}(-[0-9]+)?"`), open the line in the v4.33.0-rc1 source and fix any that are off.

- [ ] **Step 3: Full CI**

Run (foreground; wait for it): `mise run ci; echo CI_EXIT=$?`
Expected: `CI_EXIT=0`. Fix any fmt/clippy/test failure and re-run until green.

- [ ] **Step 4: Write § Landed**

Append to the spec:

```markdown
## Landed

Commits (`git log --oneline main..HEAD`, before this docs commit):

<paste>

**Mutations.** <one line per mutation 1-9: killed by <test/row> | SURVIVED (+ why, seam)>

**Corpus.** 350 → 359: <ids>.

**Smoke-test movement.** <each test whose expectation changed, with the oracle output that justified it, or "none">.

**Spec corrections.** The § Testing candidate row
`fun (n : Nat) => (fun x y w => w) n Nat.zero (Eq.refl n)` does NOT reach
the prefix branch: `n` is in the mvar's own lctx, so `processAssignment`
stops at arg 0 (`ExprDefEq.lean:1322-1323`) and the oracle gives `(w : Eq n
n)` (`defaultCase`). Recorded as `nsa/in-lctx-arg-default-case`; the
discriminating row is `nsa/let-prefix-search`. `p2/lval-two-binders` was
kept, and its both-holes form added as `p2/lval-two-binders-holes`,
rather than swapping the source back. <any other citation fixes>.

**Open seams.** <surviving mutations; anything else found>.
```

In `2026-09-29-m4b4-dot-notation-design.md` § Landed › P2, under the bullet that says "Root cause: leanr has no `numScopeArgs` constant approximation", add: "CLOSED by the numScopeArgs slice (`2026-10-03-num-scope-args-design.md`); `p2/app-fn-after-lval` is recorded."

- [ ] **Step 5: Commit**

```bash
git add -A crates/ docs/
git commit -m "docs: numScopeArgs slice — doc sweep, citations, § Landed"
```
