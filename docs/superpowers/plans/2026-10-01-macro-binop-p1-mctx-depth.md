# Macro/binop% P1 — mctx depth + `isDefEqStuckEx` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give `leanr_meta` the oracle's metavariable-context depth model (`withNewMCtxDepth`, read-only mvars), plus `Config.isDefEqStuckEx` and `isDefEqGuarded`, with no behaviour change outside a depth scope.

**Architecture:** Depth bookkeeping lives in `MetavarContext` (`mvar_ctx.rs`). `declare`/`declare_level` stamp the current depth into side maps, so none of the ~19 `MVarDecl { .. }` literal sites change. `MetaCtx::with_new_mctx_depth` is checkpoint + `incDepth` + body + rollback, which is exactly the v4.33 oracle (it restores the whole saved mctx on exit). Every site that currently hard-codes the "single flat depth" seam calls a real predicate instead. At depth 0 each predicate returns the old answer.

**Tech Stack:** Rust (workspace crate `leanr_meta`), `cargo test`, mise tasks.

**Spec:** `docs/superpowers/specs/2026-10-01-macro-expansion-binop-design.md` § P1

## Global Constraints

- Pinned oracle `leanprover/lean4:v4.33.0-rc1`. Cite oracle source from
  `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`. (The
  v4.32 toolchain is also installed; never cite it.) Open every line
  before citing it: plan citations have been off by 1–2 lines before.
- `lean-toolchain` is not bumped. No new dependencies.
- `leanr_kernel` is untouched (TCB). Changes are confined to
  `crates/leanr_meta` plus the one-line match fix in
  `crates/leanr_meta/src/synth.rs`. `leanr_elab` must compile unchanged.
- **Invariant: no behaviour change at depth 0 with `is_def_eq_stuck_ex = false`.**
  The `leanr_meta`, synth and elab oracle corpora must stay green with
  unchanged floors. The one deliberate exception is Task 4's
  proof-irrelevance port in the both-unassignable branch, which can only
  turn a leanr `false` into the oracle's `true`.
- Run `cargo fmt --all` before every commit (CI gates on
  `cargo fmt --check` and clippy `-D warnings`).
- Build under `/workspace` only, never `/tmp` (the pod's `/tmp` is a
  20 GiB EmptyDir).
- Mutation discipline: every task's "run the mutation" step is
  mandatory. If a mutation survives, add a test that kills it before
  committing. Record each mutation result in the commit message body.

## Review Focus

1. **Error path inside a scope.** The body returns `Err`, or a `?`
   unwinds from deep inside. Depth, `level_assign_depth`, assignments
   and `postponed` must all be restored. (Task 1 pins this with an
   `Err`-returning body.)
2. **Transient defeq cache across the scope boundary.** A
   read-only-induced `false` cached inside the scope must never answer
   the same query outside it. (Task 1 clears the transient cache on
   entry and exit; Task 2 adds a test that runs the same query inside
   and then outside.)
3. **`is_def_eq_guarded` swallowing resource exhaustion.** The oracle's
   `try … catch _` does not catch runtime exceptions (`Core.tryCatch`
   rethrows them). `DepthBudgetExhausted`, `StepBudgetExhausted` and
   `Kernel(BankExhausted)` must propagate. (Task 4 tests each one.)
4. **Undeclared or anonymous mvars.** An undeclared expression mvar is
   read-only. An undeclared level mvar counts as depth 0. An anonymous
   level mvar keeps today's `undef`. None of them may panic. (Tasks 1
   and 3.)
5. **Nested scopes.** `with_new_mctx_depth` inside `with_new_mctx_depth`
   restores to the intermediate depth, not to 0. (Task 1.)

---

## File structure

| File | Change |
|---|---|
| `crates/leanr_meta/src/mvar_ctx.rs` | depth fields, depth side maps, `inc_depth`, predicates |
| `crates/leanr_meta/src/metactx.rs` | `with_new_mctx_depth`, `with_def_eq_stuck_ex`, `is_def_eq_guarded` |
| `crates/leanr_meta/src/assign.rs` | `unassigned_mvar_id` depth gate; both-unassignable branch (proof irrel + stuck); module-doc seam paragraph → citations |
| `crates/leanr_meta/src/lazy_delta.rs` | `is_def_eq_singleton` assignability gains the depth half |
| `crates/leanr_meta/src/check.rs` | `ensure_type` assignability gains the depth half |
| `crates/leanr_meta/src/level.rs` | `solve` read-only + greater-depth arms, `dec_level`, `has_assignable_level_mvar`, stuck tail; module-doc seams → citations |
| `crates/leanr_meta/src/config.rs` | `is_def_eq_stuck_ex` field, size assertion 16 → 17 |
| `crates/leanr_meta/src/error.rs` | `IsDefEqStuck(ExprId)` → unit `IsDefEqStuck` |
| `crates/leanr_meta/src/synth.rs` | match arm `IsDefEqStuck(_)` → `IsDefEqStuck` |
| `docs/superpowers/specs/2026-10-01-macro-expansion-binop-design.md` | § Landed › P1 |

---

### Task 1: Depth bookkeeping + `with_new_mctx_depth`

**Files:**
- Modify: `crates/leanr_meta/src/mvar_ctx.rs` (struct `MetavarContext` at `:85-92`; `declare` at `:100`; `declare_level` at `:149`)
- Modify: `crates/leanr_meta/src/metactx.rs` (add next to `with_full_approx_def_eq`, `:522`)
- Test: `crates/leanr_meta/src/metactx.rs` `mod tests`

**Interfaces:**
- Produces, on `MetavarContext`:
  - `pub fn depth(&self) -> u32`
  - `pub fn level_assign_depth(&self) -> u32`
  - `pub fn expr_mvar_depth(&self, id: MVarId) -> Option<u32>`
  - `pub fn level_mvar_depth(&self, id: LMVarId) -> u32` (0 if undeclared)
  - `pub fn is_read_only(&self, id: MVarId) -> bool` (undeclared → `true`)
  - `pub fn is_level_mvar_read_only(&self, id: LMVarId) -> bool`
  - `pub(crate) fn inc_depth(&mut self, allow_level_assignments: bool)`
  - `pub(crate) fn set_depths(&mut self, depth: u32, level_assign_depth: u32)`
- Produces, on `MetaCtx`:
  `pub fn with_new_mctx_depth<R>(&mut self, allow_level_assignments: bool, f: impl FnOnce(&mut Self) -> R) -> R`

- [ ] **Step 1: Write the failing tests** (append to `metactx.rs` `mod tests`)

```rust
    // ---- mctx depth (macro/binop% P1, Task 1) ----
    // oracle: `addExprMVarDecl`/`addLevelMVarDecl` stamp `depth :=
    // mctx.depth` (MetavarContext.lean:813, :834); `incDepth` (:932-936);
    // `withNewMCtxDepthImp` restores the whole saved mctx and `postponed`
    // (Basic.lean:1973-1978).

    fn declare_level_named(ctx: &mut MetaCtx, s: &str) -> crate::LMVarId {
        let sid = ctx.scratch.intern_str(None, s).unwrap();
        let n = ctx.scratch.name_str(None, None, sid).unwrap();
        let id = crate::LMVarId(n);
        ctx.mctx.declare_level(id);
        id
    }

    #[test]
    fn declarations_are_stamped_with_the_current_depth() {
        with_ctx(|ctx| {
            let ty = ctx.scratch.expr_sort(None, ctx.scratch.level_zero(None).unwrap()).unwrap();
            let (_, outer) = fresh_mvar(ctx, ty);
            let lo = declare_level_named(ctx, "lo");
            assert_eq!(ctx.mctx.depth(), 0);
            assert_eq!(ctx.mctx.expr_mvar_depth(outer), Some(0));
            ctx.with_new_mctx_depth(false, |ctx| {
                assert_eq!(ctx.mctx.depth(), 1);
                assert_eq!(ctx.mctx.level_assign_depth(), 1);
                let (_, inner) = fresh_mvar(ctx, ty);
                let li = declare_level_named(ctx, "li");
                assert_eq!(ctx.mctx.expr_mvar_depth(inner), Some(1));
                assert_eq!(ctx.mctx.level_mvar_depth(li), 1);
                assert!(ctx.mctx.is_read_only(outer));
                assert!(!ctx.mctx.is_read_only(inner));
                assert!(ctx.mctx.is_level_mvar_read_only(lo));
                assert!(!ctx.mctx.is_level_mvar_read_only(li));
            });
            assert_eq!(ctx.mctx.depth(), 0);
            assert!(!ctx.mctx.is_read_only(outer));
            assert!(!ctx.mctx.is_level_mvar_read_only(lo));
        });
    }

    #[test]
    fn allow_level_assignments_keeps_the_level_assign_depth() {
        with_ctx(|ctx| {
            let lo = declare_level_named(ctx, "lo");
            ctx.with_new_mctx_depth(true, |ctx| {
                assert_eq!(ctx.mctx.depth(), 1);
                assert_eq!(ctx.mctx.level_assign_depth(), 0);
                assert!(!ctx.mctx.is_level_mvar_read_only(lo));
            });
        });
    }

    #[test]
    fn nested_scopes_restore_the_intermediate_depth() {
        with_ctx(|ctx| {
            ctx.with_new_mctx_depth(false, |ctx| {
                ctx.with_new_mctx_depth(true, |ctx| {
                    assert_eq!(ctx.mctx.depth(), 2);
                    assert_eq!(ctx.mctx.level_assign_depth(), 1);
                });
                assert_eq!(ctx.mctx.depth(), 1);
                assert_eq!(ctx.mctx.level_assign_depth(), 1);
            });
            assert_eq!((ctx.mctx.depth(), ctx.mctx.level_assign_depth()), (0, 0));
        });
    }

    #[test]
    fn scope_discards_assignments_and_restores_postponed_even_on_err() {
        with_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).unwrap();
            let ty = ctx.scratch.expr_sort(None, z).unwrap();
            let (_, m) = fresh_mvar(ctx, ty);
            ctx.postponed.push((z, z));
            let r: Result<(), MetaError> = ctx.with_new_mctx_depth(false, |ctx| {
                assert!(ctx.postponed.is_empty(), "oracle clears `postponed` on entry");
                // Assigning an outer mvar directly (bypassing isDefEq) is
                // still discarded on exit: the oracle restores `saved.mctx`.
                ctx.mctx.assign(m, ty).unwrap();
                Err(MetaError::Unsupported("boom".into()))
            });
            assert!(r.is_err());
            assert!(!ctx.mctx.is_assigned(m));
            assert_eq!(ctx.postponed, vec![(z, z)]);
            assert_eq!(ctx.mctx.depth(), 0);
        });
    }

    #[test]
    fn undeclared_expr_mvar_is_read_only_and_undeclared_level_is_depth_zero() {
        with_ctx(|ctx| {
            let sid = ctx.scratch.intern_str(None, "ghost").unwrap();
            let n = ctx.scratch.name_str(None, None, sid).unwrap();
            assert!(ctx.mctx.is_read_only(crate::MVarId(n)));
            assert_eq!(ctx.mctx.level_mvar_depth(crate::LMVarId(n)), 0);
            assert!(!ctx.mctx.is_level_mvar_read_only(crate::LMVarId(n)));
        });
    }
```

If `fresh_mvar` is not imported in this test module, add it to the `use crate::test_support::{…}` line. If `expr_sort`/`level_zero` need `Some(ctx.view.store)` rather than `None` as the base, follow `assign.rs::tests::n_type` (`:1691-1695`).

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_meta --lib metactx::tests::declarations_are_stamped 2>&1 | tail -5`
Expected: compile error, `no method named depth` / `with_new_mctx_depth`.

- [ ] **Step 3: Implement the depth fields in `mvar_ctx.rs`**

Replace `level_decls: HashSet<LMVarId>` with a map, and add the fields:

```rust
#[derive(Default)]
pub struct MetavarContext {
    decls: HashMap<MVarId, MVarDecl>,
    /// oracle: `MetavarDecl.depth` (MetavarContext.lean:251-256), kept as
    /// a side map stamped by [`Self::declare`] so `MVarDecl` literals stay
    /// depth-agnostic (`addExprMVarDecl` stamps `depth := mctx.depth`,
    /// :813).
    expr_depths: HashMap<MVarId, u32>,
    assignments: HashMap<MVarId, ExprId>,
    /// oracle: `lDecls` with `LevelMetavarDecl.depth` (:834).
    level_decls: HashMap<LMVarId, u32>,
    level_assignments: HashMap<LMVarId, LevelId>,
    d_assignment: HashMap<MVarId, DelayedMVarAssignment>,
    /// oracle: `MetavarContext.depth` (:352-353).
    depth: u32,
    /// oracle: `MetavarContext.levelAssignDepth` (:354-355).
    level_assign_depth: u32,
}
```

In `declare`, add `self.expr_depths.insert(id, self.depth);` before the
insert. In `declare_level`, use `self.level_decls.insert(id, self.depth);`.
Fix every other `level_decls` use (`contains` → `contains_key`; grep
`level_decls` in this file). Add:

```rust
    pub fn depth(&self) -> u32 { self.depth }
    pub fn level_assign_depth(&self) -> u32 { self.level_assign_depth }

    pub fn expr_mvar_depth(&self, id: MVarId) -> Option<u32> {
        self.expr_depths.get(&id).copied()
    }

    /// Undeclared level mvars count as created at depth 0. The oracle's
    /// `getLevelDecl` would panic; leanr meets undeclared level mvars in
    /// decoded/test terms, and depth 0 keeps depth-0 behaviour identical.
    pub fn level_mvar_depth(&self, id: LMVarId) -> u32 {
        self.level_decls.get(&id).copied().unwrap_or(0)
    }

    /// oracle: `MVarId.isReadOnly` (Basic.lean:971-972),
    /// `decl.depth != mctx.depth`. Undeclared → read-only (the oracle
    /// panics; leanr's callers already treat undeclared as unassignable).
    pub fn is_read_only(&self, id: MVarId) -> bool {
        self.expr_mvar_depth(id) != Some(self.depth)
    }

    /// oracle: `LMVarId.isReadOnly` (Basic.lean:1000-1001),
    /// `depth < levelAssignDepth` — the negation of
    /// `isLevelMVarAssignable` (MetavarContext.lean:470-474).
    pub fn is_level_mvar_read_only(&self, id: LMVarId) -> bool {
        self.level_mvar_depth(id) < self.level_assign_depth
    }

    /// oracle: `incDepth` (MetavarContext.lean:932-936).
    pub(crate) fn inc_depth(&mut self, allow_level_assignments: bool) {
        self.depth += 1;
        if !allow_level_assignments {
            self.level_assign_depth = self.depth;
        }
    }

    pub(crate) fn set_depths(&mut self, depth: u32, level_assign_depth: u32) {
        self.depth = depth;
        self.level_assign_depth = level_assign_depth;
    }
```

- [ ] **Step 4: Implement `with_new_mctx_depth` in `metactx.rs`** (next to `with_full_approx_def_eq`)

```rust
    /// oracle: `withNewMCtxDepthImp` (`Lean/Meta/Basic.lean:1973-1978`):
    /// `incDepth`, clear `postponed`, run, then restore the WHOLE saved
    /// mctx and `postponed` in a `finally`. Restoring the whole mctx
    /// discards every assignment made inside, including to inner mvars,
    /// so a caller that needs an inner result must instantiate it inside
    /// the scope. leanr's `checkpoint`/`rollback` restores assignments
    /// and `postponed`; declarations made inside persist harmlessly
    /// (`snapshot_assignments`' own doc). `f` returns rather than
    /// unwinds, so save/run/restore covers the `Err` path too (same
    /// panic caveat as `with_assignable_synthetic_opaque`).
    ///
    /// The transient defeq cache is cleared on entry and on exit: an
    /// answer computed while outer mvars are read-only must never answer
    /// the same query outside the scope. That only changes performance.
    pub fn with_new_mctx_depth<R>(
        &mut self,
        allow_level_assignments: bool,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let snap = self.checkpoint();
        let (depth, level_assign_depth) = (self.mctx.depth(), self.mctx.level_assign_depth());
        self.mctx.inc_depth(allow_level_assignments);
        self.postponed.clear();
        self.defeq_cache_transient.clear();
        let r = f(self);
        self.rollback(snap);
        self.mctx.set_depths(depth, level_assign_depth);
        self.defeq_cache_transient.clear();
        r
    }
```

- [ ] **Step 5: Run the tests to verify they pass**

Run: `cargo test -p leanr_meta --lib metactx::tests 2>&1 | tail -5`
Expected: all pass.

- [ ] **Step 6: Run the mutations**

For each mutation, apply it, run `cargo test -p leanr_meta --lib metactx::tests`, confirm a failure, then revert:
- (a) delete `self.rollback(snap);`
- (b) delete `self.mctx.set_depths(...)`
- (c) in `inc_depth`, drop the `if !allow_level_assignments` guard (always set)
- (d) in `declare`, stamp `0` instead of `self.depth`
- (e) delete `self.postponed.clear();`

- [ ] **Step 7: Run the whole crate (depth-0 invariant)**

Run: `cargo test -p leanr_meta 2>&1 | grep -E "^test result|FAILED|panicked" | head -20`
Expected: every `test result: ok`. Nothing reads the predicates yet, so nothing can change.

- [ ] **Step 8: Commit**

```bash
cargo fmt --all
git add crates/leanr_meta/src/mvar_ctx.rs crates/leanr_meta/src/metactx.rs
git commit -m "leanr_meta: mctx depth bookkeeping + with_new_mctx_depth (macro/binop% P1 T1)"
```

---

### Task 2: Wire the expression read-only sites

**Files:**
- Modify: `crates/leanr_meta/src/assign.rs` (`unassigned_mvar_id`, `:149-175`; module doc § "Depth / read-only seam", `:59-66`)
- Modify: `crates/leanr_meta/src/lazy_delta.rs` (`is_def_eq_singleton`'s `assignable`, `:497-501`)
- Modify: `crates/leanr_meta/src/check.rs` (`ensure_type`'s `assignable`, `:190-195`)
- Test: `crates/leanr_meta/src/assign.rs` `mod tests`

**Interfaces:**
- Consumes (Task 1): `MetavarContext::is_read_only(MVarId) -> bool`, `MetaCtx::with_new_mctx_depth`.
- Produces: no new API. `isAssignable` (ExprDefEq.lean:1731-1732) is now faithful.

The three sites transcribe `isReadOnlyOrSyntheticOpaque` (Basic.lean:979-985): read-only **or** (syntheticOpaque **and** `!assignSyntheticOpaque`). Add the read-only half to each.

- [ ] **Step 1: Write the failing tests** (in `assign.rs` `mod tests`, near `assigns_a_pattern_mvar`, `:1851`)

```rust
    // ---- mctx depth (macro/binop% P1, Task 2) ----
    // oracle: `isAssignable` → `isReadOnlyOrSyntheticOpaque`
    // (ExprDefEq.lean:1731-1732; Basic.lean:979-985).

    #[test]
    fn outer_mvar_is_not_assigned_inside_a_new_depth() {
        with_n_ctx(|ctx| {
            let ty = n_type(ctx);
            let (m_expr, m_id) = fresh_mvar(ctx, ty);
            let zero = mk_const(ctx, "N.zero");
            let inside = ctx.with_new_mctx_depth(false, |ctx| {
                let r = ctx.is_def_eq(m_expr, zero).unwrap();
                assert!(!ctx.mctx.is_assigned(m_id));
                r
            });
            assert!(!inside, "outer ?m is read-only at depth 1");
            // Review Focus 2: same query OUTSIDE must not be answered by a
            // cached in-scope `false`.
            assert!(ctx.is_def_eq(m_expr, zero).unwrap());
            assert_eq!(ctx.mctx.assignment(m_id), Some(zero));
        });
    }

    #[test]
    fn inner_mvar_is_assigned_inside_a_new_depth() {
        with_n_ctx(|ctx| {
            let ty = n_type(ctx);
            let zero = mk_const(ctx, "N.zero");
            ctx.with_new_mctx_depth(false, |ctx| {
                let (m_expr, m_id) = fresh_mvar(ctx, ty);
                assert!(ctx.is_def_eq(m_expr, zero).unwrap());
                assert_eq!(ctx.mctx.assignment(m_id), Some(zero));
            });
        });
    }

    #[test]
    fn outer_mvar_under_an_application_is_read_only_inside_a_new_depth() {
        // `N.succ ?m =?= N.succ N.zero`: the args path reaches `?m =?=
        // N.zero` — the `BitVec n =?= BitVec ?m` shape from the spec.
        with_n_ctx(|ctx| {
            let ty = n_type(ctx);
            let (m_expr, m_id) = fresh_mvar(ctx, ty);
            let zero = mk_const(ctx, "N.zero");
            let succ = mk_const(ctx, "N.succ");
            let lhs = mk_app(ctx, succ, m_expr);
            let rhs = mk_app(ctx, succ, zero);
            assert!(!ctx.with_new_mctx_depth(false, |ctx| ctx.is_def_eq(lhs, rhs).unwrap()));
            assert!(!ctx.mctx.is_assigned(m_id));
            assert!(ctx.is_def_eq(lhs, rhs).unwrap());
        });
    }
```

Also add one test each for `lazy_delta.rs::is_def_eq_singleton` and `check.rs::ensure_type`, next to their existing tests:
- For `ensure_type`, copy the existing test that shows `ensure_type` assigning `?m := Sort ?u` (`grep -n "ensure_type" crates/leanr_meta/src/check.rs` in `mod tests`). Mint `?m` **outside** the scope, call `ensure_type` **inside** `with_new_mctx_depth(false, …)`, and assert `Err(MetaError::Infer(_))` ("type expected", InferType.lean:170-172) with `?m` unassigned.
- For `is_def_eq_singleton`, copy its existing positive test (`grep -n "singleton" crates/leanr_meta/src/lazy_delta.rs` in `mod tests`). Run the same query with the mvar minted outside and the query inside the scope, and assert `false`.

If either positive test does not exist, write it first from the function's doc comment, then the depth variant.

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_meta --lib depth 2>&1 | tail -8` (also run each new singleton/ensure_type test by name)
Expected: `outer_mvar_is_not_assigned_inside_a_new_depth` FAILS (`inside` is `true`); `inner_…` passes; the singleton/ensure_type depth variants FAIL.

- [ ] **Step 3: Implement**

In `assign.rs::unassigned_mvar_id`, add the depth half before the kind check:

```rust
                match self.mctx.decl(mid) {
                    // oracle: `isAssignable` → `isReadOnlyOrSyntheticOpaque`
                    // (ExprDefEq.lean:1731-1732; Basic.lean:979-985): the
                    // depth arm (`:981-982`) first …
                    Some(_) if self.mctx.is_read_only(mid) => None,
                    // … then the `syntheticOpaque` arm (`:985`), gated by
                    // `Config.assignSyntheticOpaque`.
                    Some(d)
                        if d.kind == MVarKind::SyntheticOpaque
                            && !self.cfg.assign_synthetic_opaque =>
                    {
                        None
                    }
                    Some(_) => Some(mid),
                    None => None,
                }
```

In `lazy_delta.rs` (`:497`) and `check.rs` (`:190`), make the same predicate read `!self.mctx.is_read_only(mid) && (<existing kind test>)`, with the same two citations. In `check.rs`, delete the sentence "The depth half of `isReadOnlyOrSyntheticOpaque` is the crate's single-depth seam."

Rewrite `assign.rs`'s module-doc section "# Depth / read-only seam" (`:59-66`) to say: depth is modelled (`mvar_ctx.rs`, macro/binop% P1). `isReadOnlyOrSyntheticOpaque` is ported at `unassigned_mvar_id`, `is_def_eq_singleton` and `ensure_type`. Still seamed: the `isSubPrefixOf` arm of `CheckAssignmentQuick` (`:1075`) and the slow `checkAssignment` mvar arm (ExprDefEq.lean:901), which leanr does not port. `elimMVar`'s depth-dependent `newMVarKind` (MetavarContext.lean:1187, :1195) is nondep R9, out of scope.

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p leanr_meta --lib 2>&1 | grep -E "test result|FAILED"`
Expected: `test result: ok`.

- [ ] **Step 5: Run the mutations**

Each must fail a test:
- (a) delete the `Some(_) if self.mctx.is_read_only(mid) => None,` arm
- (b) delete the read-only half in `lazy_delta.rs`
- (c) delete the read-only half in `check.rs`
- (d) in Task 1's `with_new_mctx_depth`, delete the two `defeq_cache_transient.clear()` calls. If no test fails, the cache key already isolates the query. Record "survives: transient cache already cleared per top-level `is_def_eq` (defeq.rs:97)" in the commit body, and keep the clears as cheap insurance for nested callers.

- [ ] **Step 6: Run the oracle corpora (depth-0 invariant)**

Run: `cargo test -p leanr_meta 2>&1 | grep -E "^test result|FAILED" ; cargo test -p leanr_elab --test oracle_elab 2>&1 | tail -3`
Expected: all ok, and no floor change.

- [ ] **Step 7: Commit**

```bash
cargo fmt --all
git add crates/leanr_meta/src/{assign,lazy_delta,check}.rs
git commit -m "leanr_meta: isReadOnlyOrSyntheticOpaque depth arm at the three assignability sites (macro/binop% P1 T2)"
```

---

### Task 3: Wire the level read-only sites

**Files:**
- Modify: `crates/leanr_meta/src/level.rs`:
  - module doc § "Depth / read-only seam" (`:9-19`)
  - `solve` mvar arm (`:173-208`)
  - `dec_level` (`:490-497`)
  - `has_assignable_level_mvar` (`:685-711`)
- Test: `crates/leanr_meta/src/level.rs` `mod tests` (`:784`)

**Interfaces:**
- Consumes (Task 1): `is_level_mvar_read_only(LMVarId)`, `level_mvar_depth(LMVarId)`, `with_new_mctx_depth`.

Oracle (open each line before citing):
- `solve` (LevelDefEq.lean:101-116): `if (← mvarId.isReadOnly) then return .undef` (`:104-105`); `else if (← isMVarWithGreaterDepth v mvarId) then assignLevelMVar v.mvarId! u; return .true` (`:106-110`), where `isMVarWithGreaterDepth v m` = `v` is `.mvar m'` with `depth m' > depth m` (`:93-96`).
- `decAux?` `isReadOnly` (DecLevel.lean): grep `isReadOnly` there and cite the exact line.
- `hasAssignableLevelMVar` (HasAssignableMVar.lean:17-21) uses `isLevelMVarAssignable` (MetavarContext.lean:470-474).
- Not gated, faithfully: `tryApproxSelfMax`/`tryApproxMaxMax` (LevelDefEq.lean:39-73) and `solveSelfMax` (`:32-37`) call `assignLevelMVar` with no read-only check. Do **not** add one to `try_approx_self_max`/`try_approx_max_max`/`solve_self_max`.

- [ ] **Step 1: Write the failing tests** (append to `level.rs` `mod tests`)

```rust
    // ---- mctx depth (macro/binop% P1, Task 3) ----

    fn lmvar(ctx: &mut crate::MetaCtx, s: &str) -> (crate::LMVarId, leanr_kernel::bank::LevelId) {
        let sid = ctx.scratch.intern_str(None, s).unwrap();
        let n = ctx.scratch.name_str(None, None, sid).unwrap();
        let id = crate::LMVarId(n);
        ctx.mctx.declare_level(id);
        (id, ctx.scratch.level_mvar(None, Some(n)).unwrap())
    }

    #[test]
    fn outer_level_mvar_is_read_only_inside_a_new_depth() {
        with_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).unwrap();
            let one = ctx.scratch.level_succ(None, z).unwrap();
            let (id, u) = lmvar(ctx, "?u");
            let inside = ctx.with_new_mctx_depth(false, |ctx| {
                let r = ctx.is_level_def_eq(u, one).unwrap();
                assert!(!ctx.mctx.is_level_assigned(id));
                r
            });
            assert!(!inside);
            assert!(ctx.is_level_def_eq(u, one).unwrap());
        });
    }

    #[test]
    fn allow_level_assignments_lets_an_outer_level_mvar_be_assigned() {
        with_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).unwrap();
            let (id, u) = lmvar(ctx, "?u");
            ctx.with_new_mctx_depth(true, |ctx| {
                assert!(ctx.is_level_def_eq(u, z).unwrap());
                assert_eq!(ctx.mctx.level_assignment(id), Some(z));
            });
        });
    }

    #[test]
    fn greater_depth_level_mvar_is_assigned_to_the_shallower_one() {
        // oracle LevelDefEq.lean:106-110: `?u =?= ?v` with depth ?v > depth
        // ?u assigns `?v := ?u` (not `?u := ?v`, which the plain
        // `!u.occurs v` arm would do).
        with_ctx(|ctx| {
            let (u_id, u) = lmvar(ctx, "?u");
            ctx.with_new_mctx_depth(true, |ctx| {
                let (v_id, v) = lmvar(ctx, "?v");
                assert!(ctx.is_level_def_eq(u, v).unwrap());
                assert_eq!(ctx.mctx.level_assignment(v_id), Some(u));
                assert!(!ctx.mctx.is_level_assigned(u_id));
            });
        });
    }

    #[test]
    fn has_assignable_level_mvar_respects_depth() {
        with_ctx(|ctx| {
            let (_, u) = lmvar(ctx, "?u");
            assert!(ctx.has_assignable_level_mvar(u).unwrap());
            ctx.with_new_mctx_depth(false, |ctx| {
                assert!(!ctx.has_assignable_level_mvar(u).unwrap());
            });
        });
    }

    #[test]
    fn dec_level_does_not_assign_a_read_only_level_mvar() {
        with_ctx(|ctx| {
            let (id, u) = lmvar(ctx, "?u");
            ctx.with_new_mctx_depth(false, |ctx| {
                assert_eq!(ctx.dec_level(u, true).unwrap(), None);
                assert!(!ctx.mctx.is_level_assigned(id));
            });
            assert!(ctx.dec_level(u, true).unwrap().is_some());
        });
    }
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_meta --lib level::tests 2>&1 | tail -10`
Expected: `outer_level_mvar_…`, `greater_depth_…`, `has_assignable_…` and `dec_level_…` FAIL. `allow_level_assignments_…` passes.

- [ ] **Step 3: Implement**

In `solve`, replace the two SEAM blocks:

```rust
            let mvar_id = LMVarId(n);
            // oracle: `mvarId.isReadOnly` (LevelDefEq.lean:104-105;
            // Basic.lean:1000-1001).
            if self.mctx.is_level_mvar_read_only(mvar_id) {
                return Ok(None);
            }
            // oracle: `isMVarWithGreaterDepth v mvarId` (:106-110, :93-96)
            // — reachable when `levelAssignDepth < depth` (TC synthesis's
            // `allowLevelAssignments := true`).
            if let LevelRow::MVar(Some(vn)) = v_row {
                let v_id = LMVarId(vn);
                if self.mctx.level_mvar_depth(v_id) > self.mctx.level_mvar_depth(mvar_id) {
                    self.mctx.assign_level(v_id, u)?;
                    return Ok(Some(true));
                }
            }
```

In `dec_level`: `let is_read_only = ctx.mctx.is_level_mvar_read_only(mvar_id);` with the DecLevel.lean citation you opened.

In `has_assignable_level_mvar`:
`LevelRow::MVar(name) => Ok(name.is_some_and(|n| !ctx.mctx.is_level_mvar_read_only(LMVarId(n))))`. Update its doc so it says the depth gate is now real (`isLevelMVarAssignable`, MetavarContext.lean:470-474).

Rewrite the module doc § "Depth / read-only seam" to cite the ported sites, and to say the approx helpers are ungated just as in the oracle. If `dec_level`/`has_assignable_level_mvar` are private and the test can't reach them, the test module is a child of the file, so private items are visible. No visibility change is needed.

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p leanr_meta --lib level:: 2>&1 | tail -5`
Expected: all pass.

- [ ] **Step 5: Run the mutations**

Each must fail a test:
- (a) `is_level_mvar_read_only` call in `solve` → `false`
- (b) delete the greater-depth block
- (c) flip `>` to `>=` in the greater-depth block. This changes depth-0 behaviour: `?u =?= ?v` with both at depth 0 would assign `?v := ?u` instead of `?u := ?v`. Kill it with a depth-0 test asserting that `?u =?= ?v` (both outer) assigns `?u` (the `!u.occurs v` arm, LevelDefEq.lean:111-113 — open and cite the exact line). Add this test up front in Step 1 rather than waiting for the mutation to survive.
- (d) `dec_level` read-only → `false`
- (e) `has_assignable_level_mvar` back to `name.is_some()`

- [ ] **Step 6: Run the crate and corpora (depth-0 invariant)**

Run: `cargo test -p leanr_meta 2>&1 | grep -E "^test result|FAILED" ; cargo test -p leanr_elab --test oracle_elab 2>&1 | tail -3`
Expected: all ok.

- [ ] **Step 7: Commit**

```bash
cargo fmt --all
git add crates/leanr_meta/src/level.rs
git commit -m "leanr_meta: level read-only + isMVarWithGreaterDepth wired to mctx depth (macro/binop% P1 T3)"
```

---

### Task 4: `isDefEqStuckEx`, the stuck throws, `is_def_eq_guarded`

**Files:**
- Modify: `crates/leanr_meta/src/config.rs` (struct `:63-161`; `Default` `:172`; `ASSERT_CONFIG_SIZE` `:163`; tests)
- Modify: `crates/leanr_meta/src/error.rs:41` (`IsDefEqStuck(ExprId)` → `IsDefEqStuck`)
- Modify: `crates/leanr_meta/src/synth.rs:1802` (`Err(MetaError::IsDefEqStuck(_))` → `Err(MetaError::IsDefEqStuck)`)
- Modify: `crates/leanr_meta/src/assign.rs:129-134` (the `(None, None)` arm)
- Modify: `crates/leanr_meta/src/level.rs:154-162` (stuck tail) + module doc § "`isDefEqStuckEx` seam" (`:21-…`)
- Modify: `crates/leanr_meta/src/metactx.rs` (`with_def_eq_stuck_ex`, `is_def_eq_guarded`)
- Test: `assign.rs`, `level.rs` and `metactx.rs` `mod tests`; `config.rs` tests

**Interfaces:**
- Produces:
  - `Config::is_def_eq_stuck_ex: bool` (default `false`)
  - `MetaError::IsDefEqStuck` (unit)
  - `pub fn with_def_eq_stuck_ex<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R`
  - `pub fn is_def_eq_guarded(&mut self, t: ExprId, s: ExprId) -> Result<bool, MetaError>`. It returns `Err` only for resource exhaustion; any other error becomes `Ok(false)`.
- P3 (later plan) calls:

  ```rust
  ctx.with_new_mctx_depth(false, |c| c.with_def_eq_stuck_ex(|c| c.is_def_eq_guarded(a, b)))
  ```

Oracle:
- `isDefEqStuckEx : Bool := false` (Basic.lean:134). It is part of the config cache key (Basic.lean:206), so it goes in `Hash`.
- Throws:
  - ExprDefEq.lean:1949-1956: the `!tAssign? && !sAssign?` branch runs `isDefEqProofIrrel t s` first, `.true`/`.false` return, and `.undef` throws if the flag is on, else returns `.false`.
  - LevelDefEq.lean:167-173: `!hasAssignableLevelMVar` and flag and `(lhs.isMVar || rhs.isMVar)` throws, else returns `false`.
- Third oracle site, not ported: `unstuckMVar` (ExprDefEq.lean:1985-2020) lives inside `isDefEqOnFailure`, which leanr has not ported (`defeq.rs` "SEAM: isDefEqOnFailure"). Record this in spec § Landed (Task 5). Do not port `isDefEqOnFailure` here.
- `isDefEqGuarded` (Basic.lean:2513-2518) is `try … catch _ => false`. `Core.tryCatch` rethrows runtime exceptions (maxRecDepth, heartbeats), so they propagate.

- [ ] **Step 1: Write the failing tests**

In `assign.rs` `mod tests`:

```rust
    // ---- isDefEqStuckEx (macro/binop% P1, Task 4) ----
    // oracle ExprDefEq.lean:1949-1956.

    #[test]
    fn read_only_vs_rigid_throws_stuck_only_under_the_flag() {
        with_n_ctx(|ctx| {
            let ty = n_type(ctx);
            let (m_expr, _) = fresh_mvar(ctx, ty);
            let zero = mk_const(ctx, "N.zero");
            ctx.with_new_mctx_depth(false, |ctx| {
                assert_eq!(ctx.is_def_eq(m_expr, zero), Ok(false));
                assert_eq!(
                    ctx.with_def_eq_stuck_ex(|ctx| ctx.is_def_eq(m_expr, zero)),
                    Err(MetaError::IsDefEqStuck)
                );
                assert_eq!(
                    ctx.with_def_eq_stuck_ex(|ctx| ctx.is_def_eq_guarded(m_expr, zero)),
                    Ok(false)
                );
            });
            // Flag off outside: unaffected.
            assert!(!ctx.cfg().is_def_eq_stuck_ex);
        });
    }

    #[test]
    fn both_unassignable_props_are_closed_by_proof_irrelevance() {
        // `?p =?= ?q`, both syntheticOpaque, both of type `P : Prop` —
        // oracle returns `.true` by proof irrelevance before the stuck test.
        // Build the env with a `P : Prop` axiom: extend `with_n_ctx_cfg`'s
        // axiom list, or mint `p : Sort 0` as an fvar with `fresh_fvar`
        // and use it as both mvars' type.
        with_n_ctx(|ctx| {
            let prop = n_type(ctx); // Sort 0
            let p_ty = crate::test_support::fresh_fvar(ctx, prop, "P");
            let (p, _) = crate::test_support::fresh_mvar_of_kind(ctx, p_ty, MVarKind::SyntheticOpaque);
            let (q, _) = crate::test_support::fresh_mvar_of_kind(ctx, p_ty, MVarKind::SyntheticOpaque);
            assert_eq!(ctx.is_def_eq(p, q), Ok(true));
        });
    }
```

In `level.rs` `mod tests`:

```rust
    #[test]
    fn read_only_level_mvar_throws_stuck_only_under_the_flag() {
        with_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).unwrap();
            let one = ctx.scratch.level_succ(None, z).unwrap();
            let (_, u) = lmvar(ctx, "?u");
            ctx.with_new_mctx_depth(false, |ctx| {
                assert_eq!(ctx.is_level_def_eq(u, one), Ok(false));
                assert_eq!(
                    ctx.with_def_eq_stuck_ex(|ctx| ctx.is_level_def_eq(u, one)),
                    Err(crate::MetaError::IsDefEqStuck)
                );
            });
        });
    }
```

In `metactx.rs` `mod tests` (Review Focus 3):

```rust
    #[test]
    fn is_def_eq_guarded_rethrows_resource_exhaustion_only() {
        use leanr_kernel::KernelError;
        for (e, propagates) in [
            (MetaError::IsDefEqStuck, false),
            (MetaError::Unsupported("x".into()), false),
            (MetaError::Infer("x".into()), false),
            (MetaError::DepthBudgetExhausted, true),
            (MetaError::StepBudgetExhausted, true),
            (MetaError::Kernel(KernelError::BankExhausted), true),
        ] {
            assert_eq!(MetaCtx::guard_def_eq_result(Err(e.clone())).is_err(), propagates, "{e:?}");
        }
        assert_eq!(MetaCtx::guard_def_eq_result(Ok(true)), Ok(true));
    }
```

In `config.rs` tests, add `assert!(!c.is_def_eq_stuck_ex);` to `default_matches_oracle_defaults`, and a test that two configs differing only in `is_def_eq_stuck_ex` have different `cache_key()`s.

If `is_def_eq_proof_irrel` returns `None` in the props test because the fvar-typed setup does not satisfy `is_prop`, build the env differently (an axiom `P : Prop` in `with_n_ctx_cfg`'s list). Do not weaken the assertion.

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_meta --lib stuck 2>&1 | tail -8`
Expected: compile errors (`with_def_eq_stuck_ex`, `IsDefEqStuck` unit, field missing).

- [ ] **Step 3: Implement**

- `config.rs`: add the field with doc `oracle: Basic.lean:134 (default false); in the cache key (Basic.lean:206)`. Set `is_def_eq_stuck_ex: false` in `Default`. Change the size assertion to `17` and update its message. Fix every full `Config { … }` literal the compiler reports (add `is_def_eq_stuck_ex: false`). Literals using `..Config::default()` need nothing.
- `error.rs`: `IsDefEqStuck,` with doc `oracle: Exception.internal isDefEqStuckExceptionId (Basic.lean:33, :622-623)`.
- `synth.rs:1802`: `Err(MetaError::IsDefEqStuck) => Ok(LOption::Undef),`.
- `assign.rs` `(None, None)` arm:

```rust
            (None, None) => {
                // oracle: ExprDefEq.lean:1949-1956 — both sides
                // unassignable (read-only depth, or syntheticOpaque):
                // proof irrelevance first, then `isDefEqStuckEx`.
                if let Some(b) = self.is_def_eq_proof_irrel(t, s)? {
                    return Ok(Some(b));
                }
                if self.cfg.is_def_eq_stuck_ex {
                    return Err(MetaError::IsDefEqStuck);
                }
                Ok(Some(false))
            }
```

- `level.rs` stuck tail:

```rust
            if !assignable {
                // oracle: LevelDefEq.lean:167-173.
                let is_mvar = |l| matches!(*ctx.scratch.level_row(Some(ctx.view.store), l), LevelRow::MVar(_));
                if ctx.cfg.is_def_eq_stuck_ex && (is_mvar(lhs) || is_mvar(rhs)) {
                    return Err(MetaError::IsDefEqStuck);
                }
                Ok(false)
            }
```

  Write `is_mvar` as two plain `matches!` expressions if the closure's borrow of `ctx` conflicts. Rewrite the module-doc § "`isDefEqStuckEx` seam" to cite the two ported sites, and to say the flag is set only by `with_def_eq_stuck_ex` (synthesis's own `:963` setting stays a follow-up).
- `metactx.rs`:

```rust
    /// oracle: `withConfig (fun c => { c with isDefEqStuckEx := true })`
    /// (Extra.lean:309's use; SynthInstance.lean:963). Restores the
    /// whole config, as `withConfig` does.
    pub fn with_def_eq_stuck_ex<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = self.cfg;
        self.cfg.is_def_eq_stuck_ex = true;
        let r = f(self);
        self.cfg = saved;
        r
    }

    /// oracle: `isDefEqGuarded` / `isExprDefEqGuarded` (Basic.lean:2513-2518):
    /// `try isExprDefEq a b catch _ => return false`. `Core.tryCatch`
    /// does not catch runtime exceptions, so resource exhaustion
    /// (maxRecDepth ↔ `DepthBudgetExhausted`, heartbeats ↔
    /// `StepBudgetExhausted`, `Kernel(BankExhausted)`) propagates.
    pub fn is_def_eq_guarded(&mut self, t: ExprId, s: ExprId) -> Result<bool, MetaError> {
        let r = self.is_def_eq(t, s);
        Self::guard_def_eq_result(r)
    }

    pub(crate) fn guard_def_eq_result(r: Result<bool, MetaError>) -> Result<bool, MetaError> {
        match r {
            Ok(b) => Ok(b),
            Err(e @ (MetaError::DepthBudgetExhausted
            | MetaError::StepBudgetExhausted
            | MetaError::Kernel(leanr_kernel::KernelError::BankExhausted))) => Err(e),
            Err(_) => Ok(false),
        }
    }
```

  Check the actual line of `isExprDefEqGuarded` and `abbrev isDefEqGuarded` before citing them (the spec says `:2513-2518`).

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p leanr_meta --lib 2>&1 | grep -E "test result|FAILED"`
Expected: ok.

- [ ] **Step 5: Run the mutations**

Each must fail a test:
- (a) delete the expr stuck throw
- (b) delete the level stuck throw
- (c) drop `|| is_mvar(rhs)`, and add a `1 =?= ?u` variant if it survives
- (d) delete the proof-irrel call in `(None, None)`
- (e) `guard_def_eq_result` maps everything to `Ok(false)`
- (f) `with_def_eq_stuck_ex` forgets to restore `cfg`, and add an "outside the scope the flag is false" assertion if it survives
- (g) drop `is_def_eq_stuck_ex` from `Hash` (`#[derive(Hash)]` makes this hard; instead check the new cache-key test fails when the field is removed from the struct and the assertion size is reverted)

- [ ] **Step 6: Run the crate, workspace build and corpora**

Run: `cargo build --workspace 2>&1 | tail -3 ; cargo test -p leanr_meta 2>&1 | grep -E "^test result|FAILED" ; cargo test -p leanr_elab --test oracle_elab 2>&1 | tail -3`
Expected: builds; all ok. If an oracle record changes verdict, it can only be the proof-irrelevance port. Stop and report which record changed, and whether it now matches the oracle.

- [ ] **Step 7: Commit**

```bash
cargo fmt --all
git add crates/leanr_meta/src/{config,error,synth,assign,level,metactx}.rs
git commit -m "leanr_meta: isDefEqStuckEx (two ported sites), is_def_eq_guarded (macro/binop% P1 T4)"
```

---

### Task 5: Whole-branch gate, spec § Landed, PR

**Files:**
- Modify: `docs/superpowers/specs/2026-10-01-macro-expansion-binop-design.md` (§ Landed)

- [ ] **Step 1: Sweep stale seam text**

Run: `grep -rn "single flat\|tier-1 depth\|flat mctx depth\|depth seam\|isDefEqStuckEx.*always" crates/leanr_meta/src crates/leanr_elab/src`
Expected: no hits that describe ported sites as seams. Fix any comment that still claims "depth is not modelled". `oracle_synth.rs`'s `withNewMCtxDepth` seam strings are about synthesis, which is still on rollback, so leave them.

- [ ] **Step 2: Sweep citations**

For every oracle `file:line` added on this branch (`git diff main -- crates | grep -o "[A-Za-z/]*\.lean:[0-9-]*" | sort -u`), open the line in the v4.33.0-rc1 source and confirm it says what the comment claims. Fix any that are off.

- [ ] **Step 3: Full CI, blocking**

Run, in the foreground (do not background it): `cd /workspace && mise run ci; echo CI_EXIT=$?`
Expected: `CI_EXIT=0`.

- [ ] **Step 4: Write spec § Landed › P1**

Under `## Landed` add `### P1 (PR #N): mctx depth + isDefEqStuckEx` with:
- commits
- every mutation run and its result
- spec corrections:
  - only **two** of the three stuck sites are ported. `unstuckMVar` (ExprDefEq.lean:1985-2020) sits inside the unported `isDefEqOnFailure`.
  - the expression depth sites are `unassigned_mvar_id`, `is_def_eq_singleton` and `ensure_type`. `isAbstractedUnassignedMVar` / `isEtaUnassignedMVar` are not ported (`config.rs:128-129`). The slow `checkAssignment` mvar arm (`:901`) is not ported.
  - the oracle's `withNewMCtxDepthImp` restores the whole mctx (Basic.lean:1973-1978), which the spec text did not state.
  - the proof-irrelevance port in the both-unassignable branch.
- open follow-ups:
  - synthesis onto real depth + `isDefEqStuckEx`
  - `discr_path` read-only arm
  - nondep R9
  - `unstuckMVar`

- [ ] **Step 5: Commit, push, PR**

```bash
git add docs/superpowers/specs/2026-10-01-macro-expansion-binop-design.md
git commit -m "spec: macro/binop% § Landed › P1"
git push -c credential.helper= -c "credential.helper=!$(which gh) auth git-credential" -u origin HEAD
gh pr create --title "leanr_meta: mctx depth + isDefEqStuckEx (macro/binop% P1)" --body "<summary, mutation table, spec corrections; ends with the session's attribution lines>"
```

The `git push` credential override works around the stale gh path in `~/.gitconfig`.

- [ ] **Step 6: Merge on green**

Per the standing workflow: wait for CI green, merge (squash), confirm the merge on `main`, and delete the branch.
