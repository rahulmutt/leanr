# checkAssignment with isSubPrefixOf + ctxApprox Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Port the oracle's `checkAssignment` scope machinery (the real `isSubPrefixOf` quick check plus the slow, term-rewriting `CheckAssignment` path with its `ctxApprox` rescue) into leanr_meta. Then route `mk_lambda_fvars_with_let_deps` through `MetaCtx::mk_lambda`, which runs elimMVarDeps. This closes the silent wrong `Ok` on `fun (n : Nat) (x : F n) => x + F.mk _` and the `DepthBudgetExhausted` on `(fun a => LT.lt a 2) z0`.

**Architecture:** A new module, `crates/leanr_meta/src/check_assignment.rs`, holds the quick check (moved from `assign.rs`) and the slow path (new). The `check_assignment` driver in `assign.rs` falls through from quick to slow exactly as `ExprDefEq.lean:1151-1172` does, and returns the REWRITTEN term. `LocalCtxSnapshot` gains `is_sub_prefix_of`. leanr_kernel is untouched.

**Tech Stack:** Rust (cargo, mise tasks), Lean 4 oracle `leanprover/lean4:v4.33.0-rc1` (elan, for fixture regeneration only).

**Spec:** `docs/superpowers/specs/2026-10-02-check-assignment-ctx-approx-design.md`. Read its § Evidence before starting. It explains WHY the cycle happens, and every task assumes that context.

## Global Constraints

- Oracle pin `leanprover/lean4:v4.33.0-rc1`. Do not bump it. Open every cite against `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`. The v4.32 tree is also installed and its line numbers are 10–12 lower. Do NOT read it.
- `leanr_kernel` must not change.
- No new dependencies.
- Build only under `/workspace` (shared `target/`), never `/tmp`. `/tmp` is a 20 GiB EmptyDir, and a second cargo target there evicts the pod.
- Run `cargo fmt --all` before every commit. CI's `mise run ci` gates on `cargo fmt --check` and clippy (`-D warnings`).
- A subagent that runs `mise run ci` must run it in the FOREGROUND and block until it exits (print a `CI_EXIT=$?` marker). A backgrounded CI job dies when the subagent's turn ends.
- Oracle-differential discipline: a changed corpus answer is diagnosed against the oracle and is never re-pinned to match leanr.
- Every commit message ends with `Co-Authored-By: Claude <noreply@anthropic.com>` and lists that task's mutations and which named test killed each one.

## Review Focus

1. **Synthesis runs with `ctx_approx = true` but without a new mctx depth** (`synth.rs:2200-2205` is still on the rollback stand-in). So `check_mvar`'s depth guard (`expr_mvar_depth(id) != mctx.depth()`) cannot refuse there the way the oracle does under `withNewMCtxDepth`, and a caller's mvar may be restricted mid-search. The expected behaviour is that the search's own `checkpoint`/`rollback` undoes it and no instance answer changes. Pinned by: the full `oracle_elab` / `oracle_op` / synth unit suites staying green in Task 2. If anything there changes, stop and report.
2. **An mvar met in `v` that is undeclared.** The quick check now returns `false` and the slow `check_mvar` raises a real `MetaError::MVar`, as the oracle's `throwUnknownMVar` does. Before this change it passed silently. Pinned by `check_mvar_errors_on_an_undeclared_mvar` (Task 1).
3. **The genuine-let rescue under `zeta_delta = false`.** It must now agree with the oracle (`?m := N.zero`). Pinned by the flipped `check_fvar_follows_a_genuine_let_value_in_both_zeta_modes` (Task 2).
4. **A restriction made in the FIRST direction of `is_def_eq_mvar_mvar` that then fails `check_types_and_assign`** must be rolled back. Pinned by `failed_first_direction_rolls_back_the_restriction` (Task 2).
5. **`has_ctx_locals`, quasi-pattern route**: the slow path refuses any mvar when it is set (`:890`). Pinned by `check_mvar_refuses_under_has_ctx_locals` (Task 1) and the existing quasi-pattern tests in `assign.rs` (Task 2).

---

## File map

| File | Change |
|---|---|
| `crates/leanr_meta/src/local_snapshot.rs` | add `is_sub_prefix_of` and its tests |
| `crates/leanr_meta/src/check_assignment.rs` | **new**: the quick check (moved), the slow path (new), and unit tests |
| `crates/leanr_meta/src/lib.rs` | `mod check_assignment;` |
| `crates/leanr_meta/src/assign.rs` | the driver rewrite; delete `check_assignment_scope`/`_body` (moved); make `forall_bounded_telescope`, `check_types_and_assign`, `mk_lambda_fvars_with_let_deps` `pub(crate)`; swap to `mk_lambda` and delete `mk_lambda_over_fvars`; module doc; move/flip two tests |
| `crates/leanr_meta/src/synth.rs`, `crates/leanr_elab/src/config.rs`, `crates/leanr_meta/src/metactx.rs` | doc comments that say `ctx_approx` is inert |
| `tests/fixtures/elab/dump_elab.lean`, `tests/fixtures/elab/op-queries.jsonl` | new and restored rows, regenerated |
| `crates/leanr_elab/tests/oracle_op.rs` | `CORPUS_FLOOR` |
| `docs/superpowers/specs/2026-10-02-check-assignment-ctx-approx-design.md`, `docs/superpowers/specs/2026-10-01-macro-expansion-binop-design.md` | § Landed |

Shared test commands, used throughout:
- leanr_meta unit tests: `cargo test -p leanr_meta --lib <filter>`
- elab corpora: `cargo test -p leanr_elab --test oracle_op --test oracle_elab --test seam_audit`
- everything: `mise run ci`

---

### Task 1: `is_sub_prefix_of` and the slow `CheckAssignment` path (not yet wired in)

**Files:**
- Modify: `crates/leanr_meta/src/local_snapshot.rs` (add a method next to `entries`, at about line 145; tests in its `mod tests`, or add `#[cfg(test)] mod tests` if absent)
- Create: `crates/leanr_meta/src/check_assignment.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (add `mod check_assignment;` after `mod check;`)
- Modify: `crates/leanr_meta/src/assign.rs`. Change `fn forall_bounded_telescope` (about :633), `fn check_types_and_assign` (about :861) and `fn mk_lambda_fvars_with_let_deps` (about :902) from private to `pub(crate)`. Nothing else in this task.

**Interfaces:**
- Produces:
  - `LocalCtxSnapshot::is_sub_prefix_of(&self, other: &LocalCtxSnapshot, except: &[NameId]) -> bool`
  - `MetaCtx::check_assignment_aux(&mut self, mvar_id: MVarId, fvars: &[ExprId], has_ctx_locals: bool, v: ExprId) -> Result<Option<ExprId>, MetaError>`. `Ok(None)` means one of the oracle's two internal failures. `Err` means a real error.
  - `MetaCtx::fvar_ids(&self, xs: &[ExprId]) -> Vec<NameId>` (`pub(crate)`)
- Consumes (existing): `MetaCtx::{guarded, node, get_app_fn, get_app_args, mk_app_spine, head_beta, infer_type, occurs_check, fvar_id_of, local_decl_depends_on, reduce_local_context, mk_aux_mvar_at, local_entry, lctx_checkpoint, lctx_restore}`, plus the three newly `pub(crate)` `assign.rs` functions.

Note on the spec: § Structure gives `except_fvars: &[ExprId]`. `LocalCtxSnapshot` has no `Store`, so it cannot decode an `ExprId`. It takes `&[NameId]` instead, and callers decode with `fvar_ids`, the same split `reduced` already uses.

- [ ] **Step 1: Write the failing `is_sub_prefix_of` tests** in `local_snapshot.rs`:

```rust
#[cfg(test)]
mod sub_prefix_tests {
    use crate::test_support::{const_named, fresh_fvar, with_prelude0_ctx};

    /// oracle: `LocalContext.isSubPrefixOf` (`LocalContext.lean:534-552`):
    /// `lctx₁ - except` must be an ordered subsequence of `lctx₂`, with
    /// gaps allowed.
    #[test]
    fn is_sub_prefix_of_is_an_ordered_subsequence_test() {
        with_prelude0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let cp = ctx.lctx_checkpoint();
            let empty = ctx.current_lctx();
            let x = fresh_fvar(ctx, n, "x");
            let s_x = ctx.current_lctx();
            let y = fresh_fvar(ctx, n, "y");
            let _z = fresh_fvar(ctx, n, "z");
            let s_xyz = ctx.current_lctx();
            let (xid, yid) = (ctx.fvar_id_of(x).unwrap(), ctx.fvar_id_of(y).unwrap());
            // `[x, z]`: `y` erased, so a GAP relative to `s_xyz`.
            let s_xz = std::sync::Arc::new(s_xyz.reduced(&[(y, yid)], |f| ctx.fvar_id_of(f)));

            assert!(empty.is_sub_prefix_of(&s_xyz, &[]));
            assert!(s_x.is_sub_prefix_of(&s_xyz, &[]));
            assert!(s_xyz.is_sub_prefix_of(&s_xyz, &[]));
            assert!(s_xz.is_sub_prefix_of(&s_xyz, &[]), "gaps are allowed");
            assert!(!s_xyz.is_sub_prefix_of(&s_xz, &[]), "y is missing on the right");
            assert!(s_xyz.is_sub_prefix_of(&s_xz, &[yid]), "y is subtracted");
            assert!(!s_x.is_sub_prefix_of(&empty, &[]));
            assert!(s_x.is_sub_prefix_of(&empty, &[xid]));
            ctx.lctx_restore(cp);
        });
    }
}
```

- [ ] **Step 2: Run it and confirm it fails.** Run: `cargo test -p leanr_meta --lib is_sub_prefix_of`. Expected: a compile error, because `is_sub_prefix_of` is not defined.

- [ ] **Step 3: Implement `is_sub_prefix_of`** in `impl LocalCtxSnapshot`:

```rust
    /// oracle: `LocalContext.isSubPrefixOf` / `isSubPrefixOfAux`
    /// (`LocalContext.lean:534-552`): `self` minus `except` is of the form
    /// `x_1 … x_n`, and `other` has a prefix `B_1* x_1 … B_n* x_n`. That is,
    /// an ORDERED subsequence, with gaps allowed in `other`.
    ///
    /// The oracle walks `PArray (Option LocalDecl)`, which may hold holes
    /// (`none`) where a decl was erased. `local_names` is compacted on
    /// erase with order preserved (`reduced`), and a hole never matches,
    /// so the answer is the same on both representations. `except` is by
    /// `NameId` because this struct has no `Store` to decode an `ExprId`
    /// (`MetaCtx::fvar_ids` decodes, the same split `reduced` uses).
    pub(crate) fn is_sub_prefix_of(&self, other: &LocalCtxSnapshot, except: &[NameId]) -> bool {
        let mut j = 0;
        for e1 in &self.local_names {
            if except.contains(&e1.id) {
                continue;
            }
            loop {
                match other.local_names.get(j) {
                    None => return false,
                    Some(e2) => {
                        j += 1;
                        if e2.id == e1.id {
                            break;
                        }
                    }
                }
            }
        }
        true
    }
```

- [ ] **Step 4: Run it and confirm it passes.** Run: `cargo test -p leanr_meta --lib is_sub_prefix_of`. Expected: PASS.

- [ ] **Step 5: Write the failing slow-path tests.** Create `crates/leanr_meta/src/check_assignment.rs` holding ONLY the test module below for now (the implementation goes in Step 7). Add `mod check_assignment;` to `lib.rs`.

```rust
#[cfg(test)]
mod tests {
    use leanr_kernel::bank::ExprId;
    use leanr_kernel::bank::terms::Node;
    use leanr_kernel::BinderInfo;

    use crate::test_support::{const_dotted, const_named, fresh_fvar, fresh_mvar, with_prelude0_ctx};
    use crate::{MVarId, MVarKind, MetaCtx};

    fn sort0(ctx: &mut MetaCtx) -> ExprId {
        let base = Some(ctx.view.store);
        let z = ctx.scratch.level_zero(base).expect("level");
        ctx.scratch.expr_sort(base, z).expect("sort")
    }

    fn mvar_id(ctx: &MetaCtx, e: ExprId) -> MVarId {
        match ctx.node(e) {
            Node::MVar { id: Some(n) } => MVarId(n),
            _ => panic!("not an mvar"),
        }
    }

    /// oracle `checkMVar` (`ExprDefEq.lean:880-938`): `?o` (empty ctx)
    /// `:= ?i` (ctx `{x}`). `?i`'s ctx is not a sub-prefix of `?o`'s, the
    /// depths are equal, it is natural, `ctxApprox` is on, and `{}` is a
    /// sub-prefix of `{x}`. So `?i := ?aux` with `x` erased, and the
    /// checked term is `?aux`. This is the restriction that breaks the
    /// spec's § Evidence cycle.
    #[test]
    fn check_mvar_restricts_an_inner_mvar_under_ctx_approx() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let x = fresh_fvar(ctx, n, "x");
            let xid = ctx.fvar_id_of(x).unwrap();
            let (i, iid) = ctx.mk_aux_mvar(n).expect("inner");
            let out = ctx.check_assignment_aux(oid, &[], false, i).expect("check");
            let aux = out.expect("restricted, not refused");
            assert_ne!(aux, i);
            assert_eq!(ctx.mctx.assignment(iid), Some(aux), "inner := ?aux");
            let aux_lctx = ctx.mctx.decl(mvar_id(ctx, aux)).unwrap().lctx.clone();
            assert!(aux_lctx.lctx().get(xid).is_none(), "x erased from ?aux's ctx");
            ctx.lctx_restore(cp);
        });
    }

    /// Same shape with `ctx_approx` off: refused (`:905`), and nothing
    /// is assigned.
    #[test]
    fn check_mvar_refuses_without_ctx_approx() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = false;
            let n = const_named(ctx, "N");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let _x = fresh_fvar(ctx, n, "x");
            let (i, iid) = ctx.mk_aux_mvar(n).expect("inner");
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, i), Ok(None));
            assert!(!ctx.mctx.is_assigned(iid));
            ctx.lctx_restore(cp);
        });
    }

    /// `:901`: a syntheticOpaque inner mvar, or one at another depth, is
    /// refused.
    #[test]
    fn check_mvar_refuses_synthetic_opaque_and_other_depth() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let _x = fresh_fvar(ctx, n, "x");
            let lctx = ctx.current_lctx();
            let (so, soid) = ctx
                .mk_aux_mvar_at(lctx, n, MVarKind::SyntheticOpaque, None)
                .expect("opaque");
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, so), Ok(None));
            assert!(!ctx.mctx.is_assigned(soid));
            let (i, iid) = ctx.mk_aux_mvar(n).expect("inner");
            let r = ctx.with_new_mctx_depth(false, |c| c.check_assignment_aux(oid, &[], false, i));
            assert_eq!(r, Ok(None), "inner was minted at depth 0, check runs at 1");
            assert!(!ctx.mctx.is_assigned(iid));
            ctx.lctx_restore(cp);
        });
    }

    /// `:890`: under `has_ctx_locals` every unassigned non-self mvar
    /// fails, even a sub-prefix one.
    #[test]
    fn check_mvar_refuses_under_has_ctx_locals() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let (_o, oid) = fresh_mvar(ctx, n);
            let (m, _) = fresh_mvar(ctx, n);
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, m), Ok(Some(m)));
            assert_eq!(ctx.check_assignment_aux(oid, &[], true, m), Ok(None));
        });
    }

    /// `:880-883`: `?o` occurring in its own value fails (occurs check),
    /// and an assigned mvar is followed to its value.
    #[test]
    fn check_mvar_occurs_check_and_follows_assignments() {
        with_prelude0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let zero = const_dotted(ctx, "N", "zero");
            let (o, oid) = fresh_mvar(ctx, n);
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, o), Ok(None));
            let (m, mid) = fresh_mvar(ctx, n);
            ctx.mctx.assign(mid, zero).unwrap();
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, m), Ok(Some(zero)));
        });
    }

    /// Review Focus #2: `throwUnknownMVar`. A real error, not `None`.
    #[test]
    fn check_mvar_errors_on_an_undeclared_mvar() {
        with_prelude0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let (_o, oid) = fresh_mvar(ctx, n);
            let base = Some(ctx.view.store);
            let s = ctx.scratch.intern_str(base, "_never_declared").unwrap();
            let name = ctx.scratch.name_str(base, None, s).unwrap();
            let ghost = ctx.scratch.expr_mvar(base, Some(name)).unwrap();
            assert!(ctx.check_assignment_aux(oid, &[], false, ghost).is_err());
        });
    }

    /// `to_erase` (`:916-930`): an entry of `fvars` that DEPENDS on an
    /// erased variable is erased too. `x : Sort 0`, `y : x`, inner ctx
    /// `{x, y}`, outer ctx `{}`, `fvars = [y]`. `x` is erased (not in the
    /// outer ctx, not in `fvars`), and so is `y` (it depends on `x`).
    /// Control: `y : N` does not depend on `x`, so it survives.
    #[test]
    fn check_mvar_erases_a_dependent_fvars_entry() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let s0 = sort0(ctx);
            for (y_depends, y_survives) in [(true, false), (false, true)] {
                let cp = ctx.lctx_checkpoint();
                let (_o, oid) = fresh_mvar(ctx, n);
                let x = fresh_fvar(ctx, s0, "x");
                let y = fresh_fvar(ctx, if y_depends { x } else { n }, "y");
                let yid = ctx.fvar_id_of(y).unwrap();
                let (i, _) = ctx.mk_aux_mvar(n).expect("inner");
                let aux = ctx
                    .check_assignment_aux(oid, &[y], false, i)
                    .expect("check")
                    .expect("restricted");
                let lctx = ctx.mctx.decl(mvar_id(ctx, aux)).unwrap().lctx.clone();
                assert_eq!(lctx.lctx().get(yid).is_some(), y_survives, "y_depends={y_depends}");
                ctx.lctx_restore(cp);
            }
        });
    }

    /// `checkFVar` (`:851-878`): a genuine let outside the mvar's ctx is
    /// followed into its value; a `have` is not; a plain fvar is in scope
    /// only through `fvars`.
    #[test]
    fn check_fvar_follows_lets_not_haves() {
        with_prelude0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let zero = const_dotted(ctx, "N", "zero");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let l = ctx.push_let_decl(None, n, zero, false).expect("let");
            let h = ctx.push_let_decl(None, n, zero, true).expect("have");
            let x = fresh_fvar(ctx, n, "x");
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, l), Ok(Some(zero)));
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, h), Ok(None));
            assert_eq!(ctx.check_assignment_aux(oid, &[h], false, h), Ok(Some(h)));
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, x), Ok(None));
            assert_eq!(ctx.check_assignment_aux(oid, &[x], false, x), Ok(Some(x)));
            ctx.lctx_restore(cp);
        });
    }

    /// `check`'s `.app` arm (`:1004-1021`): on an internal failure, a
    /// head-beta target is reduced and retried. `(fun _ : N => N.zero) x`
    /// with `x` out of scope checks to `N.zero`.
    #[test]
    fn check_retries_a_head_beta_target() {
        with_prelude0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let zero = const_dotted(ctx, "N", "zero");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let x = fresh_fvar(ctx, n, "x");
            let base = Some(ctx.view.store);
            let k = ctx.scratch.expr_lam(base, None, n, zero, BinderInfo::Default).unwrap();
            let redex = ctx.scratch.expr_app(base, k, x).unwrap();
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, redex), Ok(Some(zero)));
            ctx.lctx_restore(cp);
        });
    }

    /// `checkApp`'s `ctxApprox` rescue (`:958-985`) and
    /// `assignToConstFun` (`:946-952`): `?o := ?f x` with `x` out of
    /// `?o`'s scope. `?f := fun _ => ?n`, and the checked term is `?n`,
    /// minted in `?o`'s ctx. Off without `ctx_approx`.
    #[test]
    fn check_app_rescues_an_out_of_scope_mvar_app() {
        for ctx_approx in [true, false] {
            with_prelude0_ctx(|ctx| {
                ctx.cfg.ctx_approx = ctx_approx;
                let n = const_named(ctx, "N");
                let base = Some(ctx.view.store);
                let n_to_n = ctx.scratch.expr_forall(base, None, n, n, BinderInfo::Default).unwrap();
                let cp = ctx.lctx_checkpoint();
                let (_o, oid) = fresh_mvar(ctx, n);
                let (f, fid) = fresh_mvar(ctx, n_to_n);
                let x = fresh_fvar(ctx, n, "x");
                let fx = ctx.scratch.expr_app(base, f, x).unwrap();
                let out = ctx.check_assignment_aux(oid, &[], false, fx).expect("check");
                if ctx_approx {
                    let new = out.expect("rescued");
                    assert!(matches!(ctx.node(new), Node::MVar { .. }));
                    let fval = ctx.mctx.assignment(fid).expect("?f assigned");
                    assert!(matches!(ctx.node(fval), Node::Lam { .. }), "?f := fun _ => ?n");
                } else {
                    assert_eq!(out, None);
                    assert!(!ctx.mctx.is_assigned(fid));
                }
                ctx.lctx_restore(cp);
            });
        }
    }
}
```

`mk_aux_mvar` is `pub(crate)` and mints at the AMBIENT ctx, which is how the tests get an inner mvar that sees `x`. `fresh_mvar` always mints with an EMPTY ctx.

- [ ] **Step 6: Run them and confirm they fail.** Run: `cargo test -p leanr_meta --lib check_assignment::tests`. Expected: compile errors, because `check_assignment_aux` and `fvar_ids` do not exist.

- [ ] **Step 7: Implement the slow path.** Put this ABOVE the test module in `check_assignment.rs`:

```rust
//! oracle: `CheckAssignment` and `CheckAssignmentQuick`
//! (`Lean/Meta/ExprDefEq.lean:803-1086`, v4.33.0-rc1), the scope check
//! behind `checkAssignment` (`:1151-1172`, the driver in `assign.rs`).
//!
//! The quick check is a bool predicate. When it says `false` the driver
//! runs the slow path, which REWRITES the value. It can restrict an
//! out-of-scope metavariable to a smaller context (`checkMVar` under
//! `ctxApprox`), follow a genuine let to its value (`checkFVar`),
//! turn `?f x` with `x` out of scope into a constant function
//! (`checkApp` + `assignToConstFun`), and head-beta a redex and retry
//! (`check`). The driver assigns the rewritten term, never the original
//! (spec `2026-10-02-check-assignment-ctx-approx-design.md`).

use std::collections::HashMap;
use std::sync::Arc;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::Nat;

use crate::{LocalCtxSnapshot, MVarId, MVarKind, MetaCtx, MetaError};

/// The oracle's two internal exception ids, `outOfScopeExceptionId` and
/// `checkAssignmentExceptionId`, which `run` (`:840-847`) turns into
/// `none`. A real `MetaError` (budget, depth, an unknown metavariable)
/// is NOT one of them and propagates.
enum CheckErr {
    OutOfScope,
    Failure,
    Meta(MetaError),
}

impl From<MetaError> for CheckErr {
    fn from(e: MetaError) -> Self {
        CheckErr::Meta(e)
    }
}

impl From<leanr_kernel::KernelError> for CheckErr {
    fn from(e: leanr_kernel::KernelError) -> Self {
        CheckErr::Meta(e.into())
    }
}

type CheckResult = Result<ExprId, CheckErr>;

/// oracle: `CheckAssignment.Context` (`:796-802`) plus `State.cache`.
/// The cache lives for one `check_assignment_aux` call, matching `run`'s
/// fresh state, and is keyed by hash-consed `ExprId` (the oracle's
/// `checkCache` is keyed by `Expr`).
struct CheckCtx<'a> {
    mvar_id: MVarId,
    decl_lctx: Arc<LocalCtxSnapshot>,
    fvars: &'a [ExprId],
    has_ctx_locals: bool,
    cache: HashMap<ExprId, ExprId>,
}

impl<'e> MetaCtx<'e> {
    /// The `NameId`s of the fvars among `xs`, which is the shape
    /// `LocalCtxSnapshot::is_sub_prefix_of` takes for `except`.
    pub(crate) fn fvar_ids(&self, xs: &[ExprId]) -> Vec<NameId> {
        xs.iter().filter_map(|x| self.fvar_id_of(*x)).collect()
    }

    /// oracle: `checkAssignmentAux` (`:954-956`) = `run (check v)`.
    /// `Ok(None)` is either internal failure. Its callers are the
    /// `check_assignment` driver (when the quick check fails) and
    /// `assign_to_const_fun`.
    pub(crate) fn check_assignment_aux(
        &mut self,
        mvar_id: MVarId,
        fvars: &[ExprId],
        has_ctx_locals: bool,
        v: ExprId,
    ) -> Result<Option<ExprId>, MetaError> {
        let decl_lctx = match self.mctx.decl(mvar_id) {
            Some(d) => Arc::clone(&d.lctx),
            None => {
                return Err(MetaError::MVar(format!(
                    "check_assignment_aux: unknown metavariable {mvar_id:?}"
                )))
            }
        };
        let mut cx = CheckCtx {
            mvar_id,
            decl_lctx,
            fvars,
            has_ctx_locals,
            cache: HashMap::new(),
        };
        match self.check(&mut cx, v) {
            Ok(e) => Ok(Some(e)),
            Err(CheckErr::OutOfScope | CheckErr::Failure) => Ok(None),
            Err(CheckErr::Meta(e)) => Err(e),
        }
    }

    /// oracle: `check` (`:987-1035`). Only successes are cached, as with
    /// `checkCache`.
    fn check(&mut self, cx: &mut CheckCtx, e: ExprId) -> CheckResult {
        if !self.data(e).has_expr_mvar() && !self.data(e).has_fvar() {
            return Ok(e);
        }
        if let Some(r) = cx.cache.get(&e) {
            return Ok(*r);
        }
        let r = self.guarded(|s| Ok(s.check_body(cx, e)))??;
        cx.cache.insert(e, r);
        Ok(r)
    }

    fn check_body(&mut self, cx: &mut CheckCtx, e: ExprId) -> CheckResult {
        let st = Some(self.view.store);
        match self.node(e) {
            Node::MData { data, expr } => {
                let b = self.check(cx, expr)?;
                Ok(self.scratch.expr_mdata(st, data, b)?)
            }
            Node::Proj { type_name, idx, structure } => {
                let s = self.check(cx, structure)?;
                Ok(self.scratch.expr_proj(st, type_name, &Nat::from(idx), s)?)
            }
            Node::ProjBig { type_name, idx, structure } => {
                let i = self.scratch.nat_at(st, idx).clone();
                let s = self.check(cx, structure)?;
                Ok(self.scratch.expr_proj(st, type_name, &i, s)?)
            }
            Node::Lam { binder_name, binder_type, body, binder_info } => {
                let d = self.check(cx, binder_type)?;
                let b = self.check(cx, body)?;
                Ok(self.scratch.expr_lam(st, binder_name, d, b, binder_info)?)
            }
            Node::Forall { binder_name, binder_type, body, binder_info } => {
                let d = self.check(cx, binder_type)?;
                let b = self.check(cx, body)?;
                Ok(self.scratch.expr_forall(st, binder_name, d, b, binder_info)?)
            }
            Node::LetE { decl_name, ty, value, body, non_dep } => {
                let t = self.check(cx, ty)?;
                let v = self.check(cx, value)?;
                let b = self.check(cx, body)?;
                Ok(self.scratch.expr_let(st, decl_name, t, v, b, non_dep)?)
            }
            Node::FVar { .. } => self.check_fvar(cx, e),
            Node::MVar { .. } => self.check_mvar(cx, e),
            // `:1004-1021`: on either internal failure, a head-beta
            // target is reduced and retried. The oracle's commented-out
            // `whnfR` fallback (`:1024-1034`) is not ported.
            Node::App { .. } => match self.check_app(cx, e) {
                Err(CheckErr::OutOfScope | CheckErr::Failure) if self.is_head_beta_target(e) => {
                    let e2 = self.head_beta(e)?;
                    self.check_app(cx, e2)
                }
                r => r,
            },
            _ => Ok(e),
        }
    }

    /// oracle: `Expr.isHeadBetaTarget` (`useZeta := false`): an
    /// application whose head is a lambda. Only `Lam` is modelled, the
    /// same simplification `head_beta` (`whnf.rs`) makes.
    fn is_head_beta_target(&self, e: ExprId) -> bool {
        matches!(self.node(e), Node::App { .. })
            && matches!(self.node(self.get_app_fn(e)), Node::Lam { .. })
    }

    /// oracle: `checkFVar` (`:851-878`). A genuine let (`nondep :=
    /// false`) in the AMBIENT ctx is followed into its value. A `have`
    /// is "locally a cdecl" and takes the `fvars` test.
    fn check_fvar(&mut self, cx: &mut CheckCtx, e: ExprId) -> CheckResult {
        let Node::FVar { id: Some(fid) } = self.node(e) else {
            return Ok(e);
        };
        if cx.decl_lctx.lctx().get(fid).is_some() {
            return Ok(e);
        }
        let let_value = self
            .lctx
            .get(fid)
            .and_then(|d| d.value)
            .filter(|_| self.local_entry(fid).is_some_and(|en| !en.nondep));
        if let Some(v) = let_value {
            return self.check(cx, v);
        }
        if cx.fvars.contains(&e) {
            Ok(e)
        } else {
            Err(CheckErr::OutOfScope)
        }
    }

    /// oracle: `checkMVar` (`:880-938`).
    fn check_mvar(&mut self, cx: &mut CheckCtx, e: ExprId) -> CheckResult {
        let Node::MVar { id: Some(n) } = self.node(e) else {
            return Ok(e);
        };
        let id = MVarId(n);
        if id == cx.mvar_id {
            return Err(CheckErr::Failure); // occurs check (:883-885)
        }
        if let Some(v) = self.mctx.assignment(id) {
            return self.check(cx, v);
        }
        let Some(decl) = self.mctx.decl(id) else {
            return Err(MetaError::MVar(format!("check_mvar: unknown metavariable {id:?}")).into());
        };
        let (inner_lctx, inner_ty, inner_kind) = (Arc::clone(&decl.lctx), decl.ty, decl.kind);
        if cx.has_ctx_locals {
            return Err(CheckErr::Failure); // :890
        }
        if let Some(d) = self.mctx.delayed_assignment(id) {
            // :892-895: occurs-check at the pending mvar.
            let pending = d.mvar_id_pending;
            let pending_e = self.scratch.expr_mvar(Some(self.view.store), Some(pending.0))?;
            if !self.occurs_check(cx.mvar_id, pending_e)? {
                return Err(CheckErr::Failure);
            }
        }
        let except = self.fvar_ids(cx.fvars);
        if inner_lctx.is_sub_prefix_of(&cx.decl_lctx, &except) {
            return Ok(e); // :897-900
        }
        if self.mctx.expr_mvar_depth(id) != Some(self.mctx.depth())
            || inner_kind == MVarKind::SyntheticOpaque
        {
            return Err(CheckErr::Failure); // :901-903
        }
        if !(self.cfg.ctx_approx && cx.decl_lctx.is_sub_prefix_of(&inner_lctx, &[])) {
            return Err(CheckErr::Failure); // :905-907
        }
        let to_erase = self.ctx_approx_to_erase(&inner_lctx, cx)?;
        // `lctx.erase` for each, plus the `localInstances` filter
        // (:931-933): `reduced` does both.
        let reduced = self.reduce_local_context(&inner_lctx, &to_erase)?;
        let ty = self.check(cx, inner_ty)?;
        let (aux, _) = self.mk_aux_mvar_at(reduced, ty, MVarKind::Natural, None)?;
        self.mctx.assign(id, aux)?;
        Ok(aux)
    }

    /// oracle `:920-930`: fold over the INNER ctx in declaration order.
    /// Keep a decl the assigned mvar's ctx has. An entry of `fvars` is
    /// kept unless it depends on something already erased
    /// (`findLocalDeclDependsOn`, `generalizeNondepLet := true` by
    /// default, `MetavarContext.lean:744`). Erase everything else.
    fn ctx_approx_to_erase(
        &mut self,
        inner: &LocalCtxSnapshot,
        cx: &CheckCtx,
    ) -> Result<Vec<ExprId>, MetaError> {
        let fvar_ids = self.fvar_ids(cx.fvars);
        let mut to_erase: Vec<ExprId> = Vec::new();
        let mut erased_ids: Vec<NameId> = Vec::new();
        for entry in inner.entries().to_vec() {
            if cx.decl_lctx.lctx().get(entry.id).is_some() {
                continue;
            }
            if fvar_ids.contains(&entry.id) {
                let Some(d) = inner.lctx().get(entry.id) else {
                    continue;
                };
                let (ty, value) = (d.ty, d.value);
                if !self.local_decl_depends_on(ty, value, entry.nondep, &erased_ids, true)? {
                    continue;
                }
            }
            to_erase.push(entry.fvar);
            erased_ids.push(entry.id);
        }
        Ok(to_erase)
    }

    /// oracle: `checkApp` (`:958-985`).
    fn check_app(&mut self, cx: &mut CheckCtx, e: ExprId) -> CheckResult {
        let f = self.get_app_fn(e);
        let args = self.get_app_args(e);
        let rescuable = matches!(self.node(f), Node::MVar { .. })
            && self.cfg.ctx_approx
            && args.iter().all(|a| matches!(self.node(*a), Node::FVar { .. }));
        let f2 = self.check(cx, f)?;
        let mut checked = Vec::with_capacity(args.len());
        for a in &args {
            match self.check(cx, *a) {
                Ok(a2) => checked.push(a2),
                // `catchInternalId outOfScopeExceptionId`: ONLY
                // out-of-scope is caught, and only on the rescuable path.
                Err(CheckErr::OutOfScope) if rescuable => {
                    return self.ctx_approx_const_fun(cx, e, f2, args.len());
                }
                Err(other) => return Err(other),
            }
        }
        Ok(self.mk_app_spine(f2, &checked)?)
    }

    /// The handler arm of `checkApp` (`:966-984`).
    fn ctx_approx_const_fun(
        &mut self,
        cx: &mut CheckCtx,
        e: ExprId,
        f: ExprId,
        num_args: usize,
    ) -> CheckResult {
        let Node::MVar { id: Some(fid) } = self.node(f) else {
            return Err(CheckErr::OutOfScope); // `if !f.isMVar then throw ex`
        };
        if self.mctx.is_delayed_assigned(MVarId(fid)) {
            return Err(CheckErr::OutOfScope);
        }
        let e_ty = self.infer_type(e)?;
        let mvar_ty = self.check(cx, e_ty)?;
        // `mkAuxMVar ctx.mvarDecl.lctx ctx.mvarDecl.localInstances`:
        // the ASSIGNED mvar's ctx. The instances travel inside the
        // snapshot.
        let (new_mvar, _) =
            self.mk_aux_mvar_at(Arc::clone(&cx.decl_lctx), mvar_ty, MVarKind::Natural, None)?;
        if self.assign_to_const_fun(f, num_args, new_mvar)? {
            Ok(new_mvar)
        } else {
            Err(CheckErr::OutOfScope)
        }
    }

    /// oracle: `assignToConstFun` (`:946-952`). The telescope fvars are
    /// scoped with `lctx_checkpoint`/`lctx_restore`, as `assign_const`
    /// does, because `forall_bounded_telescope` pushes into the ambient
    /// ctx.
    fn assign_to_const_fun(
        &mut self,
        mvar: ExprId,
        num_args: usize,
        new_mvar: ExprId,
    ) -> Result<bool, MetaError> {
        let mvar_ty = self.infer_type(mvar)?;
        let cp = self.lctx_checkpoint();
        let r = self.assign_to_const_fun_body(mvar, mvar_ty, num_args, new_mvar);
        self.lctx_restore(cp);
        r
    }

    fn assign_to_const_fun_body(
        &mut self,
        mvar: ExprId,
        mvar_ty: ExprId,
        num_args: usize,
        new_mvar: ExprId,
    ) -> Result<bool, MetaError> {
        let xs = self.forall_bounded_telescope(mvar_ty, num_args)?;
        if xs.len() != num_args {
            return Ok(false);
        }
        let Some(v) = self.mk_lambda_fvars_with_let_deps(&xs, new_mvar)? else {
            return Ok(false);
        };
        let Node::MVar { id: Some(n) } = self.node(mvar) else {
            return Ok(false);
        };
        let Some(v) = self.check_assignment_aux(MVarId(n), &[], false, v)? else {
            return Ok(false);
        };
        self.check_types_and_assign(mvar, v)
    }
}
```

The `impl<'e> MetaCtx<'e>` header matches `mk_binding.rs:43`. If `self.data`, `self.lctx` or `self.scratch.nat_at` are named differently, use the names `mk_binding.rs`/`whnf.rs` use (`whnf.rs:1825` uses `nat_at`).

- [ ] **Step 8: Run the tests and confirm they pass.** Run: `cargo test -p leanr_meta --lib check_assignment::tests` and `cargo test -p leanr_meta --lib`. Expected: all PASS. Behaviour is unchanged elsewhere, because nothing calls `check_assignment_aux` outside the tests yet.

- [ ] **Step 9: Run the mutations** one at a time, reverting each before the next. Record the killing test.
  - (a) `is_sub_prefix_of` returns `true` unconditionally. Expect `is_sub_prefix_of_is_an_ordered_subsequence_test`.
  - (b) Ignore `except`. Expect the same test (the `[yid]`/`[xid]` assertions).
  - (c) In `check_mvar`, delete `self.mctx.assign(id, aux)?;`. Expect `check_mvar_restricts_an_inner_mvar_under_ctx_approx`.
  - (d) In `ctx_approx_to_erase`, make the `fvars` branch always `continue`. Expect `check_mvar_erases_a_dependent_fvars_entry`.
  - (e) Delete the `self.cfg.ctx_approx &&` conjunct in `check_mvar`. Expect `check_mvar_refuses_without_ctx_approx`.
  - (f) Delete the depth comparison. Expect `check_mvar_refuses_synthetic_opaque_and_other_depth`.
  - (g) Delete the head-beta retry arm. Expect `check_retries_a_head_beta_target`.
  - (h) In `check_fvar`, delete the `let_value` follow. Expect `check_fvar_follows_lets_not_haves`.
  - (i) Make `rescuable` always `false`. Expect `check_app_rescues_an_out_of_scope_mvar_app`.
  - (j) Delete the `has_ctx_locals` early return. Expect `check_mvar_refuses_under_has_ctx_locals`.

  A survivor means a test is missing. Add the test, then re-run.

- [ ] **Step 10: Commit.**

```bash
cargo fmt --all
cargo clippy -p leanr_meta --all-targets -- -D warnings
git add crates/leanr_meta/src/local_snapshot.rs crates/leanr_meta/src/check_assignment.rs crates/leanr_meta/src/lib.rs crates/leanr_meta/src/assign.rs
git commit   # "leanr_meta: isSubPrefixOf + CheckAssignment slow path (checkAssignment T1)" + mutation list + Co-Authored-By
```

Clippy may flag `dead_code` on `check_assignment_aux` and friends. They have test callers only until Task 2, so add `#[allow(dead_code)] // wired in by Task 2` on the items that need it. Task 2 removes every such allow.

---

### Task 2: wire the driver and make the quick check real

**Files:**
- Modify: `crates/leanr_meta/src/assign.rs`. Rewrite `check_assignment` (about :990-1016). Delete `check_assignment_scope` and `check_assignment_scope_body` (about :1018-1165, doc comments included). Update the module doc's `# Depth / read-only` paragraph (about :61-66). Move `check_assignment_scope_body_treats_a_have_as_a_cdecl` (about :2741) and flip `check_fvar_seam_shows_only_with_zeta_delta_off` (about :2834). Add a rollback test.
- Modify: `crates/leanr_meta/src/check_assignment.rs` (add the quick check, remove the Task 1 `dead_code` allows)
- Modify (doc only): `crates/leanr_meta/src/synth.rs:2165-2176`, `crates/leanr_elab/src/config.rs:9-12`
- Test: `crates/leanr_meta/src/check_assignment.rs`, `crates/leanr_meta/src/assign.rs`

**Interfaces:**
- Consumes: `check_assignment_aux`, `fvar_ids`, `is_sub_prefix_of` (Task 1).
- Produces: `MetaCtx::check_assignment_scope(&mut self, mvar_id: MVarId, fvars: &[ExprId], has_ctx_locals: bool, e: ExprId) -> Result<bool, MetaError>` in `check_assignment.rs` (`pub(crate)`). The signature of `check_assignment(mvar_id, fvars, v) -> Result<Option<ExprId>, MetaError>` is unchanged.

- [ ] **Step 1: Write the failing quick-check tests** in `check_assignment.rs` `mod tests`:

```rust
    /// oracle `CheckAssignmentQuick` mvar arm (`:1070-1077`): each of
    /// the six conditions returns `false` ("use the slow path"). A
    /// declared, unassigned, sub-prefix, non-delayed mvar returns `true`.
    #[test]
    fn quick_check_mvar_arm_falls_through_on_each_condition() {
        with_prelude0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let zero = const_dotted(ctx, "N", "zero");
            let cp = ctx.lctx_checkpoint();
            let (o, oid) = fresh_mvar(ctx, n);
            let (ok, _) = fresh_mvar(ctx, n);
            assert!(ctx.check_assignment_scope(oid, &[], false, ok).unwrap(), "sub-prefix");
            let (asg, asg_id) = fresh_mvar(ctx, n);
            ctx.mctx.assign(asg_id, zero).unwrap();
            assert!(!ctx.check_assignment_scope(oid, &[], false, asg).unwrap(), "(1) assigned");
            assert!(!ctx.check_assignment_scope(oid, &[], false, o).unwrap(), "(2) self");
            let base = Some(ctx.view.store);
            let s = ctx.scratch.intern_str(base, "_never_declared_q").unwrap();
            let name = ctx.scratch.name_str(base, None, s).unwrap();
            let ghost = ctx.scratch.expr_mvar(base, Some(name)).unwrap();
            assert!(!ctx.check_assignment_scope(oid, &[], false, ghost).unwrap(), "(3) undeclared");
            assert!(!ctx.check_assignment_scope(oid, &[], true, ok).unwrap(), "(4) has_ctx_locals");
            let _x = fresh_fvar(ctx, n, "x");
            let (inner, _) = ctx.mk_aux_mvar(n).unwrap();
            assert!(!ctx.check_assignment_scope(oid, &[], false, inner).unwrap(), "(5) not sub-prefix");
            let (d, did) = fresh_mvar(ctx, n);
            let (p, pid) = fresh_mvar(ctx, n);
            let _ = p;
            ctx.mctx.assign_delayed(did, vec![], pid).unwrap();
            assert!(!ctx.check_assignment_scope(oid, &[], false, d).unwrap(), "(6) delayed");
            ctx.lctx_restore(cp);
        });
    }

    /// The driver returns the REWRITTEN term (`:1164-1168`), never the
    /// original `v`.
    #[test]
    fn driver_returns_the_slow_path_rewrite() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let _x = fresh_fvar(ctx, n, "x");
            let (i, iid) = ctx.mk_aux_mvar(n).unwrap();
            let got = ctx.check_assignment(oid, &[], i).unwrap().expect("restricted");
            assert_ne!(got, i, "assigning the original would rebuild the § Evidence cycle");
            assert_eq!(ctx.mctx.assignment(iid), Some(got));
            ctx.lctx_restore(cp);
        });
    }
```

`assign_delayed(id, fvars: Vec<ExprId>, pending)` is `mvar_ctx.rs:245`.

Move `check_assignment_scope_body_treats_a_have_as_a_cdecl` from `assign.rs` into this module, renamed `quick_check_treats_a_have_as_a_cdecl`. Change its calls to `ctx.check_assignment_scope(mid, &fvars, false, e)`. Keep its three assertions as they are: the quick check still answers `false` for a genuine let, and only the SLOW path rescues it.

- [ ] **Step 2: Flip the `checkFVar` seam pin** in `assign.rs`. Rename `check_fvar_seam_shows_only_with_zeta_delta_off` to `check_fvar_follows_a_genuine_let_value_in_both_zeta_modes`. Change the loop to `for zeta_delta in [true, false]`, with `want = true` in both arms. Replace the doc comment with: "oracle `checkFVar` (`ExprDefEq.lean:851-878`): `?m =?= l` for a genuine let `l` outside `?m`'s context is `true`, with `?m := N.zero`, whatever `zetaDelta` says (measured, v4.33.0-rc1). The slow path's let rescue gives that answer."

- [ ] **Step 3: Write the rollback test** in `assign.rs` `mod tests` (Review Focus #4). It calls the private `is_def_eq_mvar_mvar` directly, because the top-level `is_def_eq` checkpoint would roll back on its own and hide the bug:

```rust
    /// `isDefEqQuickMVarMVar`'s `checkpointDefEq` (`ExprDefEq.lean:1963-1976`):
    /// direction 1 (`?o := ?i`) restricts `?i := ?aux`, then fails
    /// `check_types_and_assign` (`N` vs `Sort 0`). The restriction must be
    /// rolled back before direction 2 runs.
    #[test]
    fn failed_first_direction_rolls_back_the_restriction() {
        use crate::test_support::{const_named, with_prelude0_ctx};
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let base = Some(ctx.view.store);
            let z = ctx.scratch.level_zero(base).unwrap();
            let s0 = ctx.scratch.expr_sort(base, z).unwrap();
            let cp = ctx.lctx_checkpoint();
            let (o, _) = fresh_mvar(ctx, n);
            let _x = fresh_fvar(ctx, n, "x");
            let (i, iid) = ctx.mk_aux_mvar(s0).unwrap();
            assert_eq!(ctx.is_def_eq_mvar_mvar(o, i).unwrap(), Some(false));
            assert!(!ctx.mctx.is_assigned(iid), "restriction leaked past rollback");
            ctx.lctx_restore(cp);
        });
    }
```

- [ ] **Step 4: Run them and confirm they fail.** Run: `cargo test -p leanr_meta --lib quick_check driver_returns check_fvar_follows failed_first_direction`. Expected: compile errors (the 4-argument `check_assignment_scope` does not exist yet), and after Step 5 alone, the flipped pin and `driver_returns_the_slow_path_rewrite` fail. The rollback test may already pass, because nothing restricts until Step 6. It is a guard, and Step 8's mutation (b) is what makes it discriminate.

- [ ] **Step 5: Add the quick check** to `check_assignment.rs`. Move the bodies of `check_assignment_scope`/`check_assignment_scope_body` from `assign.rs`, add the `has_ctx_locals` parameter, and replace the `MVar` arm:

```rust
    /// oracle: `CheckAssignmentQuick.check` (`ExprDefEq.lean:1039-1086`).
    /// A bool predicate. `false` means "the slow path decides", never
    /// "reject". See `check_assignment_aux`.
    pub(crate) fn check_assignment_scope(
        &mut self,
        mvar_id: MVarId,
        fvars: &[ExprId],
        has_ctx_locals: bool,
        e: ExprId,
    ) -> Result<bool, MetaError> {
        if !self.data(e).has_fvar() && !self.data(e).has_expr_mvar() {
            return Ok(true);
        }
        self.guarded(|ctx| ctx.check_assignment_scope_body(mvar_id, fvars, has_ctx_locals, e))
    }
```

In the body, keep the existing `FVar` arm verbatim, minus its SEAM comment. Its genuine-let `false` now means "slow path" (`:1066`). Thread `has_ctx_locals` through every recursive call, and make the `MVar` arm:

```rust
            // `:1070-1077`, in the oracle's order.
            Node::MVar { id: Some(n) } => {
                let id = MVarId(n);
                if self.mctx.is_assigned(id) || id == mvar_id {
                    return Ok(false);
                }
                let Some(inner) = self.mctx.decl(id).map(|d| Arc::clone(&d.lctx)) else {
                    return Ok(false);
                };
                if has_ctx_locals {
                    return Ok(false);
                }
                let Some(outer) = self.mctx.decl(mvar_id).map(|d| Arc::clone(&d.lctx)) else {
                    return Ok(false);
                };
                let except = self.fvar_ids(fvars);
                if !inner.is_sub_prefix_of(&outer, &except) {
                    return Ok(false);
                }
                Ok(!self.mctx.is_delayed_assigned(id))
            }
```

Delete the long `checkApp`/`ctxApprox` SEAM comment on the `App` arm. That rescue now lives in `check_app`. Keep a one-line comment: `// visit f <&&> visit a (:1054); rescues are the slow path's`.

- [ ] **Step 6: Rewrite the driver** in `assign.rs` (`check_assignment`), keeping its existing first loop:

```rust
    /// oracle: `checkAssignment` (`ExprDefEq.lean:1151-1172`). The quick
    /// check (`CheckAssignmentQuick.check`) first. If it says `false`,
    /// the slow, term-rewriting `checkAssignmentAux` over the
    /// instantiated value. The REWRITTEN term is returned and assigned,
    /// never the original: a restricted mvar (`checkMVar` under
    /// `ctxApprox`) or a followed let only exists in the rewrite. Both
    /// live in `check_assignment.rs`.
    pub(crate) fn check_assignment(
        &mut self,
        mvar_id: MVarId,
        fvars: &[ExprId],
        v: ExprId,
    ) -> Result<Option<ExprId>, MetaError> {
        for &fvar in fvars {
            let ty = self.infer_type(fvar)?;
            if !self.occurs_check(mvar_id, ty)? {
                return Ok(None);
            }
        }
        if !self.data(v).has_expr_mvar() && !self.data(v).has_fvar() {
            return Ok(Some(v));
        }
        let decl_lctx = match self.mctx.decl(mvar_id) {
            Some(d) => std::sync::Arc::clone(&d.lctx),
            None => {
                return Err(MetaError::MVar(format!(
                    "check_assignment: unknown metavariable {mvar_id:?}"
                )))
            }
        };
        // :1161
        let has_ctx_locals = fvars.iter().any(|f| {
            self.fvar_id_of(*f)
                .is_some_and(|id| decl_lctx.lctx().get(id).is_some())
        });
        let v = if self.check_assignment_scope(mvar_id, fvars, has_ctx_locals, v)? {
            v
        } else {
            let vi = self.instantiate_mvars(v)?;
            match self.check_assignment_aux(mvar_id, fvars, has_ctx_locals, vi)? {
                Some(v2) => v2,
                None => return Ok(None),
            }
        };
        if !self.type_occurs_check(mvar_id, v)? {
            return Ok(None);
        }
        Ok(Some(v))
    }
```

Remove every `#[allow(dead_code)] // wired in by Task 2` added in Task 1.

- [ ] **Step 7: Run the tests and confirm they pass.** Run, in the foreground:
  - `cargo test -p leanr_meta --lib`. Expected: PASS.
  - `cargo test -p leanr_meta` (including `tests/oracle_fast.rs`, which runs with `ctx_approx = true`). Expected: PASS.
  - `cargo test -p leanr_elab --test oracle_op --test oracle_elab --test seam_audit`. Expected: PASS, and specifically `op/postponed-binop-operand` stays green.

  If any corpus record changes, STOP. Diagnose it with `superpowers:systematic-debugging` against the oracle term in the jsonl, and report. Do not re-pin it. Review Focus #1 (synthesis without depth) is the first suspect for a changed instance.

- [ ] **Step 8: Run the mutations.** Each must turn a named test red:
  - (a) In the driver, return `Some(v)` for the original `v` after the slow path succeeds. Expect `driver_returns_the_slow_path_rewrite`.
  - (b) In `is_def_eq_mvar_mvar`, delete `self.rollback(snap);`. Expect `failed_first_direction_rolls_back_the_restriction`.
  - (c) Quick-check arm (5): delete the `is_sub_prefix_of` test. Expect `quick_check_mvar_arm_falls_through_on_each_condition` and `driver_returns_the_slow_path_rewrite`.
  - (d) The driver never calls the slow path (`return Ok(None)` in the `else`). Expect `check_fvar_follows_a_genuine_let_value_in_both_zeta_modes` and `driver_returns_the_slow_path_rewrite`.
  - (e) Quick-check arm (6): drop the delayed test (`Ok(true)`). Expect `quick_check_mvar_arm_falls_through_on_each_condition`.

- [ ] **Step 9: Update the stale docs** (comment-only):
  - `assign.rs` module doc, `# Depth / read-only`: replace "Still seamed: the `isSubPrefixOf` arm … which leanr does not port." with "The quick and slow `checkAssignment` paths, including `isSubPrefixOf` and the `ctxApprox` restriction, are ported in `check_assignment.rs`."
  - `synth.rs` (the `ctxApprox := true` bullet at about :2165): it is no longer a no-op. It enables `check_mvar`'s restriction and `check_app`'s rescue (`check_assignment.rs`). Note that the depth guard there is weaker than the oracle's because synthesis still has no `withNewMCtxDepth` (the bullet two items below).
  - `leanr_elab/src/config.rs:9-12`: `ctx_approx` is live and is read by `check_assignment.rs`'s slow path.
  - Run `grep -rn "inert\|isSubPrefixOf\|tier-1\|tier 1" crates/leanr_meta/src crates/leanr_elab/src` and fix any other comment that says the seam is open.

- [ ] **Step 10: Commit.** Run `cargo fmt --all`, `cargo clippy --workspace --all-targets -- -D warnings`, then commit: "leanr_meta: checkAssignment quick→slow fallthrough with real isSubPrefixOf (checkAssignment T2)", plus the mutation list and Co-Authored-By.

---

### Task 3: elimMVarDeps in `mk_lambda_fvars_with_let_deps`

**Files:**
- Modify: `crates/leanr_meta/src/assign.rs` (`mk_lambda_fvars_with_let_deps` about :902, delete `mk_lambda_over_fvars` about :921-962 and the then-unused `abstract_fvars` import if clippy flags it)
- Test: `crates/leanr_meta/src/assign.rs` `mod tests`

**Interfaces:**
- Consumes: `MetaCtx::mk_lambda(&mut self, fvars: &[ExprId], body: ExprId) -> Result<ExprId, MetaError>` (`metactx.rs:1223`, runs `elim_mvar_deps`).
- Produces: no signature change.

- [ ] **Step 1: Write the failing test** in `assign.rs` `mod tests`:

```rust
    /// oracle `mkLambdaFVarsWithLetDeps` → `mkLambdaFVars` (`ExprDefEq.lean:549-554`)
    /// runs `elimMVarDeps`. `?m x =?= ?i` where `?i`'s ctx holds `x`: the
    /// assignment is `?m := fun x => ?i' x`, with `?i := ?i' x`. A raw
    /// abstraction leaves `?i` unassigned under the binder, and an
    /// `fvar x` leaks when `?i` is solved later (macro/binop% § Landed ›
    /// P3, `F.mk (?m n x)`).
    #[test]
    fn process_assignment_eliminates_mvar_deps_on_the_pattern_fvars() {
        use crate::test_support::{const_named, with_prelude0_ctx};
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let base = Some(ctx.view.store);
            let n_to_n = ctx
                .scratch
                .expr_forall(base, None, n, n, leanr_kernel::BinderInfo::Default)
                .unwrap();
            let cp = ctx.lctx_checkpoint();
            let (m, mid) = fresh_mvar(ctx, n_to_n);
            let x = fresh_fvar(ctx, n, "x");
            let (i, iid) = ctx.mk_aux_mvar(n).unwrap();
            let mx = ctx.scratch.expr_app(base, m, x).unwrap();
            assert!(ctx.is_def_eq(mx, i).unwrap());
            let i_val = ctx.mctx.assignment(iid).expect("elimMVarDeps assigns ?i := ?i' x");
            assert!(matches!(ctx.node(i_val), Node::App { arg, .. } if arg == x));
            let m_val = ctx.mctx.assignment(mid).expect("?m assigned");
            let m_val = ctx.instantiate_mvars(m_val).unwrap();
            assert!(!ctx.data(m_val).has_fvar(), "no fvar leaks into ?m's value");
            ctx.lctx_restore(cp);
        });
    }
```

Before writing it, check the direction `is_def_eq` takes for `?m x =?= ?i`. `is_def_eq_mvar_mvar` puts the bare mvar `s` FIRST when `t` is not bare (`assign.rs:209`), so `?i := ?m x` is tried first. `?m x` mentions `x`, which is in `?i`'s context, so that direction may SUCCEED and assign `?i := ?m x`, never reaching `process_assignment(?m x, ?i)`. If so, make `?i` syntheticOpaque (`mk_aux_mvar_at(ctx.current_lctx(), n, MVarKind::SyntheticOpaque, None)`). That is unassignable, so `?m x := ?i` is the only direction, and `elim_mvar` then DELAY-assigns (`assign_delayed`) instead. Change the `i_val` assertion to `ctx.mctx.delayed_assignment(...)` on the new aux. Whichever variant you use, the test must fail on the current code (Step 2). Record which variant you used in the commit.

- [ ] **Step 2: Run it and confirm it fails.** Run: `cargo test -p leanr_meta --lib process_assignment_eliminates_mvar_deps`. Expected: FAIL (no assignment or delayed assignment for `?i`).

- [ ] **Step 3: Implement the swap.** In `mk_lambda_fvars_with_let_deps`, replace `Ok(Some(self.mk_lambda_over_fvars(xs, v)?))` with:

```rust
        // oracle `mkLambdaFVars` (`:554`): `mkBinding`, which runs
        // `elimMVarDeps` over the body and every binder type first
        // (`MetaCtx::mk_lambda` → `mk_binding`). A `have` among `xs` is
        // abstracted as a lambda (`generalizeNondepLet := true`).
        Ok(Some(self.mk_lambda(xs, v)?))
```

Delete `mk_lambda_over_fvars` and its doc comment. Update the doc comment of `mk_lambda_fvars_with_let_deps`, which says nothing about elimMVarDeps today. Add one sentence: "elimMVarDeps runs here through `mk_lambda`, closing macro/binop% § Landed › P3's TOP PRIORITY gap."

Check that `mk_binding` honours `have` exactly as `mk_lambda_over_fvars` did (a `have` is abstracted as a `lam` with its binder info). `mk_lambda_fvars_with_let_deps_seams_on_let_not_have` (about :2761) must stay green.

- [ ] **Step 4: Run the tests and confirm they pass.** Run: `cargo test -p leanr_meta` and `cargo test -p leanr_elab --test oracle_op --test oracle_elab --test seam_audit`. Expected: all PASS, `op/postponed-binop-operand` included. This is the exact row that failed in the reverted experiment, and it must pass now that Task 2 is in.

- [ ] **Step 5: Run the mutations.**
  - (a) Revert the swap (call the raw abstraction again; keep a local copy only for the mutation). Expect `process_assignment_eliminates_mvar_deps_on_the_pattern_fvars`.
  - (b) With the swap in place, revert Task 2's quick-check arm (5) to `Ok(true)`. Expect `oracle_op_gate` to fail on `op/postponed-binop-operand` with `DepthBudgetExhausted`. This reproduces the spec's § Evidence and proves the two changes depend on each other.

- [ ] **Step 6: Commit.** `cargo fmt --all`, clippy, then commit: "leanr_meta: mkLambdaFVarsWithLetDeps runs elimMVarDeps via mk_lambda (checkAssignment T3)", plus mutations and Co-Authored-By.

---

### Task 4: corpus rows, the `checkApp` coverage check, and close-out

**Files:**
- Modify: `tests/fixtures/elab/dump_elab.lean` (`opQueries`, about :1219-1360)
- Regenerate: `tests/fixtures/elab/op-queries.jsonl`
- Modify: `crates/leanr_elab/tests/oracle_op.rs` (`CORPUS_FLOOR`, about :174)
- Modify: `docs/superpowers/specs/2026-10-02-check-assignment-ctx-approx-design.md`, `docs/superpowers/specs/2026-10-01-macro-expansion-binop-design.md`

**Interfaces:** none (fixtures and docs).

- [ ] **Step 1: Edit `opQueries`.** Replace the depth/stuck block (about :1263-1274) with the original binder rows, keep the closed-constant spellings under `-closed` ids, and fix the comment:

```lean
  -- depth/stuck rows, under `fun` binders (restored by the checkAssignment
  -- slice: they had been respelled over closed constants because of the
  -- elimMVarDeps / isSubPrefixOf gap). The `-closed` spellings over the
  -- suffix constants (`vx`, `k0`, `fx`, `z0`) are kept: same paths, no binder.
  -- depth: `V 3 =?= V ?m` must NOT assign the outer `?m` -> uncomparable
  , ("op/depth",            "fun (n k : Nat) (x : V n) => x + (V.mk : V _) + k")
  , ("op/depth-mid",        "fun (n k : Nat) (x : V n) => x + k + (V.mk : V _)")
  , ("op/depth-closed",     "vx + (V.mk : V _) + k0")
  , ("op/depth-mid-closed", "vx + k0 + (V.mk : V _)")
  -- isDefEqStuckEx: `F n =?= F ?m` stuck -> uncomparable
  , ("op/stuck",            "fun (n : Nat) (x : F n) (z : Z) => x + F.mk _ + z")
  , ("op/stuck-closed",     "fx + F.mk _ + z0")
```

Rename only those three ids. Keep the line that follows (`-- … and with no mvar the same types ARE comparable`) and everything after it unchanged. Then, after `op/postponed-binop-operand` (about :1308), add:

```lean
  -- checkAssignment slice (spec 2026-10-02 § Evidence): a binder-local
  -- mvar must not be assigned to an outer one (isSubPrefixOf + ctxApprox).
  , ("op/binder-F-hole",    "fun (n : Nat) (x : F n) => x + F.mk _")
  , ("meta/at-hadd-V",      "fun (n : Nat) => @HAdd.hAdd _ _ _ _ (V.mk : V n) (V.mk : V _)")
  , ("meta/beta-lt",        "(fun a => LT.lt a 2) z0")
  , ("meta/beta-add",       "(fun a => a + 2) z0")
  , ("meta/beta-beq",       "(fun a => BEq.beq a 2) z0")
  , ("op/rel-lt-beta",      "(fun a => a < 2) z0")
```

Also fix the `op/rel-no-default` comment (about :1345-1348). Its "leanr fails that op-free (`DepthBudgetExhausted` …)" clause is obsolete. Say that `op/rel-lt-beta` now covers the `(fun a => a < 2) z0` spelling.

- [ ] **Step 2: Regenerate the op corpus** (foreground, from `/workspace`):

```bash
cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_elab.lean ElabOp > op-queries.jsonl; echo EXIT=$?; cd /workspace
grep -c . tests/fixtures/elab/op-queries.jsonl   # expect 90
git diff --stat tests/fixtures/elab/op-queries.jsonl
```

There must be no `dump_elab: elaboration failed` on stderr. The spec records that the oracle accepts every new row. A failure means a typo, so fix the source string. Check that the three `-closed` records are byte-identical to the old `op/depth`/`op/depth-mid`/`op/stuck` records apart from the id: `git diff` should show only id changes plus new lines. Grep for `sorryAx` in the new lines; there must be none.

ElabOp.olean is NOT regenerated, because the suffix does not change. Do not run `mise run fixtures:regen-elab-op` (it rebuilds ElabOp from Init).

- [ ] **Step 3: Raise the floor.** In `oracle_op.rs`, set `const CORPUS_FLOOR: usize = 90;` and extend the history comment: "81 -> 90 (checkAssignment T4): op/depth, op/depth-mid, op/stuck restored to binder form (the closed spellings kept as `-closed`), plus op/binder-F-hole, meta/at-hadd-V, meta/beta-{lt,add,beq}, op/rel-lt-beta."

- [ ] **Step 4: Run it and confirm it passes.** Run: `cargo test -p leanr_elab --test oracle_op`. Expected: PASS at 90.

If a row diverges, STOP and diagnose against the oracle term with `superpowers:systematic-debugging`.

- [ ] **Step 5: Re-run P3's survived mutations against the restored binder rows** (`docs/superpowers/plans/2026-10-02-macro-binop-p3-op-elab.md` Task 3 Step 10):
  - (d) Drop the final `is_def_eq_guarded(ty, max)` in the op elaborator (`crates/leanr_elab/src/builtin/op/`).
  - (h) Pass `result_is_out_param_support: true` in `apply_op`.

  Run `cargo test -p leanr_elab --test oracle_op` for each. Record killed (which row) or survived (with the reason) in the commit message, and in § Landed below.

- [ ] **Step 6: Check `checkApp` coverage.** Apply Task 1's mutation (i) (`rescuable` always `false`) and run `cargo test -p leanr_elab --test oracle_op --test oracle_elab --test seam_audit`.
  - If a corpus row goes red, record that row as the differential record for `checkApp`/`assignToConstFun`. Done.
  - If nothing goes red, probe the oracle for a candidate. Copy `dump_elab.lean` to `target/ctxapprox-probe/` (gitignored, under `/workspace`). Replace `opQueries` with the candidates below. Run it once as-is and once with the `elabTerm` block wrapped in `withConfig (fun c => { c with ctxApprox := false }) do …` (inside `.run'`), and diff the outputs:

    ```lean
    [ ("c1", "fun (n : Nat) (x : F n) (y : F n) => x + y + F.mk _")
    , ("c2", "fun (n : Nat) => (fun (f : Nat → Nat) => f n) (fun k => k + 0)")
    , ("c3", "fun (n : Nat) (x : V n) => (fun y => y + x) (V.mk : V _)")
    , ("c4", "fun (a : Nat) (b : Nat) => (fun x => x.1 + b) (PProd.mk a a)") ]
    ```

    Any candidate whose output differs (`ctxApprox`-dependent), and which goes red in leanr under mutation (i), becomes a corpus row (`meta/ctx-approx-app-N`). Raise the floor accordingly. If none qualifies, write in § Landed: "`checkApp`/`assignToConstFun` has unit coverage (`check_app_rescues_an_out_of_scope_mvar_app`) and no differential record. Mutation (i) survives the corpus. Candidates tried: c1–c4." This is the posture setElabConfig took. Delete `target/ctxapprox-probe/` afterwards.

- [ ] **Step 7: Write the close-out docs.**
  - In this slice's spec, add a `## Landed` section. Record the PR (fill the number in at PR time), the per-task mutation results, the Task 3 test variant, the Step 5/6 outcomes, and any deviation from the spec (the `except: &[NameId]` signature).
  - In `2026-10-01-macro-expansion-binop-design.md` § Landed › P3 › Open follow-ups, strike through the TOP PRIORITY item, the "leanr_meta elimMVarDeps gap" item, and the "`(fun a => LT.lt a 2) z0`" item, each with a pointer to this slice's spec. Strike R2's "respelled … because of the elimMVarDeps gap" note the same way ("restored; closed spellings kept as `-closed`").

- [ ] **Step 8: Run full CI** in the foreground and block until it exits:

```bash
mise run ci; echo CI_EXIT=$?
```

Expected: `CI_EXIT=0`.

- [ ] **Step 9: Commit.** "fixtures+docs: checkAssignment corpus rows, restored binder depth/stuck rows, § Landed (checkAssignment T4)", plus the Step 5/6 outcomes and Co-Authored-By.
