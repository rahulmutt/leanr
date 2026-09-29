# `nondep` and `LocalDeclKind` on local declarations — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give leanr's local declarations the oracle's `nondep` bit and a stored `LocalDeclKind`, then port the eight sites that read them — closing the `let`/`have` fvar leak that a postponed coercion causes.

**Architecture:** The bits live in `MetaCtx::local_names`, which is already one row per declaration and already lockstep with `lctx.decls`, already carried inside every `LocalCtxSnapshot`, and already filtered and renumbered by `reduced`. Rows become a named `LocalEntry` struct. Two expression primitives the oracle's ldecl arms need are added first: `lower_loose_bvars` in `leanr_kernel` (beside its existing twin `lift_loose_bvars`) and an exact `has_loose_bvar` in `leanr_meta`.

**Tech Stack:** Rust (workspace crates `leanr_kernel`, `leanr_meta`, `leanr_elab`), Lean 4 fixtures (`tests/fixtures/elab/dump_elab.lean`), mise tasks.

**Spec:** `docs/superpowers/specs/2026-09-29-nondep-local-decls-design.md`

## Global Constraints

- **Oracle discipline.** Correctness is defined by differential testing against the pinned toolchain (`leanprover/lean4:v4.33.0-rc1`). Never bump `lean-toolchain`. Regenerate elab fixtures with `mise run fixtures:regen-elab`.
- **Kernel TCB.** `leanr_kernel` takes exactly ONE change in this plan: `lower_loose_bvars` (Task 1). Nothing else in that crate may change. It must have no caller inside the type checker.
- **Corpora are the gate.** The elaboration corpus grows 162 → 165, additions only. The synthesis corpus (32 records) and the meta corpus must stay BYTE-IDENTICAL. If a committed record moves, STOP and report it — do not absorb it.
- **Every discriminator is measured.** A mutation named in a task is a hypothesis: apply it, watch the named test go red, revert. If it survives, strengthen the test before closing the task.
- **`mise run ci`** (fmt + clippy + full suite) before every commit that touches Rust. The test gates do not cover fmt/clippy.
- **Citations by symbol** where a line cannot be opened. The C++ kernel sources do not ship with the toolchain.

---

## File Structure

| File | Responsibility | Task |
|---|---|---|
| `crates/leanr_kernel/src/subst.rs` | add `lower_loose_bvars`, twin of `lift_loose_bvars` | 1 |
| `crates/leanr_kernel/src/lib.rs` | export it | 1 |
| `crates/leanr_meta/src/loose_bvar.rs` (new) | exact `has_loose_bvar(e, idx)` | 2 |
| `crates/leanr_meta/src/local_entry.rs` (new) | the `LocalEntry` row + its invariant doc | 3 |
| `crates/leanr_meta/src/metactx.rs` | rows, accessors, producers, `mk_let_expr` | 3, 9 |
| `crates/leanr_meta/src/local_snapshot.rs` | rows inside snapshots, `reduced` | 3 |
| `crates/leanr_meta/src/whnf.rs` | zeta-delta `nondep` | 4 |
| `crates/leanr_meta/src/assign.rs` | the three `checkAssignment`-family sites | 6 |
| `crates/leanr_meta/src/mk_binding.rs` | `local_decl_depends_on`, `mk_mvar_app`, `mk_aux_mvar_type` | 7, 8 |
| `tests/fixtures/elab/dump_elab.lean` | the three new oracle records | 9 |
| `crates/leanr_elab/tests/seam_audit.rs` | flip the gap-2 pin | 9 |

---

### Task 1: `lower_loose_bvars` in `leanr_kernel`

**Files:**
- Modify: `crates/leanr_kernel/src/subst.rs` (add beside `lift_loose_bvars`, which starts at `:373`)
- Modify: `crates/leanr_kernel/src/lib.rs:65-68` (the `pub use subst::{…}` list)
- Test: `crates/leanr_kernel/src/subst.rs` (its existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: nothing.
- Produces: `pub fn lower_loose_bvars(st: &mut Store, base: Option<&Store>, e: ExprId, s: u32, d: u32, g: &mut RecGuard) -> Result<ExprId, KernelError>` — lowers every loose bvar `>= s` by `d`. Task 8 calls it as `lower_loose_bvars(st, base, e, 1, 1, g)`.

- [ ] **Step 1: Write the failing test**

Add to `subst.rs`'s test module:

```rust
/// `lowerLooseBVars e 1 1` (oracle: `Lean/Expr.lean:1357`, the C++
/// `lower_loose_bvars`) drops every loose bvar `>= 1` by one and leaves
/// bvar 0 alone. Mirrors `lift_loose_bvars`'s own tests.
#[test]
fn lower_loose_bvars_lowers_only_at_or_above_the_cutoff() {
    let mut st = Store::default();
    let mut g = RecGuard::new();
    let b0 = st.expr_bvar(None, &Nat(&BigUint::from(0u32))).expect("bvar 0");
    let b1 = st.expr_bvar(None, &Nat(&BigUint::from(1u32))).expect("bvar 1");
    let b2 = st.expr_bvar(None, &Nat(&BigUint::from(2u32))).expect("bvar 2");
    let app = st.expr_app(None, b1, b2).expect("app");
    let app = st.expr_app(None, app, b0).expect("app");

    let out = lower_loose_bvars(&mut st, None, app, 1, 1, &mut g).expect("lower");

    // `#1 #2 #0` becomes `#0 #1 #0`.
    let expect_f = st.expr_app(None, b0, b1).expect("app");
    let expect = st.expr_app(None, expect_f, b0).expect("app");
    assert_eq!(out, expect);
}

/// A binder shifts the cutoff, exactly as `lift_go`'s `offset + 1` does.
#[test]
fn lower_loose_bvars_shifts_the_cutoff_under_a_binder() {
    let mut st = Store::default();
    let mut g = RecGuard::new();
    let sort = {
        let z = st.level_zero(None).expect("level");
        st.expr_sort(None, z).expect("sort")
    };
    let b2 = st.expr_bvar(None, &Nat(&BigUint::from(2u32))).expect("bvar 2");
    let lam = st
        .expr_lam(None, None, sort, b2, BinderInfo::Default)
        .expect("lam");

    let out = lower_loose_bvars(&mut st, None, lam, 1, 1, &mut g).expect("lower");

    // Under one binder the cutoff is 2, so `#2` is loose and becomes `#1`.
    let b1 = st.expr_bvar(None, &Nat(&BigUint::from(1u32))).expect("bvar 1");
    let expect = st
        .expr_lam(None, None, sort, b1, BinderInfo::Default)
        .expect("lam");
    assert_eq!(out, expect);
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_kernel --lib lower_loose_bvars 2>&1 | tail -20`
Expected: FAIL to COMPILE — `cannot find function lower_loose_bvars in this scope`.

- [ ] **Step 3: Write the implementation**

`lift_go` is the model: same cache, same guard, same `loose_bvar_range_exact` fast path, same rebuild-only-on-change discipline. Add after `lift_loose_bvars`'s `lift_go`:

```rust
// ---------------------------------------------------------------------
// lower_loose_bvars — oracle: `Lean.Expr.lowerLooseBVars`
// (`Lean/Expr.lean:1357`, an `opaque` over the C++ kernel's
// `lower_loose_bvars`). The C++ sources do not ship with the toolchain,
// so this cites the Lean-level declaration rather than a line in
// expr.cpp (contrast `lift_loose_bvars` above, whose expr.cpp citation
// predates that discovery).
// ---------------------------------------------------------------------

/// Lowers every loose bvar `>= s` by `d`. The exact inverse of
/// [`lift_loose_bvars`], and deliberately its structural twin: same
/// `VisitCache`, same `RecGuard`, same `loose_bvar_range_exact` skip,
/// same rebuild-only-when-a-child-changed discipline.
///
/// A bvar below `s` is untouched. A loose bvar in `s..s+d` cannot occur
/// in a well-formed call — the oracle's own `lowerLooseBVars` is only
/// invoked where the caller has just proven those indices absent (e.g.
/// `mkAuxMVarType`'s unused-let arm, guarded by `!e.hasLooseBVar 0`) —
/// so this saturates at 0 rather than inventing an error path the
/// oracle does not have.
///
/// Additive and TCB-neutral: no caller inside `tc.rs`; the type checker
/// gains no behavior. Added for `leanr_meta`'s `mk_aux_mvar_type` ldecl
/// arms, which cannot be written without it (design spec § Design 4).
pub fn lower_loose_bvars(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    s: u32,
    d: u32,
    g: &mut RecGuard,
) -> Result<ExprId, KernelError> {
    if d == 0 {
        return Ok(e);
    }
    lower_go(st, base, e, s, 0, d, g, &mut VisitCache::new())
}

#[allow(clippy::too_many_arguments)]
fn lower_go(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    s: u32,
    offset: u32,
    d: u32,
    g: &mut RecGuard,
    cache: &mut VisitCache,
) -> Result<ExprId, KernelError> {
    let s1 = match s.checked_add(offset) {
        Some(v) => v,
        None => return Ok(e),
    };
    if let Some(range) = st.expr_data(base, e).loose_bvar_range_exact() {
        if (range as u64) <= (s1 as u64) {
            return Ok(e);
        }
    }
    let key = (e, offset);
    if let Some(&r) = cache.get(&key) {
        return Ok(r);
    }
    let r = match st.expr_node(base, e) {
        node @ (Node::BVar { .. } | Node::BVarBig { .. }) => {
            let idx = bvar_index_nat(st, base, node);
            let s1_big = BigUint::from(s1);
            if idx.0 >= s1_big {
                // Exact bignum subtraction, never an `as` cast — the
                // mirror of `lift_go`'s exact add.
                let d_big = BigUint::from(d);
                let lowered = if idx.0 >= d_big { &idx.0 - &d_big } else { BigUint::from(0u32) };
                st.expr_bvar(base, &Nat(&lowered))?
            } else {
                e
            }
        }
        Node::FVar { .. }
        | Node::MVar { .. }
        | Node::Sort { .. }
        | Node::Const { .. }
        | Node::LitNat { .. }
        | Node::LitStr { .. } => e,
        Node::App { f, arg } => {
            let (f2, arg2) = g.enter(|g| {
                Ok((
                    lower_go(st, base, f, s, offset, d, g, cache)?,
                    lower_go(st, base, arg, s, offset, d, g, cache)?,
                ))
            })?;
            if f2 == f && arg2 == arg {
                e
            } else {
                st.expr_app(base, f2, arg2)?
            }
        }
        Node::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    lower_go(st, base, binder_type, s, offset, d, g, cache)?,
                    lower_go(st, base, body, s, offset + 1, d, g, cache)?,
                ))
            })?;
            if bt2 == binder_type && bd2 == body {
                e
            } else {
                st.expr_lam(base, binder_name, bt2, bd2, binder_info)?
            }
        }
        Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    lower_go(st, base, binder_type, s, offset, d, g, cache)?,
                    lower_go(st, base, body, s, offset + 1, d, g, cache)?,
                ))
            })?;
            if bt2 == binder_type && bd2 == body {
                e
            } else {
                st.expr_forall(base, binder_name, bt2, bd2, binder_info)?
            }
        }
        Node::LetE {
            decl_name,
            ty,
            value,
            body,
            non_dep,
        } => {
            let (t2, v2, b2) = g.enter(|g| {
                Ok((
                    lower_go(st, base, ty, s, offset, d, g, cache)?,
                    lower_go(st, base, value, s, offset, d, g, cache)?,
                    lower_go(st, base, body, s, offset + 1, d, g, cache)?,
                ))
            })?;
            if t2 == ty && v2 == value && b2 == body {
                e
            } else {
                st.expr_let(base, decl_name, t2, v2, b2, non_dep)?
            }
        }
        Node::MData { data, expr } => {
            let expr2 = g.enter(|g| lower_go(st, base, expr, s, offset, d, g, cache))?;
            if expr2 == expr {
                e
            } else {
                st.expr_mdata(base, data, expr2)?
            }
        }
        // `lift_go` handles `Proj` and `ProjBig` in ONE arm, destructuring
        // `type_name`/`structure` from either — copy that arm verbatim
        // (`subst.rs:512+`) rather than the two-arm sketch a reader might
        // expect; the field is `structure`, not `expr`.
        node @ (Node::Proj { .. } | Node::ProjBig { .. }) => {
            /* mirror lift_go's arm exactly */
            unimplemented!("copy lift_go's Proj/ProjBig arm, substituting lower_go")
        }
    };
    cache.insert(key, r);
    Ok(r)
}
```

**Before writing this, read `lift_go` in full (`subst.rs:373` onward)** and mirror its arms exactly — including how it handles `MData`, `Proj` and `ProjBig`. If `lift_go`'s arm list differs from the sketch above, `lift_go` is the authority: match it, and note the difference in the task report.

- [ ] **Step 4: Export it**

In `crates/leanr_kernel/src/lib.rs:65-68`:

```rust
pub use subst::{
    abstract_fvars, instantiate, instantiate_core, instantiate_level_params, instantiate_rev,
    lift_loose_bvars, lower_loose_bvars,
};
```

- [ ] **Step 5: Run the tests to verify they pass**

Run: `cargo test -p leanr_kernel --lib lower_loose_bvars`
Expected: PASS, 2 tests.

- [ ] **Step 6: Run the mutation**

Change `idx.0 >= s1_big` to `idx.0 > s1_big`. Run the tests: `lower_loose_bvars_lowers_only_at_or_above_the_cutoff` must FAIL. Revert.

- [ ] **Step 7: Verify the kernel took no other change and commit**

```bash
cd /workspace
git diff --stat crates/leanr_kernel   # subst.rs + lib.rs ONLY
mise run ci
git add crates/leanr_kernel/src/subst.rs crates/leanr_kernel/src/lib.rs
git commit -m "kernel: add lower_loose_bvars, the twin of lift_loose_bvars"
```

---

### Task 2: exact `has_loose_bvar` in `leanr_meta`

**Files:**
- Create: `crates/leanr_meta/src/loose_bvar.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (add `mod loose_bvar;`)
- Test: in the new file's `#[cfg(test)] mod tests`

**Interfaces:**
- Consumes: nothing.
- Produces: `impl MetaCtx { pub(crate) fn has_loose_bvar(&mut self, e: ExprId, idx: u32) -> Result<bool, MetaError> }` — Tasks 5 and 8 call it with `idx = 0`.

**Why this exists:** `ExprData::loose_bvar_range` is `1 + max loose index`, saturating at `LOOSE_BVAR_SAT`. So `range > 0` means "some loose bvar exists", NOT the oracle's `hasLooseBVar e 0` ("bvar 0 specifically is loose"). `loose_bvar_range_exact` is `pub(crate)` to `leanr_kernel`, so this walk uses only the public saturating accessor, and only as a sound fast path: `range == 0` proves the term is closed.

- [ ] **Step 1: Write the failing test**

```rust
#[cfg(test)]
mod tests {
    use crate::test_support::with_ctx;
    use leanr_kernel::bank::Nat;
    use num_bigint::BigUint;

    /// The case that makes this function necessary: a term whose only
    /// loose bvar is `#1`. `loose_bvar_range()` is 2 — greater than
    /// zero — but `hasLooseBVar 0` is FALSE. Using the range as a proxy
    /// gets this backwards, which is exactly the bug the design spec's
    /// § Design 4 describes in `whnf`'s `zeta_unused` branch.
    #[test]
    fn has_loose_bvar_distinguishes_index_one_from_index_zero() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let b1 = ctx
                .scratch
                .expr_bvar(base, &Nat(&BigUint::from(1u32)))
                .expect("bvar 1");
            assert!(
                ctx.data(b1).loose_bvar_range() > 0,
                "precondition: the packed range is nonzero for `#1`"
            );
            assert!(!ctx.has_loose_bvar(b1, 0).expect("has_loose_bvar"));
            assert!(ctx.has_loose_bvar(b1, 1).expect("has_loose_bvar"));
        });
    }

    /// A binder closes one level: inside `fun _ => #1`, the body's `#1`
    /// is the caller's `#0`.
    #[test]
    fn has_loose_bvar_shifts_under_a_binder() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            let b1 = ctx
                .scratch
                .expr_bvar(base, &Nat(&BigUint::from(1u32)))
                .expect("bvar 1");
            let lam = ctx
                .scratch
                .expr_lam(base, None, sort0, b1, leanr_kernel::BinderInfo::Default)
                .expect("lam");
            assert!(ctx.has_loose_bvar(lam, 0).expect("has_loose_bvar"));
            assert!(!ctx.has_loose_bvar(lam, 1).expect("has_loose_bvar"));
        });
    }

    /// The fast path: a closed term is `false` for every index.
    #[test]
    fn has_loose_bvar_is_false_for_a_closed_term() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            assert!(!ctx.has_loose_bvar(sort0, 0).expect("has_loose_bvar"));
        });
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p leanr_meta --lib has_loose_bvar 2>&1 | tail -20`
Expected: FAIL to COMPILE — no method `has_loose_bvar`.

- [ ] **Step 3: Write the implementation**

```rust
//! The exact `Expr.hasLooseBVar` test (`Lean/Expr.lean:1330`, an
//! `opaque`), which leanr otherwise lacks.
//!
//! `ExprData::loose_bvar_range` is `1 + max loose index`, saturating at
//! the kernel's `LOOSE_BVAR_SAT`, so `range > 0` answers "is ANY bvar
//! loose", not "is THIS bvar loose". The two differ exactly when every
//! loose index is `>= 1`, which is the case the oracle's
//! `mkAuxMVarType` unused-let arm turns on. `loose_bvar_range_exact` is
//! `pub(crate)` to `leanr_kernel`, so the only fast path available here
//! is the public saturating accessor — sound in one direction: a range
//! of `0` proves the term closed.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;

use crate::{MetaCtx, MetaError};

impl MetaCtx<'_> {
    /// oracle: `Expr.hasLooseBVar e bvarIdx` (`Lean/Expr.lean:1330`).
    ///
    /// Entry point: the closed fast path, one step, one guard — the
    /// shape `depends_on` (`mk_binding.rs:74-85`) uses, with the
    /// recursion re-entering here so every level steps and guards.
    pub(crate) fn has_loose_bvar(&mut self, e: ExprId, idx: u32) -> Result<bool, MetaError> {
        // A range of 0 proves the term closed. (`loose_bvar_range_exact`
        // is `pub(crate)` to `leanr_kernel`, so only the saturating
        // accessor is available here — sound in this direction only.)
        if self.data(e).loose_bvar_range() == 0 {
            return Ok(false);
        }
        self.step()?;
        self.guarded(|ctx| ctx.has_loose_bvar_body(e, idx))
    }

    fn has_loose_bvar_body(&mut self, e: ExprId, idx: u32) -> Result<bool, MetaError> {
        match self.node(e) {
            Node::BVar { idx: i } => Ok(i == idx),
            // `BVarBig` holds an index that did NOT fit a `u32`
            // (`terms.rs:260-262`), and `idx` is a `u32`, so it can
            // never be the index being asked about.
            Node::BVarBig { .. } => Ok(false),
            Node::FVar { .. }
            | Node::MVar { .. }
            | Node::Sort { .. }
            | Node::Const { .. }
            | Node::LitNat { .. }
            | Node::LitStr { .. } => Ok(false),
            Node::App { f, arg } => {
                Ok(self.has_loose_bvar(f, idx)? || self.has_loose_bvar(arg, idx)?)
            }
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => Ok(self.has_loose_bvar(binder_type, idx)?
                || self.has_loose_bvar(body, idx + 1)?),
            Node::LetE {
                ty, value, body, ..
            } => Ok(self.has_loose_bvar(ty, idx)?
                || self.has_loose_bvar(value, idx)?
                || self.has_loose_bvar(body, idx + 1)?),
            Node::MData { expr, .. } => self.has_loose_bvar(expr, idx),
            // The field is `structure`, not `expr` — see `depends_on`'s
            // own `Proj`/`ProjBig` arm (`mk_binding.rs:115-118`).
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                self.has_loose_bvar(structure, idx)
            }
        }
    }
}
```

Node shapes verified while planning: `Node::BVar { idx: u32 }` and `Node::BVarBig { idx: NatId }` (`terms.rs:256-262`), and `Proj`/`ProjBig` both carry `structure`.

- [ ] **Step 4: Register the module**

In `crates/leanr_meta/src/lib.rs`, beside the other `mod` lines: `mod loose_bvar;`

- [ ] **Step 5: Run to verify the tests pass**

Run: `cargo test -p leanr_meta --lib has_loose_bvar`
Expected: PASS, 3 tests.

- [ ] **Step 6: Run the mutation**

Replace the body with `Ok(self.data(e).loose_bvar_range() > 0)`. `has_loose_bvar_distinguishes_index_one_from_index_zero` must FAIL. Revert.

- [ ] **Step 7: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/loose_bvar.rs crates/leanr_meta/src/lib.rs
git commit -m "meta: exact has_loose_bvar, not the packed range proxy"
```

---

### Task 3: `LocalEntry` rows — the storage

**Files:**
- Create: `crates/leanr_meta/src/local_entry.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (`mod local_entry;`)
- Modify: `crates/leanr_meta/src/metactx.rs` (field at `:81`, `push_local_decl_inner:673`, `push_local_decl_with_kind:722`, `push_local_decl_without_instance:762`, `install_local_instance_for_last_pushed:~790`, `push_let_decl:826`, `push_let_decl_with_kind:837`, `lctx_lookup_by_name`, `current_lctx:521`, `install_lctx:556`, `lctx_restore:649`)
- Modify: `crates/leanr_meta/src/local_snapshot.rs` (`new:47`, `parts:123`, `entries:149`, `reduced:185`)
- Modify: `crates/leanr_meta/src/mk_binding.rs:227` (`collect_forward_deps`'s `entries` map)
- Modify: `crates/leanr_meta/src/instances.rs:1539` (a test destructuring `(_, f)`)
- Modify: `crates/leanr_elab/src/builtin/binder/mod.rs:~228` and `crates/leanr_elab/src/builtin/binder/fun.rs` (the `install_local_instance_for_last_pushed` caller)

**Interfaces:**
- Consumes: nothing.
- Produces:
  - `pub(crate) struct LocalEntry { pub fvar: ExprId, pub name: Option<NameId>, pub id: NameId, pub nondep: bool, pub kind: LocalDeclKind }`
  - `impl MetaCtx { pub(crate) fn local_entry(&self, id: NameId) -> Option<&LocalEntry> }`
  - `impl LocalCtxSnapshot { pub(crate) fn entry(&self, id: NameId) -> Option<&LocalEntry> }`
  - `MetaCtx::push_let_decl(&mut self, name, ty, value, non_dep: bool)` and `push_let_decl_with_kind(&mut self, name, ty, value, non_dep: bool, kind)` — NOTE the new `non_dep` parameter, before `kind`.
  - `MetaCtx::install_local_instance_for_last_pushed(&mut self, fvar, ty)` — the `kind` parameter is GONE; it reads the stored kind.

**This task is behaviour-neutral.** Everything it stores is either already known at the push site or already passed as a parameter. Its tests assert the rows survive the four operations that move them.

- [ ] **Step 1: Write the failing tests**

Add to `metactx.rs`'s test module:

```rust
/// The rows carry `nondep` and the kind, and they survive every
/// operation that moves a local context: restore truncates them,
/// `install_lctx` swaps them, `reduced` filters them.
#[test]
fn local_entries_record_nondep_and_kind() {
    with_class_ctx(|ctx, add| {
        let cp = ctx.lctx_checkpoint();
        let c = ctx.push_local_decl(None, add, BinderInfo::Default).expect("cdecl");
        let l = ctx.push_let_decl(None, add, c, false).expect("let");
        let h = ctx.push_let_decl(None, add, c, true).expect("have");

        let id_of = |ctx: &MetaCtx, e| match ctx.node(e) {
            Node::FVar { id: Some(id) } => id,
            other => panic!("expected fvar, got {other:?}"),
        };
        assert!(!ctx.local_entry(id_of(ctx, c)).expect("row").nondep, "a cdecl is never nondep");
        assert!(!ctx.local_entry(id_of(ctx, l)).expect("row").nondep, "`let` is nondep=false");
        assert!(ctx.local_entry(id_of(ctx, h)).expect("row").nondep, "`have` is nondep=true");

        ctx.lctx_restore(cp);
        assert!(ctx.local_entry(id_of(ctx, h)).is_none(), "restore drops the rows");
    });
}

/// A snapshot carries the same rows, and `install_lctx` puts them back.
#[test]
fn local_entries_round_trip_through_a_snapshot() {
    with_class_ctx(|ctx, add| {
        let cp = ctx.lctx_checkpoint();
        let c = ctx.push_local_decl(None, add, BinderInfo::Default).expect("cdecl");
        let h = ctx.push_let_decl(None, add, c, true).expect("have");
        let snap = ctx.current_lctx();
        let id_of = |ctx: &MetaCtx, e| match ctx.node(e) {
            Node::FVar { id: Some(id) } => id,
            other => panic!("expected fvar, got {other:?}"),
        };
        let hid = id_of(ctx, h);
        assert!(snap.entry(hid).expect("snapshot row").nondep);

        ctx.lctx_restore(cp);
        assert!(ctx.local_entry(hid).is_none());
        let _previous = ctx.install_lctx(snap);
        assert!(ctx.local_entry(hid).expect("reinstalled row").nondep);
    });
}

/// The close-out's behaviour, now read from storage rather than from a
/// parameter: an `ImplDetail` declaration installs no local instance,
/// and its stored kind says so.
#[test]
fn a_stored_impl_detail_kind_still_suppresses_the_instance_install() {
    with_class_ctx(|ctx, add| {
        let cp = ctx.lctx_checkpoint();
        let before = ctx.local_instances.entries().len();
        let f = ctx
            .push_local_decl_with_kind(None, add, BinderInfo::Default, LocalDeclKind::ImplDetail)
            .expect("push");
        let id = match ctx.node(f) {
            Node::FVar { id: Some(id) } => id,
            other => panic!("expected fvar, got {other:?}"),
        };
        assert_eq!(ctx.local_entry(id).expect("row").kind, LocalDeclKind::ImplDetail);
        assert_eq!(ctx.local_instances.entries().len(), before, "no instance installed");
        ctx.lctx_restore(cp);
    });
}
```

`with_class_ctx` is the existing helper used by `pushing_a_class_typed_decl_installs_a_local_instance` (`metactx.rs:~1919`); reuse it verbatim. If `local_instances.entries()` is not reachable from the test module, assert through whatever that existing test uses instead.

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test -p leanr_meta --lib local_entries 2>&1 | tail -20`
Expected: FAIL to COMPILE — no `local_entry` method, and `push_let_decl` takes 3 arguments.

- [ ] **Step 3: Create the row type**

`crates/leanr_meta/src/local_entry.rs`:

```rust
//! One attribute row per local declaration.
//!
//! `MetaCtx::local_names` has always been exactly one entry per
//! `push_local_decl`/`push_let_decl` call, asserted in lockstep with
//! `lctx.decls` at every push, checkpoint, restore and install. This is
//! that row, widened to carry what leanr's `LocalDecl` cannot.
//!
//! **Why not on `LocalDecl`.** `leanr_kernel::local_ctx` ports the C++
//! kernel's `local_ctx.h`, which has neither bit — `nondep` and
//! `LocalDeclKind` are `Lean.LocalDecl` (elaborator) concepts
//! (`Lean/LocalContext.lean:23`, `:55-80`). The kernel does read let
//! values during whnf (`tc.rs:1385`, `:1544`), so fields there would be
//! inert, and an inert TCB field invites a future kernel reader.
//!
//! **Why not a second sparse table.** `local_instance.rs` is sparse
//! because only class-typed declarations produce an entry; its
//! truncate-by-recorded-depth rule is the subtlety that file exists to
//! contain. These bits are dense: every declaration has a kind, every
//! ldecl a `nondep`. Dense data belongs in the row that is already
//! dense and already positional.

use leanr_kernel::bank::{ExprId, NameId};

use crate::LocalDeclKind;

/// The attributes of one local declaration, positionally parallel to
/// `LocalContext`'s own decl list.
#[derive(Clone)]
pub(crate) struct LocalEntry {
    /// The `Expr::fvar` `push_local_decl` returned.
    pub fvar: ExprId,
    /// The user-facing binder name, `None` for an anonymous binder.
    /// Read by `lctx_lookup_by_name`.
    pub name: Option<NameId>,
    /// The declaration's fvar id. Stored so a lookup compares by
    /// `NameId` — the basis `LocalCtxSnapshot::reduced` already argues
    /// for over `ExprId` — without a `Store` decode per read.
    pub id: NameId,
    /// oracle: `LocalDecl.ldecl (nondep := …)`. `true` for a `have`,
    /// `false` for a `let` and for every cdecl. A nondep ldecl is
    /// "locally a cdecl": its value is invisible to zeta-delta
    /// (`WHNF.lean:397-409`), to `getValue?` (`Meta/Basic.lean:1044`,
    /// `allowNondep := false`) and to `isLet`
    /// (`LocalContext.lean:106-109`).
    pub nondep: bool,
    /// oracle: `LocalDecl`'s `kind` field. Consumed by
    /// `install_local_instance_for`, and by `withLocalInstances` when
    /// the match slice ports it.
    pub kind: LocalDeclKind,
}
```

- [ ] **Step 4: Widen `MetaCtx`**

In `metactx.rs`: change the field to `pub(crate) local_names: Vec<LocalEntry>`, keeping its existing doc comment and adding a sentence that the row now carries `nondep`/`kind`. Then:

```rust
// push_local_decl_inner — gains `kind`, writes the row:
fn push_local_decl_inner(
    &mut self,
    name: Option<NameId>,
    ty: ExprId,
    bi: BinderInfo,
    kind: LocalDeclKind,
) -> Result<(ExprId, usize), MetaError> {
    // ... unchanged debug_assert and `let depth = self.lctx.save();` ...
    let fvar = self.lctx.mk_local_decl(/* unchanged */)?;
    let id = self
        .fvar_id_of(fvar)
        .ok_or_else(|| MetaError::Infer("push_local_decl: fresh fvar has no id".into()))?;
    self.local_names.push(LocalEntry {
        fvar,
        name,
        id,
        // A cdecl is never nondep: the bit exists only on an ldecl
        // (`LocalDecl.isNondep`, `LocalContext.lean:227-229`).
        nondep: false,
        kind,
    });
    Ok((fvar, depth))
}
```

`push_local_decl_with_kind` passes `kind` through; `push_local_decl_without_instance` passes `LocalDeclKind::Default` (its callers are `elab_fun`'s deferred-install path, which then installs with the stored kind — see Step 6).

`push_let_decl_with_kind` gains `non_dep: bool` and pushes a row with that `non_dep` and its `kind`; `push_let_decl` forwards `non_dep` and `LocalDeclKind::Default`.

- [ ] **Step 5: Add the accessors**

```rust
// on MetaCtx, beside `lctx_lookup_by_name`:
/// The attribute row for `id`, or `None` if `id` is not declared in
/// the ambient context. Reverse scan, the same idiom
/// `lctx_lookup_by_name` uses: contexts are binder-depth-sized, and a
/// hash index would be a second structure to hold in lockstep.
pub(crate) fn local_entry(&self, id: NameId) -> Option<&LocalEntry> {
    self.local_names.iter().rev().find(|e| e.id == id)
}

// on LocalCtxSnapshot:
/// The attribute row for `id` in THIS context — a metavariable's own,
/// not the ambient one. `mk_aux_mvar_type` and `mk_mvar_app` read it.
pub(crate) fn entry(&self, id: NameId) -> Option<&LocalEntry> {
    self.local_names.iter().rev().find(|e| e.id == id)
}
```

`lctx_lookup_by_name` becomes `self.local_names.iter().rev().find(|e| e.name == Some(name)).map(|e| e.fvar)`.

- [ ] **Step 6: Drop the `kind` parameter from the deferred install**

`install_local_instance_for_last_pushed` reads the stored kind instead of taking one. Its existing `debug_assert` that `fvar` is the most recently pushed declaration is what makes this sound:

```rust
pub fn install_local_instance_for_last_pushed(
    &mut self,
    fvar: ExprId,
    ty: ExprId,
) -> Result<(), MetaError> {
    debug_assert_eq!(/* unchanged lockstep assert */);
    debug_assert_eq!(
        self.local_names.last().map(|e| e.fvar),
        Some(fvar),
        "fvar must be the most recently pushed local decl"
    );
    let kind = self.local_names.last().map(|e| e.kind).unwrap_or(LocalDeclKind::Default);
    let depth = self.lctx.save().saturating_sub(1);
    self.install_local_instance_for(fvar, ty, depth, kind)
}
```

Then update its one caller in `leanr_elab` (`builtin/binder/fun.rs`'s `elab_fun`) to drop the argument — and, because the kind must now be stored BEFORE the deferred install, make `elab_fun` push through a `push_local_decl_without_instance` variant that carries the user-binder kind. Add to `metactx.rs`:

```rust
/// [`Self::push_local_decl_without_instance`] with the declaration's
/// kind, for the deferred-install path: the kind must be STORED at push
/// time, because `install_local_instance_for_last_pushed` now reads it
/// from the row rather than taking it as a parameter.
pub fn push_local_decl_without_instance_with_kind(
    &mut self,
    name: Option<NameId>,
    ty: ExprId,
    bi: BinderInfo,
    kind: LocalDeclKind,
) -> Result<ExprId, MetaError> {
    let (fvar, _depth) = self.push_local_decl_inner(name, ty, bi, kind)?;
    self.lctx_snapshot = None;
    Ok(fvar)
}
```

In `leanr_elab`'s `builtin/binder/mod.rs`, `push_user_binder` keeps computing the kind; `fun.rs` uses the `_with_kind` variant for its deferred push and then calls `install_local_instance_for_last_pushed(fvar, dom)`.

- [ ] **Step 7: Update the snapshot and its `reduced`**

`LocalCtxSnapshot::new` takes `Vec<LocalEntry>`; its two `debug_assert`s read `e.fvar` instead of destructuring the tuple. `parts` returns `&[LocalEntry]`. `entries` returns `&[LocalEntry]`. In `reduced`, the filter loop becomes:

```rust
let mut local_names: Vec<LocalEntry> = Vec::new();
for entry in &self.local_names {
    if erased(entry.fvar) {
        new_depth.push(None);
    } else {
        new_depth.push(Some(local_names.len()));
        local_names.push(entry.clone());
    }
}
```

`install_lctx` becomes `self.local_names = names.to_vec();` (unchanged in shape — `names` is now `&[LocalEntry]`).

- [ ] **Step 8: Fix the two remaining readers**

`mk_binding.rs:227`: `let entries: Vec<ExprId> = lctx.entries().iter().map(|e| e.fvar).collect();`
`instances.rs:1539`: `let pushed: Vec<ExprId> = ctx.local_names[cp..].iter().map(|e| e.fvar).collect();`

- [ ] **Step 9: Update the four `push_let_decl` producers**

Each already has the bit:

| File | Change |
|---|---|
| `whnf.rs:1592` (`sunfold_go_let`) | `self.push_let_decl(decl_name, ty, value, non_dep)?` — it already takes `non_dep` as a parameter and currently drops it |
| `infer.rs:718` | pass the `LetE` node's `non_dep` (bind it in the existing `Node::LetE { … }` pattern) |
| `transform.rs:240` | pass the `non_dep` already bound in that match arm |
| `mk_binding.rs:1180` (test) | `push_let_decl(None, sort0, sort0, false)` |
| `leanr_elab` `push_user_let_decl` | thread `non_dep` from `elab_let_like`, which already has it |

`push_user_let_decl`'s new signature: `fn push_user_let_decl(elab, name, ty, value, non_dep: bool)`.

- [ ] **Step 10: Run the tests**

Run: `cargo test -p leanr_meta --lib local_entries && cargo test -p leanr_meta --lib a_stored_impl_detail`
Expected: PASS.

- [ ] **Step 11: Prove behaviour-neutrality**

```bash
mise run meta:fast            # whnf/infer/defeq + synthesis corpora
cargo test -p leanr_elab --test oracle_elab
git diff --stat tests/fixtures   # MUST be empty
```
Expected: all pass, fixtures untouched. This task changes no behaviour; if a corpus moves, STOP and report.

- [ ] **Step 12: Run the mutation**

In `push_let_decl_with_kind`, hardcode `nondep: false`. `local_entries_record_nondep_and_kind` must FAIL. Revert.

- [ ] **Step 13: Commit**

```bash
mise run ci
git add -A crates/leanr_meta crates/leanr_elab
git commit -m "meta: per-declaration attribute rows carrying nondep and kind"
```

---

### Task 4: `whnf` zeta-delta skips a `have`

**Files:**
- Modify: `crates/leanr_meta/src/whnf.rs:278-287` (the `Node::FVar` arm of `whnf_easy_cases`)
- Test: `crates/leanr_elab/tests/binder_smoke.rs` (the acceptance test) and `crates/leanr_meta/src/whnf.rs` tests

**Interfaces:**
- Consumes: `MetaCtx::local_entry` (Task 3).
- Produces: nothing new.

**Measure first.** The spec's § Risk flags one unmeasured claim: that leanr currently ACCEPTS `have n : Nat := Nat.zero; (rfl : Eq n Nat.zero)`, which the oracle rejects with a type mismatch. Step 1 measures it.

- [ ] **Step 1: Measure the current behaviour**

```bash
cd /workspace
cat > /tmp/probe.rs <<'EOF'
mod support;
#[test]
fn probe() {
    for src in [
        "let n : Nat := Nat.zero; (rfl : Eq n Nat.zero)",
        "have n : Nat := Nat.zero; (rfl : Eq n Nat.zero)",
    ] {
        eprintln!("PROBE {src:?} -> {:?}", support::elab_result(src).map(|_| "accepted"));
    }
}
EOF
cp /tmp/probe.rs crates/leanr_elab/tests/zz_probe.rs
cargo test -p leanr_elab --test zz_probe -- --nocapture 2>&1 | grep PROBE
rm crates/leanr_elab/tests/zz_probe.rs
```

Expected: both "accepted". **If the `have` row already errors, STOP** — consumer 4's discriminator is wrong; report it and redesign the test before changing any code.

- [ ] **Step 2: Write the failing test**

In `crates/leanr_elab/tests/binder_smoke.rs`:

```rust
/// A `have`-bound variable is OPAQUE: the oracle never zeta-delta
/// expands a `nondep` let-declaration (`WHNF.lean:397-409` matches only
/// `.ldecl (nondep := false)`), so `n` is not definitionally `Nat.zero`
/// and `rfl` does not typecheck. Measured on the pinned binary: "Type
/// mismatch … has type Eq ?m ?m but is expected to have type
/// Eq n Nat.zero".
///
/// The `let` twin MUST still elaborate — that is the corpus record
/// `nondep/let-rfl` — so this pins the fix without over-correcting into
/// "no let value is ever followed".
#[test]
fn a_have_bound_variable_is_opaque_to_defeq() {
    let err = support::elab_result("have n : Nat := Nat.zero; (rfl : Eq n Nat.zero)")
        .expect_err("the oracle rejects this; leanr must too");
    assert!(
        matches!(err, leanr_elab::ElabError::TypeMismatch { .. }),
        "expected a type mismatch, got {err:?}"
    );

    support::elab_result("let n : Nat := Nat.zero; (rfl : Eq n Nat.zero)")
        .expect("a genuine `let` stays transparent");
}
```

Pin the real variant after running it — if the error is not `TypeMismatch`, use whatever variant it is and say so in the task report.

- [ ] **Step 3: Run to verify it fails**

Run: `cargo test -p leanr_elab --test binder_smoke a_have_bound_variable_is_opaque`
Expected: FAIL — `expect_err` panics because leanr accepts the term.

- [ ] **Step 4: Implement**

```rust
Node::FVar { id } => {
    // oracle (`WHNF.lean:397-409`): the pattern match considers only
    // `.ldecl (value := v) (nondep := false)`. A `have` (`nondep :=
    // true`) falls into the oracle's `_ => return e` arm and is NEVER
    // followed, whatever `cfg.zetaDelta` says — it is "locally a
    // cdecl". Before the nondep slice this followed every let-bound
    // fvar, an over-approximation that made `have n := Nat.zero;
    // (rfl : Eq n Nat.zero)` elaborate here and fail on the oracle.
    let followed = id
        .and_then(|i| {
            let genuine_let = self.local_entry(i).is_some_and(|e| !e.nondep);
            if genuine_let { self.lctx.get(i).and_then(|d| d.value) } else { None }
        })
        .filter(|_| self.cfg.zeta_delta);
    match followed {
        Some(v) => v,
        None => return Ok(EasyOrHard::Easy(e)),
    }
}
```

Borrow-checker note: `local_entry` borrows `self` immutably and so does `self.lctx.get`; if the closure fights the borrow checker, hoist both lookups into `let`s before the `match`. Also DELETE the stale paragraph in that arm's comment claiming leanr "carries NO `nondep` bit at all".

- [ ] **Step 5: Run the tests**

Run: `cargo test -p leanr_elab --test binder_smoke a_have_bound_variable_is_opaque`
Expected: PASS.

- [ ] **Step 6: Run the corpora**

```bash
mise run meta:fast
cargo test -p leanr_elab --test oracle_elab
git diff --stat tests/fixtures    # MUST be empty
```
A moved record here is a finding: STOP and report.

- [ ] **Step 7: Run the mutation**

Invert to `e.nondep`. The new test must FAIL. Revert.

- [ ] **Step 8: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/whnf.rs crates/leanr_elab/tests/binder_smoke.rs
git commit -m "meta: zeta-delta never follows a have-bound value"
```

---

### Task 5: WITHDRAWN — `whnf`'s `zeta_unused` is already exact

**Do not implement this task.** It is kept, rather than renumbered away,
so the record of why it existed survives.

The spec's § Design 4 originally claimed `whnf.rs:343`'s
`self.cfg.zeta_unused && self.data(body).loose_bvar_range() == 0` was an
approximation of the oracle's `!body.hasLooseBVar 0`, and the project
owner approved fixing it here. **That claim was wrong**, found while
firming up this plan:

- `whnfCore`'s `letE` arm reads `cfg.zetaUnused && !b.hasLooseBVars`
  (`WHNF.lean:661`) — the PLURAL predicate, defined as
  `looseBVarRange > 0` (`Lean/Expr.lean:1312-1313`).
- `consumeUnusedLet` (`WHNF.lean:639-642`) tests the same plural
  predicate and performs NO lowering — sound precisely because the body
  is closed.
- leanr's branch and its `consume_unused_let` (`whnf.rs:400-413`) match
  both, exactly.

Had this task been implemented as written, relaxing the branch to the
singular test without also lowering in `consume_unused_let` would have
emitted terms with off-by-one bvar indices.

Task 2's exact `has_loose_bvar` is still required: `mkAuxMVarType`'s
ldecl arm really does use the SINGULAR `e.hasLooseBVar 0`
(`MetavarContext.lean:1138`), which Task 8 consumes.

---


### Task 6: the three `assign.rs` let-value sites

**Files:**
- Modify: `crates/leanr_meta/src/assign.rs:796` (`simp_assignment_arg_aux`), `:863` (`mk_lambda_fvars_with_let_deps`), `:1031` (`check_assignment_scope_body`)
- Test: `crates/leanr_meta/src/assign.rs` tests

**Interfaces:**
- Consumes: `MetaCtx::local_entry` (Task 3).
- Produces: nothing new.

Oracle semantics for each: `simpAssignmentArgAux` expands through `FVarId.getValue?` (`Meta/Basic.lean:1044`, `allowNondep := false`); `checkFVar` matches `.ldecl (nondep := false)` and treats a `have` as "locally a cdecl" (`ExprDefEq.lean:851-877`); `hasLetDeclsInBetween` uses `LocalDecl.isLet`, which is `false` for a nondep ldecl (`LocalContext.lean:106-109`).

- [ ] **Step 1: Write the failing tests**

```rust
/// oracle: `simpAssignmentArgAux` expands a let-bound argument through
/// `FVarId.getValue?`, whose `allowNondep` defaults to FALSE
/// (`Meta/Basic.lean:1044`) — so a `have`-bound argument is left alone.
#[test]
fn simp_assignment_arg_expands_a_let_but_not_a_have() {
    with_prelude0_ctx(|ctx| {
        let nat = const_named(ctx, "Nat");
        let zero = const_named(ctx, "Nat.zero");
        let cp = ctx.lctx_checkpoint();
        let l = ctx.push_let_decl(None, nat, zero, false).expect("let");
        let h = ctx.push_let_decl(None, nat, zero, true).expect("have");

        assert_eq!(ctx.simp_assignment_arg(l).expect("let"), zero, "a genuine let expands");
        assert_eq!(ctx.simp_assignment_arg(h).expect("have"), h, "a have is opaque");
        ctx.lctx_restore(cp);
    });
}

/// oracle: `checkFVar` matches `.ldecl (nondep := false)`; a `have` is
/// "locally a cdecl" and so is judged by whether it is among the fvars
/// being abstracted, exactly like a cdecl.
#[test]
fn check_assignment_treats_a_have_as_a_cdecl() {
    with_prelude0_ctx(|ctx| {
        let nat = const_named(ctx, "Nat");
        let zero = const_named(ctx, "Nat.zero");
        let cp = ctx.lctx_checkpoint();
        let h = ctx.push_let_decl(None, nat, zero, true).expect("have");
        let (_m, mid) = fresh_mvar(ctx, nat);

        // `h` is not in the mvar's context and not among `fvars`, so a
        // cdecl would be out of scope: `false`. The point is that it
        // reaches that test at all rather than short-circuiting on
        // "has a value".
        assert!(!ctx.check_assignment_scope_body(mid, &[], h).expect("scope"));
        // ... and WITH it among the abstracted fvars it is in scope,
        // which a let-decl could never be.
        assert!(ctx.check_assignment_scope_body(mid, &[h], h).expect("scope"));
        ctx.lctx_restore(cp);
    });
}
```

Mirror the surrounding tests for how mvars are minted (`fresh_mvar`) and adjust visibility if these functions are private — make them `pub(crate)` only if the test module cannot otherwise reach them, and note it in the task report.

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test -p leanr_meta --lib simp_assignment_arg_expands && cargo test -p leanr_meta --lib check_assignment_treats_a_have`
Expected: FAIL — the `have` expands, and the scope check short-circuits to `false`.

- [ ] **Step 3: Implement all three**

```rust
// :796, simp_assignment_arg_aux
Node::FVar { id: Some(id) } => {
    let genuine_let = self.local_entry(id).is_some_and(|e| !e.nondep);
    match self.lctx.get(id).and_then(|d| d.value).filter(|_| genuine_let) {
        Some(v) => self.simp_assignment_arg_aux(v),
        None => Ok(e),
    }
}

// :863, mk_lambda_fvars_with_let_deps — the seam narrows to genuine lets
if self.lctx.get(id).and_then(|d| d.value).is_some()
    && self.local_entry(id).is_some_and(|e| !e.nondep)
{
    return Ok(None); // SEAM
}

// :1031, check_assignment_scope_body
let is_let = self.lctx.get(fid).and_then(|d| d.value).is_some()
    && self.local_entry(fid).is_some_and(|e| !e.nondep);
```

Each gets a one-line oracle citation as above.

- [ ] **Step 4: Run the tests and the corpora**

```bash
cargo test -p leanr_meta --lib assign
mise run meta:fast
cargo test -p leanr_elab --test oracle_elab
git diff --stat tests/fixtures    # MUST be empty
```

- [ ] **Step 5: Run the mutations**

Invert the `nondep` test at each of the three sites in turn; the matching test must FAIL each time. The `mk_lambda_fvars_with_let_deps` site has no direct test — if inverting it breaks nothing, say so in the task report and add a test that reaches it, or record it as knowingly unprotected with the reason.

- [ ] **Step 6: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/assign.rs
git commit -m "meta: checkAssignment-family sites honour nondep"
```

---

### Task 7: `local_decl_depends_on` and `mk_mvar_app`

**Files:**
- Modify: `crates/leanr_meta/src/mk_binding.rs:138` (`local_decl_depends_on`), `:227` (its caller), `:268` (`mk_mvar_app`), `:661` (the `mk_mvar_app` call in `elim_mvar`)
- Test: `crates/leanr_meta/src/mk_binding.rs` tests

**Interfaces:**
- Consumes: `LocalCtxSnapshot::entry` (Task 3).
- Produces:
  - `fn local_decl_depends_on(&mut self, ty: ExprId, value: Option<ExprId>, pf: &[NameId], generalize_nondep_let: bool) -> Result<bool, MetaError>`
  - `fn mk_mvar_app(&mut self, mvar: ExprId, xs: &[ExprId], lctx: &LocalCtxSnapshot, kind: MVarKind) -> Result<ExprId, MetaError>`

- [ ] **Step 1: Write the failing tests**

```rust
/// oracle: `findLocalDeclDependsOn` (`MetavarContext.lean:744-753`) —
/// with `generalizeNondepLet` (the default at every leanr call site),
/// a nondep ldecl is treated as a cdecl and its VALUE is ignored.
#[test]
fn local_decl_depends_on_ignores_a_nondep_value_when_generalizing() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        let ia = fvar_id(ctx, a);

        // Type mentions nothing; the VALUE mentions `a`.
        assert!(
            !ctx.local_decl_depends_on(sort0, Some(a), &[ia], true).expect("generalizing"),
            "a nondep value is ignored when generalizing"
        );
        assert!(
            ctx.local_decl_depends_on(sort0, Some(a), &[ia], false).expect("not generalizing"),
            "without the flag the value counts"
        );
        ctx.lctx_restore(cp);
    });
}

/// oracle: `mkMVarApp` (`:1090-1097`) — a genuine let-bound fvar is NOT
/// applied to the auxiliary metavariable; a `have` IS, because
/// `LocalDecl.isLet` is false for a nondep ldecl.
#[test]
fn mk_mvar_app_skips_a_let_but_applies_a_have() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
        let cp = ctx.lctx_checkpoint();
        let l = ctx.push_let_decl(None, sort0, sort0, false).expect("let");
        let h = ctx.push_let_decl(None, sort0, sort0, true).expect("have");
        let (m, _mid) = fresh_mvar(ctx, sort0);
        let snap = ctx.current_lctx();
        ctx.lctx_restore(cp);

        let app = ctx
            .mk_mvar_app(m, &[l, h], &snap, crate::MVarKind::Natural)
            .expect("mk_mvar_app");
        // Only the `have` is applied: `?m h`.
        match ctx.node(app) {
            Node::App { f, arg } => {
                assert_eq!(f, m, "the let must not be applied");
                assert_eq!(arg, h, "the have must be applied");
            }
            other => panic!("expected one application, got {other:?}"),
        }

        // A syntheticOpaque metavariable applies EVERYTHING (`:1096`).
        let opaque = ctx
            .mk_mvar_app(m, &[l, h], &snap, crate::MVarKind::SyntheticOpaque)
            .expect("mk_mvar_app");
        assert_ne!(opaque, app, "syntheticOpaque applies the let too");
    });
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test -p leanr_meta --lib local_decl_depends_on_ignores && cargo test -p leanr_meta --lib mk_mvar_app_skips`
Expected: FAIL to COMPILE (arity changed).

- [ ] **Step 3: Implement**

```rust
// local_decl_depends_on — oracle `:744-753`
pub(crate) fn local_decl_depends_on(
    &mut self,
    ty: ExprId,
    value: Option<ExprId>,
    pf: &[NameId],
    generalize_nondep_let: bool,
) -> Result<bool, MetaError> {
    if self.depends_on(ty, pf)? {
        return Ok(true);
    }
    // oracle `:748-749`: `generalizeNondepLet && nondep` → the type
    // alone decides; a nondep ldecl is a cdecl for dependency purposes.
    match value.filter(|_| !generalize_nondep_let) {
        Some(v) => self.depends_on(v, pf),
        None => Ok(false),
    }
}
```

The caller at `:227` reads the row and passes the flag. Note the shape: the oracle's condition is `generalizeNondepLet && nondep`, so the caller must supply BOTH — read `nondep` from `lctx.entry(id)` and pass `generalize_nondep_let && entry.nondep` as the "skip the value" decision, or keep the flag literal and test `nondep` inside. Pick one and be consistent; the test above assumes the caller passes the already-combined decision as `generalize_nondep_let`.

```rust
// the :227 call site
let skip_value = lctx.entry(id).is_some_and(|e| e.nondep); // generalizeNondepLet is true here
if self.local_decl_depends_on(ty, value, &collected_ids, skip_value)? {
```

```rust
// mk_mvar_app — oracle `:1090-1097`
pub(crate) fn mk_mvar_app(
    &mut self,
    mvar: ExprId,
    xs: &[ExprId],
    lctx: &LocalCtxSnapshot,
    kind: crate::MVarKind,
) -> Result<ExprId, MetaError> {
    let mut e = mvar;
    for x in xs {
        // oracle `:1095-1097`: a syntheticOpaque metavariable applies
        // every fvar; otherwise a genuine let-bound one is skipped,
        // because `LocalDecl.isLet` is FALSE for a nondep ldecl
        // (`LocalContext.lean:106-109`) — a `have` is applied like a
        // cdecl.
        if kind != crate::MVarKind::SyntheticOpaque {
            if let Some(id) = self.fvar_id_of(*x) {
                let is_let = lctx.lctx().get(id).and_then(|d| d.value).is_some()
                    && lctx.entry(id).is_some_and(|en| !en.nondep);
                if is_let {
                    continue;
                }
            }
        }
        e = self.scratch.expr_app(Some(self.view.store), e, *x)?;
    }
    Ok(e)
}
```

Update `elim_mvar`'s call (`:661`) to `self.mk_mvar_app(new_mvar, &to_revert, &mvar_lctx, kind)?`, and delete the stale doc paragraph claiming the two kind branches coincide under an ldecl refusal.

- [ ] **Step 4: Run the tests and corpora**

```bash
cargo test -p leanr_meta --lib mk_binding
mise run meta:fast
cargo test -p leanr_elab --test oracle_elab
git diff --stat tests/fixtures    # MUST be empty
```

- [ ] **Step 5: Run the mutations**

Drop the `isLet` skip (apply everything): `mk_mvar_app_skips_a_let_but_applies_a_have` must FAIL. Drop the `generalize_nondep_let` filter: the depends-on test must FAIL. Revert each.

- [ ] **Step 6: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/mk_binding.rs
git commit -m "meta: mkMVarApp's isLet and localDeclDependsOn's generalizeNondepLet"
```

---

### Task 8: `mk_aux_mvar_type`'s ldecl arms

**Files:**
- Modify: `crates/leanr_meta/src/mk_binding.rs:688-810` (`mk_aux_mvar_type`, `mk_aux_mvar_type_with`, and the `elim_mvar` call at `:659`)
- Test: `crates/leanr_meta/src/mk_binding.rs` tests (and REPLACE `mk_aux_mvar_type_refuses_a_let_decl_in_to_revert` at `:1169+`)

**Interfaces:**
- Consumes: `LocalCtxSnapshot::entry` (Task 3), `MetaCtx::has_loose_bvar` (Task 2), `leanr_kernel::lower_loose_bvars` (Task 1), `lift_loose_bvars` (existing).
- Produces: `fn mk_aux_mvar_type_with(&mut self, lctx, xs, ty, kind: MVarKind, used_let_only: bool, cache) -> Result<ExprId, MetaError>`.

The oracle (`MetavarContext.lean:1133-1156`), for each reverted entry, innermost last:

| Decl | Condition | Result |
|---|---|---|
| ldecl, `nondep := true` | — | `mkForall n .default type e` |
| ldecl, `nondep := false` | `!usedLetOnly \|\| e.hasLooseBVar 0`, kind syntheticOpaque | `mkLet n type value e false`, then `liftLooseBVars 0 1`, then `mkForall n .default type e` |
| ldecl, `nondep := false` | same condition, other kinds | `mkLet n type value e false` |
| ldecl, `nondep := false` | condition false, kind syntheticOpaque | `mkForall n .default type e` |
| ldecl, `nondep := false` | condition false, other kinds | `e.lowerLooseBVars 1 1` |

leanr's only caller reaches this through `elim_app`'s unassigned arm, where the oracle passes `usedLetOnly := true` (`:1219-1221`); `revert`, its `false` caller, has no leanr producer. Pass the constant `true` from `elim_mvar` and document it.

- [ ] **Step 1: Write the failing tests**

```rust
/// oracle `:1133-1136`: a `have` in `to_revert` becomes a plain
/// `forall` with `BinderInfo::Default` — it is a cdecl here.
#[test]
fn mk_aux_mvar_type_turns_a_have_into_a_forall() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
        let cp = ctx.lctx_checkpoint();
        let h = ctx.push_let_decl(None, sort0, sort0, true).expect("have");
        let snap = ctx.current_lctx();
        ctx.lctx_restore(cp);

        let out = ctx
            .mk_aux_mvar_type(&snap, &[h], sort0, crate::MVarKind::Natural, true)
            .expect("mk_aux_mvar_type");
        match ctx.node(out) {
            Node::Forall { binder_info, .. } => {
                assert_eq!(binder_info, leanr_kernel::BinderInfo::Default)
            }
            other => panic!("expected Forall, got {other:?}"),
        }
    });
}

/// oracle `:1137-1148`: a genuine `let` whose binder the accumulated
/// type USES becomes a `letE` (with `nondep := false`, `:1142`).
#[test]
fn mk_aux_mvar_type_keeps_a_used_let_as_a_let() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
        let cp = ctx.lctx_checkpoint();
        let l = ctx.push_let_decl(None, sort0, sort0, false).expect("let");
        let snap = ctx.current_lctx();
        ctx.lctx_restore(cp);

        // The mvar's type mentions `l`, so after abstraction the
        // accumulated `e` has `#0` loose.
        let out = ctx
            .mk_aux_mvar_type(&snap, &[l], l, crate::MVarKind::Natural, true)
            .expect("mk_aux_mvar_type");
        match ctx.node(out) {
            Node::LetE { non_dep, .. } => assert!(!non_dep, "oracle :1142 passes `false`"),
            other => panic!("expected LetE, got {other:?}"),
        }
    });
}

/// oracle `:1149-1156`: an UNUSED genuine let is dropped and the
/// accumulated type lowered by one — the arm that needs
/// `lower_loose_bvars`.
#[test]
fn mk_aux_mvar_type_drops_an_unused_let_and_lowers() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
        let cp = ctx.lctx_checkpoint();
        let l = ctx.push_let_decl(None, sort0, sort0, false).expect("let");
        let snap = ctx.current_lctx();
        ctx.lctx_restore(cp);

        // The type does NOT mention `l`.
        let out = ctx
            .mk_aux_mvar_type(&snap, &[l], sort0, crate::MVarKind::Natural, true)
            .expect("mk_aux_mvar_type");
        assert_eq!(out, sort0, "the unused let leaves no binder behind");
    });
}
```

DELETE `mk_aux_mvar_type_refuses_a_let_decl_in_to_revert` — its refusal is what this task removes.

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test -p leanr_meta --lib mk_aux_mvar_type 2>&1 | tail -30`
Expected: FAIL to COMPILE (arity), and once compiling, the refusal error.

- [ ] **Step 3: Implement**

Replace the `if decl.value.is_some() { return Err(...) }` refusal with the arms. Restructure the loop body so an ldecl entry can produce `e` directly (the cdecl and mvar arms still fall through to the shared `expr_forall` tail):

```rust
let is_opaque = kind == crate::MVarKind::SyntheticOpaque;
// ... inside the fvar branch, after fetching `decl`:
if let Some(value) = decl.value {
    let nondep = lctx.entry(id).is_some_and(|en| en.nondep);
    let bty = self.head_beta(decl.ty)?;
    let bty = self.abstract_range_aux(xs, i, bty, cache)?;
    if nondep {
        // oracle :1133-1136 — a have is a cdecl here.
        e = self.scratch.expr_forall(
            Some(self.view.store), decl.binder_name, bty, e,
            leanr_kernel::BinderInfo::Default,
        )?;
    } else if !used_let_only || self.has_loose_bvar(e, 0)? {
        // oracle :1138-1148
        let value = self.abstract_range_aux(xs, i, value, cache)?;
        let built = self.scratch.expr_let(
            Some(self.view.store), decl.binder_name, bty, value, e, false,
        )?;
        e = if is_opaque {
            // oracle :1144-1147 — see the file's "Gruesome details".
            let lifted = leanr_kernel::lift_loose_bvars(
                self.scratch, Some(self.view.store), built, 0, 1, &mut self.guard,
            )?;
            self.scratch.expr_forall(
                Some(self.view.store), decl.binder_name, bty, lifted,
                leanr_kernel::BinderInfo::Default,
            )?
        } else {
            built
        };
    } else if is_opaque {
        // oracle :1150-1154
        e = self.scratch.expr_forall(
            Some(self.view.store), decl.binder_name, bty, e,
            leanr_kernel::BinderInfo::Default,
        )?;
    } else {
        // oracle :1155-1156
        e = leanr_kernel::lower_loose_bvars(
            self.scratch, Some(self.view.store), e, 1, 1, &mut self.guard,
        )?;
    }
    continue;
}
```

**Read `:1123-1168` of `MetavarContext.lean` while writing this** and match the arm order and the abstraction points exactly — in particular that `type.headBeta` precedes `abstractRangeAux` and that the syntheticOpaque let-arm lifts the WHOLE built `letE`, not just the body.

Thread the two new parameters: `mk_aux_mvar_type_with(&mut self, lctx, xs, ty, kind, used_let_only, cache)`; the `#[cfg(test)] mk_aux_mvar_type` wrapper takes them too; `elim_mvar` passes `kind` and the literal `true` with a comment citing `:1219-1221`.

- [ ] **Step 4: Run the tests and corpora**

```bash
cargo test -p leanr_meta --lib mk_aux_mvar_type
mise run meta:fast
cargo test -p leanr_elab --test oracle_elab
git diff --stat tests/fixtures    # MUST be empty
```

- [ ] **Step 5: Run the mutations**

Swap `lower_loose_bvars` for `lift_loose_bvars` in the last arm (the drop test must FAIL); treat `nondep` as `false` (the have test must FAIL); drop the `has_loose_bvar` condition so every genuine let takes the let-arm (the drop test must FAIL). Revert each.

- [ ] **Step 6: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/mk_binding.rs
git commit -m "meta: port mkAuxMVarType's ldecl arms"
```

---

### Task 9: `mk_let_expr` runs `elim_mvar_deps` — the gap closes

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs:1096-1130` (`mk_let_expr` and its doc)
- Modify: `tests/fixtures/elab/dump_elab.lean` (new `nondepQueries` group + the `main` concat list at `:871`)
- Modify: `tests/fixtures/elab/elab-queries.jsonl` (regenerated)
- Modify: `crates/leanr_elab/tests/seam_audit.rs` (`a_coercion_postponed_under_a_let_leaks_an_fvar`)

**Interfaces:**
- Consumes: Tasks 7 and 8 (without the ldecl arms this errors instead of leaking).
- Produces: nothing new.

- [ ] **Step 1: Add the oracle records**

In `dump_elab.lean`, after `closeoutExplicitQueries`:

```lean
/-- The nondep slice (spec `2026-09-29-nondep-local-decls-design.md`).

`*-coe`: a `.coe` metavariable postponed inside a `let`/`have` body is
still UNASSIGNED when the binder closes, so `mk_let_expr` must run
`elim_mvar_deps` (`mkLetFVars` → `mkBinding` → `abstractRange`) or the
resumed coercion leaks the let-bound fvar. The `fun` twin of these is
`coe/postponedThenResumedUnderBinder`.

`let-rfl` guards the other direction: `whnf` still zeta-delta expands a
GENUINE let, so `rfl` typechecks here. Its `have` twin is rejected by
the oracle and is pinned by `binder_smoke.rs`'s
`a_have_bound_variable_is_opaque_to_defeq` instead — a rejected term
emits no record. -/
def nondepQueries : List (String × String) :=
  [ ("nondep/let-coe",  "let n : Nat := Nat.zero; pairW n Nat.zero")
  , ("nondep/have-coe", "have n : Nat := Nat.zero; pairW n Nat.zero")
  , ("nondep/let-rfl",  "let n : Nat := Nat.zero; (rfl : Eq n Nat.zero)")
  ]
```

and append `++ nondepQueries` to the `for (id, src) in …` list at `:871`.

- [ ] **Step 2: Regenerate and verify the corpus grew by exactly three**

```bash
mise run fixtures:regen-elab
git diff --numstat tests/fixtures/elab/elab-queries.jsonl   # MUST be "3	0"
grep -c '' tests/fixtures/elab/elab-queries.jsonl           # 165
```

- [ ] **Step 3: Run to verify the corpus gate fails**

Run: `cargo test -p leanr_elab --test oracle_elab 2>&1 | tail -20`
Expected: FAIL on `nondep/let-coe` and `nondep/have-coe` — leanr emits `fvar` where the oracle has `bvar 0`. (`nondep/let-rfl` should already pass.)

- [ ] **Step 4: Implement**

```rust
let body = self.elim_mvar_deps(std::slice::from_ref(&fvar), body)?;
let body = abstract_fvars(/* unchanged */)?;
```

with a comment citing `mkBinding`'s `abstractRange` (`MetavarContext.lean:1313`, which is `elimMVarDeps` then `abstractRange`), and REWRITE the "Known gap" paragraph in the doc: the gap is closed; what remains is that `mk_let_expr` abstracts exactly one fvar, the shape `elabLetDeclAux` needs.

- [ ] **Step 5: Run the corpus gate**

Run: `cargo test -p leanr_elab --test oracle_elab`
Expected: PASS, 165 records.

- [ ] **Step 6: Flip the gap-2 pin**

In `seam_audit.rs`, `a_coercion_postponed_under_a_let_leaks_an_fvar` becomes:

```rust
/// A `.coe` metavariable postponed inside a `let`/`have` body and
/// resumed after the binder closed comes back ABSTRACTED — `bvar 0`,
/// the oracle's answer for both forms. Until the nondep slice this
/// pinned the wrong answer (an unabstracted `fvar`), because
/// `mk_let_expr` abstracted with a bare `abstract_fvars` and
/// `mkAuxMVarType`'s ldecl arms had no `nondep` bit to read.
///
/// The corpus carries the same two queries (`nondep/let-coe`,
/// `nondep/have-coe`); this test keeps the oracle's answer inline, so a
/// regeneration cannot silently move the target — the same posture as
/// `postponed_coe_under_a_binder_abstracts_via_elim_mvar_deps`.
#[test]
fn a_coercion_postponed_under_a_let_abstracts_to_bvar_0() {
    for src in [
        "let n : Nat := Nat.zero; pairW n Nat.zero",
        "have n : Nat := Nat.zero; pairW n Nat.zero",
    ] {
        let j = support::elab_and_synthesize(src).expect("elaborates and synthesizes");
        assert_eq!(j["k"], "let", "{src}");
        let n = &j["b"]["f"]["a"]["a"];
        assert_eq!(
            *n,
            serde_json::json!({"k": "bvar", "i": 0}),
            "`{src}`: the let-bound variable must come back abstracted. Got {n}"
        );
    }
}
```

- [ ] **Step 7: Run the mutation**

Delete the `elim_mvar_deps` line. The two `nondep/*-coe` records AND the flipped test must FAIL. Revert.

- [ ] **Step 8: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/metactx.rs crates/leanr_elab/tests/seam_audit.rs tests/fixtures/elab/
git commit -m "meta: mk_let_expr eliminates mvar deps before abstracting"
```

---

### Task 10: branch sweep, spec § Landed, PR

**Files:**
- Modify: `docs/superpowers/specs/2026-09-29-nondep-local-decls-design.md` (add § Landed)
- Modify: any stale comment the sweep finds

- [ ] **Step 1: Sweep for stale claims**

```bash
cd /workspace
grep -rn "carries no \`nondep\`\|carries NO \`nondep\`\|no nondep bit\|nondep bit .*does not carry" crates --include=*.rs
grep -rn "let-decl fvar in to_revert" crates --include=*.rs
grep -rn "consumed_by_synthesis_leaks_an_fvar\|a_coercion_postponed_under_a_let_leaks_an_fvar" crates --include=*.rs
```
Every hit in LIVE code must be gone or rewritten. Hits in `docs/superpowers/plans/` are historical records — leave them.

- [ ] **Step 2: Verify the branch gate**

```bash
git diff --stat main
git diff --stat main -- crates/leanr_kernel        # subst.rs + lib.rs ONLY
git diff --numstat main -- tests/fixtures/elab/elab-queries.jsonl   # "3	0"
git diff --stat main -- tests/fixtures/meta        # EMPTY
git diff main -- lean-toolchain                    # EMPTY
mise run ci
mise run meta:fast
```

- [ ] **Step 3: Write § Landed**

Append to the spec, in the style of the close-out spec's own § Landed: measured corpus counts, the kernel diff, every mutation row with its result, and any ruling made during execution (including the Task 4 measurement and any test whose variant differed from the plan's guess).

- [ ] **Step 4: Commit and open the PR**

```bash
git add docs/superpowers/specs/2026-09-29-nondep-local-decls-design.md
git commit -m "spec: § Landed for the nondep slice"
git push -u origin nondep-local-decls
gh pr create --base main --title "nondep and LocalDeclKind on local declarations" --body "<summary + the evidence table + verification>"
```

- [ ] **Step 5: Merge on green**

Wait for CI, merge, delete the branch, sync main — the standing workflow.

---

## Self-Review

**Spec coverage.** § Design 1 (storage) → Task 3. § Design 2 (producers) → Task 3 Step 9. § Design 3 consumers: 1 → Task 9, 2 → Task 8, 3 → Task 7, 4 → Task 4, 5/6/7 → Task 6, 8 → Task 7. § Design 4 primitives → Tasks 1 and 2; its `zeta_unused` paragraph is WITHDRAWN and Task 5 records why. § Design 5 → Task 9. § Verification records → Task 9 Step 1; unit tests distributed per task; mutation table → one mutation step per task; branch gate → Task 10.

**Type consistency.** `LocalEntry`'s five fields are used as declared in Tasks 3-9. `push_let_decl(name, ty, value, non_dep)` has the same arity everywhere it appears (Tasks 3, 6, 7, 8). `mk_mvar_app(mvar, xs, lctx, kind)` and `mk_aux_mvar_type(lctx, xs, ty, kind, used_let_only)` match between their defining task (7, 8) and their tests.

**Softness resolved during self-review, not handed off.** The first draft asked the implementer to check `Node::BVar`'s field shape and `consume_unused_let`'s semantics themselves. Both were read instead:

- `Node::BVar { idx: u32 }`, `Node::BVarBig { idx: NatId }`, and `Proj`/`ProjBig` carry `structure` — Task 2's code is now written against the real shapes.
- `consume_unused_let` performs no lowering, which is sound only because the branch guarding it requires a CLOSED body. That is what exposed Task 5's premise as false and got the task withdrawn. Implementing it as first written would have produced off-by-one bvar indices.

**Remaining softness, stated rather than hidden:** Task 1 Step 3's `lower_go` leaves the `Proj`/`ProjBig` arm as `unimplemented!` with an instruction to copy `lift_go`'s, because that arm destructures across two node kinds and transcribing it blind invites a subtle error. Task 4 Step 1 measures leanr's current acceptance of the `have … rfl` term before any code changes, and says to stop if the measurement contradicts the spec.
