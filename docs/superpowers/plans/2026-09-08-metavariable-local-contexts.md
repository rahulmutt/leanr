# Metavariable local contexts — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give every metavariable the local context it was minted in, and
reinstall that context when the metavariable is worked on, so a
metavariable can be unified with a `fun`-bound variable and a postponed
one can still resolve its payload after its binder scope closes.

**Architecture:** `leanr_kernel::LocalContext` gains a `Clone` derive —
the one kernel edit, and the reason the current code cannot do this at
all. `leanr_meta` gains `LocalCtxSnapshot` (the context plus `MetaCtx`'s
parallel name index, the two halves that must travel together to keep
their lockstep invariant), shared behind an `Arc` and cached so that one
binder scope costs one copy no matter how many metavariables are minted
in it. Both minting sites store the ambient snapshot; a new
`MetaCtx::with_mvar_context` installs it again; the synthetic-metavariable
ladder runs every arm under it. The out-of-scope check itself is NOT
touched — it already transcribes the oracle correctly and merely starts
receiving truthful input.

**Tech Stack:** Rust (workspace crates `leanr_kernel`, `leanr_meta`,
`leanr_elab`), `mise` task runner, the committed differential corpora.

**Spec:** `docs/superpowers/specs/2026-09-08-metavariable-local-contexts-design.md`
— executors read it first; § The finding, measured is where the three
acceptance behaviours come from. The slice it unblocks is described in
`docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md`
§ Amendment 6.

## Global Constraints

Copied from the spec and `AGENTS.md`. Every task's requirements
implicitly include this section.

- **Pinned oracle: `leanprover/lean4:v4.33.0-rc1`** (`lean-toolchain`),
  sources at
  `/home/dev/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`.
  **Never bump the pin.**
- **The kernel edit is exactly one derive** — `Clone` on
  `LocalContext` (Task 1). No kernel function body changes, no new
  kernel dependency, no other kernel file touched. If a task seems to
  need a second kernel change, stop and report rather than making it.
- **Both committed corpora stay byte-identical**: 107 records in
  `tests/fixtures/elab/elab-queries.jsonl`, 24 compared records in
  `tests/fixtures/meta/synth-queries.jsonl`. Never re-baseline a record
  to make a test pass. A record that moves means an existing agreement
  with the oracle was accidental — stop, record the exact before/after,
  and report.
- **No fixture regeneration.** This slice changes no `.lean` fixture and
  no `.olean`. `mise run fixtures:regen` should not be run at all; if a
  task appears to need it, that is a signal something is wrong.
- **The scope check is not rewritten.**
  `assign.rs::check_assignment_scope_body`'s `FVar` arm and its `MVar`
  seam stay exactly as they are. This slice changes what they are told,
  not what they conclude.
- **`mise run ci` gates `cargo fmt --check` and clippy**, not only
  tests. Run it before every commit; the test tasks alone do not cover
  it.
- **Every discriminator is measured.** Each task that adds a test names
  the mutation it kills, applies that mutation, watches the test go red,
  and reverts. A test that survives its mutation is replaced, not
  shipped.
- **Determinism:** no wall-clock, no `maxHeartbeats`.
- **Commit messages** end with:
  `Claude-Session: https://claude.ai/code/session_01J5wHdBxtXr9M1ixudAhtmA`

## File Structure

**Created:**
- `crates/leanr_meta/src/local_snapshot.rs` — `LocalCtxSnapshot`, its
  empty singleton, and `MetaCtx`'s snapshot cache accessor. One
  responsibility: owning the "ambient context as a shareable value"
  concept, so `metactx.rs` does not grow another concern (Task 2).

**Modified:**
- `crates/leanr_kernel/src/local_ctx.rs` — the `Clone` derive (Task 1).
- `crates/leanr_meta/src/lib.rs` — `mod local_snapshot;` and the
  re-export (Task 2).
- `crates/leanr_meta/src/mvar_ctx.rs` — `MVarDecl::lctx`'s type and its
  doc (Task 2).
- `crates/leanr_meta/src/metactx.rs` — the cache field, its invalidation
  in `push_local_decl` / `push_let_decl` / `lctx_restore`, and
  `with_mvar_context` (Tasks 2, 3).
- `crates/leanr_meta/src/assign.rs` — `mk_aux_mvar` mints ambient
  (Task 2); its `#[cfg(test)]` `MVarDecl` literal (Task 2).
- `crates/leanr_meta/src/{infer.rs,lazy_delta.rs,whnf.rs,test_support.rs}`
  and `crates/leanr_meta/tests/{oracle_synth.rs,oracle_fast.rs}` — the
  remaining `MVarDecl` literals (Task 2).
- `crates/leanr_elab/src/elab.rs` — `mk_fresh_expr_mvar_of_kind` mints
  ambient (Task 4).
- `crates/leanr_elab/src/synthetic/ladder.rs` —
  `synthesize_synthetic_mvar` runs under the metavariable's context
  (Task 4).
- `crates/leanr_meta/src/coe.rs` — the permanent coercion-under-a-binder
  test (Task 5).

## Orientation for the implementer

Read these before Task 1; they are short and they are what the code
below mirrors.

- **The oracle.** `MetavarContext.lean:305-311` — `MetavarDecl.lctx`,
  "The local context containing the free variables that the mvar is
  permitted to depend upon". `Meta/Basic.lean:866-867` —
  `mkFreshExprMVarCore` mints at `(← getLCtx)`, via `mkFreshExprMVarAt`
  (`:855-859`). `Meta/Basic.lean:2043-2052` — `withMVarContextImp` is
  `withLocalContextImp mvarDecl.lctx mvarDecl.localInstances`, exposed as
  `MVarId.withContext`. `Elab/SyntheticMVars.lean:32-36` —
  `resumePostponed` is `withRef stx <| mvarId.withContext do …
  withSavedContext savedContext do`; `:545` — the `.coe` arm carries its
  own `mvarId.withContext`. `Meta/ExprDefEq.lean:1060` —
  `if mvarDecl.lctx.contains fvarId then`, the check whose input this
  slice fixes.
- **leanr today.** `crates/leanr_meta/src/metactx.rs` — the `lctx` and
  `local_names` fields (grep `local_names`), whose doc explains why the
  parallel index exists and why the two stay in lockstep; `lctx_checkpoint`
  / `lctx_restore` / `push_local_decl` / `push_let_decl` are the only
  writers. `crates/leanr_meta/src/assign.rs` — `mk_aux_mvar` (grep
  `fn mk_aux_mvar`), whose own doc says it "Always mints with an EMPTY
  lctx", and `check_assignment_scope_body` (grep
  `fn check_assignment_scope_body`), whose `FVar` arm is the rejection.
  `crates/leanr_meta/src/mvar_ctx.rs` — `MVarDecl`, whose doc explains
  that it has no `Clone` because `LocalContext` has none.
  `crates/leanr_elab/src/elab.rs` — `mk_fresh_expr_mvar_of_kind`.
  `crates/leanr_elab/src/synthetic/ladder.rs` —
  `synthesize_synthetic_mvar`.

**One mechanism to hold in mind.** The bug is not in any predicate. A
metavariable is a promise that "some term with these free variables goes
here", and leanr has been recording that promise with the variable list
left blank. Everything below is about filling it in truthfully and
putting it back when the promise is redeemed.

---

### Task 1: `LocalContext` derives `Clone`

The one kernel edit. `LocalDecl` already derives `Clone`
(`local_ctx.rs`, grep `pub struct LocalDecl`), and `LocalContext` is a
`Vec<LocalDecl>` plus a `HashMap<NameId, usize>`, so the derive is
mechanical. It adds no logic and changes no function body, so it moves
no soundness surface.

**Files:**
- Modify: `crates/leanr_kernel/src/local_ctx.rs` (the `#[derive(Default)]`
  above `pub struct LocalContext`)
- Test: `crates/leanr_kernel/src/local_ctx.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: nothing.
- Produces: `impl Clone for LocalContext`.

- [ ] **Step 1: Write the failing test**

Append inside `local_ctx.rs`'s `#[cfg(test)] mod tests` (if the file has
no test module, create one at the end of the file with the same `use`
lines its neighbours use):

```rust
    /// `LocalContext` is cloneable, and a clone is INDEPENDENT of its
    /// source: pushing into one must not be visible in the other, and a
    /// decl present at clone time must remain reachable in the clone
    /// after the source is restored past it. This is the whole reason
    /// the derive exists — `leanr_meta` stores a clone in every
    /// `MVarDecl` and restores the ambient context around it (oracle:
    /// `MetavarDecl.lctx`, `MetavarContext.lean:305-311`).
    #[test]
    fn local_context_clone_is_independent_of_its_source() {
        let mut st = Store::default();
        let mut gen = FVarIdGen::default();
        let mut lctx = LocalContext::default();
        let ty = st.expr_sort(None, st.level_zero(None).expect("level")).expect("sort");
        let name = {
            let s = st.intern_str(None, "x").expect("intern");
            st.name_str(None, None, s).expect("name")
        };
        let fvar = lctx
            .mk_local_decl(&mut st, None, &mut gen, Some(name), ty, BinderInfo::Default)
            .expect("decl");
        let id = match st.expr_node(None, fvar) {
            crate::bank::terms::Node::FVar { id: Some(id) } => id,
            other => panic!("expected an fvar, got {other:?}"),
        };
        let snapshot = lctx.clone();
        let before = lctx.save();

        // The source grows and then shrinks past the cloned decl.
        let _ = lctx
            .mk_local_decl(&mut st, None, &mut gen, Some(name), ty, BinderInfo::Default)
            .expect("decl");
        assert_eq!(snapshot.save(), before, "the clone did not grow with its source");
        lctx.restore(0);
        assert!(lctx.get(id).is_none(), "source dropped the decl");
        assert!(
            snapshot.get(id).is_some(),
            "the clone still resolves a decl its source has dropped"
        );
    }
```

If `Store::expr_sort`/`level_zero`/`expr_node` have different names in
this crate, use the ones the file's neighbouring tests use (grep
`fn ` inside the existing `mod tests`); the assertions are the point,
not the construction.

- [ ] **Step 2: Run it to verify it fails**

```bash
cargo test -p leanr_kernel local_context_clone_is_independent_of_its_source
```

Expected: a compile error — `no method named clone found for struct LocalContext`.

- [ ] **Step 3: Add the derive**

In `crates/leanr_kernel/src/local_ctx.rs`, above `pub struct LocalContext`:

```rust
/// `Clone` (2026-09-08, the metavariable-local-contexts slice): a
/// metavariable's declaration stores the local context it was minted in
/// (oracle: `MetavarDecl.lctx`, `MetavarContext.lean:305-311`), and
/// `leanr_meta` cannot build one otherwise — `decls`/`index` are
/// module-private and there is no enumeration API. Derive only: no
/// logic, no function body changed, no new dependency, so the kernel's
/// soundness surface is unchanged.
#[derive(Default, Clone)]
pub struct LocalContext {
```

- [ ] **Step 4: Run it to verify it passes**

```bash
cargo test -p leanr_kernel local_context_clone_is_independent_of_its_source
```

Expected: PASS.

- [ ] **Step 5: Measure the discriminator**

Remove `Clone` from the derive, re-run the test, confirm it fails to
compile, restore. Record the outcome in the commit message.

- [ ] **Step 6: Run the kernel crate and commit**

```bash
cargo test -p leanr_kernel
mise run ci
git add crates/leanr_kernel/src/local_ctx.rs
git commit -F - <<'MSG'
mvar-lctx task 1: LocalContext derives Clone

The one kernel edit of this slice, and the reason leanr_meta cannot give
a metavariable a truthful local context today: decls/index are
module-private with no enumeration API, so no caller can copy the
ambient context. LocalDecl already derived Clone; this is a derive only,
no function body changed, no new dependency, soundness surface
unchanged. Mutation measured: dropping the derive fails to compile
local_context_clone_is_independent_of_its_source.

Claude-Session: https://claude.ai/code/session_01J5wHdBxtXr9M1ixudAhtmA
MSG
```

---

### Task 2: `LocalCtxSnapshot`, the cache, and truthful minting in `leanr_meta`

The snapshot carries BOTH halves of the ambient context — the
`LocalContext` and `MetaCtx`'s parallel `local_names` index — because
their lockstep invariant is asserted on every `lctx_checkpoint` /
`lctx_restore` / `push_local_decl` call and would fire immediately if
one were installed without the other. The cache exists so that instance
search, which mints one metavariable per candidate-telescope binder,
pays one copy per binder scope rather than one per metavariable.

**Files:**
- Create: `crates/leanr_meta/src/local_snapshot.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (`mod local_snapshot;` +
  `pub use local_snapshot::LocalCtxSnapshot;`)
- Modify: `crates/leanr_meta/src/mvar_ctx.rs` (`MVarDecl::lctx`'s type and doc)
- Modify: `crates/leanr_meta/src/metactx.rs` (the cache field; invalidation
  in `push_local_decl`, `push_let_decl`, `lctx_restore`)
- Modify: `crates/leanr_meta/src/assign.rs` (`mk_aux_mvar`)
- Modify — every remaining `MVarDecl { .. }` literal (the compiler lists
  them; the full set today):
  `crates/leanr_meta/src/infer.rs`, `src/lazy_delta.rs`, `src/metactx.rs`,
  `src/whnf.rs` (two), `src/test_support.rs`, `src/assign.rs` (the
  `#[cfg(test)]` one), `crates/leanr_meta/tests/oracle_synth.rs` (three),
  `crates/leanr_meta/tests/oracle_fast.rs`, `crates/leanr_elab/src/elab.rs`
  (Task 4 changes its VALUE; this task only makes it compile)
- Test: `crates/leanr_meta/src/assign.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `LocalContext: Clone` (Task 1).
- Produces: `pub struct LocalCtxSnapshot { lctx: LocalContext, local_names: Vec<(Option<NameId>, ExprId)> }`
  with `pub fn empty() -> Arc<LocalCtxSnapshot>`, `pub fn lctx(&self) -> &LocalContext`,
  `pub fn depth(&self) -> usize`;
  `MetaCtx::current_lctx(&mut self) -> Arc<LocalCtxSnapshot>` (`pub`);
  `MVarDecl::lctx: Arc<LocalCtxSnapshot>`.
- Consumed by: Task 3 (`with_mvar_context`), Task 4 (the elaborator's
  minting site).

- [ ] **Step 1: Write the failing test**

Append inside `assign.rs`'s `#[cfg(test)] mod tests`:

```rust
    /// A metavariable minted while a local binder is open may be
    /// assigned that binder's variable (oracle: `mkFreshExprMVarCore`
    /// mints at `(← getLCtx)`, `Meta/Basic.lean:866-867`, and
    /// `CheckAssignmentQuick.check` accepts an fvar the declaration can
    /// see, `ExprDefEq.lean:1060`). Before this slice every declaration
    /// carried an EMPTY context, so this answered `false` — the whole
    /// finding (design spec § The finding, measured).
    ///
    /// The second half is the part that must NOT regress: a variable
    /// that was NOT in scope when the metavariable was minted is still
    /// rejected. The fix makes the check truthful, not permissive.
    #[test]
    fn a_metavariable_may_be_assigned_a_variable_its_context_can_see() {
        with_n_ctx(|ctx| {
            let n_type = ctx.scratch.expr_sort(
                Some(ctx.view.store),
                ctx.scratch.level_zero(Some(ctx.view.store)).expect("level"),
            ).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let visible = ctx
                .push_local_decl(None, n_type, leanr_kernel::BinderInfo::Default)
                .expect("decl");
            // Minted with `visible` in scope.
            let (mv_in, _) = ctx.mk_aux_mvar(n_type).expect("mvar");
            assert_eq!(
                ctx.is_def_eq(mv_in, visible).expect("defeq"),
                true,
                "a metavariable must accept a variable its own context can see"
            );

            // A sibling scope: `later` did not exist when `mv_in` was minted.
            ctx.lctx_restore(cp);
            let (mv_before, _) = ctx.mk_aux_mvar(n_type).expect("mvar");
            let later = ctx
                .push_local_decl(None, n_type, leanr_kernel::BinderInfo::Default)
                .expect("decl");
            assert_eq!(
                ctx.is_def_eq(mv_before, later).expect("defeq"),
                false,
                "a metavariable must still reject a variable minted after it"
            );
            ctx.lctx_restore(cp);
        });
    }
```

`with_n_ctx` is the module's existing helper (grep `fn with_n_ctx`); its
environment declares `N.zero`/`N.succ` as `Sort 0`-typed axioms, which is
why `Sort 0` is the metavariable type here.

- [ ] **Step 2: Run it to verify it fails**

```bash
cargo test -p leanr_meta a_metavariable_may_be_assigned_a_variable_its_context_can_see
```

Expected: FAIL on the FIRST assertion — `left: false, right: true`. (The
second assertion already holds today; it is the guard against
over-correcting.)

- [ ] **Step 3: Create `local_snapshot.rs`**

```rust
//! The ambient local context as a shareable value.
//!
//! oracle: `MetavarDecl.lctx` (`MetavarContext.lean:305-311`) — "The
//! local context containing the free variables that the mvar is
//! permitted to depend upon". Lean's `LocalContext` is persistent, so
//! the oracle stores one per metavariable for free; leanr's is a
//! mutate-in-place stack, so a stored context is a copy, and this module
//! is where that copy is made and shared.
//!
//! Two halves travel together because `MetaCtx` keeps a `local_names`
//! index parallel to `lctx`'s decl list and asserts their lockstep on
//! every checkpoint, restore and push. Installing one without the other
//! trips that assertion immediately.

use std::sync::Arc;

use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::LocalContext;

/// A copy of the ambient local context plus `MetaCtx::local_names`.
///
/// Shared behind an `Arc`: every metavariable minted at one binder depth
/// points at the same snapshot, so instance search — which mints one
/// metavariable per candidate-telescope binder — pays one copy per
/// scope, not one per metavariable.
pub struct LocalCtxSnapshot {
    lctx: LocalContext,
    local_names: Vec<(Option<NameId>, ExprId)>,
}

impl LocalCtxSnapshot {
    pub(crate) fn new(lctx: LocalContext, local_names: Vec<(Option<NameId>, ExprId)>) -> Self {
        debug_assert_eq!(
            local_names.len(),
            lctx.save(),
            "local_names/lctx lockstep invariant violated in a snapshot"
        );
        LocalCtxSnapshot { lctx, local_names }
    }

    /// The empty context — what a metavariable minted outside any binder
    /// carries, and what every `#[cfg(test)]` literal that does not care
    /// about scoping uses. A fresh `Arc` each call: an empty `Vec` and an
    /// empty `HashMap` allocate nothing, so there is no singleton to
    /// justify.
    pub fn empty() -> Arc<LocalCtxSnapshot> {
        Arc::new(LocalCtxSnapshot {
            lctx: LocalContext::default(),
            local_names: Vec::new(),
        })
    }

    /// The context itself — read by `check_assignment_scope_body`'s
    /// `FVar` arm via `MVarDecl::lctx`.
    pub fn lctx(&self) -> &LocalContext {
        &self.lctx
    }

    pub fn depth(&self) -> usize {
        self.local_names.len()
    }

    pub(crate) fn parts(&self) -> (&LocalContext, &[(Option<NameId>, ExprId)]) {
        (&self.lctx, &self.local_names)
    }
}
```

Add to `crates/leanr_meta/src/lib.rs`, beside the other module lines:

```rust
mod local_snapshot;
pub use local_snapshot::LocalCtxSnapshot;
```

- [ ] **Step 4: Add the cache to `MetaCtx` and invalidate it**

In `crates/leanr_meta/src/metactx.rs`, add a field to `pub struct MetaCtx<'e>`
directly after `local_names`:

```rust
    /// Memoized `LocalCtxSnapshot` of the CURRENT `lctx`/`local_names`,
    /// dropped by every writer of either. `current_lctx` rebuilds it on
    /// demand, so N metavariables minted at one binder depth share one
    /// copy — the difference between one clone per binder scope and one
    /// per metavariable on instance search's hottest path.
    lctx_snapshot: Option<Arc<LocalCtxSnapshot>>,
```

Add `use std::sync::Arc;` and `use crate::local_snapshot::LocalCtxSnapshot;`
if absent, and `lctx_snapshot: None,` to the struct literal `MetaCtx::new`
returns.

Add the accessor beside `lctx_checkpoint`:

```rust
    /// The ambient local context as a shareable value — what a freshly
    /// minted metavariable records (oracle: `mkFreshExprMVarCore`'s
    /// `(← getLCtx)`, `Meta/Basic.lean:866-867`).
    pub fn current_lctx(&mut self) -> Arc<LocalCtxSnapshot> {
        if let Some(snap) = &self.lctx_snapshot {
            return Arc::clone(snap);
        }
        let snap = Arc::new(LocalCtxSnapshot::new(
            self.lctx.clone(),
            self.local_names.clone(),
        ));
        self.lctx_snapshot = Some(Arc::clone(&snap));
        snap
    }
```

Then add `self.lctx_snapshot = None;` as the LAST statement of
`push_local_decl` before `Ok(fvar)`, the last statement of
`push_let_decl` before `Ok(fvar)`, and the last statement of
`lctx_restore`. Those three are the only writers of `lctx`/`local_names`
that outlive a call (per `local_names`'s own doc comment); every other
`mk_local_decl` / `restore` site inside the crate brackets its own
additions and returns the context as it found it.

**The invalidation is load-bearing.** A stale snapshot would hand a
later metavariable a context that omits a binder it can genuinely see,
or includes one it cannot. Step 8's mutation measures exactly this.

- [ ] **Step 5: Change `MVarDecl::lctx` and every literal**

In `crates/leanr_meta/src/mvar_ctx.rs`, replace the field and correct
the struct's doc (its current text says there is no `Clone` derive
*because* `LocalContext` has none — that reason is gone as of Task 1,
but the field is now an `Arc`, so the doc should say the sharing is
deliberate):

```rust
/// oracle: `MetavarDecl` (`MetavarContext.lean:305-311`). `lctx` is the
/// local context the mvar was created in — part of the declaration, not
/// ambient state, because an mvar may only be assigned a term whose free
/// variables it can see (`ExprDefEq.lean:1060`).
///
/// The context is shared, not owned: every mvar minted at one binder
/// depth points at the same `LocalCtxSnapshot`.
///
/// No `Debug` derive: `LocalContext` has none.
pub struct MVarDecl {
    pub user_name: Option<NameId>,
    pub ty: ExprId,
    pub lctx: Arc<LocalCtxSnapshot>,
    pub kind: MVarKind,
}
```

Then build and fix every literal the compiler reports. The rule:

- inside a function that has a `MetaCtx` in scope and mints a real
  metavariable → `lctx: self.current_lctx()` (or `ctx.current_lctx()`);
- every `#[cfg(test)]` literal and every site with no `MetaCtx` →
  `lctx: LocalCtxSnapshot::empty()` — those metavariables model
  context-free ones and the empty context is what they carried before.

The one site that must use `current_lctx()` in this task is
`assign.rs::mk_aux_mvar`; `crates/leanr_elab/src/elab.rs`'s literal takes
`LocalCtxSnapshot::empty()` FOR NOW so the workspace compiles, and Task 4
changes it. Leave a comment there:

```rust
                // Task 4 replaces this with the ambient snapshot; an
                // empty one preserves today's behaviour exactly until
                // then.
                lctx: LocalCtxSnapshot::empty(),
```

- [ ] **Step 6: Mint ambient in `mk_aux_mvar`**

In `crates/leanr_meta/src/assign.rs::mk_aux_mvar`, replace
`lctx: LocalContext::default(),` with `lctx: self.current_lctx(),`, and
replace the paragraph of its doc comment that begins "Always mints with
an EMPTY lctx" with:

```rust
    /// Mints with the AMBIENT local context (`self.current_lctx()`), as
    /// the oracle's `mkFreshExprMVarCore` does with `(← getLCtx)`
    /// (`Meta/Basic.lean:866-867`). Before the
    /// metavariable-local-contexts slice this minted an empty context,
    /// which made every ambient free variable look out of scope to
    /// `check_assignment_scope_body` and so made a metavariable
    /// unassignable to any `fun`-bound variable.
```

`mk_aux_mvar_for`'s own guard (`lctx_len != 0`, reading
`d.lctx.save()`) becomes `d.lctx.depth() != 0`. Its meaning is
unchanged — it still refuses to rescue a metavariable whose own context
is non-empty, which is exactly the case it cannot port faithfully — but
it will now actually fire, where before it was vacuous. Keep the
behaviour and update its doc's parenthetical accordingly.

- [ ] **Step 7: Run the test and both corpora**

```bash
cargo build --workspace --all-targets
cargo test -p leanr_meta a_metavariable_may_be_assigned_a_variable_its_context_can_see
cargo test -p leanr_meta
mise run meta:fast
cargo test -p leanr_elab --test oracle_elab
```

Expected: the test PASSES (both assertions); `leanr_meta` green;
`meta:fast` green at 24 compared records; `oracle_elab` green at 107
records, byte-identical.

**If a corpus record moves**, stop and report with the record id and its
before/after. Two places are the likely cause and both are worth naming
in the report: `assign.rs`'s `args.any (mvarDecl.lctx.containsFVar)`
guard (grep `hasCtxLocals` or `args.any`), whose doc says it is
"vacuously false" today and which a truthful context can now make fire;
and `check_assignment_scope_body`'s `FVar` arm accepting an assignment it
used to reject. Neither is a licence to re-baseline — per § Risk in the
spec, a moved record means an existing agreement was accidental.

- [ ] **Step 8: Measure the discriminators**

Apply each mutation, run the named test, confirm RED, revert:

- `mk_aux_mvar` back to `LocalContext::default()` →
  `a_metavariable_may_be_assigned_a_variable_its_context_can_see` fails
  its FIRST assertion.
- delete the `self.lctx_snapshot = None;` from `push_local_decl` →
  the same test fails its first assertion (the metavariable is minted
  against a snapshot taken before the binder existed).
- delete the `self.lctx_snapshot = None;` from `lctx_restore` →
  the same test fails its SECOND assertion (the metavariable minted
  after the restore still carries the pre-restore snapshot, so the
  sibling variable looks visible).

Record the three outcomes in the commit message.

- [ ] **Step 9: Commit**

```bash
mise run ci
git add crates/leanr_meta crates/leanr_elab/src/elab.rs
git commit -F - <<'MSG'
mvar-lctx task 2: metavariables record the context they were minted in

LocalCtxSnapshot carries the ambient LocalContext together with
MetaCtx's parallel local_names index (their lockstep invariant is
asserted on every push/checkpoint/restore, so the halves cannot travel
apart), shared behind an Arc and memoized per binder scope so instance
search pays one copy per scope rather than one per metavariable.
MVarDecl::lctx becomes that snapshot and mk_aux_mvar mints the ambient
one, as mkFreshExprMVarCore does with (getLCtx). The out-of-scope check
is untouched: it starts receiving truthful input and starts answering
correctly. Both corpora byte-identical.

Mutations measured: <fill in from step 8>.

Claude-Session: https://claude.ai/code/session_01J5wHdBxtXr9M1ixudAhtmA
MSG
```

---

### Task 3: `MetaCtx::with_mvar_context`

Installing a metavariable's own context, which is what the oracle does
before touching one. Both halves are swapped together so the lockstep
invariant holds inside the closure as well as outside it.

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs` (after `current_lctx`)
- Test: `crates/leanr_meta/src/metactx.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `LocalCtxSnapshot`, `MetaCtx::current_lctx` (Task 2).
- Produces: `MetaCtx::mvar_lctx(&self, mvar_id: MVarId) -> Option<Arc<LocalCtxSnapshot>>` (`pub`);
  `MetaCtx::install_lctx(&mut self, snapshot: Arc<LocalCtxSnapshot>) -> Arc<LocalCtxSnapshot>` (`pub`, returns the snapshot it replaced);
  `MetaCtx::with_mvar_context<R>(&mut self, mvar_id: MVarId, f: impl FnOnce(&mut Self) -> R) -> R` (`pub`, built from the two above).
- Consumed by: Task 4 — the ladder's forwarder needs the two primitives
  directly, because its closure owns the whole elaborator rather than
  just `MetaCtx`.

- [ ] **Step 1: Write the failing test**

Append inside `metactx.rs`'s `#[cfg(test)] mod tests`:

```rust
    /// `with_mvar_context` installs a metavariable's own local context
    /// and restores the ambient one on the way out (oracle:
    /// `withMVarContextImp` = `withLocalContextImp mvarDecl.lctx
    /// mvarDecl.localInstances`, `Meta/Basic.lean:2043-2045`). The
    /// discriminating shape is a variable whose binder scope has CLOSED:
    /// outside the closure it does not resolve, inside it does.
    #[test]
    fn with_mvar_context_reinstalls_a_closed_binder_scope() {
        use crate::test_support::with_prelude0_ctx;
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let x = ctx
                .push_local_decl(None, sort0, leanr_kernel::BinderInfo::Default)
                .expect("decl");
            let (_, mvar_id) = ctx.mk_aux_mvar(sort0).expect("mvar");
            ctx.lctx_restore(cp);

            // The binder is gone: `x` no longer types.
            assert!(
                ctx.infer_type(x).is_err(),
                "the ambient context has dropped the binder"
            );
            // Under the metavariable's own context it does.
            let inside = ctx.with_mvar_context(mvar_id, |ctx| ctx.infer_type(x).is_ok());
            assert!(inside, "the metavariable's context still has the binder");
            // And the ambient context is restored afterwards.
            assert!(
                ctx.infer_type(x).is_err(),
                "the ambient context was restored on the way out"
            );
        });
    }
```

- [ ] **Step 2: Run it to verify it fails**

```bash
cargo test -p leanr_meta with_mvar_context_reinstalls_a_closed_binder_scope
```

Expected: a compile error — `no method named with_mvar_context`.

- [ ] **Step 3: Implement it**

In `crates/leanr_meta/src/metactx.rs`, after `current_lctx`:

```rust
    /// The local context a metavariable was minted in, if it is declared.
    pub fn mvar_lctx(&self, mvar_id: MVarId) -> Option<Arc<LocalCtxSnapshot>> {
        self.mctx.decl(mvar_id).map(|d| Arc::clone(&d.lctx))
    }

    /// Install `snapshot` as the ambient local context, returning the one
    /// it replaced. Both halves swap together, because `local_names` and
    /// `lctx` are asserted to stay in lockstep at every checkpoint,
    /// restore and push — including the ones the caller performs while
    /// the snapshot is installed. The cache is set to the installed
    /// snapshot so a metavariable minted while it is in force records the
    /// installed context without a fresh copy.
    ///
    /// Callers must pair the two calls. `with_mvar_context` is the safe
    /// wrapper and is what in-crate code should use;
    /// `install_lctx` is `pub` only because `leanr_elab`'s ladder needs
    /// the closure to own the whole elaborator, not just `MetaCtx`.
    pub fn install_lctx(&mut self, snapshot: Arc<LocalCtxSnapshot>) -> Arc<LocalCtxSnapshot> {
        let previous = self.current_lctx();
        let (lctx, names) = snapshot.parts();
        self.lctx = lctx.clone();
        self.local_names = names.to_vec();
        self.lctx_snapshot = Some(snapshot);
        previous
    }

    /// oracle: `MVarId.withContext` / `withMVarContextImp`
    /// (`Meta/Basic.lean:2043-2052`) — `withLocalContextImp
    /// mvarDecl.lctx mvarDecl.localInstances x`. Runs `f` with the
    /// metavariable's own local context installed as the ambient one,
    /// and restores the caller's on the way out.
    ///
    /// `localInstances` is NOT modelled: leanr has no local-instance
    /// concept — instances come from the environment extension — so the
    /// oracle's instance-cache flush has nothing to flush. SEAM, owner:
    /// the slice that adds local instances.
    ///
    /// Plain save/run/restore with no drop guard, the same posture (and
    /// the same justification) as `with_transparency` and
    /// `with_assignable_synthetic_opaque`: every caller is `Result`-based
    /// and catches nothing, so an unwinding caller cannot observe the
    /// un-restored context.
    ///
    /// An UNDECLARED metavariable leaves the ambient context alone and
    /// runs `f` as-is: the oracle's `getDecl` would throw, but every
    /// leanr caller reaches this with an id it has just read a
    /// declaration for, and inventing an error variant for an
    /// unreachable case is surface without a producer.
    pub fn with_mvar_context<R>(
        &mut self,
        mvar_id: MVarId,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let Some(snapshot) = self.mvar_lctx(mvar_id) else {
            return f(self);
        };
        let saved = self.install_lctx(snapshot);
        let out = f(self);
        self.install_lctx(saved);
        out
    }
```

`install_lctx` returns the snapshot it replaced, so the restore is the
same call with the saved value — one implementation of the swap, used
by both this wrapper and (in Task 4) `leanr_elab`'s.

- [ ] **Step 4: Run it to verify it passes**

```bash
cargo test -p leanr_meta with_mvar_context_reinstalls_a_closed_binder_scope
```

Expected: PASS.

- [ ] **Step 5: Measure the discriminators**

Apply each mutation, run the test, confirm RED, revert:

- drop `install_lctx`'s `self.local_names = names.to_vec();` (swap only
  `lctx`) → the test fails on the `local_names/lctx lockstep invariant
  violated` debug assertion.
- drop the second `self.install_lctx(saved);` after `f` → the test's
  THIRD assertion fails (the ambient context was not restored).
- drop `install_lctx`'s `self.lctx_snapshot = Some(snapshot);` → the test
  still passes, but a metavariable minted inside the closure would record
  the wrong context; add a temporary assertion inside the closure that
  `ctx.current_lctx().depth()` equals 1 and confirm it fails, then revert
  both the mutation and the temporary assertion.

- [ ] **Step 6: Run the crate and commit**

```bash
cargo test -p leanr_meta
mise run meta:fast
mise run ci
git add crates/leanr_meta/src/metactx.rs
git commit -F - <<'MSG'
mvar-lctx task 3: MetaCtx::with_mvar_context

Meta/Basic.lean:2043-2052 — run with a metavariable's own local context
installed, restore the caller's on the way out. Both halves of the
ambient context swap together so the local_names/lctx lockstep holds
inside the closure too, and the snapshot cache is set on entry and
cleared on exit. localInstances is a named seam: leanr has no
local-instance concept.

Mutations measured: <fill in from step 5>.

Claude-Session: https://claude.ai/code/session_01J5wHdBxtXr9M1ixudAhtmA
MSG
```

---

### Task 4: the elaborator mints ambient and resumes under context

The elaborator's own minting site, and the ladder wrapper that makes
postponement survive a closed binder scope.

**Files:**
- Modify: `crates/leanr_elab/src/elab.rs` (`mk_fresh_expr_mvar_of_kind`)
- Modify: `crates/leanr_elab/src/synthetic/ladder.rs` (`synthesize_synthetic_mvar`)
- Test: `crates/leanr_elab/tests/synthetic_smoke.rs`

**Interfaces:**
- Consumes: `MetaCtx::current_lctx` (Task 2), `MetaCtx::with_mvar_context` (Task 3).
- Produces: no new public surface — `mk_fresh_expr_mvar_of_kind` and
  `synthesize_synthetic_mvar` keep their signatures.

- [ ] **Step 1: Write the failing test**

Append to `crates/leanr_elab/tests/synthetic_smoke.rs`:

```rust
/// A synthetic metavariable registered inside a binder is resumed by the
/// fixpoint AFTER that binder's scope has closed, so the ladder must run
/// each arm under the metavariable's own context — the oracle wraps
/// every arm in `mvarId.withContext` (`SyntheticMVars.lean:32-36`, and
/// the `.coe` arm's own at `:545`). Before the
/// metavariable-local-contexts slice the metavariable's own TYPE was
/// unresolvable by resume time and the arm failed with "unknown free
/// variable".
///
/// The discriminating shape needs a metavariable whose type MENTIONS the
/// binder, so the binder must itself be a type variable: `a : Type` is
/// obtained by inferring the type of a fixture constant, and the
/// metavariable is then `?m : a`. Kill: drop the
/// `with_mvar_local_context` wrapper in `synthesize_synthetic_mvar` and
/// this errors instead of answering.
#[test]
fn a_synthetic_mvar_resumes_under_its_own_local_context() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        let nat = support::fixture_const(app, "Nat");
        // `Nat : Type`, so inferring gives the sort to bind `a` at.
        let type_sort = app.elab.mctx.infer_type(nat).expect("Type");
        let cp = app.elab.mctx.lctx_checkpoint();
        let a = app
            .elab
            .mctx
            .push_local_decl(None, type_sort, leanr_kernel::BinderInfo::Default)
            .expect("decl");
        // `?m : a` — its type mentions the binder, so resolving it at all
        // requires `a` to be back in scope.
        let (_, mvar_id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(a, leanr_meta::MVarKind::Natural)
            .expect("mvar");
        app.elab.register_synthetic_mvar(
            support::any_syn_elem(),
            mvar_id,
            leanr_elab::synthetic::SyntheticMVarKind::TypeClass,
        );
        // The binder closes before the fixpoint runs.
        app.elab.mctx.lctx_restore(cp);

        let out = app.elab.synthesize_synthetic_mvars_no_postponing(&kinds);
        // The arm may legitimately fail to find an instance for `a`; what
        // it must NOT do is fail to resolve the metavariable's own type.
        if let Err(e) = &out {
            let msg = format!("{e:?}");
            assert!(
                !msg.contains("unknown free variable"),
                "resumed outside its own local context: {msg}"
            );
        }
    });
}
```

If `with_app_harness`'s closure field is not `app.elab`, or
`synthesize_synthetic_mvars_no_postponing` has a different name, use what
the file's existing tests use (grep `synthesize_synthetic_mvars` in that
file). The assertion — no `unknown free variable` — is the point.

- [ ] **Step 2: Run it to verify it fails**

```bash
cargo test -p leanr_elab --test synthetic_smoke a_synthetic_mvar_resumes_under_its_own_local_context
```

Expected: FAIL with `resumed outside its own local context: … unknown free variable …`.

- [ ] **Step 3: Mint ambient in the elaborator**

In `crates/leanr_elab/src/elab.rs::mk_fresh_expr_mvar_of_kind`, replace
the placeholder Task 2 left:

```rust
                lctx: self.mctx.current_lctx(),
```

and add to the function's doc:

```rust
    /// Mints with the AMBIENT local context (oracle:
    /// `mkFreshExprMVarCore`'s `(← getLCtx)`, `Meta/Basic.lean:866-867`),
    /// so the metavariable may be assigned a term mentioning binders that
    /// are in scope at the point it is created.
```

Note the borrow: `self.mctx.current_lctx()` takes `&mut self.mctx`, so
compute it into a local BEFORE the `self.mctx.mctx_mut().declare(..)`
call rather than inside the `MVarDecl` literal if the borrow checker
objects.

- [ ] **Step 4: Wrap the ladder's arms**

In `crates/leanr_elab/src/synthetic/ladder.rs`, add the forwarder above
`synthesize_synthetic_mvar`. `MetaCtx::with_mvar_context` (Task 3) takes a
closure over `MetaCtx`, but the arms need the whole elaborator, so this
one drives the same swap through Task 3's two `pub` primitives:

```rust
    /// `MetaCtx::with_mvar_context` lifted to `TermElabM`: the arms need
    /// `&mut TermElabM`, not `&mut MetaCtx`, so the swap runs around the
    /// closure instead of inside it. Same primitives, same pairing —
    /// `install_lctx` returns the snapshot it replaced, and putting that
    /// one back is the restore.
    fn with_mvar_local_context<R>(
        &mut self,
        mvar_id: MVarId,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let Some(snapshot) = self.mctx.mvar_lctx(mvar_id) else {
            return f(self);
        };
        let saved = self.mctx.install_lctx(snapshot);
        let out = f(self);
        self.mctx.install_lctx(saved);
        out
    }
```

Then wrap the existing `match decl.kind { .. }` with it, leaving every
arm's body untouched:

```rust
        let Some(decl) = self.synthetic_mvar_decl(mvar_id).cloned() else {
            return Ok(true);
        };
        // oracle: every arm runs under `mvarId.withContext` — the driver
        // `resumePostponed` (`SyntheticMVars.lean:32-36`) and the `.coe`
        // arm's own (`:545`). A synthetic metavariable is resumed after
        // the binder it was registered under has closed, so without this
        // its type and payload no longer resolve.
        self.with_mvar_local_context(mvar_id, |elab| match decl.kind {
            // ... every existing arm, unchanged, with `self` renamed to
            // `elab` inside the closure ...
        })
```

`decl` is cloned out before the closure, so the borrow is clean. The
`Postponed` arm's `ref ctx` binding stays as it is.

- [ ] **Step 5: Run the test, the crate, and both corpora**

```bash
cargo test -p leanr_elab --test synthetic_smoke a_synthetic_mvar_resumes_under_its_own_local_context
cargo test -p leanr_elab
cargo test -p leanr_meta
mise run meta:fast
```

Expected: the new test PASSES; every pre-existing test green;
`oracle_elab` at 107 records and `meta:fast` at 24 compared records,
byte-identical. A moved record is a stop-and-report (Task 2 step 7's
rule applies unchanged).

- [ ] **Step 6: Measure the discriminators**

Apply each mutation, run the named test, confirm RED, revert:

- remove the `with_mvar_local_context` wrapper from
  `synthesize_synthetic_mvar` →
  `a_synthetic_mvar_resumes_under_its_own_local_context` fails with
  `unknown free variable`.
- revert `mk_fresh_expr_mvar_of_kind` to `LocalCtxSnapshot::empty()` →
  the same test fails (the metavariable carries no binder to reinstall).

- [ ] **Step 7: Commit**

```bash
mise run ci
git add crates/leanr_elab crates/leanr_meta/src/metactx.rs
git commit -F - <<'MSG'
mvar-lctx task 4: the elaborator mints ambient and resumes under context

mk_fresh_expr_mvar_of_kind records the ambient context, as
mkFreshExprMVarCore does with (getLCtx); synthesize_synthetic_mvar runs
every arm under the metavariable's own context, as the oracle's driver
and its .coe arm both do (SyntheticMVars.lean:32-36, :545). A synthetic
metavariable registered inside a binder now resumes after that binder
closes instead of failing with "unknown free variable". Both corpora
byte-identical.

Mutations measured: <fill in from step 6>.

Claude-Session: https://claude.ai/code/session_01J5wHdBxtXr9M1ixudAhtmA
MSG
```

---

### Task 5: the finding's own measurements become permanent tests

The probes that diagnosed this slice are throwaway diagnostics until
they live in the suite. Two of the three already have permanent homes
(Task 2 pins the assignment itself, Task 3 the closed binder scope);
this task lands the remaining one — coercion of a `fun`-bound value, the
shape that blocked four of P4's six records — together with the
regression guard for the two coercion routes that were never blocked.

**Files:**
- Modify: `crates/leanr_meta/src/coe.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: everything above; `MetaCtx::coerce_simple` (shipped in #37).
- Produces: nothing new.

- [ ] **Step 1: Write the failing-until-now test**

Append inside `coe.rs`'s `#[cfg(test)] mod tests`:

```rust
    /// Coercing a `fun`-bound VALUE, not a constant — the shape that
    /// blocked M4b-3 P4's elaborator tier (design spec § The finding,
    /// measured). `CoeT α a β` takes the coerced value as a class
    /// parameter, so the search must assign a candidate's telescope
    /// metavariable to a local variable; before the
    /// metavariable-local-contexts slice that assignment was rejected as
    /// out of scope and this answered `.none`.
    ///
    /// The expansion is pinned, not just the verdict: a `Some` still
    /// carrying `CoeT.coe` or a projection node would mean the search
    /// succeeded but `expand_coe` did not run.
    #[test]
    fn coerce_simple_expands_a_locally_bound_value() {
        with_synth0_ctx(|ctx| {
            let n_ty = const_named(ctx, "N");
            let m = const_named(ctx, "M");
            let of_n = const_dotted(ctx, "M", "ofN");
            let cp = ctx.lctx_checkpoint();
            let x = ctx
                .push_local_decl(None, n_ty, leanr_kernel::BinderInfo::Default)
                .expect("decl");
            let want = app(ctx, of_n, &[x]);
            let got = ctx.coerce_simple(x, m).expect("coerce");
            ctx.lctx_restore(cp);
            match got {
                LOption::Some(got) => {
                    let rendered = render_expr(ctx, got);
                    assert_eq!(rendered, render_expr(ctx, want));
                    assert!(!rendered.contains("CoeT"), "unexpanded: {rendered}");
                }
                other => panic!("expected Some, got {other:?}"),
            }
        });
    }
```


And, directly after it, the guard for the routes that already worked —
without it, a later change could "fix" the `CoeT` route by loosening the
scope check and silently break the two that never needed it:

```rust
    /// `CoeFun` and `CoeSort` coercions of a `fun`-bound value worked
    /// BEFORE the metavariable-local-contexts slice and must keep
    /// working: their class parameters are types only
    /// (`CoeFun FnN ?γ`, `CoeSort SortN ?β`), so their goals never
    /// mention the local variable and the out-of-scope rejection never
    /// applied to them. This is the measurement that scoped the finding
    /// to `CoeT` alone (design spec § The finding, measured), kept as a
    /// regression guard.
    #[test]
    fn coerce_to_function_and_sort_still_accept_a_locally_bound_value() {
        with_synth0_ctx(|ctx| {
            let fnn = const_named(ctx, "FnN");
            let sortn = const_named(ctx, "SortN");
            let cp = ctx.lctx_checkpoint();
            let g = ctx
                .push_local_decl(None, fnn, leanr_kernel::BinderInfo::Default)
                .expect("decl");
            let s = ctx
                .push_local_decl(None, sortn, leanr_kernel::BinderInfo::Default)
                .expect("decl");
            let f_case = ctx.coerce_to_function(g).expect("coerce");
            let s_case = ctx.coerce_to_sort(s).expect("coerce");
            ctx.lctx_restore(cp);
            assert!(f_case.is_some(), "CoeFun on a local value");
            assert!(s_case.is_some(), "CoeSort on a local value");
        });
    }
```

- [ ] **Step 2: Run them**

```bash
cargo test -p leanr_meta coerce_simple_expands_a_locally_bound_value
cargo test -p leanr_meta coerce_to_function_and_sort_still_accept_a_locally_bound_value
```

Expected: both PASS. The first is what Tasks 1–4 make pass; the
second passed before this slice too and must still. If the first fails with
`None`, the minting change did not reach the instance-search path; check
that `forall_meta_telescope_reducing` goes through `mk_aux_mvar` (grep
`mk_aux_mvar` in `synth.rs`) and that Task 2 step 4's invalidation is
present.

- [ ] **Step 3: Measure the discriminator**

Revert `mk_aux_mvar` to `LocalContext::default()`, run the test, confirm
it fails with `expected Some, got None` — the exact symptom this slice
exists to fix — and revert the mutation.

- [ ] **Step 4: Full verification and commit**

```bash
cargo test --workspace
mise run meta:fast
mise run ci
git add crates/leanr_meta/src/coe.rs
git commit -F - <<'MSG'
mvar-lctx task 5: coercion of a fun-bound value, as a permanent test

The measurement that diagnosed this slice becomes a test: coerce_simple
on a locally bound value answers Some and expands to the instance
function, where before the metavariable-local-contexts work it answered
None because the candidate telescope's metavariable could not be
assigned a local variable. Mutation measured: reverting mk_aux_mvar to
an empty context returns None again.

Claude-Session: https://claude.ai/code/session_01J5wHdBxtXr9M1ixudAhtmA
MSG
```

Then open the PR per the repository's standing workflow (push, PR titled
`Metavariable local contexts`, merge on green CI, verify, delete the
branch).

---

## Verification summary

After Task 5, these must all hold:

- `mise run ci` green, `cargo test --workspace` green.
- `mise run meta:fast` at 24 compared synthesis records and
  `cargo test -p leanr_elab --test oracle_elab` at 107 elaboration
  records, every one byte-identical to what #37 merged.
- `leanr_kernel`'s diff against `origin/main` is exactly one derive line
  plus its doc comment.
- A metavariable accepts a variable its own context can see and still
  rejects one minted after it.
- A synthetic metavariable resumed after its binder scope closes
  resolves its payload.
- `coerce_simple` on a `fun`-bound value expands to the instance
  function with no `CoeT.coe` and no projection node.
- No `.lean` fixture and no `.olean` changed.

## What this plan deliberately does NOT do

- **No `localInstances`.** leanr has no local-instance concept; the
  oracle's instance-cache flush in `withMVarContextImp` has nothing to
  flush. Named seam in `with_mvar_context`'s doc.
- **No metavariable-depth model.** `MetavarDecl.depth`
  (`MetavarContext.lean:312-319`) stays unmodelled, as does
  `isSubPrefixOf` in the scope check's `MVar` arm — both keep their
  existing owners.
- **No `ctxApprox` slow path.** `check_assignment_scope_body`'s doc
  already explains why the rescue cannot be grafted onto a bool-only
  predicate; nothing here changes that.
- **No change to the out-of-scope check itself**, and no fixture
  regeneration.
- **No P4 work.** P4's elaborator tier resumes at its own plan's task 7,
  from `m4b3-p4-task7-wip`, after this slice lands.
