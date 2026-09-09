# `MkBinding.elimMVarDeps` — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Port the oracle's `MkBinding.elimMVarDeps` into `leanr_meta` and
run it inside `MetaCtx::mk_binding`, so a metavariable that survives past
a binder is replaced by an auxiliary metavariable applied to that binder's
free variables — and therefore abstracts like any other argument instead
of leaving an unabstracted `fvar` where the oracle emits `bvar 0`.

**Architecture:** A new `crates/leanr_meta/src/mk_binding.rs` holds the
whole transcription as one `impl<'e> MetaCtx<'e>` block — the house
pattern. `MetaCtx::mk_binding` keeps its existing peel-one-fvar-at-a-time
abstraction loop and gains `elim_mvar_deps` calls at the oracle's two
insertion points. The `syntheticOpaque` branch needs a delayed-assignment
channel, which `leanr_meta` does not have at all: `MetavarContext` gains
one, `instantiate_mvars` gains its arm, and `whnf.rs`'s hardcoded
`whnf_delayed_assigned` stub becomes the real thing. One additive,
TCB-neutral kernel edit — `LocalContext::erase` — because
`reduceLocalContext` is repeated `erase` and `mk_local_decl` mints a
*fresh* fvar id, so a filtered context cannot be rebuilt from the public
surface.

**Tech Stack:** Rust (workspace crates `leanr_kernel`, `leanr_meta`,
`leanr_elab`), `mise` task runner, the committed differential corpora,
the pinned Lean toolchain as oracle.

**Spec:** `docs/superpowers/specs/2026-09-09-elim-mvar-deps-design.md` —
executors read it first. It is argued from
`docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md`
§ Amendment 6, which sequenced this slice ahead of M4b-3 P5.

## Global Constraints

Copied from the spec and `AGENTS.md`. Every task's requirements
implicitly include this section.

- **Pinned oracle: `leanprover/lean4:v4.33.0-rc1`** (`lean-toolchain`),
  sources at
  `/home/dev/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`.
  **Never bump the pin.** Every `MetavarContext.lean` line number in this
  plan is against that file.
- **The kernel edit is exactly one function** — `LocalContext::erase`
  (Task 2). No other kernel file, no other kernel function body, no new
  kernel dependency. If a task seems to need a second kernel change,
  stop and report rather than making it.
- **`leanr_elab/src` is not touched.** `mk_forall` / `mk_lambda` keep
  their signatures; the fix lands underneath them. The elab-side work is
  test and fixture only (Tasks 11–12). If a task appears to need an
  `leanr_elab/src` change, stop and report.
- **The committed corpora stay byte-identical**: 107 records in
  `tests/fixtures/elab/elab-queries.jsonl`, 24 compared records in
  `tests/fixtures/meta/synth-queries.jsonl`, plus the defeq/whnf/infer
  records `oracle_fast` gates. Task 11 adds records; **no task ever
  re-baselines an existing one.** A record that moves means an existing
  agreement with the oracle was accidental — stop, record the exact
  before/after, and report.
- **Every discriminator is measured.** Each task below names the mutation
  its test is supposed to kill. That is a *hypothesis*, not a verified
  fact: apply the mutation, watch the test go red, revert. If the test
  survives, strengthen it before closing the task. This repo has a
  documented history of plan briefs naming kills their tests do not
  deliver — four of five tasks in one recent slice.
- **`mise run ci` gates `cargo fmt --check` and clippy**, not only tests.
  Run it before every commit; `mise run test` alone does not cover it.
- **Dead code between Tasks 2 and 10.** Everything built in Tasks 2–9 has
  no production caller until Task 10 wires it in. Mark each new item
  `#[allow(dead_code)]` when you add it and **remove those attributes in
  Task 10**; clippy's `dead_code` lint will otherwise fail `mise run ci`
  mid-plan. Task 10 has an explicit step for the removal.
- **No Mathlib sweep.** This slice touches no parser. `mise run
  parse:mathlib:fast` is the only Mathlib-adjacent gate, and only in
  Task 10.

---

## File Structure

**Created:**

- `crates/leanr_meta/src/mk_binding.rs` — the entire `MkBinding`
  transcription plus its `#[cfg(test)] mod tests`. One responsibility:
  eliminate metavariable dependencies on a set of free variables before
  abstraction. Separated from `metactx.rs` because that file is already
  1753 lines and is the crate's *accessor surface*; a 400-line fidelity
  transcription against `MetavarContext.lean:938-1349` belongs where a
  reviewer can diff it in one pass.
- `docs/superpowers/specs/2026-09-09-elim-mvar-deps-findings.md` —
  Task 1's measurement. Sibling convention:
  `2026-07-09-nat-brecon-reduction-divergence-findings.md`.

**Modified:**

- `crates/leanr_kernel/src/local_ctx.rs` — `erase` (Task 2).
- `crates/leanr_meta/src/local_snapshot.rs` — `entries`, `reduced`
  (Task 2).
- `crates/leanr_meta/src/lib.rs` — `mod mk_binding;` and the
  `DelayedMVarAssignment` re-export (Tasks 2, 5).
- `crates/leanr_meta/src/mvar_ctx.rs` — the delayed channel (Task 5).
- `crates/leanr_meta/src/assign.rs` — `get_delayed_mvar_root`, the
  `instantiate_mvars_body` delayed arm, `mk_aux_mvar_at` (Tasks 6, 7).
- `crates/leanr_meta/src/whnf.rs` — the real `whnf_delayed_assigned`
  (Task 6).
- `crates/leanr_meta/src/metactx.rs` — the two `elim_mvar_deps`
  insertions and the `# UNMODELLED` retirement (Tasks 10, 12).
- `tests/fixtures/elab/Elab0.lean`, `tests/fixtures/elab/dump_elab.lean`
  — new declarations and records (Task 11).
- `crates/leanr_elab/tests/seam_audit.rs`,
  `crates/leanr_elab/tests/oracle_elab.rs` — retirement (Tasks 11, 12).

---

## Orientation for the implementer

You are porting one Lean function and its helpers. Read these first:

- **The spec**, all of it. § The entry point and § Let-declarations are
  the two places where leanr deliberately differs from the oracle.
- **`MetavarContext.lean:938-1349`** (namespace `MkBinding`) and
  **`:660-725`** (namespace `DependsOn`). Open the file; the plan quotes
  it but the surrounding comments matter, especially the "Gruesome
  details" block at the top of the file.
- **`crates/leanr_meta/src/metactx.rs:710-800`** — `mk_binding`, its
  `# UNMODELLED` heading, and its existing let-decl refusal, which is the
  model for the refusal this slice adds.
- **`crates/leanr_elab/tests/seam_audit.rs:690-760`** — the executable
  characterization of the bug, including the oracle's pinned answer.

**Vocabulary.** `xs` is the telescope being abstracted. `to_revert` is
the subset of `xs` that is actually in a given metavariable's own
declared local context, closed under forward dependencies. "The original"
is `?m`, the metavariable found in the term; "the auxiliary" or "the new
one" is `?new`, minted at the reduced context.

**Test idioms** — all in `crates/leanr_meta/src/test_support.rs`:

```rust
use crate::test_support::{with_ctx, with_prelude0_ctx, fresh_fvar, fresh_mvar, fresh_mvar_of_kind};
```

`with_ctx` gives an empty environment (no constants); `with_prelude0_ctx`
replays `Prelude0.olean` so `const_named(ctx, "Nat")` works. A `Sort 0`
without any environment is:

```rust
let base = Some(ctx.view.store);
let zero = ctx.scratch.level_zero(base).expect("level");
let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
```

`fresh_fvar(ctx, ty, "x")` pushes a cdecl through `push_local_decl`, so
`local_names` and the snapshot cache stay in lockstep. Bracket binder
scopes with `ctx.lctx_checkpoint()` / `ctx.lctx_restore(cp)`.

---

### Task 1: Blast-radius probe (measurement; gates every later task)

`elim_mvar`'s **plain-assign** branch fires whenever a `fun` body still
holds an unassigned instance metavariable at `mk_lambda` time. Those
records currently come out right *by accident* — a synthesized instance
is a closed term, so the missing abstraction is invisible — and after
Task 10 they route through `?m := ?new ys` plus the ladder's
`is_assigned` reconciliation, a path that has never run. This task
measures that population **before** any of it is built.

Nothing here ships. The deliverable is a committed findings document.

**Files:**
- Temporarily modify: `crates/leanr_meta/src/metactx.rs:737` (reverted in
  Step 5)
- Create: `docs/superpowers/specs/2026-09-09-elim-mvar-deps-findings.md`

**Interfaces:**
- Consumes: nothing.
- Produces: the findings document. Task 10's neutrality gate reads its
  "affected records" list to distinguish an expected change from a
  regression.

- [ ] **Step 1: Add the temporary probe to `mk_binding`**

Insert at the very top of `MetaCtx::mk_binding`'s body, before
`let mut r = body;`:

```rust
// TEMPORARY probe — plan task 1. Reverted at task 1 step 5.
// Does `body` carry an unassigned mvar whose OWN declared local
// context contains one of the fvars we are about to abstract?
{
    let mut hits: Vec<String> = Vec::new();
    let mut stack = vec![body];
    while let Some(cur) = stack.pop() {
        match self.node(cur) {
            Node::MVar { id: Some(n) } => {
                let mid = crate::MVarId(n);
                if self.mctx.assignment(mid).is_none() {
                    if let Some(decl) = self.mctx.decl(mid) {
                        let kind = decl.kind;
                        let lctx = std::sync::Arc::clone(&decl.lctx);
                        let in_scope = fvars.iter().any(|x| match self.node(*x) {
                            Node::FVar { id: Some(fid) } => lctx.lctx().get(fid).is_some(),
                            _ => false,
                        });
                        if in_scope {
                            hits.push(format!("{mid:?} kind={kind:?}"));
                        }
                    }
                }
            }
            Node::App { f, arg } => {
                stack.push(f);
                stack.push(arg);
            }
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => {
                stack.push(binder_type);
                stack.push(body);
            }
            Node::LetE {
                ty, value, body, ..
            } => {
                stack.push(ty);
                stack.push(value);
                stack.push(body);
            }
            Node::MData { expr, .. } => stack.push(expr),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                stack.push(structure)
            }
            _ => {}
        }
    }
    if !hits.is_empty() {
        eprintln!("LEANR_PROBE is_lambda={is_lambda} hits={hits:?}");
    }
}
```

If the borrow checker objects to reading `self.mctx.decl(mid)` while
calling `self.node(*x)`, the `kind` copy and `Arc::clone` above already
end the `decl` borrow before the closure — keep that shape.

- [ ] **Step 2: Run the elaboration corpus under the probe**

```bash
cargo test -p leanr_elab --test oracle_elab -- --nocapture 2>&1 | grep LEANR_PROBE | sort | uniq -c | sort -rn
```

Expected: a non-empty list. Every line is a `mk_binding` call whose body
holds an in-scope unassigned metavariable — i.e. a call whose behavior
Task 10 changes.

- [ ] **Step 3: Attribute the hits to records**

Re-run with the record id in view so you can name the affected records,
not just count calls:

```bash
cargo test -p leanr_elab --test oracle_elab -- --nocapture 2>&1 \
  | grep -E 'LEANR_PROBE|^replaying ' | head -100
```

If `oracle_elab.rs` does not already print the record id per query, add a
temporary `eprintln!("LEANR_PROBE_ID {id}");` immediately after `let src
= q["src"]...` in `crates/leanr_elab/tests/oracle_elab.rs` — it is
reverted with everything else in Step 5.

- [ ] **Step 4: Run the meta corpora under the probe**

```bash
cargo test -p leanr_meta --test oracle_fast -- --nocapture 2>&1 | grep -c LEANR_PROBE
cargo test -p leanr_meta --test oracle_synth -- --nocapture 2>&1 | grep -c LEANR_PROBE
cargo test -p leanr_meta --lib -- --nocapture 2>&1 | grep -c LEANR_PROBE
```

- [ ] **Step 5: Write the findings document**

Create `docs/superpowers/specs/2026-09-09-elim-mvar-deps-findings.md`
with this structure, filled in from Steps 2–4 — **actual numbers and
actual record ids, no estimates**:

```markdown
# `elimMVarDeps` blast radius — findings

Measured at <commit sha> with the temporary `mk_binding` probe described
in the implementation plan's Task 1. The probe reports every
`mk_binding` call whose body carries an unassigned metavariable whose own
declared local context contains a telescope free variable — exactly the
population whose behavior `elim_mvar_deps` changes.

## Totals

| Corpus | `mk_binding` calls hit | distinct records affected |
| --- | --- | --- |
| `oracle_elab` (107 records) | N | M |
| `oracle_synth` (24 compared) | N | M |
| `oracle_fast` | N | M |
| `leanr_meta` unit tests | N | — |

## Affected records

<one line per record id, with the metavariable kind(s) the probe saw>

## Kinds observed

| `MVarKind` | count | branch it will take in `elim_mvar` |
| --- | --- | --- |
| `Natural` | N | plain assign |
| `Synthetic` | N | plain assign |
| `SyntheticOpaque` | N | delayed |

## What this means for Task 10

<Two or three sentences. If the affected-record list is empty, say so
explicitly — that makes Task 10's byte-identical gate a formality. If it
is non-empty, these are the records to watch, and a move in any of them
is the first thing to investigate.>
```

- [ ] **Step 6: Revert every probe edit**

```bash
git checkout -- crates/leanr_meta/src/metactx.rs crates/leanr_elab/tests/oracle_elab.rs
git status --short
```

Expected: only the new findings document is modified/untracked. **The
probe must not be committed.**

- [ ] **Step 7: Verify the tree is clean and gates pass**

```bash
mise run ci
```

Expected: PASS, and identical to what it was before this task — nothing
in `crates/` changed.

- [ ] **Step 8: Commit**

```bash
git add docs/superpowers/specs/2026-09-09-elim-mvar-deps-findings.md
git commit -m "elimMVarDeps task 1: blast-radius measurement

The plain-assign branch of elimMVar fires on existing records that hold
a pending instance mvar at mk_lambda time. Measured before building the
port, so task 10's byte-identical gate has a known expected population
rather than discovering it as a red corpus."
```

---

### Task 2: `LocalContext::erase` and the reduced snapshot

`reduceLocalContext` (`MetavarContext.lean:1065-1067`) is literally
`toRevert.foldr (fun x lctx => lctx.erase x.fvarId!)`. `LocalContext` has
no `erase`, and `mk_local_decl` (`local_ctx.rs:110`) mints a *fresh* fvar
id, so a filtered context cannot be rebuilt from the public surface.

**Files:**
- Modify: `crates/leanr_kernel/src/local_ctx.rs` (after `restore`, `:200`)
- Modify: `crates/leanr_meta/src/local_snapshot.rs`
- Test: `crates/leanr_kernel/src/local_ctx.rs` (`#[cfg(test)] mod tests`),
  `crates/leanr_meta/src/local_snapshot.rs` (new `#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: nothing.
- Produces:
  - `LocalContext::erase(&mut self, fvar_id: NameId)` — public, kernel.
  - `LocalCtxSnapshot::entries(&self) -> &[(Option<NameId>, ExprId)]` —
    `pub(crate)`, declaration order.
  - `LocalCtxSnapshot::reduced(&self, to_remove: &[(ExprId, NameId)]) ->
    LocalCtxSnapshot` — `pub(crate)`.

- [ ] **Step 1: Write the failing kernel test**

Append to `crates/leanr_kernel/src/local_ctx.rs`'s `mod tests`:

```rust
#[test]
fn erase_removes_one_decl_and_keeps_the_rest_addressable() {
    let mut st = Store::scratch();
    let mut gen = FVarIdGen::default();
    let mut lctx = LocalContext::default();
    let zero = st.level_zero(None).expect("level");
    let sort0 = st.expr_sort(None, zero).expect("Sort 0");

    let a = lctx
        .mk_local_decl(&mut st, None, &mut gen, None, sort0, BinderInfo::Default)
        .expect("a");
    let b = lctx
        .mk_local_decl(&mut st, None, &mut gen, None, sort0, BinderInfo::Default)
        .expect("b");
    let c = lctx
        .mk_local_decl(&mut st, None, &mut gen, None, sort0, BinderInfo::Default)
        .expect("c");

    let id_of = |st: &mut Store, e| match st.expr_node(None, e) {
        Node::FVar { id: Some(id) } => id,
        other => panic!("expected fvar, got {other:?}"),
    };
    let (ia, ib, ic) = (id_of(&mut st, a), id_of(&mut st, b), id_of(&mut st, c));

    lctx.erase(ib);

    assert_eq!(lctx.save(), 2, "one decl removed");
    assert!(lctx.get(ia).is_some(), "the decl before the erased one survives");
    assert!(lctx.get(ib).is_none(), "the erased decl is gone");
    assert!(
        lctx.get(ic).is_some(),
        "the decl AFTER the erased one is still addressable — this is the \
         index-shift the naive `decls.remove(pos)` without reindexing breaks"
    );
}
```

- [ ] **Step 2: Run it and verify it fails**

Run: `cargo test -p leanr_kernel local_ctx::tests::erase_removes_one_decl -- --exact`
Expected: FAIL — `no method named 'erase' found`.

- [ ] **Step 3: Implement `erase`**

Insert into `impl LocalContext` immediately after `restore`:

```rust
/// oracle: `LocalContext.erase` (`local_ctx.h`), the primitive
/// `MetavarContext.lean:1065-1067`'s `reduceLocalContext` folds over
/// when it builds an auxiliary metavariable's restricted context.
///
/// Removing from the middle of `decls` shifts every later decl's
/// position, so `index` must be repaired — the same bookkeeping
/// `restore` (above) does for the truncating case. Erasing an id that
/// is not present is a no-op, matching the oracle: `erase` on a
/// `PersistentHashMap` key that is absent returns the map unchanged.
///
/// Additive and TCB-neutral: the type checker gains no caller, no
/// existing function body changes, and no new dependency is
/// introduced. `leanr_meta` cannot express a restricted context
/// otherwise — `decls`/`index` are module-private and
/// `mk_local_decl` mints a FRESH fvar id, so a filtered context
/// cannot be rebuilt from the public surface.
pub fn erase(&mut self, fvar_id: NameId) {
    let Some(pos) = self.index.remove(&fvar_id) else {
        return;
    };
    self.decls.remove(pos);
    for i in self.index.values_mut() {
        if *i > pos {
            *i -= 1;
        }
    }
}
```

- [ ] **Step 4: Run the kernel test and verify it passes**

Run: `cargo test -p leanr_kernel local_ctx::tests::erase_removes_one_decl -- --exact`
Expected: PASS.

- [ ] **Step 5: Measure the discriminator**

Delete the `for i in self.index.values_mut()` reindexing loop. Re-run
Step 4. Expected: FAIL on the third assertion (`c` is no longer
addressable). **Revert the mutation.** If it passes, the test does not
discriminate — strengthen it (add a fourth decl, assert `get(ic)`'s decl
identity, not just presence) before continuing.

- [ ] **Step 6: Write the failing snapshot test**

Create a `#[cfg(test)] mod tests` at the bottom of
`crates/leanr_meta/src/local_snapshot.rs`:

```rust
#[cfg(test)]
mod tests {
    use crate::test_support::{fresh_fvar, with_ctx};
    use leanr_kernel::bank::terms::Node;

    /// TDD RED/GREEN for plan task 2. `reduced` must drop the named
    /// fvars from BOTH halves — the `LocalContext` and the parallel
    /// `local_names` index — because `LocalCtxSnapshot::new`'s
    /// `debug_assert` requires them to stay in lockstep, and because
    /// `check_assignment_scope_body` reads `lctx()` while
    /// `lctx_lookup_by_name` reads the other half.
    #[test]
    fn reduced_drops_the_named_fvars_from_both_halves() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let b = fresh_fvar(ctx, sort0, "b");
            let c = fresh_fvar(ctx, sort0, "c");
            let snap = ctx.current_lctx();
            ctx.lctx_restore(cp);

            let id_of = |ctx: &crate::MetaCtx, e| match ctx.node(e) {
                Node::FVar { id: Some(id) } => id,
                other => panic!("expected fvar, got {other:?}"),
            };
            let ib = id_of(ctx, b);

            assert_eq!(snap.entries().len(), 3, "the full context has three decls");

            let reduced = snap.reduced(&[(b, ib)]);

            assert_eq!(reduced.entries().len(), 2, "local_names lost exactly one");
            assert!(reduced.lctx().get(ib).is_none(), "lctx lost the erased fvar");
            assert!(
                reduced.entries().iter().all(|(_, f)| *f != b),
                "local_names lost the erased fvar too — dropping it from lctx \
                 alone leaves the two halves out of lockstep, which \
                 LocalCtxSnapshot::new debug_asserts against"
            );
            assert_eq!(
                reduced.entries().iter().map(|(_, f)| *f).collect::<Vec<_>>(),
                vec![a, c],
                "declaration order is preserved for the survivors"
            );
        });
    }
}
```

- [ ] **Step 7: Run it and verify it fails**

Run: `cargo test -p leanr_meta local_snapshot::tests::reduced_drops -- --exact`
Expected: FAIL — `no method named 'entries'`.

- [ ] **Step 8: Implement `entries` and `reduced`**

Add to `impl LocalCtxSnapshot` in
`crates/leanr_meta/src/local_snapshot.rs`:

```rust
/// The declared fvars in DECLARATION ORDER, paired with their user
/// names — the enumeration `collect_forward_deps`
/// (`MetavarContext.lean:1037-1062`) needs and that
/// `leanr_kernel::LocalContext` does not expose (its `decls`/`index`
/// are module-private; the public surface is `get(fvar_id)` by id and
/// `save`/`restore` by count). Positionally parallel to the
/// `LocalContext`'s own decl list, by this struct's lockstep
/// invariant, so an index into this slice is an index into that list.
#[allow(dead_code)]
pub(crate) fn entries(&self) -> &[(Option<NameId>, ExprId)] {
    &self.local_names
}

/// oracle: `reduceLocalContext` (`MetavarContext.lean:1065-1067`) —
/// this context with every fvar in `to_remove` erased. Each entry is
/// the fvar's `Expr::fvar` reference paired with its `FVarId`: the
/// first filters `local_names`, the second drives
/// `LocalContext::erase`, and taking both spares this module a
/// `Store` borrow it has no other reason to hold.
///
/// Both halves are filtered together, because `LocalCtxSnapshot::new`
/// debug-asserts they are in lockstep and every reader of one is
/// paired with a reader of the other.
#[allow(dead_code)]
pub(crate) fn reduced(&self, to_remove: &[(ExprId, NameId)]) -> LocalCtxSnapshot {
    let mut lctx = self.lctx.clone();
    for (_, fvar_id) in to_remove {
        lctx.erase(*fvar_id);
    }
    let local_names = self
        .local_names
        .iter()
        .filter(|(_, f)| !to_remove.iter().any(|(rf, _)| rf == f))
        .cloned()
        .collect();
    LocalCtxSnapshot::new(lctx, local_names)
}
```

- [ ] **Step 9: Run the snapshot test and verify it passes**

Run: `cargo test -p leanr_meta local_snapshot::tests::reduced_drops -- --exact`
Expected: PASS.

- [ ] **Step 10: Measure the discriminator**

Change `reduced` to filter only `lctx` and leave `local_names` intact
(delete the `.filter(...)` and just `self.local_names.clone()`). Re-run
Step 9. Expected: FAIL — in a debug build `LocalCtxSnapshot::new`'s
`debug_assert_eq!` trips first, and the `all(|(_, f)| *f != b)` assertion
backs it up. **Revert the mutation.**

- [ ] **Step 11: Run the full gate**

```bash
mise run ci
```

Expected: PASS. The two new `#[allow(dead_code)]` attributes are what
keep clippy quiet here; they come off in Task 10.

- [ ] **Step 12: Commit**

```bash
git add crates/leanr_kernel/src/local_ctx.rs crates/leanr_meta/src/local_snapshot.rs
git commit -m "elimMVarDeps task 2: LocalContext::erase and the reduced snapshot

reduceLocalContext is repeated LocalContext.erase, and the kernel had
none; mk_local_decl mints a fresh fvar id, so a filtered context cannot
be rebuilt from the public surface. Additive and TCB-neutral: the type
checker gains no caller and no existing body changes."
```

---

### Task 3: `depends_on` and `local_decl_depends_on`

`collectForwardDeps` asks, for each declaration in a metavariable's
context, "does this depend on anything already being reverted?" The
oracle answers with `DependsOn` (`MetavarContext.lean:660-725`) via
`findLocalDeclDependsOn` (`:744`) and `localDeclDependsOn` (`:767`).
leanr has no such traversal.

The part that is easy to get wrong is the **may-depend** case: a term
depends on `x` not only when it mentions `x` syntactically, but also when
it mentions a *metavariable whose own local context contains `x`* — that
metavariable might later be assigned a term mentioning `x`.

**Files:**
- Create: `crates/leanr_meta/src/mk_binding.rs`
- Modify: `crates/leanr_meta/src/lib.rs`
- Test: `crates/leanr_meta/src/mk_binding.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `LocalCtxSnapshot::entries` (Task 2).
- Produces:
  - `MetaCtx::fvar_id_of(&self, e: ExprId) -> Option<NameId>`
  - `MetaCtx::depends_on(&mut self, e: ExprId, pf: &[NameId]) ->
    Result<bool, MetaError>`
  - `MetaCtx::local_decl_depends_on(&mut self, ty: ExprId, value:
    Option<ExprId>, pf: &[NameId]) -> Result<bool, MetaError>`

- [ ] **Step 1: Create the module skeleton and register it**

Create `crates/leanr_meta/src/mk_binding.rs`:

```rust
//! `MkBinding` — eliminating metavariable dependencies before
//! abstraction.
//!
//! oracle: `Lean.MetavarContext.MkBinding`
//! (`src/Lean/MetavarContext.lean:938-1349`) plus `DependsOn`
//! (`:660-725`), toolchain `leanprover/lean4:v4.33.0-rc1`.
//!
//! The oracle's `mkBinding` never abstracts directly: it abstracts
//! through `abstractRange`, which runs `elimMVarDeps` first. An
//! unassigned metavariable whose own local context contains the free
//! variables being abstracted is replaced by a fresh auxiliary
//! metavariable APPLIED to them, so the occurrence abstracts like any
//! other argument and the original stays assignable in its own context.
//! Without it, such a metavariable assigned LATER — the elaborator's
//! synthetic-metavariable fixpoint resuming a postponed goal after the
//! binder has closed — contributes an unabstracted `fvar` where the
//! oracle emits a `bvar`.
//!
//! Its own file, not part of `metactx.rs`, so a reviewer can diff this
//! transcription against the oracle's namespace in one pass;
//! `metactx.rs` is the crate's accessor surface and is already the
//! second-largest file in it.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};

use crate::{MetaCtx, MetaError};

impl<'e> MetaCtx<'e> {}
```

Add to `crates/leanr_meta/src/lib.rs`, in the existing `mod` block, in
alphabetical position:

```rust
mod mk_binding;
```

- [ ] **Step 2: Write the failing test**

Add to the bottom of `crates/leanr_meta/src/mk_binding.rs`:

```rust
#[cfg(test)]
mod tests {
    use crate::test_support::{fresh_fvar, fresh_mvar, with_ctx};
    use leanr_kernel::bank::terms::Node;

    fn fvar_id(ctx: &crate::MetaCtx, e: leanr_kernel::bank::ExprId) -> leanr_kernel::bank::NameId {
        match ctx.node(e) {
            Node::FVar { id: Some(id) } => id,
            other => panic!("expected fvar, got {other:?}"),
        }
    }

    /// TDD RED/GREEN for plan task 3, the SYNTACTIC half.
    #[test]
    fn depends_on_sees_a_direct_fvar_occurrence() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let b = fresh_fvar(ctx, sort0, "b");
            let ia = fvar_id(ctx, a);
            let ib = fvar_id(ctx, b);

            let app = ctx.scratch.expr_app(base, a, sort0).expect("app");

            assert!(ctx.depends_on(app, &[ia]).expect("depends_on"));
            assert!(!ctx.depends_on(app, &[ib]).expect("depends_on"));
            ctx.lctx_restore(cp);
        });
    }

    /// TDD RED/GREEN for plan task 3, the MAY-DEPEND half — the case
    /// that makes this more than a syntactic fvar scan. `e` mentions
    /// `?m` and nothing else; `?m`'s own declared context contains `a`;
    /// so `e` may depend on `a`, because `?m` may later be assigned a
    /// term that mentions it.
    #[test]
    fn depends_on_sees_an_mvar_whose_own_context_holds_the_fvar() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let ia = fvar_id(ctx, a);
            // `?m` is minted HERE, so its declared context contains `a`.
            let (m, _) = fresh_mvar_in_ambient_ctx(ctx, sort0);
            ctx.lctx_restore(cp);

            // `m` mentions no fvar at all, syntactically.
            assert!(
                ctx.depends_on(m, &[ia]).expect("depends_on"),
                "a bare mvar whose own local context contains `a` MAY depend on \
                 `a` — dropping this case is what makes collect_forward_deps \
                 miss a forward dependency and mint an aux mvar at a context \
                 that is still too permissive"
            );
        });
    }

    /// `fresh_mvar` mints with an EMPTY declared context, which is
    /// exactly wrong for the may-depend test above. This mints at the
    /// AMBIENT one, the way production code does.
    fn fresh_mvar_in_ambient_ctx(
        ctx: &mut crate::MetaCtx,
        ty: leanr_kernel::bank::ExprId,
    ) -> (leanr_kernel::bank::ExprId, crate::MVarId) {
        ctx.mk_aux_mvar(ty).expect("mk_aux_mvar mints at current_lctx")
    }

}
```

`fresh_mvar` is imported for the third test Step 6 adds; if your editor
flags it as unused before then, leave it — do not delete the import.

Note: `mk_aux_mvar` is `pub(crate)` and already mints at
`current_lctx()` — see `assign.rs:689-710`. That is exactly the ambient
minting this test needs, so no new helper is required.

- [ ] **Step 3: Run the tests and verify they fail**

Run: `cargo test -p leanr_meta mk_binding::tests -- --nocapture`
Expected: FAIL — `no method named 'depends_on'`.

- [ ] **Step 4: Implement the traversal**

Replace `impl<'e> MetaCtx<'e> {}` in `mk_binding.rs` with:

```rust
impl<'e> MetaCtx<'e> {
    /// The `FVarId` behind an `Expr::fvar`, or `None` for anything
    /// else. `xs` and `to_revert` are carried as `Expr::fvar`
    /// references throughout (the oracle carries `Array Expr` too), so
    /// this is the one place the id is read out.
    #[allow(dead_code)]
    pub(crate) fn fvar_id_of(&self, e: ExprId) -> Option<NameId> {
        match self.node(e) {
            Node::FVar { id } => id,
            _ => None,
        }
    }

    /// oracle: `DependsOn` (`MetavarContext.lean:660-725`) reached via
    /// `findExprDependsOn` (`:733`) — does `e` depend on any free
    /// variable in `pf`?
    ///
    /// Two ways to depend, and the second is the one worth stating:
    ///
    /// 1. **Syntactically** — `e` mentions the fvar.
    /// 2. **May-depend** — `e` mentions an unassigned METAVARIABLE
    ///    whose own declared local context contains the fvar
    ///    (`:700-716`). That metavariable may later be assigned a term
    ///    that mentions it, so a dependency that does not exist yet
    ///    still counts. Dropping this case makes
    ///    `collect_forward_deps` miss a forward dependency, which mints
    ///    the auxiliary metavariable at a context that is still too
    ///    permissive — the bug this slice exists to remove, reappearing
    ///    one level down.
    ///
    /// An ASSIGNED metavariable is followed to its value instead
    /// (`:697-699`): its assignment is what the term really is.
    #[allow(dead_code)]
    pub(crate) fn depends_on(&mut self, e: ExprId, pf: &[NameId]) -> Result<bool, MetaError> {
        if pf.is_empty() {
            return Ok(false);
        }
        // Fast path, oracle `:686-689`: a term with neither an fvar nor
        // an expr mvar cannot depend on a free variable by either route.
        let d = self.data(e);
        if !d.has_fvar() && !d.has_expr_mvar() {
            return Ok(false);
        }
        self.step()?;
        self.guarded(|ctx| ctx.depends_on_body(e, pf))
    }

    fn depends_on_body(&mut self, e: ExprId, pf: &[NameId]) -> Result<bool, MetaError> {
        match self.node(e) {
            Node::FVar { id: Some(id) } => Ok(pf.contains(&id)),
            Node::FVar { id: None } => Ok(false),
            Node::MVar { id: Some(id) } => {
                let mid = crate::MVarId(id);
                if let Some(v) = self.mctx.assignment(mid) {
                    return self.depends_on(v, pf);
                }
                let Some(lctx) = self.mvar_lctx(mid) else {
                    return Ok(false);
                };
                Ok(pf.iter().any(|f| lctx.lctx().get(*f).is_some()))
            }
            Node::MVar { id: None } => Ok(false),
            Node::App { f, arg } => {
                Ok(self.depends_on(f, pf)? || self.depends_on(arg, pf)?)
            }
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => Ok(self.depends_on(binder_type, pf)? || self.depends_on(body, pf)?),
            Node::LetE {
                ty, value, body, ..
            } => Ok(self.depends_on(ty, pf)?
                || self.depends_on(value, pf)?
                || self.depends_on(body, pf)?),
            Node::MData { expr, .. } => self.depends_on(expr, pf),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                self.depends_on(structure, pf)
            }
            Node::BVar { .. }
            | Node::BVarBig { .. }
            | Node::Sort { .. }
            | Node::Const { .. }
            | Node::LitNat { .. }
            | Node::LitStr { .. } => Ok(false),
        }
    }

    /// oracle: `findLocalDeclDependsOn` (`:744`) / `localDeclDependsOn`
    /// (`:767`) — does a local declaration depend on any fvar in `pf`?
    /// Its type always counts; its value counts when it has one.
    ///
    /// The oracle's `generalizeNondepLet` parameter is NOT modelled:
    /// leanr's `LocalDecl` carries no `nondep` bit at all
    /// (`leanr_kernel/src/local_ctx.rs:37-43` — `mk_let_binding` takes
    /// it as a caller argument instead), so there is nothing to branch
    /// on. This is the same missing bit that makes `mk_aux_mvar_type`
    /// refuse an ldecl in `to_revert`; see that function's doc.
    #[allow(dead_code)]
    pub(crate) fn local_decl_depends_on(
        &mut self,
        ty: ExprId,
        value: Option<ExprId>,
        pf: &[NameId],
    ) -> Result<bool, MetaError> {
        if self.depends_on(ty, pf)? {
            return Ok(true);
        }
        match value {
            Some(v) => self.depends_on(v, pf),
            None => Ok(false),
        }
    }
}
```

- [ ] **Step 5: Run the tests and verify they pass**

Run: `cargo test -p leanr_meta mk_binding::tests -- --nocapture`
Expected: both PASS.

- [ ] **Step 6: Measure both discriminators**

**Mutation A (may-depend).** In `depends_on_body`'s `Node::MVar` arm,
replace the `lctx` lookup with `Ok(false)`. Re-run Step 5. Expected:
`depends_on_sees_an_mvar_whose_own_context_holds_the_fvar` goes RED,
`depends_on_sees_a_direct_fvar_occurrence` stays green. **Revert.**

**Mutation B (assigned-mvar following).** Replace the
`if let Some(v) = self.mctx.assignment(mid)` early return with nothing,
so an assigned metavariable falls through to the lctx test. Re-run
Step 5. Expected: **both tests still pass** — nothing here covers it.
That is a real coverage gap, so **before reverting**, add this third
test and confirm it goes red under the mutation and green without it:

```rust
/// An ASSIGNED metavariable is its value, not its declaration:
/// `?m := a` depends on `a` even if `?m`'s own context does not
/// mention it.
#[test]
fn depends_on_follows_an_assigned_mvar_to_its_value() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        // `?m` is minted OUTSIDE the binder, so its own context is empty.
        let (m, mid) = fresh_mvar(ctx, sort0);
        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        let ia = fvar_id(ctx, a);
        ctx.mctx_mut().assign(mid, a).expect("assign");

        assert!(
            ctx.depends_on(m, &[ia]).expect("depends_on"),
            "an assigned mvar is followed to its value"
        );
        ctx.lctx_restore(cp);
    });
}
```

Then **revert Mutation B**.

- [ ] **Step 7: Run the full gate**

```bash
mise run ci
```

Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add crates/leanr_meta/src/mk_binding.rs crates/leanr_meta/src/lib.rs
git commit -m "elimMVarDeps task 3: DependsOn, including the may-depend case

A term depends on x not only when it mentions x, but when it mentions an
unassigned mvar whose own declared context contains x — that mvar may
later be assigned a term mentioning it. Dropping that case makes
collect_forward_deps miss a forward dependency."
```

---

### Task 4: `get_in_scope`, `collect_forward_deps`, `reduce_local_context`, `mk_mvar_app`

The four helpers `elim_mvar` calls before it mints anything.

**Files:**
- Modify: `crates/leanr_meta/src/mk_binding.rs`
- Test: `crates/leanr_meta/src/mk_binding.rs` (`mod tests`)

**Interfaces:**
- Consumes: `depends_on` / `local_decl_depends_on` / `fvar_id_of`
  (Task 3); `LocalCtxSnapshot::entries` / `reduced` (Task 2).
- Produces:
  - `get_in_scope(&self, lctx: &LocalCtxSnapshot, xs: &[ExprId]) ->
    Vec<ExprId>`
  - `collect_forward_deps(&mut self, lctx: &LocalCtxSnapshot, to_revert:
    Vec<ExprId>) -> Result<Vec<ExprId>, MetaError>`
  - `reduce_local_context(&self, lctx: &LocalCtxSnapshot, to_revert:
    &[ExprId]) -> Result<Arc<LocalCtxSnapshot>, MetaError>`
  - `mk_mvar_app(&mut self, mvar: ExprId, xs: &[ExprId]) ->
    Result<ExprId, MetaError>`

- [ ] **Step 1: Write the failing tests**

Add to `mk_binding.rs`'s `mod tests`:

```rust
/// TDD RED/GREEN for plan task 4. `get_in_scope` keeps only the
/// members of `xs` that the metavariable's OWN context declares —
/// oracle `:1070-1077`.
#[test]
fn get_in_scope_keeps_only_the_fvars_the_mvar_can_see() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        // Snapshot taken with `a` only — `b` comes later.
        let snap = ctx.current_lctx();
        let b = fresh_fvar(ctx, sort0, "b");
        ctx.lctx_restore(cp);

        let in_scope = ctx.get_in_scope(&snap, &[a, b]);
        assert_eq!(
            in_scope,
            vec![a],
            "only `a` is in the snapshot; keeping `b` would revert a binder \
             the metavariable never saw"
        );
    });
}

/// `collect_forward_deps` closes `to_revert` under forward
/// dependencies: `y : a` must join when `a` is reverted, or the
/// auxiliary metavariable is minted at a context holding a
/// declaration whose type mentions an erased fvar. Oracle `:1037-1062`.
#[test]
fn collect_forward_deps_pulls_in_a_dependent_later_decl() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        // `y : a` — its TYPE is the fvar `a`, so it depends on it.
        let y = fresh_fvar(ctx, a, "y");
        let snap = ctx.current_lctx();
        ctx.lctx_restore(cp);

        let closed = ctx
            .collect_forward_deps(&snap, vec![a])
            .expect("collect_forward_deps");
        assert_eq!(
            closed,
            vec![a, y],
            "y : a depends on a, so reverting a must revert y too, in \
             declaration order"
        );
    });
}

/// `reduce_local_context` removes exactly `to_revert`. Oracle
/// `:1065-1067`.
#[test]
fn reduce_local_context_removes_exactly_the_reverted_fvars() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        let b = fresh_fvar(ctx, sort0, "b");
        let snap = ctx.current_lctx();
        ctx.lctx_restore(cp);

        let ia = fvar_id(ctx, a);
        let ib = fvar_id(ctx, b);
        let reduced = ctx
            .reduce_local_context(&snap, &[a])
            .expect("reduce_local_context");

        assert!(reduced.lctx().get(ia).is_none(), "a is erased");
        assert!(reduced.lctx().get(ib).is_some(), "b survives");
    });
}

/// `mk_mvar_app` applies the auxiliary metavariable to the reverted
/// fvars, innermost LAST — the application order that makes
/// `?new #0` come out right after abstraction. Oracle `:1090-1097`.
#[test]
fn mk_mvar_app_applies_the_fvars_in_declaration_order() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        let b = fresh_fvar(ctx, sort0, "b");
        let (m, _) = fresh_mvar(ctx, sort0);
        ctx.lctx_restore(cp);

        let app = ctx.mk_mvar_app(m, &[a, b]).expect("mk_mvar_app");
        // Expect `((m a) b)`: the LAST-declared fvar is the OUTERMOST
        // argument.
        match ctx.node(app) {
            Node::App { f, arg } => {
                assert_eq!(arg, b, "the last fvar is the outermost argument");
                match ctx.node(f) {
                    Node::App { f: inner, arg: a2 } => {
                        assert_eq!(a2, a);
                        assert_eq!(inner, m);
                    }
                    other => panic!("expected nested App, got {other:?}"),
                }
            }
            other => panic!("expected App, got {other:?}"),
        }
    });
}
```

- [ ] **Step 2: Run them and verify they fail**

Run: `cargo test -p leanr_meta mk_binding::tests -- --nocapture`
Expected: four FAILs — `no method named 'get_in_scope'` etc.

- [ ] **Step 3: Implement the four helpers**

Add to `mk_binding.rs`'s `impl<'e> MetaCtx<'e>` block. You will need
`use std::sync::Arc;` and `use crate::local_snapshot::LocalCtxSnapshot;`
at the top of the file.

```rust
/// oracle: `getInScope` (`:1070-1077`) — the members of `xs` that
/// `lctx` actually declares. Anything else is a binder this
/// metavariable never saw, and reverting it would be reverting a
/// variable that is not in its context.
#[allow(dead_code)]
pub(crate) fn get_in_scope(&self, lctx: &LocalCtxSnapshot, xs: &[ExprId]) -> Vec<ExprId> {
    xs.iter()
        .filter(|x| {
            self.fvar_id_of(**x)
                .is_some_and(|id| lctx.lctx().get(id).is_some())
        })
        .copied()
        .collect()
}

/// oracle: `collectForwardDeps` (`:1037-1062`) — close `to_revert`
/// under forward dependencies, walking `lctx` in declaration order
/// from the earliest reverted declaration onward. A later declaration
/// joins when it IS one of `to_revert`, or when it depends on
/// something already collected.
///
/// The oracle's `preserveOrder` branch (`:1042-1050`, which can throw
/// `Exception.revertFailure`) is NOT modelled: `preserveOrder` is a
/// tactic-framework flag and leanr has no producer for it — the only
/// caller here passes the `false` case. Named in the design spec's
/// § What this ships.
#[allow(dead_code)]
pub(crate) fn collect_forward_deps(
    &mut self,
    lctx: &LocalCtxSnapshot,
    to_revert: Vec<ExprId>,
) -> Result<Vec<ExprId>, MetaError> {
    if to_revert.is_empty() {
        return Ok(to_revert);
    }
    let entries: Vec<ExprId> = lctx.entries().iter().map(|(_, f)| *f).collect();
    // oracle `getLocalDeclWithSmallestIdx` (`:1052`): start at the
    // earliest declaration that is being reverted. Everything before it
    // is declared earlier than anything reverted, so it cannot depend
    // on one.
    let start = entries
        .iter()
        .position(|f| to_revert.contains(f))
        .unwrap_or(entries.len());

    let mut collected: Vec<ExprId> = Vec::with_capacity(to_revert.len());
    for fvar in entries.into_iter().skip(start) {
        if to_revert.contains(&fvar) {
            collected.push(fvar);
            continue;
        }
        let Some(id) = self.fvar_id_of(fvar) else {
            continue;
        };
        let Some(decl) = lctx.lctx().get(id) else {
            continue;
        };
        let (ty, value) = (decl.ty, decl.value);
        let pf: Vec<NameId> = collected
            .iter()
            .filter_map(|f| self.fvar_id_of(*f))
            .collect();
        if self.local_decl_depends_on(ty, value, &pf)? {
            collected.push(fvar);
        }
    }
    Ok(collected)
}

/// oracle: `reduceLocalContext` (`:1065-1067`) — `lctx` with every
/// fvar in `to_revert` erased. This is the context the auxiliary
/// metavariable is minted at, and erasing is the whole point: leaving
/// the reverted fvars in place would let the new metavariable be
/// assigned the very variable the abstraction is removing, which is
/// this slice's own bug reappearing one level down.
#[allow(dead_code)]
pub(crate) fn reduce_local_context(
    &self,
    lctx: &LocalCtxSnapshot,
    to_revert: &[ExprId],
) -> Result<Arc<LocalCtxSnapshot>, MetaError> {
    let pairs: Vec<(ExprId, NameId)> = to_revert
        .iter()
        .filter_map(|f| self.fvar_id_of(*f).map(|id| (*f, id)))
        .collect();
    Ok(Arc::new(lctx.reduced(&pairs)))
}

/// oracle: `mkMVarApp` (`:1090-1097`) — `mvar` applied to `xs`, first
/// declared innermost, so that after abstraction the arguments read
/// `?new #(n-1) … #0`.
///
/// The oracle's two kind branches (`:1094-1097`) differ only in
/// whether a LET-bound fvar is applied. Under this port's ldecl
/// refusal (see `mk_aux_mvar_type`) `xs` never contains one, so the
/// branches coincide and the `syntheticOpaque` form — apply
/// everything — is the one written.
#[allow(dead_code)]
pub(crate) fn mk_mvar_app(&mut self, mvar: ExprId, xs: &[ExprId]) -> Result<ExprId, MetaError> {
    let mut e = mvar;
    for x in xs {
        e = self.scratch.expr_app(Some(self.view.store), e, *x)?;
    }
    Ok(e)
}
```

- [ ] **Step 4: Run the tests and verify they pass**

Run: `cargo test -p leanr_meta mk_binding::tests -- --nocapture`
Expected: all PASS.

- [ ] **Step 5: Measure the four discriminators**

Apply each mutation, run Step 4, confirm the named test goes red, revert.

| Mutation | Test that must go red |
| --- | --- |
| `get_in_scope` returns `xs.to_vec()` unfiltered | `get_in_scope_keeps_only_the_fvars_the_mvar_can_see` |
| `collect_forward_deps` returns `to_revert` unchanged | `collect_forward_deps_pulls_in_a_dependent_later_decl` |
| `reduce_local_context` returns `Arc::new(lctx.reduced(&[]))` | `reduce_local_context_removes_exactly_the_reverted_fvars` |
| `mk_mvar_app` iterates `xs.iter().rev()` | `mk_mvar_app_applies_the_fvars_in_declaration_order` |

If any survives, strengthen the test before continuing.

- [ ] **Step 6: Run the full gate and commit**

```bash
mise run ci
git add crates/leanr_meta/src/mk_binding.rs
git commit -m "elimMVarDeps task 4: getInScope, collectForwardDeps, reduceLocalContext, mkMVarApp

The four helpers elimMVar calls before it mints anything. Erasing the
reverted fvars from the auxiliary metavariable's context is the
load-bearing one: leaving them in lets the new metavariable be assigned
the very variable the abstraction removes."
```

---

### Task 5: the delayed-assignment channel

`elimMVar`'s `syntheticOpaque` branch (`:1216-1228`) does not assign the
original — it delayed-assigns the **new** one back to it. `leanr_meta`
has no delayed-assignment concept at all: `assign.rs:93` and
`whnf.rs:476` both say so.

**Files:**
- Modify: `crates/leanr_meta/src/mvar_ctx.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (re-export)
- Modify: `crates/leanr_meta/src/assign.rs` (`get_delayed_mvar_root`)
- Test: `crates/leanr_meta/src/mvar_ctx.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: nothing.
- Produces:
  - `pub struct DelayedMVarAssignment { pub fvars: Vec<ExprId>, pub
    mvar_id_pending: MVarId }`
  - `MetavarContext::assign_delayed(&mut self, id: MVarId, fvars:
    Vec<ExprId>, pending: MVarId) -> Result<(), MetaError>`
  - `MetavarContext::delayed_assignment(&self, id: MVarId) ->
    Option<&DelayedMVarAssignment>`
  - `MetavarContext::is_delayed_assigned(&self, id: MVarId) -> bool`
  - `MetaCtx::get_delayed_mvar_root(&self, id: MVarId) -> MVarId`

- [ ] **Step 1: Write the failing test**

Add a `#[cfg(test)] mod tests` at the bottom of
`crates/leanr_meta/src/mvar_ctx.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{fresh_mvar, with_ctx};

    /// TDD RED/GREEN for plan task 5.
    #[test]
    fn delayed_assignment_round_trips_and_refuses_a_second_one() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            let (_, new_id) = fresh_mvar(ctx, sort0);
            let (_, pending) = fresh_mvar(ctx, sort0);

            assert!(!ctx.mctx().is_delayed_assigned(new_id));
            ctx.mctx_mut()
                .assign_delayed(new_id, vec![sort0], pending)
                .expect("first delayed assignment");
            assert!(ctx.mctx().is_delayed_assigned(new_id));

            let d = ctx
                .mctx()
                .delayed_assignment(new_id)
                .expect("round-trips");
            assert_eq!(d.fvars, vec![sort0]);
            assert_eq!(d.mvar_id_pending, pending);

            assert!(
                ctx.mctx_mut()
                    .assign_delayed(new_id, vec![], pending)
                    .is_err(),
                "a delayed assignment is permanent, exactly like an ordinary \
                 one — silently overwriting turns a bug into a wrong answer"
            );
        });
    }

    /// `getDelayedMVarRoot` (`MetavarContext.lean:436-440`) follows the
    /// chain to the metavariable that is NOT delayed-assigned.
    #[test]
    fn get_delayed_mvar_root_follows_a_chain() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            let (_, a) = fresh_mvar(ctx, sort0);
            let (_, b) = fresh_mvar(ctx, sort0);
            let (_, c) = fresh_mvar(ctx, sort0);

            ctx.mctx_mut().assign_delayed(a, vec![], b).expect("a := b");
            ctx.mctx_mut().assign_delayed(b, vec![], c).expect("b := c");

            assert_eq!(ctx.get_delayed_mvar_root(a), c);
            assert_eq!(ctx.get_delayed_mvar_root(c), c, "a root is its own root");
        });
    }
}
```

- [ ] **Step 2: Run and verify failure**

Run: `cargo test -p leanr_meta mvar_ctx::tests -- --nocapture`
Expected: FAIL — `no method named 'is_delayed_assigned'`.

- [ ] **Step 3: Implement the channel**

In `crates/leanr_meta/src/mvar_ctx.rs`, add the struct after `MVarDecl`:

```rust
/// oracle: `DelayedMetavarAssignment` (`MetavarContext.lean:335`).
///
/// `?id #[x_1, …, x_n] := ?mvar_id_pending` — read as: once
/// `mvar_id_pending` is assigned, `?id` applied to at least `n`
/// arguments becomes that value with `fvars` abstracted and the
/// arguments substituted in. `elimMVar` (`:1216-1228`) is this
/// crate's only producer: a `syntheticOpaque` metavariable must never
/// be assigned by anything but the elaborator that created it, so the
/// AUXILIARY metavariable is delayed-assigned back to the original
/// rather than the original being assigned outright.
///
/// No `Debug` derive would be a problem here — `ExprId` and `MVarId`
/// both have one — so it derives normally.
#[derive(Debug, Clone)]
pub struct DelayedMVarAssignment {
    pub fvars: Vec<ExprId>,
    pub mvar_id_pending: MVarId,
}
```

Add the field to `MetavarContext`:

```rust
    d_assignment: HashMap<MVarId, DelayedMVarAssignment>,
```

and the three methods inside `impl MetavarContext`:

```rust
    /// oracle: `assignDelayedMVar` (`MetavarContext.lean:543`).
    ///
    /// Refuses to redefine an existing delayed assignment, and refuses
    /// an undeclared metavariable, for the same reason `assign` does:
    /// in Lean an assignment is permanent for the lifetime of the
    /// context, and silently overwriting one turns a bug into a wrong
    /// answer instead of an error.
    pub fn assign_delayed(
        &mut self,
        id: MVarId,
        fvars: Vec<ExprId>,
        mvar_id_pending: MVarId,
    ) -> Result<(), MetaError> {
        if !self.decls.contains_key(&id) {
            return Err(MetaError::MVar(format!(
                "assign_delayed: metavariable {id:?} was never declared"
            )));
        }
        if self.d_assignment.contains_key(&id) {
            return Err(MetaError::MVar(format!(
                "assign_delayed: metavariable {id:?} is already delayed-assigned"
            )));
        }
        self.d_assignment.insert(
            id,
            DelayedMVarAssignment {
                fvars,
                mvar_id_pending,
            },
        );
        Ok(())
    }

    /// oracle: `getDelayedMVarAssignment?` (`:425-426`).
    pub fn delayed_assignment(&self, id: MVarId) -> Option<&DelayedMVarAssignment> {
        self.d_assignment.get(&id)
    }

    /// oracle: `MVarId.isDelayedAssigned` (`:449-450`).
    pub fn is_delayed_assigned(&self, id: MVarId) -> bool {
        self.d_assignment.contains_key(&id)
    }
```

Re-export from `crates/leanr_meta/src/lib.rs` alongside the existing
`MVarDecl` / `MVarId` re-exports:

```rust
pub use mvar_ctx::DelayedMVarAssignment;
```

Add `get_delayed_mvar_root` to `crates/leanr_meta/src/assign.rs`'s
`impl<'e> MetaCtx<'e>` block, next to `instantiate_mvars`:

```rust
    /// oracle: `getDelayedMVarRoot` (`MetavarContext.lean:436-440`) —
    /// follow a chain of delayed assignments
    /// `?m₁ := ?m₂; …; ?mₙ := ?root` to the metavariable that is not
    /// itself delayed-assigned. A metavariable with no delayed
    /// assignment is its own root.
    ///
    /// Written as a LOOP, not the oracle's recursion: the chain is
    /// unbounded in principle, and this crate's recursion budget
    /// (`guarded`) is for term traversal, not for a map walk. A cycle
    /// would hang, which cannot arise — `elimMVar` only ever
    /// delayed-assigns a FRESHLY minted id, so every edge points from
    /// a newer metavariable to an older one.
    pub fn get_delayed_mvar_root(&self, mvar_id: MVarId) -> MVarId {
        let mut cur = mvar_id;
        while let Some(d) = self.mctx.delayed_assignment(cur) {
            cur = d.mvar_id_pending;
        }
        cur
    }
```

- [ ] **Step 4: Run the tests and verify they pass**

Run: `cargo test -p leanr_meta mvar_ctx::tests -- --nocapture`
Expected: both PASS.

- [ ] **Step 5: Measure the discriminators**

**Mutation A.** Delete the `if self.d_assignment.contains_key(&id)`
guard in `assign_delayed`. Expected:
`delayed_assignment_round_trips_and_refuses_a_second_one` goes RED on the
final assertion. **Revert.**

**Mutation B.** Change `get_delayed_mvar_root`'s loop to a single step
(`if let Some(d) = … { return d.mvar_id_pending; } mvar_id`). Expected:
`get_delayed_mvar_root_follows_a_chain` goes RED (`a` resolves to `b`,
not `c`). **Revert.**

- [ ] **Step 6: Run the full gate and commit**

```bash
mise run ci
git add crates/leanr_meta/src/mvar_ctx.rs crates/leanr_meta/src/lib.rs crates/leanr_meta/src/assign.rs
git commit -m "elimMVarDeps task 5: the delayed-assignment channel

elimMVar's syntheticOpaque branch delayed-assigns the auxiliary
metavariable back to the original rather than assigning the original,
because a syntheticOpaque mvar must only be assigned by the elaborator
that created it. leanr had no delayed-assignment concept at all."
```

---

### Task 6: `instantiate_mvars`' delayed arm and the real `whnf_delayed_assigned`

A delayed assignment that nothing consumes is worse than none: the term
keeps an auxiliary metavariable that never resolves. Two consumers.

**Files:**
- Modify: `crates/leanr_meta/src/assign.rs` (`instantiate_mvars_body`,
  `:1202`)
- Modify: `crates/leanr_meta/src/whnf.rs` (`whnf_delayed_assigned`,
  `:481`)
- Test: `crates/leanr_meta/src/assign.rs` (`mod tests`)

**Interfaces:**
- Consumes: the Task 5 channel; `MetaCtx::mk_lambda` (existing,
  `metactx.rs:815`).
- Produces: no new public names — two existing functions gain behavior.

- [ ] **Step 1: Write the failing test**

Add to `crates/leanr_meta/src/assign.rs`'s `mod tests`:

```rust
/// TDD RED/GREEN for plan task 6. `?new #[a] := ?m` with `?m := a`
/// means `?new a` instantiates to `a`: abstract `a` out of the pending
/// value, then apply it back.
#[test]
fn instantiate_mvars_resolves_a_delayed_assignment() {
    use crate::test_support::{fresh_fvar, with_ctx};
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        let (new_e, new_id) = ctx.mk_aux_mvar(sort0).expect("aux");
        let (_, pending) = ctx.mk_aux_mvar(sort0).expect("pending");

        ctx.mctx_mut()
            .assign_delayed(new_id, vec![a], pending)
            .expect("delayed");
        ctx.mctx_mut().assign(pending, a).expect("pending := a");

        // `?new a`
        let applied = ctx.scratch.expr_app(base, new_e, a).expect("app");
        let got = ctx.instantiate_mvars(applied).expect("instantiate");

        assert_eq!(
            got, a,
            "?new #[a] := ?m with ?m := a means `?new a` is `a`: \
             (fun a => a) a, beta-reduced"
        );
        ctx.lctx_restore(cp);
    });
}

/// The delayed assignment must NOT fire while the pending
/// metavariable is still unassigned — the term is not resolvable yet,
/// and collapsing it early loses the "not yet".
#[test]
fn instantiate_mvars_leaves_an_unresolved_delayed_assignment_alone() {
    use crate::test_support::{fresh_fvar, with_ctx};
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        let (new_e, new_id) = ctx.mk_aux_mvar(sort0).expect("aux");
        let (_, pending) = ctx.mk_aux_mvar(sort0).expect("pending");
        ctx.mctx_mut()
            .assign_delayed(new_id, vec![a], pending)
            .expect("delayed");

        let applied = ctx.scratch.expr_app(base, new_e, a).expect("app");
        let got = ctx.instantiate_mvars(applied).expect("instantiate");

        assert_eq!(got, applied, "unresolved: the term is returned unchanged");
        ctx.lctx_restore(cp);
    });
}
```

- [ ] **Step 2: Run and verify failure**

Run: `cargo test -p leanr_meta assign::tests::instantiate_mvars_resolves_a_delayed -- --exact`
Expected: FAIL — `got` is the unchanged application, not `a`.

- [ ] **Step 3: Implement the `instantiate_mvars` delayed arm**

`instantiate_mvars_body`'s `Node::App` arm currently instantiates head
and argument independently. Replace it with a version that first tries
the delayed channel on the spine:

```rust
            Node::App { f, arg } => {
                // oracle: `instantiateExprMVars`' delayed-assignment
                // case. A delayed assignment `?new #[y…] := ?m` is
                // resolvable only once `?m` is assigned; until then the
                // application stands, and collapsing it early would
                // lose the "not yet".
                if let Some(resolved) = self.instantiate_delayed_app(e)? {
                    return self.instantiate_mvars(resolved);
                }
                let f2 = self.instantiate_mvars(f)?;
                let a2 = self.instantiate_mvars(arg)?;
                if f2 == f && a2 == arg {
                    Ok(e)
                } else {
                    Ok(self.scratch.expr_app(Some(self.view.store), f2, a2)?)
                }
            }
```

and add the helper next to it:

```rust
    /// oracle: the delayed-assignment case of `instantiateExprMVars`
    /// (`instantiateExprMVarsImp`, `MetavarContext.lean:577-583`; the
    /// body is C++, and `whnfDelayedAssigned?`,
    /// `Meta/WHNF.lean:587-606`, is the readable statement of the same
    /// rule).
    ///
    /// `?new #[y_1 … y_n] := ?m` applied to at least `n` arguments,
    /// with `?m` assigned to `v`: the result is `v` with the `y`s
    /// abstracted, applied to those arguments — which beta-reduces to
    /// `v` with each `y_i` replaced by the matching argument.
    /// `mk_lambda` is the abstraction, `beta_rev` the application.
    ///
    /// `None` (leave the term alone) in three cases, each matching the
    /// oracle's own guard: the head is not a delayed-assigned
    /// metavariable; there are fewer arguments than abstracted fvars
    /// (`WHNF.lean:593-595`); or the pending value still carries a
    /// metavariable (`:598-600`), so the answer is not settled yet.
    fn instantiate_delayed_app(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        let f = self.get_app_fn(e);
        let Node::MVar { id: Some(name) } = self.node(f) else {
            return Ok(None);
        };
        let head = MVarId(name);
        let Some(d) = self.mctx.delayed_assignment(head) else {
            return Ok(None);
        };
        let (fvars, pending) = (d.fvars.clone(), d.mvar_id_pending);
        let args = self.get_app_args(e);
        if fvars.len() > args.len() {
            return Ok(None);
        }
        let Some(val) = self.mctx.assignment(pending) else {
            return Ok(None);
        };
        let val = self.instantiate_mvars(val)?;
        if self.data(val).has_expr_mvar() {
            return Ok(None);
        }
        let abstracted = self.mk_lambda(&fvars, val)?;
        let mut rev: Vec<ExprId> = args[..fvars.len()].to_vec();
        rev.reverse();
        let applied = self.beta_rev(abstracted, &rev)?;
        if args.len() == fvars.len() {
            return Ok(Some(applied));
        }
        Ok(Some(self.mk_app_spine(applied, &args[fvars.len()..])?))
    }
```

If `beta_rev`'s argument-order convention differs from the `rev` above,
check `whnf.rs`'s own `whnf_core_app` call
(`let applied = self.beta_rev(f_prime, &args)?;`) and match it exactly —
that is the in-crate ground truth, not this plan.

- [ ] **Step 4: Run the tests and verify they pass**

Run: `cargo test -p leanr_meta assign::tests::instantiate_mvars -- --nocapture`
Expected: both PASS.

- [ ] **Step 5: Implement the real `whnf_delayed_assigned`**

Replace the stub at `crates/leanr_meta/src/whnf.rs:481` — body and doc
comment together, deleting the `SEAM:` heading:

```rust
    /// oracle: `whnfDelayedAssigned?` (`Meta/WHNF.lean:587-606`).
    ///
    /// The same rule `instantiate_delayed_app` implements, on the whnf
    /// hot path: a delayed-assigned metavariable head applied to at
    /// least as many arguments as it abstracts, whose pending
    /// metavariable is assigned to a metavariable-free value, reduces
    /// to that value with the abstracted fvars substituted.
    ///
    /// Delegates rather than duplicating: this is `whnf_core_app`'s
    /// single call site (`:426`), the rule is one rule, and two
    /// transcriptions of it would be two things to keep in step.
    fn whnf_delayed_assigned(
        &mut self,
        f_prime: ExprId,
        e: ExprId,
    ) -> Result<Option<ExprId>, MetaError> {
        if !matches!(self.node(f_prime), Node::MVar { .. }) {
            return Ok(None);
        }
        self.instantiate_delayed_app(e)
    }
```

`instantiate_delayed_app` must be `pub(crate)` for this — change its
declaration in `assign.rs` from `fn` to `pub(crate) fn`.

- [ ] **Step 6: Run the whole crate's tests**

```bash
cargo test -p leanr_meta
```

Expected: PASS, including `oracle_fast` and `oracle_synth`. **No record
may move.** If one does, stop and report — no delayed assignment exists
in any committed corpus yet, so a move here means the `Node::App` arm
restructure changed something it should not have.

- [ ] **Step 7: Measure the discriminators**

**Mutation A.** Delete the `if self.data(val).has_expr_mvar()` guard.
Expected: no test goes red — nothing covers it yet. That guard is
load-bearing at Task 11, so add this test now, confirm it goes red under
the mutation and green without it, then revert:

```rust
/// The pending value still carrying a metavariable means the answer
/// is not settled: firing anyway bakes an unresolved metavariable
/// into the abstraction. Oracle `WHNF.lean:598-600`.
#[test]
fn instantiate_mvars_waits_when_the_pending_value_is_not_settled() {
    use crate::test_support::{fresh_fvar, with_ctx};
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        let (new_e, new_id) = ctx.mk_aux_mvar(sort0).expect("aux");
        let (_, pending) = ctx.mk_aux_mvar(sort0).expect("pending");
        let (open_e, _) = ctx.mk_aux_mvar(sort0).expect("still open");

        ctx.mctx_mut()
            .assign_delayed(new_id, vec![a], pending)
            .expect("delayed");
        // pending := an application that still mentions an unassigned mvar
        let v = ctx.scratch.expr_app(base, open_e, a).expect("app");
        ctx.mctx_mut().assign(pending, v).expect("pending := v");

        let applied = ctx.scratch.expr_app(base, new_e, a).expect("app");
        let got = ctx.instantiate_mvars(applied).expect("instantiate");
        assert_eq!(got, applied, "not settled: leave it alone");
        ctx.lctx_restore(cp);
    });
}
```

**Mutation B.** Delete the `if fvars.len() > args.len()` guard. Expected:
no existing test goes red. Confirm by adding a partial-application case
to `instantiate_mvars_leaves_an_unresolved_delayed_assignment_alone`
(delayed on `vec![a, b]`, applied to one argument only) — it must go red
under the mutation and green without it. Revert.

- [ ] **Step 8: Run the full gate and commit**

```bash
mise run ci
git add crates/leanr_meta/src/assign.rs crates/leanr_meta/src/whnf.rs
git commit -m "elimMVarDeps task 6: consume the delayed channel

instantiate_mvars gains its delayed arm and whnf_delayed_assigned stops
being a hardcoded None. A delayed assignment nothing consumes is worse
than none: the term keeps an auxiliary metavariable that never resolves."
```

---

### Task 7: `mk_aux_mvar_at`

`elim_mvar` mints its auxiliary metavariable at an **explicitly
constructed reduced** context — neither the ambient one nor an existing
metavariable's. `mk_aux_mvar` (`assign.rs:689`) always mints at
`current_lctx()`, and it hardcodes `MVarKind::Natural`.

This is a **refactor, not an addition**, and therefore a flagged
`leanr_meta` change. Precedent: M4b-3 P3 generalized
`forall_meta_telescope_reducing` out of `synth.rs` on exactly this
rationale. Rejected alternative: a second minting function duplicating
the declare-and-intern sequence.

**Files:**
- Modify: `crates/leanr_meta/src/assign.rs:689-710`
- Test: `crates/leanr_meta/src/assign.rs` (`mod tests`)

**Interfaces:**
- Consumes: `LocalCtxSnapshot` (existing).
- Produces: `MetaCtx::mk_aux_mvar_at(&mut self, lctx:
  Arc<LocalCtxSnapshot>, ty: ExprId, kind: MVarKind) -> Result<(ExprId,
  MVarId), MetaError>`. `mk_aux_mvar` keeps its exact signature and
  behavior.

- [ ] **Step 1: Write the failing test**

```rust
/// TDD RED/GREEN for plan task 7. `mk_aux_mvar_at` mints at the
/// GIVEN context and kind, not the ambient ones.
#[test]
fn mk_aux_mvar_at_uses_the_given_context_and_kind() {
    use crate::test_support::{fresh_fvar, with_ctx};
    use crate::LocalCtxSnapshot;
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let _a = fresh_fvar(ctx, sort0, "a");
        // Ambient context now has one decl; mint at the EMPTY one.
        let (_, id) = ctx
            .mk_aux_mvar_at(LocalCtxSnapshot::empty(), sort0, MVarKind::SyntheticOpaque)
            .expect("mk_aux_mvar_at");

        let decl = ctx.mctx().decl(id).expect("declared");
        assert_eq!(
            decl.lctx.depth(),
            0,
            "minted at the GIVEN context, not the ambient one — minting at \
             the ambient context is what lets the new metavariable be \
             assigned the very fvar the abstraction removes"
        );
        assert_eq!(decl.kind, MVarKind::SyntheticOpaque, "the given kind");
        ctx.lctx_restore(cp);
    });
}

/// `mk_aux_mvar` keeps its exact prior behavior: ambient context,
/// `Natural` kind. The generalization must be behavior-neutral for the
/// existing entry point.
#[test]
fn mk_aux_mvar_still_mints_at_the_ambient_context_as_natural() {
    use crate::test_support::{fresh_fvar, with_ctx};
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let _a = fresh_fvar(ctx, sort0, "a");
        let (_, id) = ctx.mk_aux_mvar(sort0).expect("mk_aux_mvar");
        let decl = ctx.mctx().decl(id).expect("declared");
        assert_eq!(decl.lctx.depth(), 1, "the ambient context, as before");
        assert_eq!(decl.kind, MVarKind::Natural, "Natural, as before");
        ctx.lctx_restore(cp);
    });
}
```

- [ ] **Step 2: Run and verify failure**

Run: `cargo test -p leanr_meta assign::tests::mk_aux_mvar -- --nocapture`
Expected: the first FAILs (`no method named 'mk_aux_mvar_at'`), the
second PASSes.

- [ ] **Step 3: Generalize**

Replace `mk_aux_mvar`'s body at `assign.rs:689-710` with a delegation,
and add the general form beneath it. Keep `mk_aux_mvar`'s existing doc
comment; append one sentence saying it is now the ambient/`Natural`
specialization.

```rust
    pub(crate) fn mk_aux_mvar(&mut self, ty: ExprId) -> Result<(ExprId, MVarId), MetaError> {
        let lctx = self.current_lctx();
        self.mk_aux_mvar_at(lctx, ty, MVarKind::Natural)
    }

    /// `mk_aux_mvar` with the local context and kind chosen by the
    /// caller — the form `elim_mvar` (`mk_binding.rs`) needs, which
    /// mints at an explicitly constructed REDUCED context that is
    /// neither the ambient one nor any existing metavariable's, and
    /// which must carry the kind `elimMVar` computes
    /// (`MetavarContext.lean:1195`) rather than always `Natural`.
    ///
    /// A generalization, not an addition: duplicating the
    /// declare-and-intern sequence into a second minting function
    /// would be two places to keep in step for one behavior. Flagged
    /// per the M4b accessor precedent; behavior-neutral for
    /// `mk_aux_mvar`, whose two tests above pin the ambient/`Natural`
    /// pair it had before.
    pub(crate) fn mk_aux_mvar_at(
        &mut self,
        lctx: std::sync::Arc<crate::LocalCtxSnapshot>,
        ty: ExprId,
        kind: MVarKind,
    ) -> Result<(ExprId, MVarId), MetaError> {
        let idx = self.expr_mvar_gen;
        self.expr_mvar_gen += 1;
        let base = Some(self.view.store);
        let prefix_str = self.scratch.intern_str(base, "_leanr_aux_mvar")?;
        let prefix = self.scratch.name_str(base, None, prefix_str)?;
        let idx_id = self.scratch.intern_nat(base, &Nat::from(idx))?;
        let name = self.scratch.name_num(base, Some(prefix), idx_id)?;
        let id = MVarId(name);
        self.mctx.declare(
            id,
            MVarDecl {
                user_name: None,
                ty,
                lctx,
                kind,
            },
        );
        let expr = self.scratch.expr_mvar(base, Some(name))?;
        Ok((expr, id))
    }
```

- [ ] **Step 4: Run the tests and verify they pass**

Run: `cargo test -p leanr_meta assign::tests::mk_aux_mvar -- --nocapture`
Expected: both PASS.

- [ ] **Step 5: Run the neutrality gate for this refactor**

```bash
cargo test -p leanr_meta
cargo test -p leanr_elab
```

Expected: PASS, every record byte-identical. `mk_aux_mvar` is reached
from deep inside `is_def_eq` via `constApprox`, so this is the check that
matters — a behavior change here would show up as a moved record, not a
failed unit test.

- [ ] **Step 6: Measure the discriminator**

Change `mk_aux_mvar_at` to ignore its `lctx` parameter and use
`self.current_lctx()`. Expected:
`mk_aux_mvar_at_uses_the_given_context_and_kind` goes RED on the
`depth() == 0` assertion. **Revert.**

- [ ] **Step 7: Run the full gate and commit**

```bash
mise run ci
git add crates/leanr_meta/src/assign.rs
git commit -m "elimMVarDeps task 7: generalize mk_aux_mvar to mk_aux_mvar_at

elimMVar mints at an explicitly constructed reduced context with a
computed kind. Refactor, not addition — flagged per the M4b accessor
precedent; the ambient/Natural entry point is unchanged and pinned."
```

---

### Task 8: `mk_aux_mvar_type`, and the ldecl refusal

The auxiliary metavariable's type is the original's type abstracted over
`to_revert` and wrapped in `forall`s — oracle `mkAuxMVarType`
(`:1123-1168`).

The oracle branches on `LocalDecl.ldecl (nondep := …)`, and **leanr's
`LocalDecl` has no `nondep` field** (`local_ctx.rs:37-43`;
`mk_let_binding` takes it as a caller argument, `metactx.rs:835`). Any
ldecl arm written here would be guessing. So: refuse, shape-guarded and
named, mirroring `mk_binding`'s existing let-decl refusal.

The metavariable arm (`:1157-1163`) IS transcribed: `collect_forward_deps`
is its producer and it is five lines.

**Files:**
- Modify: `crates/leanr_meta/src/mk_binding.rs`
- Test: `crates/leanr_meta/src/mk_binding.rs` (`mod tests`)

**Interfaces:**
- Consumes: `abstract_range` — **not yet built** (Task 9). Until then
  `mk_aux_mvar_type` calls `abstract_fvars` directly and Task 9 swaps the
  call. This is called out explicitly in Task 9 Step 6.
- Produces: `mk_aux_mvar_type(&mut self, lctx: &LocalCtxSnapshot, xs:
  &[ExprId], ty: ExprId) -> Result<ExprId, MetaError>`

- [ ] **Step 1: Write the failing tests**

```rust
/// TDD RED/GREEN for plan task 8. `?m : Sort 0` reverted over
/// `[a : Sort 0]` gets the type `∀ (a : Sort 0), Sort 0`.
#[test]
fn mk_aux_mvar_type_wraps_the_reverted_binders() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        let snap = ctx.current_lctx();
        ctx.lctx_restore(cp);

        let ty = ctx
            .mk_aux_mvar_type(&snap, &[a], sort0)
            .expect("mk_aux_mvar_type");
        match ctx.node(ty) {
            Node::Forall { binder_type, body, .. } => {
                assert_eq!(binder_type, sort0, "the reverted binder's type");
                assert_eq!(body, sort0, "the original type, with nothing to abstract");
            }
            other => panic!("expected Forall, got {other:?}"),
        }
    });
}

/// The reverted binder must actually be ABSTRACTED out of the
/// original type, not merely prefixed: `?m : a` reverted over `[a]`
/// gets `∀ (a : Sort 0), #0`, never `∀ (a : Sort 0), <fvar a>`.
#[test]
fn mk_aux_mvar_type_abstracts_the_reverted_fvar_out_of_the_type() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        let snap = ctx.current_lctx();
        ctx.lctx_restore(cp);

        // The metavariable's own type IS the fvar.
        let ty = ctx.mk_aux_mvar_type(&snap, &[a], a).expect("mk_aux_mvar_type");
        match ctx.node(ty) {
            Node::Forall { body, .. } => assert!(
                matches!(ctx.node(body), Node::BVar { idx: 0 }),
                "the reverted fvar is abstracted to bvar 0 — leaving it as an \
                 fvar is precisely the bug this whole slice removes, one level \
                 down in the auxiliary metavariable's own type"
            ),
            other => panic!("expected Forall, got {other:?}"),
        }
    });
}

/// A let-declaration in `to_revert` is REFUSED, not guessed at:
/// leanr's LocalDecl carries no `nondep` bit, so the oracle's two
/// ldecl arms have no input.
#[test]
fn mk_aux_mvar_type_refuses_a_let_decl_in_to_revert() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let v = ctx
            .push_let_decl(None, sort0, sort0)
            .expect("push_let_decl");
        let snap = ctx.current_lctx();
        ctx.lctx_restore(cp);

        let err = ctx
            .mk_aux_mvar_type(&snap, &[v], sort0)
            .expect_err("a let-decl in to_revert is refused");
        assert!(
            format!("{err:?}").contains("let-decl"),
            "the refusal names itself: {err:?}"
        );
    });
}
```

- [ ] **Step 2: Run and verify failure**

Run: `cargo test -p leanr_meta mk_binding::tests::mk_aux_mvar_type -- --nocapture`
Expected: three FAILs.

- [ ] **Step 3: Implement**

Add to `mk_binding.rs`'s impl block. You will need
`use leanr_kernel::subst::abstract_fvars;` — check `metactx.rs`'s own
import for the exact path.

```rust
/// oracle: `mkAuxMVarType` (`:1123-1168`) — the type of the auxiliary
/// metavariable `elim_mvar` mints: the original's type abstracted
/// over `xs` and wrapped in one `forall` per reverted entry,
/// innermost last.
///
/// **Let-declarations are REFUSED, not handled.** The oracle branches
/// on `LocalDecl.ldecl (nondep := …)` (`:1131-1160`) and leanr's
/// `LocalDecl` carries no `nondep` bit at all
/// (`leanr_kernel/src/local_ctx.rs:37-43`; `mk_let_binding` takes it
/// as a caller argument, `metactx.rs:835`), so both ldecl arms have
/// no input. Writing one would be guessing, and a wrong `ExprId` is
/// worse than a named refusal — the same judgement, for the same
/// reason, as `mk_binding`'s existing
/// `"let-decl fvar in a cdecl telescope"` (`metactx.rs:769-772`).
///
/// The METAVARIABLE arm (`:1157-1163`) is transcribed: `xs` may carry
/// a metavariable as a "may dependency" once `collect_forward_deps`
/// has run, and the oracle wraps it in a `forall` over the
/// metavariable's own type with `binderInfoForMVars` (default
/// `.implicit`).
///
/// The oracle's `kind` and `usedLetOnly` parameters are absent here
/// because every arm that reads them is an ldecl arm (`:1140-1157`),
/// and those refuse. Adding parameters no branch can consult would be
/// surface without a producer.
#[allow(dead_code)]
pub(crate) fn mk_aux_mvar_type(
    &mut self,
    lctx: &LocalCtxSnapshot,
    xs: &[ExprId],
    ty: ExprId,
) -> Result<ExprId, MetaError> {
    let mut e = abstract_fvars(
        self.scratch,
        Some(self.view.store),
        ty,
        xs,
        &mut self.guard,
    )?;
    for i in (0..xs.len()).rev() {
        let x = xs[i];
        let (binder_name, binder_ty, binder_info) = match self.fvar_id_of(x) {
            Some(id) => {
                let decl = lctx.lctx().get(id).ok_or_else(|| {
                    MetaError::Infer("mk_aux_mvar_type: fvar not declared in the mvar's context".into())
                })?;
                if decl.value.is_some() {
                    return Err(MetaError::Infer(
                        "mk_aux_mvar_type: let-decl fvar in to_revert (leanr's LocalDecl \
                         carries no `nondep` bit, so the oracle's ldecl arms have no input)"
                            .into(),
                    ));
                }
                (decl.binder_name, decl.ty, decl.binder_info)
            }
            None => {
                // oracle `:1157-1163` — a "may dependency" metavariable.
                let Node::MVar { id: Some(n) } = self.node(x) else {
                    return Err(MetaError::Infer(
                        "mk_aux_mvar_type: to_revert entry is neither an fvar nor an mvar".into(),
                    ));
                };
                let decl = self.mctx.decl(crate::MVarId(n)).ok_or_else(|| {
                    MetaError::Infer("mk_aux_mvar_type: undeclared may-dependency mvar".into())
                })?;
                (decl.user_name, decl.ty, leanr_kernel::BinderInfo::Implicit)
            }
        };
        let binder_ty = abstract_fvars(
            self.scratch,
            Some(self.view.store),
            binder_ty,
            &xs[..i],
            &mut self.guard,
        )?;
        e = self.scratch.expr_forall(
            Some(self.view.store),
            binder_name,
            binder_ty,
            e,
            binder_info,
        )?;
    }
    Ok(e)
}
```

- [ ] **Step 4: Run the tests and verify they pass**

Run: `cargo test -p leanr_meta mk_binding::tests::mk_aux_mvar_type -- --nocapture`
Expected: all three PASS.

- [ ] **Step 5: Measure the discriminators**

| Mutation | Test that must go red |
| --- | --- |
| skip the first `abstract_fvars` (use `ty` directly as `e`) | `mk_aux_mvar_type_abstracts_the_reverted_fvar_out_of_the_type` |
| delete the `decl.value.is_some()` refusal | `mk_aux_mvar_type_refuses_a_let_decl_in_to_revert` |
| iterate `0..xs.len()` forward instead of `.rev()` | `mk_aux_mvar_type_wraps_the_reverted_binders` — **likely survives with one binder.** Add a two-binder case with distinguishable binder types and confirm it goes red, before reverting. |

- [ ] **Step 6: Run the full gate and commit**

```bash
mise run ci
git add crates/leanr_meta/src/mk_binding.rs
git commit -m "elimMVarDeps task 8: mkAuxMVarType, with an ldecl refusal

The oracle branches on LocalDecl.ldecl (nondep := ...); leanr's
LocalDecl carries no nondep bit, so both ldecl arms have no input.
Refuse rather than guess — a wrong ExprId is worse than a named seam."
```

---

### Task 9: `elim`, `visit`, `elim_app`, `elim_mvar`, `elim_mvar_deps`, `abstract_range`

The core. Everything before this was a helper.

**Files:**
- Modify: `crates/leanr_meta/src/mk_binding.rs`
- Test: `crates/leanr_meta/src/mk_binding.rs` (`mod tests`)

**Interfaces:**
- Consumes: Tasks 3–8, in full.
- Produces:
  - `MetaCtx::elim_mvar_deps(&mut self, xs: &[ExprId], e: ExprId) ->
    Result<ExprId, MetaError>`
  - `MetaCtx::abstract_range(&mut self, xs: &[ExprId], i: usize, e:
    ExprId) -> Result<ExprId, MetaError>`

- [ ] **Step 1: Write the failing tests**

```rust
/// TDD RED/GREEN for plan task 9, the DELAYED branch. A
/// `SyntheticOpaque` metavariable minted under `a`, met while
/// abstracting `[a]`, is replaced by `?new a`; the ORIGINAL is left
/// unassigned (it must only be assigned by the elaborator that made
/// it) and the NEW one is delayed-assigned back to it.
#[test]
fn elim_mvar_deps_delays_a_synthetic_opaque_metavariable() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        let lctx = ctx.current_lctx();
        let (m, mid) = ctx
            .mk_aux_mvar_at(lctx, sort0, crate::MVarKind::SyntheticOpaque)
            .expect("opaque mvar under the binder");

        let out = ctx.elim_mvar_deps(&[a], m).expect("elim_mvar_deps");

        assert_ne!(out, m, "the occurrence was rewritten");
        match ctx.node(out) {
            Node::App { f, arg } => {
                assert_eq!(arg, a, "applied to the reverted fvar");
                let Node::MVar { id: Some(n) } = ctx.node(f) else {
                    panic!("head should be the auxiliary metavariable");
                };
                let new_id = crate::MVarId(n);
                assert_ne!(new_id, mid, "a FRESH metavariable");
                assert!(
                    ctx.mctx().assignment(mid).is_none(),
                    "the syntheticOpaque original is NOT assigned — only the \
                     elaborator that created it may assign it"
                );
                let d = ctx
                    .mctx()
                    .delayed_assignment(new_id)
                    .expect("the new one is delayed-assigned back to the original");
                assert_eq!(d.mvar_id_pending, mid);
                assert_eq!(d.fvars, vec![a]);
                assert_eq!(
                    ctx.mctx().decl(new_id).expect("declared").lctx.depth(),
                    0,
                    "minted at the REDUCED context — `a` is erased"
                );
            }
            other => panic!("expected App, got {other:?}"),
        }
        ctx.lctx_restore(cp);
    });
}

/// The PLAIN-ASSIGN branch: a `Synthetic` metavariable is assigned
/// outright, `?m := ?new a`. Oracle `:1214-1215`.
#[test]
fn elim_mvar_deps_assigns_a_synthetic_metavariable_outright() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        let lctx = ctx.current_lctx();
        let (m, mid) = ctx
            .mk_aux_mvar_at(lctx, sort0, crate::MVarKind::Synthetic)
            .expect("synthetic mvar under the binder");

        let _ = ctx.elim_mvar_deps(&[a], m).expect("elim_mvar_deps");

        let assigned = ctx
            .mctx()
            .assignment(mid)
            .expect("a non-opaque original IS assigned outright");
        match ctx.node(assigned) {
            Node::App { arg, .. } => assert_eq!(arg, a),
            other => panic!("expected `?new a`, got {other:?}"),
        }
        assert!(
            !ctx.mctx().is_delayed_assigned(mid),
            "the plain branch uses no delayed assignment"
        );
        ctx.lctx_restore(cp);
    });
}

/// A metavariable whose own context does NOT contain any of `xs` is
/// left completely alone — `getInScope` is empty, oracle `:1180-1182`.
#[test]
fn elim_mvar_deps_leaves_an_out_of_scope_metavariable_alone() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

        // Minted OUTSIDE the binder: empty declared context.
        let (m, mid) = ctx.mk_aux_mvar(sort0).expect("mvar");
        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");

        let out = ctx.elim_mvar_deps(&[a], m).expect("elim_mvar_deps");
        assert_eq!(out, m, "untouched");
        assert!(ctx.mctx().assignment(mid).is_none());
        assert!(!ctx.mctx().is_delayed_assigned(mid));
        ctx.lctx_restore(cp);
    });
}

/// The fast path: a term with no expr metavariable is returned
/// unchanged, allocating nothing. Oracle `:1253-1254`.
#[test]
fn elim_mvar_deps_is_identity_on_a_metavariable_free_term() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let zero = ctx.scratch.level_zero(base).expect("level");
        let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
        let cp = ctx.lctx_checkpoint();
        let a = fresh_fvar(ctx, sort0, "a");
        let app = ctx.scratch.expr_app(base, a, sort0).expect("app");
        assert_eq!(ctx.elim_mvar_deps(&[a], app).expect("elim"), app);
        ctx.lctx_restore(cp);
    });
}
```

- [ ] **Step 2: Run and verify failure**

Run: `cargo test -p leanr_meta mk_binding::tests::elim_mvar_deps -- --nocapture`
Expected: four FAILs.

- [ ] **Step 3: Implement the core**

Add to `mk_binding.rs`. Put the cache type above the impl block:

```rust
/// oracle: `MkBinding.State.cache` (`:956-960`). Scoped to one
/// `elim_mvar_deps` call and reset again inside `elim_mvar` before
/// `mk_aux_mvar_type` (`:1205`, "we must reset the cache because
/// `toRevert` may not be equal to `xs`"), which is why it is a
/// threaded parameter rather than a `MetaCtx` field: its lifetime is a
/// matter of type here, not of discipline.
#[derive(Default)]
pub(crate) struct ElimCache(std::collections::HashMap<ExprId, ExprId>);
```

and the methods inside the impl block:

```rust
/// oracle: `elimMVarDeps` (`:1252-1257`).
///
/// Returns `e` unchanged when it carries no expr metavariable — the
/// fast path that makes every `mk_binding` call over a
/// metavariable-free body a strict no-op. For a body that DOES carry
/// one, behavior genuinely changes; see the design spec's § Risk
/// item 1 and the Task 1 findings document.
#[allow(dead_code)]
pub(crate) fn elim_mvar_deps(&mut self, xs: &[ExprId], e: ExprId) -> Result<ExprId, MetaError> {
    if !self.data(e).has_expr_mvar() {
        return Ok(e);
    }
    let mut cache = ElimCache::default();
    self.elim(xs, e, &mut cache)
}

/// oracle: `abstractRange` (`:1277-1279`) — `elimMVarDeps` over the
/// FULL `xs`, then abstract only the first `i`. The asymmetry is
/// deliberate and is the oracle's, not a simplification: a binder
/// type at position `i` has its metavariable dependencies eliminated
/// with respect to every telescope variable, including ones declared
/// after it.
#[allow(dead_code)]
pub(crate) fn abstract_range(
    &mut self,
    xs: &[ExprId],
    i: usize,
    e: ExprId,
) -> Result<ExprId, MetaError> {
    let e = self.elim_mvar_deps(xs, e)?;
    Ok(abstract_fvars(
        self.scratch,
        Some(self.view.store),
        e,
        &xs[..i],
        &mut self.guard,
    )?)
}

/// oracle: `elim` (`:1104`) — the cached entry to the traversal.
fn elim(
    &mut self,
    xs: &[ExprId],
    e: ExprId,
    cache: &mut ElimCache,
) -> Result<ExprId, MetaError> {
    if !self.data(e).has_expr_mvar() {
        return Ok(e);
    }
    if let Some(hit) = cache.0.get(&e) {
        return Ok(*hit);
    }
    self.step()?;
    let out = self.guarded(|ctx| ctx.visit(xs, e, cache))?;
    cache.0.insert(e, out);
    Ok(out)
}

/// oracle: `visit` (`:1101`) — the structural arms. An application is
/// decomposed into head plus arguments and routed to `elim_app`,
/// because the head being a metavariable is what `elim_mvar` needs to
/// see.
fn visit(
    &mut self,
    xs: &[ExprId],
    e: ExprId,
    cache: &mut ElimCache,
) -> Result<ExprId, MetaError> {
    match self.node(e) {
        Node::App { .. } => {
            let f = self.get_app_fn(e);
            let args = self.get_app_args(e);
            self.elim_app(xs, f, &args, cache)
        }
        Node::MVar { .. } => self.elim_app(xs, e, &[], cache),
        Node::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let t = self.elim(xs, binder_type, cache)?;
            let b = self.elim(xs, body, cache)?;
            if t == binder_type && b == body {
                Ok(e)
            } else {
                Ok(self
                    .scratch
                    .expr_lam(Some(self.view.store), binder_name, t, b, binder_info)?)
            }
        }
        Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let t = self.elim(xs, binder_type, cache)?;
            let b = self.elim(xs, body, cache)?;
            if t == binder_type && b == body {
                Ok(e)
            } else {
                Ok(self
                    .scratch
                    .expr_forall(Some(self.view.store), binder_name, t, b, binder_info)?)
            }
        }
        Node::LetE {
            binder_name,
            ty,
            value,
            body,
            non_dep,
        } => {
            let t = self.elim(xs, ty, cache)?;
            let v = self.elim(xs, value, cache)?;
            let b = self.elim(xs, body, cache)?;
            if t == ty && v == value && b == body {
                Ok(e)
            } else {
                Ok(self.scratch.expr_let(
                    Some(self.view.store),
                    binder_name,
                    t,
                    v,
                    b,
                    non_dep,
                )?)
            }
        }
        _ => Ok(e),
    }
}

/// oracle: `elimApp` (`:1230-1249`).
fn elim_app(
    &mut self,
    xs: &[ExprId],
    f: ExprId,
    args: &[ExprId],
    cache: &mut ElimCache,
) -> Result<ExprId, MetaError> {
    if let Node::MVar { id: Some(n) } = self.node(f) {
        let mid = crate::MVarId(n);
        match self.mctx.assignment(mid) {
            Some(new_f) => {
                if matches!(self.node(new_f), Node::Lam { .. }) {
                    // oracle `:1236-1239`: arguments can become
                    // irrelevant after beta, so beta FIRST, then elim.
                    let mut visited = Vec::with_capacity(args.len());
                    for a in args {
                        visited.push(self.elim(xs, *a, cache)?);
                    }
                    let mut rev = visited;
                    rev.reverse();
                    let applied = self.beta_rev(new_f, &rev)?;
                    return self.elim(xs, applied, cache);
                }
                return self.elim_app(xs, new_f, args, cache);
            }
            None => {
                let (out, _) = self.elim_mvar(xs, mid, args, cache)?;
                return Ok(out);
            }
        }
    }
    let f2 = self.elim(xs, f, cache)?;
    let mut out = f2;
    for a in args {
        let a2 = self.elim(xs, *a, cache)?;
        out = self.scratch.expr_app(Some(self.view.store), out, a2)?;
    }
    Ok(out)
}

/// oracle: `elimMVar` (`:1176-1229`). Returns the rewritten
/// occurrence and the `to_revert` list, mirroring the oracle's pair
/// (the second component is `revert`'s, which leanr has no caller
/// for, but keeping the shape keeps the transcription readable).
fn elim_mvar(
    &mut self,
    xs: &[ExprId],
    mvar_id: crate::MVarId,
    args: &[ExprId],
    cache: &mut ElimCache,
) -> Result<(ExprId, Vec<ExprId>), MetaError> {
    let Some(decl) = self.mctx.decl(mvar_id) else {
        return Err(MetaError::MVar(format!(
            "elim_mvar: metavariable {mvar_id:?} was never declared"
        )));
    };
    let kind = decl.kind;
    let decl_ty = decl.ty;
    let mvar_lctx = std::sync::Arc::clone(&decl.lctx);

    let to_revert = self.get_in_scope(&mvar_lctx, xs);
    let mvar_expr = self.scratch.expr_mvar(Some(self.view.store), Some(mvar_id.0))?;
    if to_revert.is_empty() {
        // oracle `:1180-1182`: nothing in this metavariable's context
        // is being abstracted, so it stands; only the arguments are
        // visited.
        let mut out = mvar_expr;
        for a in args {
            let a2 = self.elim(xs, *a, cache)?;
            out = self.scratch.expr_app(Some(self.view.store), out, a2)?;
        }
        return Ok((out, Vec::new()));
    }

    let mut visited = Vec::with_capacity(args.len());
    for a in args {
        visited.push(self.elim(xs, *a, cache)?);
    }

    let to_revert = self.collect_forward_deps(&mvar_lctx, to_revert)?;
    let new_lctx = self.reduce_local_context(&mvar_lctx, &to_revert)?;
    // oracle `:1205`: a FRESH cache here, because `to_revert` may
    // differ from `xs` and a cached rewrite for one is wrong for the
    // other.
    let new_ty = self.mk_aux_mvar_type(&mvar_lctx, &to_revert, decl_ty)?;
    let (new_mvar, new_id) = self.mk_aux_mvar_at(new_lctx, new_ty, kind)?;
    let result = self.mk_mvar_app(new_mvar, &to_revert)?;

    if kind != crate::MVarKind::SyntheticOpaque {
        // oracle `:1214-1215`.
        self.mctx.assign(mvar_id, result)?;
    } else {
        // oracle `:1216-1228`. A syntheticOpaque metavariable must
        // only ever be assigned by the elaborator that created it, so
        // the NEW one is delayed-assigned back to the original
        // instead. `nested` carries any delayed assignment the
        // original already had (`:1224-1226`).
        let (pending, nested) = match self.mctx.delayed_assignment(mvar_id) {
            Some(d) => (d.mvar_id_pending, d.fvars.clone()),
            None => (mvar_id, Vec::new()),
        };
        let mut fvars = to_revert.clone();
        fvars.extend(nested);
        self.mctx.assign_delayed(new_id, fvars, pending)?;
    }

    let mut out = result;
    for a in visited {
        out = self.scratch.expr_app(Some(self.view.store), out, a)?;
    }
    Ok((out, to_revert))
}
```

- [ ] **Step 4: Run the tests and verify they pass**

Run: `cargo test -p leanr_meta mk_binding::tests -- --nocapture`
Expected: all PASS.

- [ ] **Step 5: Measure the discriminators**

| Mutation | Test that must go red |
| --- | --- |
| in `elim_mvar`, take the plain-assign branch for every kind | `elim_mvar_deps_delays_a_synthetic_opaque_metavariable` |
| in `elim_mvar`, take the delayed branch for every kind | `elim_mvar_deps_assigns_a_synthetic_metavariable_outright` |
| in `elim_mvar`, drop the `to_revert.is_empty()` early return | `elim_mvar_deps_leaves_an_out_of_scope_metavariable_alone` |
| in `elim_mvar_deps`, drop the `has_expr_mvar` fast path | **likely survives** — the slow path returns the same term. That is fine; the fast path is an optimization, not a behavior. Note it and move on rather than inventing a test for it. |

The first two are the `MVarKind::SyntheticOpaque` discriminator this
repo has been missing — record that in the commit message.

- [ ] **Step 6: Swap `mk_aux_mvar_type`'s abstraction onto `abstract_range`**

Task 8 built `mk_aux_mvar_type` against `abstract_fvars` because
`abstract_range` did not exist yet. The oracle's `mkAuxMVarType` uses
`abstractRangeAux` (`:1165-1167`), which is `elim` then abstract. Change
both `abstract_fvars` calls in `mk_aux_mvar_type` to
`self.abstract_range(xs, xs.len(), ty)?` and
`self.abstract_range(xs, i, binder_ty)?` respectively.

Re-run Step 4. Expected: still PASS. If any test moves, the two are not
equivalent on that input and you have found something the plan did not
anticipate — stop and report.

- [ ] **Step 7: Run the whole workspace**

```bash
cargo test --workspace
```

Expected: PASS with every record byte-identical — nothing calls
`elim_mvar_deps` from production code yet.

- [ ] **Step 8: Run the full gate and commit**

```bash
mise run ci
git add crates/leanr_meta/src/mk_binding.rs
git commit -m "elimMVarDeps task 9: elim, visit, elimApp, elimMVar, abstractRange

The core. The two branches are the SyntheticOpaque discriminator this
tree has been missing: a syntheticOpaque original is left unassigned and
the auxiliary metavariable is delayed-assigned back to it, while any
other kind is assigned outright."
```

---

### Task 10: wire into `mk_binding`, and run the neutrality gate

The first task whose changes are observable in production.

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs:737` (`mk_binding`)
- Modify: `crates/leanr_meta/src/mk_binding.rs`,
  `crates/leanr_meta/src/local_snapshot.rs` (remove
  `#[allow(dead_code)]`)

**Interfaces:**
- Consumes: `abstract_range` / `elim_mvar_deps` (Task 9).
- Produces: `mk_forall` / `mk_lambda` now eliminate metavariable
  dependencies. Signatures unchanged.

- [ ] **Step 1: Insert the two `elim_mvar_deps` calls**

In `MetaCtx::mk_binding`, insert before `let mut r = body;`:

```rust
        // oracle: `mkBinding` abstracts through `abstractRange`
        // (`MetavarContext.lean:1313`), which runs `elimMVarDeps` over
        // the FULL telescope before abstracting. The peel-one-fvar-at-
        // a-time loop below is leanr's own oracle-verified abstraction
        // (transcribed from `infer.rs::rebuild_forall`), so the
        // insertion points are what change, not the loop.
        let body = self.elim_mvar_deps(fvars, body)?;
```

and inside the loop, immediately before the `let ty2 = abstract_fvars(`
call, replace that call's input with an eliminated one:

```rust
            // oracle: `abstractRange xs i type` (`:1320`) — note the
            // FULL `fvars`, not `&fvars[..i]`: a binder type has its
            // metavariable dependencies eliminated with respect to
            // every telescope variable, including ones declared after
            // it.
            let ty = self.elim_mvar_deps(fvars, ty)?;
            let ty2 = abstract_fvars(
                self.scratch,
                Some(self.view.store),
                ty,
                &fvars[..i],
                &mut self.guard,
            )?;
```

- [ ] **Step 2: Remove every `#[allow(dead_code)]` added in Tasks 2–9**

```bash
grep -rn "allow(dead_code)" crates/leanr_meta/src/mk_binding.rs crates/leanr_meta/src/local_snapshot.rs crates/leanr_meta/src/assign.rs
```

Delete each one this plan added. Anything that clippy now reports as
genuinely dead is a function with no caller — report it rather than
silencing it.

- [ ] **Step 3: Run the elaboration corpus**

```bash
cargo test -p leanr_elab --test oracle_elab
```

Expected: PASS, 107 records byte-identical.

**If a record moved:** open the Task 1 findings document. If the record
is on its affected list, this is the expected population and the move is
a real divergence to diagnose, not a surprise — record the exact
before/after and report. If it is NOT on that list, something outside the
measured population changed, which is more serious; stop and report.
**Never re-baseline.**

**The most likely diagnosis, and it is the spec's § Risk item 2.** A
record on the affected list that moves, or that now fails with a
type-class synthesis error, points at the reconciliation step rather
than at this slice's own code: `elim_mvar`'s plain-assign branch leaves
`?m := ?new ys`, and `synthesize_inst_mvar_core`
(`crates/leanr_elab/src/synthetic/ladder.rs:207-234`) then runs
`is_def_eq(old_val, val)` with `old_val = ?new ys` — a Miller pattern,
an auxiliary metavariable applied to distinct free variables. If
leanr's `process_assignment` cannot solve that shape, this is where it
shows. Confirm by probing `is_def_eq` on the pattern directly before
concluding anything about `mk_binding`. That gap would be **inherited,
not introduced** — report it as its own finding rather than widening
this slice to fix it.

- [ ] **Step 4: Run the remaining corpora**

```bash
cargo test -p leanr_meta
cargo test --workspace
mise run meta:fast
mise run elab:fast
mise run parse:mathlib:fast
```

Expected: all PASS. `parse:mathlib:fast` needs `mise run mathlib:fetch`
once; if the Mathlib checkout is absent, note that it was skipped rather
than claiming it passed.

- [ ] **Step 5: Confirm the seam test now trips**

```bash
cargo test -p leanr_elab --test seam_audit postponed_coe_under_a_binder
```

Expected: **FAIL** on the `assert_ne!` — "leanr now agrees with the
oracle here — `elimMVarDeps` (or an equivalent) has landed." That failure
is the slice working. Task 11 retires the test.

If it still passes, `elim_mvar_deps` is not reaching the coercion
metavariable. Do not proceed to Task 11 — diagnose here.

- [ ] **Step 6: Measure the discriminator**

Delete the body-side `elim_mvar_deps` call from Step 1. Expected: the
seam test goes back to passing (the `assert_ne!` holds again). **Revert.**
This is the whole slice's kill, so confirm it rather than assuming it.

- [ ] **Step 7: Run the full gate and commit**

```bash
mise run ci
git add crates/leanr_meta/src/metactx.rs crates/leanr_meta/src/mk_binding.rs crates/leanr_meta/src/local_snapshot.rs crates/leanr_meta/src/assign.rs
git commit -m "elimMVarDeps task 10: run it inside mk_binding

The two insertion points are the oracle's own: elimMVarDeps over the
full telescope for the body, and again for each binder type before
abstracting only the prefix. Every committed record stays
byte-identical; the seam_audit characterization now trips, which is the
point of it."
```

---

### Task 11: the differential records, the discriminator, and the seam retirement

Five records, one per mechanism. Each must die if its mechanism is
removed — and **none of these source strings has been run**, so every
stated kill below is a hypothesis you verify, not a fact you inherit.

**Files:**
- Modify: `tests/fixtures/elab/Elab0.lean`
- Modify: `tests/fixtures/elab/dump_elab.lean`
- Regenerate: `tests/fixtures/elab/Elab0.olean`,
  `tests/fixtures/elab/elab-queries.jsonl`
- Modify: `crates/leanr_elab/tests/seam_audit.rs`

**Interfaces:**
- Consumes: the whole slice.
- Produces: the corpus rows Task 12's retirement text refers to.

- [ ] **Step 1: Add the first record and confirm it captures the bug**

In `tests/fixtures/elab/dump_elab.lean`, extend `coeQueries` (`:630`):

```lean
  , ("coe/postponedThenResumedUnderBinder", "fun (n : Nat) => pairW n Nat.zero")
```

This is `seam_audit.rs:727`'s exact query. `Wrapper`, `pairW` and
`instCoeNatWrapper` already exist in `Elab0.lean:574-579`, so no new
declarations are needed for it.

- [ ] **Step 2: Construct the remaining four**

Each needs a source string that reaches its mechanism. Build them one at
a time, and **verify reachability before adding the record** by running
the query through `support::elab_and_synthesize` in a scratch test and
confirming the mechanism fires (a temporary `eprintln!` in
`elim_mvar` naming the branch and `to_revert.len()` is the cheapest
way).

| Record id | Mechanism | Shape to build |
| --- | --- | --- |
| `elimMVarDeps/pendingInstanceUnderBinder` | plain-assign branch | a `fun (n : Nat) => …` whose body carries an instance-implicit argument that is still `.undef` at application finalization, so it survives to `mk_lambda` as a `Synthetic` metavariable |
| `elimMVarDeps/nestedBindersPartialScope` | `get_in_scope`'s filter | nested `fun`s where the postponed metavariable's context holds BOTH binders and the inner `mk_lambda`'s telescope holds one — a "revert everything in the metavariable's context" bug diverges here |
| `elimMVarDeps/dependentPairForwardDep` | `collect_forward_deps` | a `coe/sortDomain`-shaped dependent pair (`fun (c : Carrier) (x : c) => …`, `Elab0.lean:595`) carrying a postponed metavariable, so a later declaration's TYPE mentions the reverted variable |
| — | `reduce_local_context` | **a unit test, not a record**: assert the auxiliary metavariable's declared context does not contain the reverted fvar. `elim_mvar_deps_delays_a_synthetic_opaque_metavariable` (Task 9) already asserts `depth() == 0`; extend it to a two-binder context so it asserts the survivor is still there |

Add whatever `Elab0.lean` declarations these need, in the style of the
existing `Wrapper`/`pairW` block (`:568-579`) — a comment above each new
declaration saying which record it serves and why.

**If a shape turns out not to be constructible** against this fixture
environment, say so explicitly in the commit message and in the Task 12
documentation rather than shipping a record that does not reach its
mechanism. A record that cannot discriminate is worse than an absent one:
it reads as coverage.

- [ ] **Step 3: Regenerate the fixtures**

```bash
mise run fixtures:regen-elab
git diff --stat tests/fixtures/elab/
```

Expected: `elab-queries.jsonl` gains exactly the new records and
`Elab0.olean` changes only if you edited `Elab0.lean`. **Every
pre-existing line in `elab-queries.jsonl` must be unchanged.** If an
existing record moved, the regen environment drifted — stop and report
rather than committing it.

- [ ] **Step 4: Run the corpus**

```bash
cargo test -p leanr_elab --test oracle_elab
```

Expected: PASS, now with 107 + N records, including the no-`fvar`
class-wide assertion at `oracle_elab.rs:169-192`.

- [ ] **Step 5: Measure every record's kill**

For each new record, apply the mutation that removes its mechanism, run
Step 4, confirm **that record** fails, and revert:

| Record | Mutation |
| --- | --- |
| `coe/postponedThenResumedUnderBinder` | in `elim_mvar`, take the plain-assign branch for `SyntheticOpaque` too |
| `elimMVarDeps/pendingInstanceUnderBinder` | in `elim_mvar`, take the delayed branch for every kind |
| `elimMVarDeps/nestedBindersPartialScope` | `get_in_scope` returns `xs.to_vec()` |
| `elimMVarDeps/dependentPairForwardDep` | `collect_forward_deps` returns `to_revert` unchanged |

**A record whose mutation it survives is not carrying its stated kill.**
Either find a shape that does, or delete the record and document the
gap. Do not keep it and describe it as coverage.

- [ ] **Step 6: Retire the seam characterization**

In `crates/leanr_elab/tests/seam_audit.rs:727`, follow the instructions
the test itself carries: replace the `assert_ne!` with the positive
assertion and delete the now-false framing.

```rust
/// The `elimMVarDeps` gap is CLOSED (implemented in
/// `leanr_meta/src/mk_binding.rs`). This test was the executable
/// characterization of the divergence; it is kept, inverted, as the
/// regression gate — `fun (n : Nat) => pairW n Nat.zero` postpones a
/// `.coe` metavariable under a binder, resumes it after the binder has
/// closed, and must now agree with the oracle byte-for-byte.
///
/// `coe/postponedThenResumedUnderBinder` covers the same query in the
/// corpus. This stays as well: it carries the oracle's answer inline,
/// so a corpus regeneration cannot silently move the target.
#[test]
fn postponed_coe_under_a_binder_abstracts_via_elim_mvar_deps() {
    // ... ORACLE const unchanged ...
    let leanr = support::elab_and_synthesize("fun (n : Nat) => pairW n Nat.zero")
        .expect("the coercion resolves and the binder abstracts")
        .to_string();
    assert_eq!(leanr, ORACLE);
}
```

Rename the test as shown, and update `seam_audit.rs`'s module doc
(`:30`), which names the old test.

- [ ] **Step 7: Run everything**

```bash
cargo test --workspace
mise run ci
```

Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add tests/fixtures/elab/ crates/leanr_elab/tests/seam_audit.rs
git commit -m "elimMVarDeps task 11: the differential records and the seam retirement

One record per mechanism, each verified by applying the mutation that
removes its mechanism and watching that record fail. The seam_audit
characterization is inverted from assert_ne to assert_eq, as its own
retirement instructions specified."
```

---

### Task 12: retire the documentation the gap left behind

The gap is documented in five places. All five said what was true; none
is true now. Leaving any one of them is worse than never having written
it — a future reader would design around a seam that no longer exists.

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs:710-736`
- Modify: `crates/leanr_meta/src/whnf.rs` (the retired SEAM comment, if
  Task 6 left any trace)
- Modify: `tests/fixtures/elab/dump_elab.lean` (the `coeQueries` doc
  block)
- Modify: `crates/leanr_elab/tests/oracle_elab.rs:135-192`
- Modify: `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md`

**Interfaces:**
- Consumes: Tasks 10–11.
- Produces: nothing executable.

- [ ] **Step 1: `metactx.rs` — delete the `# UNMODELLED` heading**

Remove the entire `# UNMODELLED: MkBinding.elimMVarDeps` section from
`mk_binding`'s doc comment (`:710-736`) and replace it with a short
statement of what the function now does:

```rust
    /// Runs `elim_mvar_deps` (`mk_binding.rs`) over the body and over
    /// each binder type before abstracting, exactly as the oracle's
    /// `mkBinding` abstracts through `abstractRange`
    /// (`MetavarContext.lean:1313`, `:1277-1279`). An unassigned
    /// metavariable whose own local context contains a telescope free
    /// variable is therefore replaced by an auxiliary metavariable
    /// applied to it, and abstracts like any other argument.
    ///
    /// The let-decl refusal below is unchanged, and is joined by
    /// `mk_aux_mvar_type`'s own ldecl refusal for the same reason:
    /// leanr's `LocalDecl` carries no `nondep` bit.
```

- [ ] **Step 2: `oracle_elab.rs` — rewrite the leaked-fvar rationale**

The comment block at `:135-192` explains the assertion by citing the
gap. The assertion itself stays — it is a good class-wide invariant —
but its justification changes from "this is the known gap" to "every
corpus query is a closed term, so an `fvar` in an answer is a bug".
Rewrite it, and delete the reference to the old seam test name.

- [ ] **Step 3: `dump_elab.lean` — update the `coeQueries` doc block**

It records that `coe/postponedThenResumed` is the binder-free case
because the binder-ful one could not pass. Replace with a note that both
now ship, and why the pair is worth keeping (binder-free and binder-ful
exercise different `elim_mvar` paths).

- [ ] **Step 4: `whnf.rs` — confirm the SEAM comment is gone**

```bash
grep -n "SEAM" crates/leanr_meta/src/whnf.rs | grep -i delayed
```

Expected: no output. Task 6 replaced it; this is the check that it did.

- [ ] **Step 5: Amend the M4b-3 spec**

Add a short amendment to
`docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md`
recording that the `elimMVarDeps` slice landed and P5 is next — the same
shape as § Amendment 6 item 6, which sequenced this slice. Cite this
plan and the design spec by path.

- [ ] **Step 6: Verify no stale reference survives**

```bash
grep -rn "UNMODELLED\|elimMVarDeps\|elim_mvar_deps" crates/ tests/ docs/ --include=*.rs --include=*.lean --include=*.md | grep -v target
```

Read every hit. Each should now be either a live citation in
`mk_binding.rs` / the design spec / this plan, or the retired-and-updated
text from Steps 1–5. Any surviving "not modelled" / "pending" / "the gap"
phrasing about this mechanism is stale — fix it.

- [ ] **Step 7: Run everything and commit**

```bash
cargo test --workspace
mise run ci
git add -A
git commit -m "elimMVarDeps task 12: retire the gap documentation

Five places described a gap that no longer exists. Leaving any one is
worse than never having written it: a future reader would design around
a seam that is gone."
```

---

## Verification summary

Run at the end of the slice, before opening the PR:

```bash
mise run ci                      # fmt + clippy + tests
cargo test --workspace
mise run meta:fast               # oracle_fast + oracle_synth
mise run elab:fast               # the 107 + N elaboration records
mise run parse:mathlib:fast      # unaffected, but cheap and gates the parser
```

**Acceptance:**

1. `fun (n : Nat) => pairW n Nat.zero` elaborates to the oracle's answer
   byte-for-byte — the divergence `seam_audit.rs` characterized is gone,
   and that test now asserts agreement.
2. No corpus answer contains an `fvar` node
   (`oracle_elab.rs`'s class-wide assertion).
3. Every pre-existing record is byte-identical; the only corpus growth
   is Task 11's records.
4. `MVarKind::SyntheticOpaque` has a discriminator: mutating
   `elim_mvar`'s branch either way fails a named test.
5. A let-declaration in `to_revert` produces a named `MetaError`, never
   a wrong `ExprId`.

## What this plan deliberately does NOT do

Each is named in the design spec's § What this ships, and each stays a
seam with no producer in leanr:

- `mkAuxMVarType`'s ldecl arms (`nondep` does not exist on
  `LocalDecl`) — a refusal instead.
- `revert` (no tactic framework), `preserveOrder`, `etaReduce`,
  `usedOnly`, `mvarIdsToAbstract`, `quotContext`.
- `numScopeArgs`, the occurs check's delayed channel, and `isDefEq`'s
  delayed arms. Task 1's probe plus Task 10's byte-identical corpora are
  what make "unreached" a measurement rather than a claim.
- `newLocalInsts` — not a seam of this slice; leanr has no
  `LocalInstance` concept at all (`instances.rs:96`).
- Any `leanr_elab/src` change. `synthesizeInstMVarCore`'s `is_assigned`
  arm already exists at `synthetic/ladder.rs:207-234`, which is why the
  plain-assign branch needs no elaborator work.
