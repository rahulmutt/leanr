# M4b-2 Plan 1 (Foundation) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land the local-context foundation for `leanr_elab` binders — the `MetaCtx` `lctx_checkpoint`/`push_local_decl`/`lctx_restore` + `mk_forall` accessors — and the three universal-quantifier elaborators (`forall`, `arrow`, `depArrow`), differentially verified against the pinned oracle.

**Architecture:** Two additive, TCB-neutral accessors on `leanr_meta`'s `MetaCtx` expose the local-context telescope machinery `leanr_meta` already uses internally (`save → mk_local_decl → restore`, `abstract_fvars` + `expr_forall`). A new `leanr_elab::builtin::binder` module elaborates the three type-former kinds on top of them: `arrow` builds a non-dependent `forallE` directly (no fvar); `forall`/`depArrow` introduce fvars via `push_local_decl` (bracketed by `lctx_checkpoint`/`lctx_restore`) and abstract via `mk_forall`. The entry-point pipeline and the synthetic-mvar fixpoint are **not** touched in this plan (they arrive in Plan 2 with postponement).

**Tech Stack:** Rust (workspace crates `leanr_meta`, `leanr_elab`, `leanr_kernel`, `leanr_syntax`); Lean 4 v4.33.0-rc1 as the differential oracle; `mise` task runner.

## Global Constraints

- **Kernel/olean TCB is byte-untouched.** `leanr_kernel` depends on no workspace crate and is not modified in this plan.
- **`leanr_meta/src` accessor precedent.** New public methods on `leanr_meta` must be purely **additive**, **TCB-neutral**, and **behavior-neutral** (they expose capability `leanr_meta` already exercises internally). Any non-additive / behavior-changing `leanr_meta` change is out of scope and must be flagged.
- **Named-seam discipline.** Every dispatch arm is a named seam; unregistered kinds fall through to `ElabError::UnsupportedSyntax(kind)` — never a panic, never a wrong `ExprId`.
- **Oracle discipline.** Correctness is byte-for-byte agreement with the pinned oracle's canonical `Expr` via the `oracle_elab` gate. The `lean-toolchain` pin (`leanprover/lean4:v4.33.0-rc1`) is not bumped.
- **Binder names are erased** by the differential encoder (`encode_expr`), so the exact `binder_name` on a `forallE`/fvar decl never affects the gate; correctness of *structure* (domain, body, binder-info, de Bruijn indices) is what is verified.
- **Entry point unchanged in this plan.** `elab_term_ensuring_type → instantiate_mvars` stays as M4b-1 shipped it. No `synthesize_synthetic_mvars`, no new `TermElabM` fields — those land in Plan 2 (see the design spec's § canonical entry-point pipeline correction).

## Reference: pinned-oracle constructions (v4.33.0-rc1, `Lean/Elab/Binders.lean`)

```lean
-- :278  forall (bracketed binders, no trailing `: ty` → no macro expansion)
elabForall stx _ := match stx with
  | `(forall $binders*, $term) => elabBinders binders fun xs => do
      let e ← elabType term; mkForallFVars xs e

-- :293  arrow (non-dependent)
elabArrow stx _ := match stx with
  | `($dom:term -> $rng) => do
      let dom ← elabType dom; let rng ← elabType rng
      return mkForall `_internal.a BinderInfo.default dom rng   -- name erased downstream

-- :310  depArrow (single bracketed binder, dependent)
elabDepArrow stx _ :=
  let binder := stx[0]; let term := stx[2]
  elabBinders #[binder] fun xs => mkForallFVars xs (← elabType term)
```

`elabBinders`/`mkForallFVars` map onto this plan's `push_local_decl` + `mk_forall`. `elabType t` maps onto this plan's `elab_type` helper (a fresh `Sort ?u`, then `elab_term_ensuring_type`).

## File Structure

- **Modify** `crates/leanr_meta/src/metactx.rs` — add `lctx_checkpoint`, `push_local_decl`, `lctx_restore`, and `mk_forall` methods to `impl<'e> MetaCtx<'e>` (near the existing `store`/`mctx` accessors, ~line 384). Add imports for `abstract_fvars`, `BinderInfo`, and `Node` if not already present.
- **Create** `crates/leanr_elab/src/builtin/binder.rs` — `elab_arrow`, `elab_forall`, `elab_dep_arrow`, plus the private helpers `elab_type` and `extract_binder_group` / `BinderGroup`.
- **Modify** `crates/leanr_elab/src/builtin/mod.rs` — add `pub mod binder;`.
- **Modify** `crates/leanr_elab/src/dispatch.rs` — register the three kind names in `elaborator_name_for` and add three arms to `dispatch`; update the "Deferred" doc comment.
- **Create** `crates/leanr_elab/tests/binder_smoke.rs` — fast, hermetic leanr-side structural tests (committed `Elab0.olean`, no Lean toolchain needed). Grows one block per elaborator task.
- **Modify** `tests/fixtures/elab/dump_elab.lean` — add a `binderQueries` list and concatenate it into the emit loop (Task 5).
- **Modify** (only if a corpus term needs a new constant) `tests/fixtures/elab/Elab0.lean` — none expected; the corpus terms use only `Nat`/`Type`, already in scope.

---

### Task 1: `MetaCtx` local-context accessors (`lctx_checkpoint` / `push_local_decl` / `lctx_restore`) + `mk_forall`

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs`
- Test: `crates/leanr_meta/src/metactx.rs` (add a `#[cfg(test)] mod` case, or extend the existing test module)

**Interfaces:**
- Produces:
  - `pub fn lctx_checkpoint(&mut self) -> usize`
  - `pub fn push_local_decl(&mut self, name: Option<NameId>, ty: ExprId, bi: BinderInfo) -> Result<ExprId, MetaError>`
  - `pub fn lctx_restore(&mut self, checkpoint: usize)`
  - `pub fn mk_forall(&mut self, fvars: &[ExprId], body: ExprId) -> Result<ExprId, MetaError>`
- Consumes (existing, in-crate): `self.lctx` (`LocalContext`), `self.scratch` (`&mut Store`), `self.fvar_gen` (`FVarIdGen`), `self.guard` (`RecGuard`), `self.view.store` (`&Store`), `self.node(id) -> Node`, `abstract_fvars`, `Store::expr_forall`, `LocalContext::{save, mk_local_decl, restore, get}`.

**Why a checkpoint/push/restore trio rather than a closure `with_local_decl`:** the design spec sketches `with_local_decl(name, ty, bi, f)` whose closure receives `&mut MetaCtx`. But the binder elaborators live one layer up and need `&mut TermElabM` (which *owns* the `MetaCtx` plus `view`/level counters/`level_names`); a closure taking `&mut MetaCtx` cannot reach that outer state without splitting `TermElabM`. The trio exposes the identical capability (`save` → `mk_local_decl` → `restore`, already used internally at assign.rs:563-566/633) as three flat calls, so the `leanr_elab` telescope driver (Task 3) can bracket the checkpoint in `TermElabM` space with restore-on-error. This is the same additive/TCB-neutral seam, just closure-free.

- [ ] **Step 1: Confirm imports present in `metactx.rs`**

At the top of `crates/leanr_meta/src/metactx.rs`, ensure these are imported (add any missing — they are all already used elsewhere in the crate, so this is import-plumbing only):

```rust
use leanr_kernel::abstract_fvars;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;
// (LocalContext, Store, MetaError, RecGuard are already in scope in this file)
```

- [ ] **Step 2: Write the failing test**

Add to the test module at the bottom of `crates/leanr_meta/src/metactx.rs` (mirror the setup of the existing tests in that file — they build a `MetaCtx` over a small `testenv`). The test declares a local `(x : Nat)`, checks the fvar is visible inside the closure and gone after, then abstracts `x` back into `∀ (x : Nat), x`:

```rust
#[test]
fn push_local_decl_scopes_and_mk_forall_abstracts() {
    with_test_ctx(|ctx| {
        let nat = ctx.const_nat();          // helper: the `Nat` const ExprId (see note)
        let checkpoint = ctx.lctx_checkpoint();
        let fvar = ctx
            .push_local_decl(None, nat, BinderInfo::Default)
            .expect("push_local_decl");
        // fvar is a declared local while the checkpoint is open
        assert!(matches!(ctx.node(fvar), Node::FVar { .. }));
        // body = the fvar itself → ∀ (x : Nat), x  (a `pi` whose body is `bvar 0`)
        let built = ctx
            .mk_forall(std::slice::from_ref(&fvar), fvar)
            .expect("mk_forall");
        ctx.lctx_restore(checkpoint);
        // lctx restored: the decl count is back to the checkpoint
        assert_eq!(ctx.lctx.save(), checkpoint);
        // built is a Forall node whose body is bvar 0
        match ctx.node(built) {
            Node::Forall { body, .. } => {
                assert!(matches!(ctx.node(body), Node::BVar { idx: 0 }));
            }
            other => panic!("expected Forall, got {other:?}"),
        }
    });
}
```

Note: `with_test_ctx` and `const_nat` are thin test helpers — reuse the file's existing test-context builder (the tests in this file already build a `MetaCtx` over a small `testenv`; `const_nat` is the `Nat` const `ExprId` in that env). The test module is inside the crate, so `ctx.lctx.save()` and `ctx.node(..)` are reachable directly; do not add public API just for the test. If `Node::FVar`/`Node::BVar` field shapes differ, copy the exact patterns from `infer.rs::rebuild_forall` (infer.rs:817) and the crate's bvar handling.

- [ ] **Step 3: Run test to verify it fails**

Run: `cargo test -p leanr_meta push_local_decl_scopes_and_mk_forall_abstracts`
Expected: FAIL to compile with "no method named `lctx_checkpoint`" / "`push_local_decl`" / "`mk_forall`".

- [ ] **Step 4: Implement the accessors**

Add to `impl<'e> MetaCtx<'e>` in `crates/leanr_meta/src/metactx.rs` (after the `store`/`store_mut` accessors, ~line 390):

```rust
/// Record the current `lctx` depth. Pair with `lctx_restore` to bracket
/// a telescope (the `flet<local_ctx> save_lctx` idiom, assign.rs:563).
/// Additive + behavior-neutral.
pub fn lctx_checkpoint(&mut self) -> usize {
    self.lctx.save()
}

/// Restore `lctx` to a `lctx_checkpoint` depth, dropping every decl
/// added since (fvar ids are globally unique via `fvar_gen`, so the
/// truncation is exact).
pub fn lctx_restore(&mut self, checkpoint: usize) {
    self.lctx.restore(checkpoint);
}

/// Mint a cdecl fvar `(name : ty)` with binder-info `bi` into the ambient
/// `lctx` and return its `Expr::fvar`. The additive elab-layer seam for
/// `mk_local_decl`, already used internally at assign.rs:633. The caller
/// brackets with `lctx_checkpoint`/`lctx_restore`.
pub fn push_local_decl(
    &mut self,
    name: Option<NameId>,
    ty: ExprId,
    bi: BinderInfo,
) -> Result<ExprId, MetaError> {
    let fvar = self.lctx.mk_local_decl(
        self.scratch,
        Some(self.view.store),
        &mut self.fvar_gen,
        name,
        ty,
        bi,
    )?;
    Ok(fvar)
}

/// oracle: `mkForallFVars` (the cdecl case). Abstract `body` over the
/// telescope `fvars` (each an fvar declared in `self.lctx`, no let
/// value in this plan) and wrap in nested `forallE`, innermost fvar
/// last. Transcribed from `infer.rs::rebuild_forall`'s `None`-value
/// branch (infer.rs:802), the crate's own oracle-verified abstraction
/// loop, since the kernel's `mk_pi` is not re-exported from
/// `leanr_kernel`.
pub fn mk_forall(&mut self, fvars: &[ExprId], body: ExprId) -> Result<ExprId, MetaError> {
    let mut r = body;
    let mut i = fvars.len();
    while i > 0 {
        i -= 1;
        r = abstract_fvars(
            self.scratch,
            Some(self.view.store),
            r,
            std::slice::from_ref(&fvars[i]),
            &mut self.guard,
        )?;
        let (binder_name, ty, binder_info) = match self.node(fvars[i]) {
            Node::FVar { id: Some(id) } => {
                let decl = self.lctx.get(id).ok_or_else(|| {
                    MetaError::Infer("mk_forall: telescope fvar not declared".into())
                })?;
                (decl.binder_name, decl.ty, decl.binder_info)
            }
            _ => {
                return Err(MetaError::Infer(
                    "mk_forall: telescope entry is not an fvar".into(),
                ))
            }
        };
        let ty2 = abstract_fvars(
            self.scratch,
            Some(self.view.store),
            ty,
            &fvars[..i],
            &mut self.guard,
        )?;
        r = self
            .scratch
            .expr_forall(Some(self.view.store), binder_name, ty2, r, binder_info)?;
    }
    Ok(r)
}
```

Note: `self.node(...)`, `self.lctx`, `self.scratch`, `self.guard`, `self.view`, `self.fvar_gen` are all in-crate (`pub(crate)`); the `?` on `mk_local_decl`/`expr_forall` converts `KernelError → MetaError` via the existing `From` impl. If `Node::FVar`'s field is named differently than `{ id: Some(id) }` or `Node::BVar`'s than `{ idx }`, match the exact variant shape used in `infer.rs::rebuild_forall` (infer.rs:817) and `infer.rs`'s bvar handling — copy those patterns verbatim.

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p leanr_meta push_local_decl_scopes_and_mk_forall_abstracts`
Expected: PASS.

- [ ] **Step 6: Run the meta gate to confirm no regression**

Run: `mise run meta:fast`
Expected: PASS (existing `oracle_fast` + `oracle_synth` unaffected — the additions are new methods only).

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_meta/src/metactx.rs
git commit -m "M4b-2 plan1: additive MetaCtx local-context accessors (checkpoint/push/restore) + mk_forall"
```

---

### Task 2: `elab_arrow` + the binder module scaffold

**Files:**
- Create: `crates/leanr_elab/src/builtin/binder.rs`
- Modify: `crates/leanr_elab/src/builtin/mod.rs`
- Modify: `crates/leanr_elab/src/dispatch.rs`
- Create/Test: `crates/leanr_elab/tests/binder_smoke.rs`

**Interfaces:**
- Produces:
  - `pub fn elab_arrow(elab: &mut TermElabM, node: &SyntaxNode, kinds: &KindInterner) -> Result<ExprId, ElabError>`
  - `pub(crate) fn elab_type(elab: &mut TermElabM, elem: &SynElem, kinds: &KindInterner) -> Result<ExprId, ElabError>`
- Consumes: `TermElabM::{mk_fresh_level_mvar, elab_term_ensuring_type, mctx, view}`, `MetaCtx::store_mut`, `Store::{expr_sort, expr_forall}`, `dispatch::{SynElem, non_trivia_children}`, `BinderInfo`.

- [ ] **Step 1: Add the module + the smoke-test harness (failing test)**

Create `crates/leanr_elab/tests/binder_smoke.rs`:

```rust
//! Fast, hermetic leanr-side structural checks for the binder
//! elaborators. Uses the committed `Elab0.olean` (no Lean toolchain
//! needed). The AUTHORITATIVE differential check is `oracle_elab` (see
//! Task 5); these assert coarse structure for a quick red/green loop and
//! deliberately do not pin exact encoder bytes (universe levels etc.).

mod support;
use support::{encode_expr, replay_fixture_in, EncSt, Replayed};

use leanr_elab::TermElabM;
use leanr_kernel::bank::Store;
use leanr_kernel::EnvView;
use leanr_meta::{Config, MetaCtx};
use leanr_syntax::{builtin, parse_term};

/// Parse `src` through leanr's own parser, elaborate with `expected =
/// None`, `instantiate_mvars`, and return the canonical JSON encoding —
/// exactly the `oracle_elab` pipeline (Task 5 keeps them identical).
fn elab_json(src: &str) -> serde_json::Value {
    let Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
    } = replay_fixture_in("elab", "Elab0.olean");
    let snap = builtin::snapshot();
    let view: EnvView = env.view();
    let parsed = parse_term(src, &snap);
    assert!(
        parsed.errors.is_empty(),
        "parse errors for {src:?}: {:?}",
        parsed.errors
    );
    let root = parsed.tree.root();
    let term_elem = root
        .first_child_or_token()
        .unwrap_or_else(|| panic!("no term child for {src:?}"));
    let mut scratch = Store::scratch();
    let mctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        &reducibility,
        &matchers,
        &instances,
        &default_instances,
        &projection_fns,
    );
    let mut elab = TermElabM::new(mctx, view);
    let e = elab
        .elab_term_ensuring_type(&term_elem, &parsed.tree.kinds, None)
        .and_then(|e| {
            elab.mctx
                .instantiate_mvars(e)
                .map_err(leanr_elab::ElabError::from)
        })
        .unwrap_or_else(|err| panic!("elaboration failed for {src:?}: {err:?}"));
    let mut st = EncSt::default();
    encode_expr(elab.mctx.store(), Some(view.store), e, &mut st)
}

#[test]
fn arrow_is_nondependent_pi() {
    let j = elab_json("Nat -> Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["bi"], "d");
    assert_eq!(j["t"], serde_json::json!({"k": "const", "n": "Nat", "us": []}));
    assert_eq!(j["b"], serde_json::json!({"k": "const", "n": "Nat", "us": []}));
}

#[test]
fn arrow_right_associates() {
    // Nat -> Nat -> Nat  ==  Nat -> (Nat -> Nat)
    let j = elab_json("Nat -> Nat -> Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(j["b"]["k"], "pi"); // body is itself an arrow
    assert_eq!(j["b"]["b"]["n"], "Nat");
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p leanr_elab --test binder_smoke`
Expected: FAIL — compile error (the `Nat -> Nat` term dispatches to `UnsupportedSyntax("Lean.Parser.Term.arrow")`, so `elab_json` panics), or the panic "elaboration failed … UnsupportedSyntax".

- [ ] **Step 3: Create the binder module with `elab_type` + `elab_arrow`**

Create `crates/leanr_elab/src/builtin/binder.rs`:

```rust
//! Binder elaborators. M4b-2 plan 1: the three universal-quantifier
//! type-former kinds — `forall`, `arrow`, `depArrow`. `arrow` is
//! non-dependent (no fvar); `forall`/`depArrow` introduce fvars via
//! `MetaCtx::push_local_decl` and abstract via `MetaCtx::mk_forall`
//! (Task 1). Oracle: `elabForall`/`elabArrow`/`elabDepArrow`
//! (Lean/Elab/Binders.lean:278/293/310).

use leanr_kernel::bank::ExprId;
use leanr_kernel::BinderInfo;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `elabType t` = `elabTerm t (mkSort (mkLevelMVar u))` then
/// ensure-is-type. Here: a fresh level mvar `?u`, a `Sort ?u` expected
/// type, and `elab_term_ensuring_type` (which drives `is_def_eq` between
/// the inferred type and `Sort ?u`). Returns the elaborated type expr.
pub(crate) fn elab_type(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let u = elab.mk_fresh_level_mvar()?;
    let sort = elab
        .mctx
        .store_mut()
        .expr_sort(None, u)
        .map_err(leanr_meta::MetaError::from)?;
    elab.elab_term_ensuring_type(elem, kinds, Some(sort))
}

/// oracle: `elabArrow` (Binders.lean:293). `A -> B`: elaborate `A` and
/// `B` independently as types, build the NON-dependent `forallE` — the
/// body `B` refers to no binder, so no fvar/abstraction is needed. The
/// binder name is anonymous (`None`); it is erased by the encoder anyway.
/// Trailing-node children (parse.rs:3 — "Pratt trailing wrap inserts
/// Start at the lhs event index", so the LHS is wrapped in): `[A, ->, B]`.
pub fn elab_arrow(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let children = non_trivia_children(node);
    let dom_elem = children
        .first()
        .ok_or_else(|| ElabError::UnsupportedSyntax("arrow: missing domain".into()))?;
    let rng_elem = children
        .get(2)
        .ok_or_else(|| ElabError::UnsupportedSyntax("arrow: missing range".into()))?;
    let dom = elab_type(elab, dom_elem, kinds)?;
    let rng = elab_type(elab, rng_elem, kinds)?;
    // `base = Some(elab.view.store)`, bound before `store_mut()` — the
    // same convention as `ident.rs:74` (disjoint-field borrow, and the
    // persistent store is the dedup base for anything a child may
    // reference). Binder name `None`: erased by the encoder.
    let base = elab.view.store;
    let e = elab
        .mctx
        .store_mut()
        .expr_forall(Some(base), None, dom, rng, BinderInfo::Default)
        .map_err(leanr_meta::MetaError::from)?;
    Ok(e)
}
```

- [ ] **Step 4: Wire the module + dispatch arm**

In `crates/leanr_elab/src/builtin/mod.rs`, add:

```rust
pub mod binder;
```

In `crates/leanr_elab/src/dispatch.rs`, add to `elaborator_name_for`'s match (after the `hole` arm):

```rust
        "Lean.Parser.Term.arrow" => Some("arrow"),
```

and to `dispatch`'s match (before the catch-all `(other, _)` arm):

```rust
        ("Lean.Parser.Term.arrow", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_arrow(elab, node, kinds)
        }
```

(Also update the "Deferred" doc block in `dispatch.rs` — remove `arrow` from the binder line; leave `fun`/`forall`/`let`/`have` noted as M4b-2 in-progress. The exact comment text is cosmetic; keep it accurate.)

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p leanr_elab --test binder_smoke`
Expected: PASS (both `arrow_*` tests).

- [ ] **Step 6: Confirm the existing gate still passes**

Run: `mise run elab:fast`
Expected: PASS (M4b-1 leaf corpus unchanged; `arrow` was previously `UnsupportedSyntax` but no corpus entry exercised it).

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_elab/src/builtin/binder.rs crates/leanr_elab/src/builtin/mod.rs crates/leanr_elab/src/dispatch.rs crates/leanr_elab/tests/binder_smoke.rs
git commit -m "M4b-2 plan1: elab_arrow (non-dependent Pi) + binder module scaffold"
```

---

### Task 3: binder-group extraction + `elab_forall`

**Files:**
- Modify: `crates/leanr_elab/src/builtin/binder.rs`
- Modify: `crates/leanr_elab/src/dispatch.rs`
- Modify: `crates/leanr_elab/tests/binder_smoke.rs`

**Interfaces:**
- Produces:
  - `pub fn elab_forall(elab: &mut TermElabM, node: &SyntaxNode, kinds: &KindInterner) -> Result<ExprId, ElabError>`
  - `pub(crate) struct BinderGroup { names: Vec<Option<NameId>>, ty: SynElem, bi: BinderInfo }`
  - `pub(crate) fn extract_binder_group(elab: &mut TermElabM, group: &SyntaxNode, kinds: &KindInterner) -> Result<BinderGroup, ElabError>`
  - `pub(crate) fn elab_binders_and_forall(elab, groups: &[BinderGroup], body_elem, kinds) -> Result<ExprId, ElabError>` (the shared telescope driver reused by `elab_dep_arrow` in Task 4)
- Consumes: Task 1's `MetaCtx::{lctx_checkpoint, push_local_decl, lctx_restore, mk_forall}`, Task 2's `elab_type`, `dispatch::non_trivia_children`, `Store::{intern_str, name_str}`.

**Scope note (bite-sized):** Plan-1 corpus foralls use **bracketed binders with an explicit type** — `forall (x : Nat), ...`. Bare-ident foralls (`forall x, ...`) and the trailing-`: ty` form (`forall x y : T, B`) go through the oracle's `expandForall` **macro** (Binders.lean:271) and are deferred to the macro slice; `extract_binder_group` returns `UnsupportedSyntax` for a bare-ident item or an empty binder-type, naming the seam.

- [ ] **Step 1: Write the failing tests**

Append to `crates/leanr_elab/tests/binder_smoke.rs`:

```rust
#[test]
fn forall_nondependent() {
    // forall (x : Nat), Nat  — body ignores x → same shape as an arrow
    let j = elab_json("forall (x : Nat), Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["bi"], "d");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(j["b"], serde_json::json!({"k": "const", "n": "Nat", "us": []}));
}

#[test]
fn forall_dependent_body_is_bvar() {
    // forall (a : Type), a  — body is the binder → bvar 0
    let j = elab_json("forall (a : Type), a");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn forall_two_names_one_group_nests() {
    // forall (x y : Nat), Nat  → pi (pi ...)
    let j = elab_json("forall (x y : Nat), Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["b"]["k"], "pi");
    assert_eq!(j["b"]["b"]["n"], "Nat");
}

#[test]
fn forall_two_groups_nests() {
    let j = elab_json("forall (x : Nat) (y : Nat), Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["b"]["k"], "pi");
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p leanr_elab --test binder_smoke forall`
Expected: FAIL — `forall …` dispatches to `UnsupportedSyntax`, so `elab_json` panics.

- [ ] **Step 3: Implement extraction + the telescope driver + `elab_forall`**

Append to `crates/leanr_elab/src/builtin/binder.rs` (add `use leanr_kernel::bank::NameId;` and `use leanr_syntax::tree::NodeOrToken;` to the imports):

```rust
/// One bracketed binder group `(x y : T)` — its names, the shared type
/// syntax, and its binder-info. Plan 1: type is always present
/// (`extract_binder_group` errors on an empty binder-type).
pub(crate) struct BinderGroup {
    pub names: Vec<Option<NameId>>,
    pub ty: SynElem,
    pub bi: BinderInfo,
}

/// Map a bracketed-binder kind name to its `BinderInfo`. `instBinder`
/// (`[…]`, a different child layout — optional name + bare type) is not
/// used by any Plan-1 corpus term and is deferred to M4b-3 (instance
/// args); it returns `None` here so the caller names the seam.
fn binder_info_of(kind: &str) -> Option<BinderInfo> {
    match kind {
        "Lean.Parser.Term.explicitBinder" => Some(BinderInfo::Default),
        "Lean.Parser.Term.implicitBinder" => Some(BinderInfo::Implicit),
        "Lean.Parser.Term.strictImplicitBinder" => Some(BinderInfo::StrictImplicit),
        _ => None,
    }
}

/// Extract `(names, type-syntax, binder-info)` from a bracketed binder
/// group. Layout for explicit/implicit/strict (term.rs:134/152/160):
/// child `[1]` is the names `KIND_NULL` (each item a bare ident token or
/// a `_` hole node), child `[2]` is the binder-type `KIND_NULL`
/// (`[":", T]` when present). Names are interned best-effort from token
/// text (erased by the encoder, so exact form does not affect the gate).
pub(crate) fn extract_binder_group(
    elab: &mut TermElabM,
    group: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<BinderGroup, ElabError> {
    let kind = kinds.name(group.kind());
    let bi = binder_info_of(kind)
        .ok_or_else(|| ElabError::UnsupportedSyntax(format!("binder group: {kind}")))?;
    let ch = non_trivia_children(group);
    let names_node = ch
        .get(1)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("binder group: names slot".into()))?;
    let type_node = ch
        .get(2)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("binder group: type slot".into()))?;
    let type_children = non_trivia_children(type_node);
    // `[":", T]`; an empty type slot is the untyped-bracketed form we defer.
    let ty = type_children
        .get(1)
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("binder group: missing `: T`".into()))?;

    // Collect the raw name texts first, then intern (avoids overlapping
    // borrows of the store while walking the tree).
    let name_texts: Vec<Option<String>> = non_trivia_children(names_node)
        .iter()
        .map(|el| match el {
            NodeOrToken::Token(tok) if kinds.name(tok.kind()) == "<ident>" => {
                Some(tok.text().to_string())
            }
            // `_` hole binder → anonymous
            _ => None,
        })
        .collect();

    let mut names = Vec::with_capacity(name_texts.len());
    for t in name_texts {
        let id = match t {
            None => None,
            Some(text) => {
                let store = elab.mctx.store_mut();
                let s = store
                    .intern_str(None, &text)
                    .map_err(leanr_meta::MetaError::from)?;
                let n = store
                    .name_str(None, None, s)
                    .map_err(leanr_meta::MetaError::from)?;
                Some(n)
            }
        };
        names.push(id);
    }
    if names.is_empty() {
        return Err(ElabError::UnsupportedSyntax("binder group: no names".into()));
    }
    Ok(BinderGroup { names, ty, bi })
}

/// Shared telescope driver: elaborate each group's type once (in the
/// context BEFORE that group's names), introduce one fvar per name via
/// `push_local_decl`, elaborate `body_elem` as a type under the full
/// telescope, and `mk_forall` over all collected fvars. Reused by both
/// `elab_forall` and `elab_dep_arrow` (Task 4). oracle: `elabBinders …
/// fun xs => mkForallFVars xs (← elabType body)`.
pub(crate) fn elab_binders_and_forall(
    elab: &mut TermElabM,
    groups: &[BinderGroup],
    body_elem: &SynElem,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    // Bracket the whole telescope: restore `lctx` on EVERY exit path
    // (Ok or Err) — a failed body elaboration must not leak fvars into
    // the ambient context.
    let checkpoint = elab.mctx.lctx_checkpoint();
    let result = (|| {
        let mut fvars: Vec<ExprId> = Vec::new();
        for g in groups {
            // Elaborate the group's shared type ONCE, before its own
            // names enter scope (so `(x y : T)` elaborates `T` in the
            // context that excludes x and y).
            let dom = elab_type(elab, &g.ty, kinds)?;
            for &name in &g.names {
                let fvar = elab
                    .mctx
                    .push_local_decl(name, dom, g.bi)
                    .map_err(ElabError::from)?;
                fvars.push(fvar);
            }
        }
        let body = elab_type(elab, body_elem, kinds)?;
        elab.mctx.mk_forall(&fvars, body).map_err(ElabError::from)
    })();
    elab.mctx.lctx_restore(checkpoint);
    result
}
```

Now `elab_forall` itself:

```rust
/// oracle: `elabForall` (Binders.lean:278), bracketed-binder path (no
/// `expandForall` macro — that fires only on the trailing `: ty` form).
/// forall children (term.rs:410): `[∀atom, binderList(KIND_NULL), optType,
/// ",", body]`. Plan 1 handles bracketed binder items only.
pub fn elab_forall(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let ch = non_trivia_children(node);
    let binder_list = ch
        .get(1)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("forall: binder list".into()))?;
    // Plan 1: reject the trailing construct-level `optType` (bare-ident
    // form via `expandForall`) — child [2], non-empty → deferred.
    if let Some(opt) = ch.get(2).and_then(|el| el.as_node()) {
        if !non_trivia_children(opt).is_empty() {
            return Err(ElabError::UnsupportedSyntax(
                "forall: trailing `: ty` (expandForall macro)".into(),
            ));
        }
    }
    let body_elem = ch
        .last()
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("forall: body".into()))?;

    let mut groups = Vec::new();
    for item in non_trivia_children(binder_list) {
        match item.as_node() {
            Some(item_node) => groups.push(extract_binder_group(elab, item_node, kinds)?),
            // A bare ident/hole binder item (no brackets) → expandForall
            // territory, deferred.
            None => {
                return Err(ElabError::UnsupportedSyntax(
                    "forall: bare-ident binder (expandForall macro)".into(),
                ))
            }
        }
    }
    elab_binders_and_forall(elab, &groups, &body_elem, kinds)
}
```

- [ ] **Step 4: Register the dispatch arm**

In `dispatch.rs` `elaborator_name_for`:

```rust
        "Lean.Parser.Term.forall" => Some("forall"),
```

In `dispatch`:

```rust
        ("Lean.Parser.Term.forall", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_forall(elab, node, kinds)
        }
```

- [ ] **Step 5: Run to verify it passes**

Run: `cargo test -p leanr_elab --test binder_smoke forall`
Expected: PASS (all four `forall_*` tests).

- [ ] **Step 6: Full crate tests + gate**

Run: `cargo test -p leanr_elab && mise run elab:fast`
Expected: PASS (arrow tests + forall tests + M4b-1 leaf corpus).

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_elab/src/builtin/binder.rs crates/leanr_elab/src/dispatch.rs crates/leanr_elab/tests/binder_smoke.rs crates/leanr_meta/src/metactx.rs
git commit -m "M4b-2 plan1: elab_forall + bracketed binder-group extraction + telescope driver"
```

---

### Task 4: `elab_dep_arrow`

**Files:**
- Modify: `crates/leanr_elab/src/builtin/binder.rs`
- Modify: `crates/leanr_elab/src/dispatch.rs`
- Modify: `crates/leanr_elab/tests/binder_smoke.rs`

**Interfaces:**
- Produces: `pub fn elab_dep_arrow(elab: &mut TermElabM, node: &SyntaxNode, kinds: &KindInterner) -> Result<ExprId, ElabError>`
- Consumes: Task 3's `extract_binder_group` + `elab_binders_and_forall`.

- [ ] **Step 1: Write the failing tests**

Append to `crates/leanr_elab/tests/binder_smoke.rs`:

```rust
#[test]
fn dep_arrow_nondependent() {
    // (x : Nat) -> Nat
    let j = elab_json("(x : Nat) -> Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["bi"], "d");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(j["b"], serde_json::json!({"k": "const", "n": "Nat", "us": []}));
}

#[test]
fn dep_arrow_dependent_body_is_bvar() {
    // (a : Type) -> a
    let j = elab_json("(a : Type) -> a");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p leanr_elab --test binder_smoke dep_arrow`
Expected: FAIL — `(x : Nat) -> Nat` dispatches to `UnsupportedSyntax("Lean.Parser.Term.depArrow")`.

- [ ] **Step 3: Implement `elab_dep_arrow`**

Append to `crates/leanr_elab/src/builtin/binder.rs`:

```rust
/// oracle: `elabDepArrow` (Binders.lean:310). depArrow children
/// (term.rs:1103): `[bracketedBinder, "->", body]` — always exactly one
/// bracketed binder with a mandatory type (`require_type = true`).
/// Dependent: the body may reference the binder, so it goes through the
/// full `push_local_decl` + `mk_forall` telescope, unlike `arrow`.
pub fn elab_dep_arrow(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let ch = non_trivia_children(node);
    let binder_node = ch
        .first()
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("depArrow: binder".into()))?;
    let body_elem = ch
        .get(2)
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("depArrow: body".into()))?;
    let group = extract_binder_group(elab, binder_node, kinds)?;
    elab_binders_and_forall(elab, &[group], &body_elem, kinds)
}
```

- [ ] **Step 4: Register the dispatch arm**

In `dispatch.rs` `elaborator_name_for`:

```rust
        "Lean.Parser.Term.depArrow" => Some("depArrow"),
```

In `dispatch`:

```rust
        ("Lean.Parser.Term.depArrow", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_dep_arrow(elab, node, kinds)
        }
```

- [ ] **Step 5: Run to verify it passes**

Run: `cargo test -p leanr_elab --test binder_smoke dep_arrow`
Expected: PASS.

- [ ] **Step 6: Full crate tests + gate**

Run: `cargo test -p leanr_elab && mise run elab:fast`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_elab/src/builtin/binder.rs crates/leanr_elab/src/dispatch.rs crates/leanr_elab/tests/binder_smoke.rs
git commit -m "M4b-2 plan1: elab_dep_arrow (dependent Pi via the shared telescope)"
```

---

### Task 5: differential oracle corpus — the authoritative gate

**Files:**
- Modify: `tests/fixtures/elab/dump_elab.lean`
- (Verify only, expected no change) `tests/fixtures/elab/Elab0.lean`
- Regenerate: `tests/fixtures/elab/elab-queries.jsonl`

**Interfaces:**
- Consumes: the three elaborators from Tasks 2-4; the existing `oracle_elab` gate auto-iterates every corpus line, so no Rust change is needed unless a new `exp` node kind appears (it does not — `pi`/`bvar`/`const`/`sort` are already encoded).

**Prerequisite:** the pinned Lean toolchain (`mise run elan:bootstrap` provides it). This task regenerates the committed fixtures; it is the only task that runs Lean.

- [ ] **Step 1: Add the binder query list to the dumper**

In `tests/fixtures/elab/dump_elab.lean`, add a new list next to `sortAscHoleQueries` (the exact insertion point mirrors the existing `List (String × String)` lists):

```lean
def binderQueries : List (String × String) := [
  ("arrow/natNat",        "Nat -> Nat"),
  ("arrow/rightAssoc",    "Nat -> Nat -> Nat"),
  ("forall/nondep",       "forall (x : Nat), Nat"),
  ("forall/dep",          "forall (a : Type), a"),
  ("forall/twoNames",     "forall (x y : Nat), Nat"),
  ("forall/twoGroups",    "forall (x : Nat) (y : Nat), Nat"),
  ("depArrow/nondep",     "(x : Nat) -> Nat"),
  ("depArrow/dep",        "(a : Type) -> a")
]
```

Concatenate it into the emit loop (the `for (id, src) in …` line, dump_elab.lean ~:240):

```lean
  for (id, src) in strQueries ++ identQueries ++ sortAscHoleQueries ++ binderQueries do
```

- [ ] **Step 2: Confirm no new constant is needed in `Elab0.lean`**

Every term above references only `Nat` and `Type`, both already declared in `tests/fixtures/elab/Elab0.lean`. Verify:

Run: `grep -nE 'inductive Nat|Type' tests/fixtures/elab/Elab0.lean`
Expected: `Nat` inductive present; `Type` is a keyword (no declaration needed). If a future term needs a new constant, add it prelude-style (`genCtorIdx false` for multi-ctor inductives) — not required here.

- [ ] **Step 3: Regenerate the corpus**

Run: `mise run fixtures:regen-elab`
Expected: `tests/fixtures/elab/elab-queries.jsonl` gains 8 new lines (ids `arrow/*`, `forall/*`, `depArrow/*`). Review the diff:

Run: `git diff tests/fixtures/elab/elab-queries.jsonl`
Expected: only additions; the eight new records carry `pi`/`bvar`/`const`/`sort` `exp` values. Sanity-check `arrow/natNat` → `{"k":"pi","bi":"d","t":{"k":"const","n":"Nat","us":[]},"b":{"k":"const","n":"Nat","us":[]}}` and `forall/dep` → a `pi` whose `b` is `{"k":"bvar","i":0}`.

- [ ] **Step 4: Run the authoritative differential gate**

Run: `mise run elab:fast`
Expected: PASS — leanr's elaboration of all 28 corpus terms (20 leaf + 8 binder) matches the oracle byte-for-byte. If a binder term diverges, that is the differential test doing its job: fix the elaborator (not the fixture) and re-run. Cross-check any divergence against the smoke tests from Tasks 2-4.

- [ ] **Step 5: Run the full workspace test + CI gate locally**

Run: `mise run test`
Expected: PASS (the workspace test picks up `oracle_elab` and `binder_smoke`).

- [ ] **Step 6: Commit**

```bash
git add tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -m "M4b-2 plan1: differential corpus for arrow/forall/depArrow (8 terms)"
```

---

## Self-Review

**Spec coverage (against the design's Plan 1 row):**
- Local-context accessor family (`lctx_checkpoint`/`push_local_decl`/`lctx_restore` + `mk_forall`) → Task 1. ✔
- The three universal-quantifier forms (`forall`/`arrow`/`depArrow`) → Tasks 2/3/4. ✔
- Entry point unchanged; no fixpoint/ladder fields in Plan 1 → honored (Global Constraints; no task touches `elab.rs` state or the entry point). ✔ (matches the design's corrected § canonical entry-point pipeline.)
- Differential oracle tier for `∀`/`→`/`(x:A)→B` → Task 5. ✔
- Named-seam discipline (bare-ident forall, `expandForall`, `instBinder` all named `UnsupportedSyntax`) → Task 3. ✔

**Placeholder scan:** No `TBD`/`implement later`/"handle edge cases" remains. Task 1 defines the `lctx_checkpoint`/`push_local_decl`/`lctx_restore` + `mk_forall` accessors in full; Task 3's telescope driver is a single concrete loop (no closure/borrow fork left open). Every code step shows the actual code; every run step shows the command and expected result.

**Type consistency:** `elab_type`, `extract_binder_group`, `BinderGroup`, `elab_binders_and_forall` names are used identically across Tasks 2-4. `mk_forall(&[ExprId], ExprId) -> Result<ExprId, MetaError>` and `push_local_decl(Option<NameId>, ExprId, BinderInfo) -> Result<ExprId, MetaError>` signatures are consistent between the `leanr_meta` definitions (Task 1 / Task 3 note) and the `leanr_elab` call sites. Dispatch kind strings (`Lean.Parser.Term.arrow`/`forall`/`depArrow`) match the grammar-confirmed names.

**Known follow-ups (out of Plan 1, named for later slices):** bare-ident foralls + trailing `: ty` (`expandForall` macro slice); `instBinder`/implicit-instance binder groups (M4b-3); `fun`/`let`/`have` + the postponement fixpoint (M4b-2 Plans 2-3).
