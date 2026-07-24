# M4b-2 Plan 3 (`let` / `have`) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land the `let` and `have` term elaborators — one `elab_let_like` function differing only by a `non_dep` bool — plus the two additive `MetaCtx` accessors they need, differentially verified against the pinned oracle, with **no** synthetic-mvar scheduler.

**Architecture:** The pinned toolchain elaborates `have` as `elabLetDeclCore stx expectedType? { nondep := true }` over the *same* `elabLetDeclAux` as `let`, so `have h : T := v; b` and `let h : T := v; b` produce byte-identical `Expr.letE` nodes except for the `non_dep` bit (design spec § Amendment 2, probe-pinned). Plan 3 therefore adds ONE elaborator in `leanr_elab::builtin::binder` registered on two dispatch arms, plus two additive `leanr_meta` accessors — `push_let_decl` (wrapping the kernel's existing ldecl overload) and `mk_let_expr` (abstract-then-`expr_let`, carrying `non_dep`, because the kernel's own rebuild path hardcodes `non_dep = false`). Binder scoping reuses plan 1's `lctx_checkpoint`/`push_local_decl`/`lctx_restore` bracket; the `letIdBinders` telescope reuses plan 1's `extract_binder_group` + `mk_forall` and plan 2's `mk_lambda` verbatim.

**Tech Stack:** Rust (workspace crates `leanr_meta`, `leanr_elab`, `leanr_kernel`, `leanr_syntax`); Lean 4 v4.33.0-rc1 as the differential oracle; `mise` task runner.

## Global Constraints

- **Kernel/olean TCB is byte-untouched.** `leanr_kernel` depends on no workspace crate and is not modified in this plan. `LocalContext::{mk_local_decl, mk_let_decl, get, save, restore}`, `abstract_fvars`, and `Store::expr_let` already exist and are reused as-is.
- **`leanr_meta/src` accessor precedent.** New public methods on `leanr_meta` must be purely **additive**, **TCB-neutral**, and **behavior-neutral** (they expose capability `leanr_meta` already exercises internally). Any non-additive / behavior-changing `leanr_meta` change is out of scope and must be flagged. This plan adds exactly two: `MetaCtx::push_let_decl` and `MetaCtx::mk_let_expr`.
- **Named-seam discipline.** Every dispatch arm is a named seam; unregistered kinds fall through to `ElabError::UnsupportedSyntax(kind)` — never a panic, never a wrong `ExprId`. Within `let`/`have`, the non-`letIdDecl` `letDecl` alternatives, a non-empty `letConfig`, and implicit/strict/instance let binders are each their own named seam.
- **No scheduler.** No `synthesize_synthetic_mvars`, no `TermElabM` ladder fields, no `may_postpone` threading, no entry-point change. The pipeline stays `elab_term_ensuring_type → instantiate_mvars` exactly as plans 1 and 2 left it (design spec § Amendment; the entire fixpoint moves to M4b-3).
- **Oracle discipline.** Correctness is byte-for-byte agreement with the pinned oracle's canonical `Expr` via the `oracle_elab` gate. The `lean-toolchain` pin (`leanprover/lean4:v4.33.0-rc1`) is not bumped.
- **Binder names are erased** by the differential encoder (`encode_expr` drops `binder_name`/`decl_name`), so the exact interned name on a `letE` never affects the gate; correctness of *structure* (type, value, body, de Bruijn indices, `non_dep`) is what is verified. Names must still resolve correctly, since a body occurrence of a binder name is looked up by `NameId` equality (`lctx_lookup_by_name`).
- **CI lint gate.** CI's `mise run ci` gates on `cargo fmt --check` + clippy. Run `cargo fmt` (or `mise run ci`) before each commit; the test gates do not cover formatting.

## Reference: pinned-oracle construction (v4.33.0-rc1, `Lean/Elab/Binders.lean`)

```lean
-- :939  @[builtin_term_elab «let»]  elabLetDecl  := fun stx et? => elabLetDeclCore stx et? {}
-- :942  @[builtin_term_elab «have»] elabHaveDecl := fun stx et? => elabLetDeclCore stx et? { nondep := true }
-- :745  elabLetDeclAux id binders typeStx valStx body expectedType? config
--   (type, val) ← elabBindersEx binders fun xs => do
--       let type ← elabType typeStx
--       let val  ← elabTermEnsuringType valStx type
--       pure (← mkForallFVars fvars type, ← mkLambdaFVars fvars val (usedLetOnly := false))
--   withLetDecl id.getId type val (nondep := config.nondep) fun x => do
--       let body ← elabTermEnsuringType body expectedType?
--       mkLetFVars #[x] body (usedLetOnly := config.usedOnly) (generalizeNondepLet := false)
```

`config.usedOnly` is `false` for both `let` and `have`, so an unused binding is **retained**. `generalizeNondepLet := false` keeps a nondep decl an `Expr.letE` carrying the bit — there is no `letFun` and no application node. Elided type: `mkLetIdDeclView` runs `expandOptType`, which yields a `_` hole (⇒ a fresh mvar assigned by the value's `elabTermEnsuringType`).

## Confirmed oracle outputs (design-phase probe, v4.33.0-rc1 over the committed `Elab0` env — not committed)

```text
let  x : Nat := Nat.zero; x  →  {"k":"let","nd":false,"t":Nat,"v":Nat.zero,"b":{"k":"bvar","i":0}}
have h : Nat := Nat.zero; h  →  {"k":"let","nd":true ,"t":Nat,"v":Nat.zero,"b":{"k":"bvar","i":0}}
let x := Nat.zero; x         →  identical to let/typed (the elided type resolves to Nat)
let x : Nat := Nat.zero; Nat →  {"k":"let","nd":false,"t":Nat,"v":Nat.zero,"b":Nat}      (unused, retained)
let f (y : Nat) : Nat := y; f→  {"k":"let","nd":false,"t":Nat→Nat,"v":(fun y => bvar 0),"b":{"k":"bvar","i":0}}
let f y : Nat := y; f        →  identical to let/binders (?α unified to Nat at the use site)
have : Nat := Nat.zero; this →  identical to have/typed (the hygiene binder is named `this`)
```

## Confirmed parse-tree shapes (leanr's own parser, throwaway probe — not committed)

```text
let x : Nat := Nat.zero; x
  Term.let[ TOK "let",
            Term.letConfig[ null{} ],
            Term.letDecl[ Term.letIdDecl[ Term.letId[ TOK <ident> "x" ],
                                          null{},                                   -- binders
                                          null[ Term.typeSpec[ TOK ":", «Nat» ] ],  -- optType
                                          TOK ":=",
                                          «Nat.zero» ] ],
            TOK ";",
            «x» ]

let x := Nat.zero; x          -- same, with an EMPTY optType null
let f (y : Nat) : Nat := y; f -- binders null holds a Term.explicitBinder node
let f y : Nat := y; f         -- binders null holds a bare <ident> token
have : Nat := Nat.zero; this  -- letId's child is a `hygieneInfo` node (empty ident token)
let _ : Nat := Nat.zero; Nat  -- letId's child is a `Term.hole` node
```

Key facts used below:
- `Term.let` / `Term.have` non-trivia children: `[ ("let"|"have") , Term.letConfig , Term.letDecl , ";" , body ]` — body is child `[4]`.
- `Term.letDecl` non-trivia children: `[ Term.letIdDecl ]` (leanr's parser ports only the `letIdDecl` alternative).
- `Term.letIdDecl` non-trivia children: `[ Term.letId , null(binders) , null(optType) , ":=" , value ]` — value is child `[4]`.
- `Term.letId` non-trivia children: `[ <ident> ]` | `[ hygieneInfo ]` | `[ Term.hole ]`.
- `null(optType)` is empty when the type is elided, else holds one `Term.typeSpec` whose non-trivia children are `[ ":" , T ]` — T is child `[1]`.
- `Term.let` and `Term.have` are structurally identical; only the keyword token differs.
- Dotted global idents already resolve (`Nat.zero` elaborates to `{"k":"const","n":"Nat.zero","us":[]}` through the shipped `elab_ident` + `resolve_global`) — verified by probe, so the corpus may use constructors.

## File Structure

- **Modify** `crates/leanr_meta/src/metactx.rs` — add `push_let_decl` (next to `push_local_decl`, ~line 453) and `mk_let_expr` (after `mk_lambda`, ~line 578) to `impl<'e> MetaCtx<'e>`; extend the `#[cfg(test)] mod tests`. No new imports (`abstract_fvars`, `Node`, `expr_let`, `LocalContext::mk_let_decl` are all already reachable — the same set `push_local_decl`/`mk_binding` use).
- **Modify** `crates/leanr_elab/src/builtin/binder.rs` — add `elab_let_like`, plus private helpers `extract_let_id_name` and `push_let_binders`. Reuses the file's existing `elab_type`, `fresh_type_mvar`, `intern_binder_name`, `extract_binder_group`.
- **Modify** `crates/leanr_elab/src/dispatch.rs` — register `"Lean.Parser.Term.let"` and `"Lean.Parser.Term.have"` in `elaborator_name_for`, add two arms to `dispatch`, update the "Deferred" doc block.
- **Modify** `crates/leanr_elab/tests/binder_smoke.rs` — add the fast, hermetic leanr-side `let`/`have` structural tests.
- **Modify** `tests/fixtures/elab/dump_elab.lean` — add `letQueries` + `haveQueries` lists and concatenate them into the emit loop.
- **Regenerate** `tests/fixtures/elab/elab-queries.jsonl` (19 new lines).
- (No change) `tests/fixtures/elab/Elab0.lean` / `Elab0.olean` — every corpus term references only `Nat`, `Nat.zero`, and `Type`, all already in scope.

---

### Task 1: `MetaCtx::push_let_decl` + `mk_let_expr` (additive, TCB-neutral)

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs`
- Test: `crates/leanr_meta/src/metactx.rs` (extend the existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Produces:
  - `pub fn push_let_decl(&mut self, name: Option<NameId>, ty: ExprId, value: ExprId) -> Result<ExprId, MetaError>`
  - `pub fn mk_let_expr(&mut self, fvar: ExprId, body: ExprId, non_dep: bool) -> Result<ExprId, MetaError>`
- Consumes (existing, in-crate): `self.lctx` (`mk_let_decl`, `get`, `save`), `self.local_names`, `self.scratch`, `self.view.store`, `self.fvar_gen`, `self.guard`, `self.node`, `abstract_fvars`, `Store::expr_let` — the exact set `push_local_decl` (metactx.rs:453) and `mk_binding` (metactx.rs:498) already use.

- [ ] **Step 1: Write the failing tests**

Add to the test module at the bottom of `crates/leanr_meta/src/metactx.rs`, after `mk_lambda_abstracts_body_over_fvar`. These use the module's existing helpers (`with_prelude0_ctx`, `const_named` from `crate::test_support`) — the same ones the plan-1 and plan-2 tests use.

```rust
    /// TDD RED/GREEN for M4b-2 plan3 task 1: the let-decl pair
    /// (`push_let_decl` + `mk_let_expr`). Structure only — the value
    /// here is `Nat` rather than a `Nat`-typed term, since abstraction
    /// and the `non_dep` bit are what is under test, not type checking.
    /// Both `non_dep` values are exercised: `false` is `let`, `true` is
    /// `have` (the ONLY difference between the two forms, design spec
    /// § Amendment 2).
    #[test]
    fn push_let_decl_and_mk_let_expr_carry_non_dep() {
        with_prelude0_ctx(|ctx| {
            let nat = const_named(ctx, "Nat");
            for want_non_dep in [false, true] {
                let checkpoint = ctx.lctx_checkpoint();
                let fvar = ctx.push_let_decl(None, nat, nat).expect("push_let_decl");
                assert!(matches!(ctx.node(fvar), Node::FVar { .. }));
                // body = the fvar itself → `let x : Nat := Nat; x`
                // (a `LetE` whose body is `bvar 0`).
                let built = ctx
                    .mk_let_expr(fvar, fvar, want_non_dep)
                    .expect("mk_let_expr");
                ctx.lctx_restore(checkpoint);
                assert_eq!(ctx.lctx.save(), checkpoint);
                match ctx.node(built) {
                    Node::LetE {
                        ty, value, body, non_dep, ..
                    } => {
                        assert_eq!(ty, nat);
                        assert_eq!(value, nat);
                        assert!(matches!(ctx.node(body), Node::BVar { idx: 0 }));
                        assert_eq!(non_dep, want_non_dep);
                    }
                    other => panic!("expected LetE, got {other:?}"),
                }
            }
        });
    }

    /// `mk_let_expr` on a cdecl (non-let) fvar is an error, never a
    /// silently wrong node: a `LetE` needs a value and a cdecl has none.
    #[test]
    fn mk_let_expr_rejects_a_cdecl_fvar() {
        with_prelude0_ctx(|ctx| {
            let nat = const_named(ctx, "Nat");
            let checkpoint = ctx.lctx_checkpoint();
            let fvar = ctx
                .push_local_decl(None, nat, BinderInfo::Default)
                .expect("push_local_decl");
            let err = ctx.mk_let_expr(fvar, fvar, false);
            ctx.lctx_restore(checkpoint);
            assert!(err.is_err(), "expected Err for a cdecl fvar, got {err:?}");
        });
    }
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_meta push_let_decl_and_mk_let_expr_carry_non_dep mk_let_expr_rejects_a_cdecl_fvar`
Expected: FAIL to compile with "no method named `push_let_decl`" / "no method named `mk_let_expr`".

- [ ] **Step 3: Implement `push_let_decl`**

Add to `impl<'e> MetaCtx<'e>` in `crates/leanr_meta/src/metactx.rs`, directly after `push_local_decl` (which ends ~line 476, just before `lctx_lookup_by_name`). This is `push_local_decl` with the kernel's ldecl overload swapped in:

```rust
    /// Mint an ldecl fvar `(name : ty := value)` into the ambient `lctx`
    /// and return its `Expr::fvar` — the let twin of `push_local_decl`,
    /// wrapping the kernel's existing `LocalContext::mk_let_decl` (the
    /// ldecl overload, local_ctx.rs:128). Oracle: `withLetDecl`'s
    /// declaration half. The caller brackets with `lctx_checkpoint`/
    /// `lctx_restore`. Additive + behavior-neutral: no new state, no
    /// existing path changed.
    pub fn push_let_decl(
        &mut self,
        name: Option<NameId>,
        ty: ExprId,
        value: ExprId,
    ) -> Result<ExprId, MetaError> {
        debug_assert_eq!(
            self.local_names.len(),
            self.lctx.save(),
            "local_names/lctx lockstep invariant violated"
        );
        let fvar = self.lctx.mk_let_decl(
            self.scratch,
            Some(self.view.store),
            &mut self.fvar_gen,
            name,
            ty,
            value,
        )?;
        // Same `local_names` bookkeeping as `push_local_decl`: one entry
        // per call, matching `lctx.decls`'s own growth exactly, so a body
        // occurrence of the binder name resolves via
        // `lctx_lookup_by_name`.
        self.local_names.push((name, fvar));
        Ok(fvar)
    }
```

- [ ] **Step 4: Implement `mk_let_expr`**

Add to the same `impl` block, directly after `mk_lambda` (~line 578):

```rust
    /// oracle: `mkLetFVars #[fvar] body (usedLetOnly := false)
    /// (generalizeNondepLet := false)` — abstract `body` over the single
    /// let-bound `fvar` and wrap in `Expr.letE`, carrying `non_dep`
    /// (`false` for `let`, `true` for `have`; design spec § Amendment 2).
    ///
    /// Deliberately NOT a `mk_binding` case: the kernel's own rebuild
    /// path (`subst.rs`'s `mk_binding`, :1017) hardcodes `non_dep =
    /// false` for a rebuilt `LetE`, so it cannot express `have`. Reads
    /// `ty`/`value` off the lctx decl exactly as `mk_binding` reads
    /// `ty`/`binder_info`. Additive + behavior-neutral: exposes
    /// capability the crate already exercises (`expr_let` +
    /// `abstract_fvars`), adds no state, changes no existing path.
    pub fn mk_let_expr(
        &mut self,
        fvar: ExprId,
        body: ExprId,
        non_dep: bool,
    ) -> Result<ExprId, MetaError> {
        let (binder_name, ty, value) = match self.node(fvar) {
            Node::FVar { id: Some(id) } => {
                let decl = self
                    .lctx
                    .get(id)
                    .ok_or_else(|| MetaError::Infer("mk_let_expr: fvar not declared".into()))?;
                let value = decl.value.ok_or_else(|| {
                    MetaError::Infer("mk_let_expr: fvar is not a let-bound decl".into())
                })?;
                (decl.binder_name, decl.ty, value)
            }
            _ => {
                return Err(MetaError::Infer(
                    "mk_let_expr: telescope entry is not an fvar".into(),
                ))
            }
        };
        let body = abstract_fvars(
            self.scratch,
            Some(self.view.store),
            body,
            std::slice::from_ref(&fvar),
            &mut self.guard,
        )?;
        let e = self
            .scratch
            .expr_let(Some(self.view.store), binder_name, ty, value, body, non_dep)?;
        Ok(e)
    }
```

- [ ] **Step 5: Run the tests to verify they pass**

Run: `cargo test -p leanr_meta push_let_decl_and_mk_let_expr_carry_non_dep mk_let_expr_rejects_a_cdecl_fvar`
Expected: PASS (both).

- [ ] **Step 6: Run the meta gate to confirm no regression**

Run: `mise run meta:fast`
Expected: PASS (existing gates unaffected — the addition is two new methods only).

- [ ] **Step 7: Format + commit**

```bash
cargo fmt
git add crates/leanr_meta/src/metactx.rs
git commit -m "M4b-2 plan3: additive MetaCtx::push_let_decl + mk_let_expr (non_dep-carrying letE builder)"
```

---

### Task 2: `elab_let_like` + the two dispatch arms + smoke tests

**Files:**
- Modify: `crates/leanr_elab/src/builtin/binder.rs`
- Modify: `crates/leanr_elab/src/dispatch.rs`
- Modify: `crates/leanr_elab/tests/binder_smoke.rs`

**Interfaces:**
- Produces: `pub fn elab_let_like(elab: &mut TermElabM, node: &SyntaxNode, kinds: &KindInterner, expected: Option<ExprId>, non_dep: bool) -> Result<ExprId, ElabError>`
- Consumes: Task 1's `MetaCtx::{push_let_decl, mk_let_expr}`; existing `MetaCtx::{lctx_checkpoint, push_local_decl, lctx_restore, mk_forall, mk_lambda}`; `TermElabM::{elab_term_ensuring_type}`; binder.rs's existing `elab_type`, `fresh_type_mvar`, `intern_binder_name`, `extract_binder_group` (returning `BinderGroup { names, ty, bi }`); `dispatch::{non_trivia_children, SynElem}`; `BinderInfo`, `NameId`, `NodeOrToken`, `SyntaxNode`.

**Design note (why one function with a `non_dep` bool):** the pinned toolchain's `elabHaveDecl` *is* `elabLetDeclCore stx expectedType? { nondep := true }` over the same `elabLetDeclAux` as `elabLetDecl` (`Binders.lean:939`/`:942`), and the design-phase probe confirmed the outputs differ by exactly the `non_dep` bit. Two elaborators would duplicate the entire flow for one bool. The remaining `LetConfig` variants (`letI`/`haveI`/`let_fun`/`let_delayed`/`let_tmp`) are distinct `SyntaxKind`s that already fall through to the dispatch catch-all; their `zeta`/`postponeValue`/`usedOnly` configs change the emitted term, so each needs its own oracle tier in a later slice.

- [ ] **Step 1: Write the failing tests**

Append to `crates/leanr_elab/tests/binder_smoke.rs` (the file already defines `elab_json` and imports `serde_json`):

```rust
#[test]
fn let_typed_binding() {
    // let x : Nat := Nat.zero; x  →  letE Nat Nat.zero (bvar 0), nd=false
    let j = elab_json("let x : Nat := Nat.zero; x");
    assert_eq!(j["k"], "let");
    assert_eq!(j["nd"], false);
    assert_eq!(j["t"], serde_json::json!({"k": "const", "n": "Nat", "us": []}));
    assert_eq!(j["v"], serde_json::json!({"k": "const", "n": "Nat.zero", "us": []}));
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn have_is_a_let_with_non_dep_set() {
    // have h : Nat := Nat.zero; h  →  byte-identical to the `let` above
    // EXCEPT nd=true (design spec § Amendment 2).
    let j = elab_json("have h : Nat := Nat.zero; h");
    assert_eq!(j["k"], "let");
    assert_eq!(j["nd"], true);
    assert_eq!(j["t"], serde_json::json!({"k": "const", "n": "Nat", "us": []}));
    assert_eq!(j["v"], serde_json::json!({"k": "const", "n": "Nat.zero", "us": []}));
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn let_elided_type_is_inferred_from_the_value() {
    // let x := Nat.zero; x — the elided type is a fresh mvar the value's
    // `elab_term_ensuring_type` assigns to Nat; instantiate_mvars fills it.
    let j = elab_json("let x := Nat.zero; x");
    assert_eq!(j["k"], "let");
    assert_eq!(j["t"], serde_json::json!({"k": "const", "n": "Nat", "us": []}));
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn let_unused_binding_is_retained() {
    // let x : Nat := Nat.zero; Nat — `usedLetOnly := false` on the oracle
    // side, so the binding survives even though the body ignores it.
    let j = elab_json("let x : Nat := Nat.zero; Nat");
    assert_eq!(j["k"], "let");
    assert_eq!(j["b"], serde_json::json!({"k": "const", "n": "Nat", "us": []}));
}

#[test]
fn let_anonymous_binder() {
    // let _ : Nat := Nat.zero; Nat — the `Term.hole` letId shape.
    let j = elab_json("let _ : Nat := Nat.zero; Nat");
    assert_eq!(j["k"], "let");
    assert_eq!(j["t"], serde_json::json!({"k": "const", "n": "Nat", "us": []}));
}

#[test]
fn let_bracketed_binder_telescope() {
    // let f (y : Nat) : Nat := y; f  →  letE (Nat → Nat) (fun y => bvar 0) (bvar 0)
    let j = elab_json("let f (y : Nat) : Nat := y; f");
    assert_eq!(j["k"], "let");
    assert_eq!(j["t"]["k"], "pi");
    assert_eq!(j["v"]["k"], "lam");
    assert_eq!(j["v"]["b"], serde_json::json!({"k": "bvar", "i": 0}));
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn let_bare_ident_binder_unifies_its_domain() {
    // let f y : Nat := y; f — the bare-ident binder's domain is a fresh
    // mvar unified to Nat by the value's use site, so this matches the
    // bracketed form exactly.
    let j = elab_json("let f y : Nat := y; f");
    assert_eq!(j["k"], "let");
    assert_eq!(j["t"]["k"], "pi");
    assert_eq!(j["t"]["t"], serde_json::json!({"k": "const", "n": "Nat", "us": []}));
    assert_eq!(j["v"]["k"], "lam");
}

#[test]
fn have_hygiene_binder_is_named_this() {
    // have : Nat := Nat.zero; this — the `hygieneInfo` letId shape; the
    // oracle names the binder `this`, and the body's `this` must resolve
    // to it (binder names are erased by the encoder, but resolution is
    // what makes the body a `bvar` rather than an UnknownIdent error).
    let j = elab_json("have : Nat := Nat.zero; this");
    assert_eq!(j["k"], "let");
    assert_eq!(j["nd"], true);
    assert_eq!(j["b"], serde_json::json!({"k": "bvar", "i": 0}));
}

#[test]
fn let_nested_indexes_bvars() {
    // let x : Nat := Nat.zero; let y : Nat := x; y
    //   →  letE Nat Nat.zero (letE Nat (bvar 0) (bvar 0))
    let j = elab_json("let x : Nat := Nat.zero; let y : Nat := x; y");
    assert_eq!(j["k"], "let");
    assert_eq!(j["b"]["k"], "let");
    assert_eq!(j["b"]["v"], serde_json::json!({"k": "bvar", "i": 0}));
    assert_eq!(j["b"]["b"], serde_json::json!({"k": "bvar", "i": 0}));
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_elab --test binder_smoke -- let_ have_`
Expected: FAIL — `let …`/`have …` dispatch to `UnsupportedSyntax("Lean.Parser.Term.let")` / `…Term.have`, so `elab_json` panics with "elaboration failed … UnsupportedSyntax".

- [ ] **Step 3: Implement the helpers**

Append to `crates/leanr_elab/src/builtin/binder.rs`, after `elab_fun`. All imports needed (`NameId`, `NodeOrToken`, `SyntaxNode`, `BinderInfo`, `SynElem`, `non_trivia_children`) are already present at the top of the file.

```rust
/// Extract the binder name from a `Term.letId` node. Three
/// probe-confirmed shapes: a bare `<ident>` token (`let x := …`); a
/// `Term.hole` node (`let _ := …`) → anonymous; a `hygieneInfo` node
/// (`have : T := v; …`), which the oracle names `this`
/// (`mkLetIdDeclView`: `HygieneInfo.mkIdent letId[0] `this`).
///
/// leanr has no macro-scope hygiene, so the `this` minted here resolves
/// to a body occurrence of `this` by plain `NameId` equality — correct
/// for every non-shadowing term, a stated simplification of the design
/// spec (§ Plan 3 — canonical, "Stated simplification: hygiene").
fn extract_let_id_name(
    elab: &mut TermElabM,
    let_id: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<Option<NameId>, ElabError> {
    let ch = non_trivia_children(let_id);
    let first = ch
        .first()
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: empty letId".into()))?;
    match first {
        NodeOrToken::Token(tok) if kinds.name(tok.kind()) == "<ident>" => {
            Ok(Some(intern_binder_name(elab, tok.text())?))
        }
        NodeOrToken::Node(n) => match kinds.name(n.kind()) {
            "Lean.Parser.Term.hole" => Ok(None),
            "hygieneInfo" => Ok(Some(intern_binder_name(elab, "this")?)),
            other => Err(ElabError::UnsupportedSyntax(format!("let: letId {other}"))),
        },
        _ => Err(ElabError::UnsupportedSyntax("let: letId shape".into())),
    }
}

/// Push the `letIdBinders` telescope (`let f (y : Nat) : Nat := …`) into
/// the local context, returning its fvars in declaration order. Each
/// item is either a bracketed binder group (plan 1's
/// `extract_binder_group`) or a bare ident (`let f y := …`), whose
/// domain is a fresh type mvar unified at the value's use site —
/// exactly plan 2's elided-`fun`-binder treatment.
///
/// Named seams (→ `UnsupportedSyntax`): implicit / strict-implicit /
/// instance bracketed binders (M4b-3, which brings implicit and
/// instance arguments), and any other item shape.
///
/// The CALLER owns the `lctx_checkpoint`/`lctx_restore` bracket.
fn push_let_binders(
    elab: &mut TermElabM,
    items: &[SynElem],
    kinds: &KindInterner,
) -> Result<Vec<ExprId>, ElabError> {
    let mut fvars: Vec<ExprId> = Vec::new();
    for item in items {
        match item {
            NodeOrToken::Node(n) => {
                let g = extract_binder_group(elab, n, kinds)?;
                if !matches!(g.bi, BinderInfo::Default) {
                    return Err(ElabError::UnsupportedSyntax(
                        "let: implicit/strict/instance binder (M4b-3)".into(),
                    ));
                }
                // The group's shared type elaborates ONCE, before its own
                // names enter scope — same rule as `elab_binders_and_forall`.
                let dom = elab_type(elab, &g.ty, kinds)?;
                for &name in &g.names {
                    let fvar = elab
                        .mctx
                        .push_local_decl(name, dom, BinderInfo::Default)
                        .map_err(ElabError::from)?;
                    fvars.push(fvar);
                }
            }
            NodeOrToken::Token(tok) if kinds.name(tok.kind()) == "<ident>" => {
                let name = intern_binder_name(elab, tok.text())?;
                let dom = fresh_type_mvar(elab)?;
                let fvar = elab
                    .mctx
                    .push_local_decl(Some(name), dom, BinderInfo::Default)
                    .map_err(ElabError::from)?;
                fvars.push(fvar);
            }
            _ => {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "let: unsupported binder kind {}",
                    kinds.name(item.kind())
                )))
            }
        }
    }
    Ok(fvars)
}
```

- [ ] **Step 4: Implement `elab_let_like`**

Append to `crates/leanr_elab/src/builtin/binder.rs`, after the helpers from Step 3:

```rust
/// oracle: `elabLetDeclCore` (Binders.lean:891) → `elabLetDeclAux`
/// (:745), the `letIdDecl` alternative. ONE elaborator for both forms:
/// `Lean.Parser.Term.let` passes `non_dep = false` (`elabLetDecl`, :939)
/// and `Lean.Parser.Term.have` passes `non_dep = true` (`elabHaveDecl`,
/// :942, i.e. `elabLetDeclCore … { nondep := true }`). The two outputs
/// differ by exactly that bit — probe-pinned, design spec § Amendment 2.
///
/// Elaboration order mirrors the oracle: binders → type → value →
/// (declare) → body. The value is checked against the declared type, and
/// the BODY is what receives `expected` (the oracle's
/// `elabTermEnsuringType body expectedType?`); this is plain
/// propagation, not the deferred postponement machinery.
///
/// `Term.let`/`Term.have` children: `[("let"|"have"), letConfig,
/// letDecl, ";", body]`. `Term.letIdDecl` children: `[letId,
/// null(binders), null(optType), ":=", value]`.
///
/// Named seams: a `letDecl` alternative other than `letIdDecl`
/// (`letPatDecl`/`letEqnsDecl` — leanr's parser does not emit them, so
/// the guard is defensive), a non-empty `letConfig` (leanr's parser
/// models the item list as always-empty), and the binder forms
/// `push_let_binders` rejects.
pub fn elab_let_like(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
    non_dep: bool,
) -> Result<ExprId, ElabError> {
    let ch = non_trivia_children(node);

    // [1] letConfig: `+nondep` / `(eq := h)` / … are not ported by
    // leanr's parser (always-empty `many(never())`), so a non-empty
    // item list is unreachable today — guarded as a named seam anyway.
    let cfg = ch
        .get(1)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: letConfig slot".into()))?;
    if let Some(items) = non_trivia_children(cfg).first().and_then(|el| el.as_node()) {
        if !non_trivia_children(items).is_empty() {
            return Err(ElabError::UnsupportedSyntax("let: letConfig items".into()));
        }
    }

    // [2] letDecl → its single alternative.
    let let_decl = ch
        .get(2)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: letDecl slot".into()))?;
    let id_decl = non_trivia_children(let_decl)
        .first()
        .and_then(|el| el.as_node())
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: empty letDecl".into()))?;
    let id_kind = kinds.name(id_decl.kind());
    if id_kind != "Lean.Parser.Term.letIdDecl" {
        // letPatDecl / letEqnsDecl → not ported by leanr's parser.
        return Err(ElabError::UnsupportedSyntax(format!("let: {id_kind}")));
    }

    // letIdDecl: [letId, null(binders), null(optType), ":=", value].
    let dch = non_trivia_children(&id_decl);
    let let_id = dch
        .first()
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: letId slot".into()))?;
    let binders_null = dch
        .get(1)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: binders slot".into()))?;
    let opt_type = dch
        .get(2)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: optType slot".into()))?;
    let value_elem = dch
        .get(4)
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: value".into()))?;
    // [4] the body, after the `;`.
    let body_elem = ch
        .get(4)
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: body".into()))?;

    // optType: empty (elided) or one `typeSpec` whose children are
    // `[":", T]`.
    let ty_syntax: Option<SynElem> =
        match non_trivia_children(opt_type).first().and_then(|el| el.as_node()) {
            Some(spec) => {
                let spec_kind = kinds.name(spec.kind());
                if spec_kind != "Lean.Parser.Term.typeSpec" {
                    return Err(ElabError::UnsupportedSyntax(format!(
                        "let: optType {spec_kind}"
                    )));
                }
                Some(
                    non_trivia_children(spec)
                        .get(1)
                        .cloned()
                        .ok_or_else(|| ElabError::UnsupportedSyntax("let: typeSpec type".into()))?,
                )
            }
            None => None,
        };

    let name = extract_let_id_name(elab, let_id, kinds)?;
    let binder_items = non_trivia_children(binders_null);

    // Bracket 1 — the `letIdBinders` telescope. Type and value are
    // elaborated UNDER the binders (oracle: `elabBindersEx binders fun
    // xs => …`), then abstracted back out with `mk_forall`/`mk_lambda`.
    // With no binders both abstractions are no-ops. Restores `lctx` on
    // EVERY exit path (Ok or Err), exactly as `elab_binders_and_forall`
    // does.
    let cp_binders = elab.mctx.lctx_checkpoint();
    let built = (|| {
        let fvars = push_let_binders(elab, &binder_items, kinds)?;
        let ty = match &ty_syntax {
            Some(t) => elab_type(elab, t, kinds)?,
            // Elided type: a fresh mvar, the observable twin of the
            // oracle's `expandOptType`-to-`_` hole; the value's
            // `elab_term_ensuring_type` assigns it.
            None => fresh_type_mvar(elab)?,
        };
        let value = elab.elab_term_ensuring_type(&value_elem, kinds, Some(ty))?;
        // oracle: `mkLambdaFVars fvars val (usedLetOnly := false)` and
        // `mkForallFVars fvars type`.
        let value = elab.mctx.mk_lambda(&fvars, value).map_err(ElabError::from)?;
        let ty = elab.mctx.mk_forall(&fvars, ty).map_err(ElabError::from)?;
        Ok::<(ExprId, ExprId), ElabError>((ty, value))
    })();
    elab.mctx.lctx_restore(cp_binders);
    let (ty, value) = built?;

    // Bracket 2 — the let-bound decl itself (oracle: `withLetDecl …
    // (nondep := config.nondep) fun x => …`), same restore-on-every-path
    // discipline.
    let cp_let = elab.mctx.lctx_checkpoint();
    let result = (|| {
        let fvar = elab
            .mctx
            .push_let_decl(name, ty, value)
            .map_err(ElabError::from)?;
        let body = elab.elab_term_ensuring_type(&body_elem, kinds, expected)?;
        elab.mctx
            .mk_let_expr(fvar, body, non_dep)
            .map_err(ElabError::from)
    })();
    elab.mctx.lctx_restore(cp_let);
    result
}
```

- [ ] **Step 5: Register the dispatch arms**

In `crates/leanr_elab/src/dispatch.rs` `elaborator_name_for`, add after the `fun` arm:

```rust
        "Lean.Parser.Term.let" => Some("let"),
        "Lean.Parser.Term.have" => Some("have"),
```

In `dispatch`, add after the `Lean.Parser.Term.fun` arm and before the catch-all `(other, _)` arm:

```rust
        ("Lean.Parser.Term.let", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_let_like(elab, node, kinds, expected, false)
        }
        ("Lean.Parser.Term.have", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_let_like(elab, node, kinds, expected, true)
        }
```

In the "Deferred" doc block of `dispatch.rs`, replace the binders line — every M4b-2 binder form has now landed:

```text
///   letI / haveI / let_fun / let_delayed / letrec  later slice (own oracle tier each)
///   application, @, named/optional args ........ M4b-3
```

(The `binders: let/have … M4b-2 plan 3` line goes away; the remaining lines are unchanged.)

- [ ] **Step 6: Run the smoke tests to verify they pass**

Run: `cargo test -p leanr_elab --test binder_smoke -- let_ have_`
Expected: PASS (all nine new `let_*`/`have_*` tests).

- [ ] **Step 7: Full crate tests + the existing gate**

Run: `cargo test -p leanr_elab && mise run elab:fast`
Expected: PASS — the new tests, plan-1/plan-2 smoke tests, and the M4b-1/plan-1/plan-2 differential corpus, all unchanged.

- [ ] **Step 8: Format + commit**

```bash
cargo fmt
git add crates/leanr_elab/src/builtin/binder.rs crates/leanr_elab/src/dispatch.rs crates/leanr_elab/tests/binder_smoke.rs
git commit -m "M4b-2 plan3: elab_let_like (let/have, one elaborator + non_dep bool) + dispatch arms + smoke tests"
```

---

### Task 3: differential oracle corpus — the authoritative gate

**Files:**
- Modify: `tests/fixtures/elab/dump_elab.lean`
- Regenerate: `tests/fixtures/elab/elab-queries.jsonl`
- (Verify only, expected no change) `tests/fixtures/elab/Elab0.lean` / `Elab0.olean`

**Interfaces:**
- Consumes: Task 2's `elab_let_like` via the dispatch arms; the existing `oracle_elab` gate auto-iterates every corpus line, so no Rust change is needed — `let` (with its `nd` bit), `lam`, `pi`, `bvar`, `const`, and `mvar` are all already encoded and decoded (`crates/leanr_meta/tests/support/mod.rs`).

**Prerequisite:** the pinned Lean toolchain (`mise run elan:bootstrap` provides it). This task regenerates the committed fixtures; it is the only task that runs Lean.

- [ ] **Step 1: Add the `let` and `have` query lists to the dumper**

In `tests/fixtures/elab/dump_elab.lean`, add two lists immediately after `funQueries` (~line 248), mirroring the existing `List (String × String)` lists:

```lean
def letQueries : List (String × String) := [
  ("let/typed",       "let x : Nat := Nat.zero; x"),
  ("let/elided",      "let x := Nat.zero; x"),
  ("let/unused",      "let x : Nat := Nat.zero; Nat"),
  ("let/anon",        "let _ : Nat := Nat.zero; Nat"),
  ("let/nested",      "let x : Nat := Nat.zero; let y : Nat := x; y"),
  ("let/typeValue",   "let a : Type := Nat; a"),
  ("let/funValue",    "let f : Nat -> Nat := fun y => y; f"),
  ("let/binders",     "let f (y : Nat) : Nat := y; f"),
  ("let/twoBinders",  "let f (y : Nat) (z : Nat) : Nat := y; f"),
  ("let/binderIdent", "let f y : Nat := y; f"),
  ("let/inFun",       "fun (z : Nat) => let x : Nat := z; x"),
  ("let/ascribed",    "(let x : Nat := Nat.zero; x : Nat)")
]

def haveQueries : List (String × String) := [
  ("have/typed",    "have h : Nat := Nat.zero; h"),
  ("have/elided",   "have h := Nat.zero; h"),
  ("have/unused",   "have h : Nat := Nat.zero; Nat"),
  ("have/hygiene",  "have : Nat := Nat.zero; this"),
  ("have/nested",   "have h : Nat := Nat.zero; have g : Nat := h; g"),
  ("have/funValue", "have f : Nat -> Nat := fun y => y; f"),
  ("have/ascribed", "(have h : Nat := Nat.zero; h : Nat)")
]
```

Concatenate them into the emit loop (dump_elab.lean, the `for (id, src) in …` line):

```lean
    for (id, src) in strQueries ++ identQueries ++ sortAscHoleQueries ++ binderQueries ++ funQueries ++ letQueries ++ haveQueries do
```

- [ ] **Step 2: Confirm no new constant is needed in `Elab0.lean`**

Every term above references only `Nat`, `Nat.zero`, and `Type`. `Nat` is declared as an `inductive` with constructors `zero`/`succ` in `Elab0.lean`, so `Nat.zero` exists; `Type` is a keyword.

Run: `grep -n "inductive Nat" -A 3 tests/fixtures/elab/Elab0.lean`
Expected: the `inductive Nat` block with `| zero : Nat`. No edit to `Elab0.lean`, and therefore **no `Elab0.olean` regeneration**, is required.

- [ ] **Step 3: Regenerate the corpus**

Run: `mise run fixtures:regen-elab`
Expected: `tests/fixtures/elab/elab-queries.jsonl` gains 19 lines (ids `let/*`, `have/*`).

Run: `git diff tests/fixtures/elab/elab-queries.jsonl`
Expected: additions only. Sanity-check the oracle's emitted `exp` against the design-phase probe:
- `let/typed` → `{"k":"let","nd":false,"t":{"k":"const","n":"Nat","us":[]},"v":{"k":"const","n":"Nat.zero","us":[]},"b":{"k":"bvar","i":0}}`
- `have/typed` → the same object with `"nd":true`.
- `let/elided` → identical to `let/typed` (the elided type resolves to `Nat`).
- `let/unused` and `let/anon` → a `let` whose `b` is `{"k":"const","n":"Nat","us":[]}` (the binding is retained).
- `let/binders`, `let/twoBinders`, `let/binderIdent` → `t` a `pi` chain of `Nat`s, `v` a `lam` chain, `b` `{"k":"bvar","i":0}`.
- `have/hygiene` → identical to `have/typed`.
- `let/ascribed` / `have/ascribed` → identical to `let/typed` / `have/typed` (the ascription does not change the emitted node).

If any oracle `exp` differs from the above, **do not edit the fixture to match the elaborator** — that is the differential gate surfacing a real shape assumption to reconcile (the M4b-1 num/char lesson). Re-read the divergence against `elab_let_like` and the design spec, fix the code, and regenerate.

- [ ] **Step 4: Run the authoritative differential gate**

Run: `mise run elab:fast`
Expected: PASS — leanr's elaboration of every corpus term (M4b-1 + plan-1 + plan-2 tiers + the 19 `let`/`have` terms) matches the oracle byte-for-byte after canonicalization. A divergence is the differential test doing its job: fix `elab_let_like` (not the fixture) and re-run, cross-checking against the Task 2 smoke tests.

- [ ] **Step 5: Run the full workspace test + CI gate locally**

Run: `mise run ci`
Expected: PASS (`cargo fmt --check` + clippy + the full workspace test, which picks up `oracle_elab`, `binder_smoke`, and the Task 1 unit tests).

- [ ] **Step 6: Commit**

```bash
git add tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -m "M4b-2 plan3: differential corpus for let/have (19 terms)"
```

---

## Self-Review

**Spec coverage (against the design spec's § Amendment 2 + § Plan 3 — canonical):**
- One `elab_let_like` + `non_dep` bool on two dispatch arms → Task 2 (Steps 4-5). ✔
- `MetaCtx::push_let_decl` + `mk_let_expr` (additive, TCB-neutral, `non_dep`-carrying because the kernel's `mk_binding` hardcodes `false`) → Task 1. ✔
- Grammar walk (`letConfig` / `letDecl` → `letIdDecl` / `letId` / binders / optType / value / body) → Task 2 Step 4, against the probe-confirmed shapes in § Confirmed parse-tree shapes. ✔
- `letId` three shapes — `<ident>`, `Term.hole` → anonymous, `hygieneInfo` → `this` → Task 2 Step 3 (`extract_let_id_name`); verified by `let_anonymous_binder` / `have_hygiene_binder_is_named_this` and corpus `let/anon` / `have/hygiene`. ✔
- Elided type → fresh mvar assigned by the value → Task 2 Step 4; verified by `let_elided_type_is_inferred_from_the_value` and corpus `let/elided`, `have/elided`. ✔
- `letIdBinders` telescope, bracketed-explicit **and** bare-ident → Task 2 Step 3 (`push_let_binders`); verified by `let_bracketed_binder_telescope` / `let_bare_ident_binder_unifies_its_domain` and corpus `let/binders`, `let/twoBinders`, `let/binderIdent`. ✔
- Expected type propagated to the body (not the value) → Task 2 Step 4 (`elab_term_ensuring_type(&body_elem, kinds, expected)`); verified by corpus `let/ascribed`, `have/ascribed`. ✔
- Restore on every exit path including `Err`, both brackets → Task 2 Step 4 (`lctx_restore` outside each closure's `?`-carrying body). ✔
- Named seams: implicit/strict/instance let binders, non-`letIdDecl` alternatives, non-empty `letConfig` → Task 2 Steps 3-4, each an `UnsupportedSyntax` naming its owner; `letI`/`haveI`/`let_fun`/`let_delayed`/`let_tmp`/`letrec` fall through to the catch-all and are named in the Deferred doc block (Step 5). ✔
- 19-term differential tier, no new `Elab0` constant → Task 3. ✔
- No scheduler / no ladder fields / entry point unchanged → honored; no task touches `elab.rs` state or the entry point. ✔

**Placeholder scan:** No `TBD` / "implement later" / "handle edge cases". Every code step shows the actual code; every run step shows the command and the expected result; every deferred form returns a named `UnsupportedSyntax` rather than a silent gap.

**Type consistency:** `push_let_decl(Option<NameId>, ExprId, ExprId) -> Result<ExprId, MetaError>` and `mk_let_expr(ExprId, ExprId, bool) -> Result<ExprId, MetaError>` are defined in Task 1 and called in Task 2 with exactly those argument shapes. `elab_let_like(&mut TermElabM, &SyntaxNode, &KindInterner, Option<ExprId>, bool) -> Result<ExprId, ElabError>` matches both dispatch-arm call sites. `extract_let_id_name` returns `Option<NameId>`, which is what `push_let_decl`'s `name` parameter takes. `push_let_binders` returns `Vec<ExprId>`, consumed by `mk_lambda`/`mk_forall` (`&[ExprId]`). `BinderGroup`'s fields (`names: Vec<Option<NameId>>`, `ty: SynElem`, `bi: BinderInfo`) are used as plan 1 defines them. `Node::LetE { ty, value, body, non_dep, .. }` matches the kernel variant (`bank/terms.rs:663`) and the encoder's `"k":"let"` arm with its `"t"`/`"v"`/`"b"`/`"nd"` keys. Kind strings (`Lean.Parser.Term.let`/`.have`/`.letDecl`/`.letIdDecl`/`.letId`/`.typeSpec`/`.hole`, `hygieneInfo`, `<ident>`) are the probe-confirmed names.

**Known follow-ups (out of plan 3, named for later slices):** the entire `synthesizeSyntheticMVars` fixpoint + postponement + `TypeClass`/default-instance/error pass, application/`@`/named args, coercions, num/char literals, implicit and instance let binders (M4b-3); `letI`/`haveI`/`let_fun`/`let_delayed`/`let_tmp`/`letrec` and `let rec` lifting (later M4, each needing its own oracle tier); real macro-scope hygiene (whichever slice first needs it).
