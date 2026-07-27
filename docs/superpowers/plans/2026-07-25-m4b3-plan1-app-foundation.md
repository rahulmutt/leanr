# M4b-3 Plan 1 — Application Foundation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the `ElabAppArgs` state machine so that function applications — explicit, implicit and strict-implicit arguments, named arguments, eta-expansion, and expected-type propagation — elaborate byte-for-byte identically to the pinned Lean oracle, and route bare identifiers, `@f`, and `f.{u}` through it as the oracle does.

**Architecture:** A new `leanr_elab/src/app/` module transliterates `Lean/Elab/App.lean`'s `ElabAppArgs` namespace. Lean's `ReaderT Context (StateRefT State TermElabM)` becomes one `AppElab` struct holding an immutable `Context`, a mutable `State`, and `&mut TermElabM`; each `private def foo : M α` in the oracle becomes a method. M4b-1's standalone leaf `ident` elaborator is retired and its constant-resolution logic moves into the application head resolver, because in the oracle a bare identifier *is* a zero-argument application. Instance-implicit arguments, the synthetic-mvar fixpoint, coercions, and literals are **not** in this plan — each is a named seam owned by M4b-3 plans 2-5.

**Tech Stack:** Rust (workspace crates `leanr_elab`, `leanr_meta`, `leanr_kernel`, `leanr_syntax`), `cargo test`, mise tasks, Lean 4 `v4.33.0-rc1` as the differential oracle (dumper: `tests/fixtures/elab/dump_elab.lean`).

**Spec:** `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` (§ Plan decomposition → P1; § P1 — the application machinery).

## Global Constraints

- **Pinned oracle:** `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`). Every oracle citation below is against `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`. **Never bump the pin.**
- **`leanr_kernel` is byte-untouched.** It depends on no workspace crate; no existing kernel function is modified. No new kernel function is added by this plan.
- **`leanr_meta/src` additions are additive, TCB-neutral, behavior-neutral accessors only.** This plan adds exactly one: `MetaCtx::instantiate_beta_rev_range` (Task 1). Nothing else in `leanr_meta` changes. `Expr` destructuring from `leanr_elab` uses the already-public `Store::expr_node` (`crates/leanr_kernel/src/bank/terms.rs:615`).
- **Named-seam discipline.** Every unimplemented construct returns `ElabError::UnsupportedSyntax` carrying a message that names the owning slice — never a panic, never a wrong `ExprId`, never a silent fall-through that emits a different term.
- **Oracle discipline.** Correctness is byte-for-byte agreement with the oracle's canonical `Expr` via `crates/leanr_elab/tests/oracle_elab.rs`. **Never hand-write an `exp` value in `elab-queries.jsonl`** — always regenerate with `mise run fixtures:regen-elab` and commit what the oracle emits.
- **The dumper's entry point does NOT change in this plan.** It stays `elabTerm stx none` + `instantiateMVars` (`dump_elab.lean`'s module doc). Expected types are induced from **source ascription** — `(f x : T)` — which the existing dumper already supports. Adding `synthesizeSyntheticMVars` is P2's job.
- **Before every commit:** `mise run fmt` then `mise run lint` then `mise run test` (or `mise run ci`, which gates all three plus `cargo fmt --check`). Test gates do not cover formatting; CI does.
- **Regeneration needs the elan toolchain** (`mise run elan:bootstrap` once). It never runs in CI.

---

## File Structure

**Created:**

| File | Responsibility |
|---|---|
| `crates/leanr_elab/src/app/mod.rs` | module wiring + `elab_app` / `elab_atom` public entry points |
| `crates/leanr_elab/src/app/expand.rs` | `Arg`, `NamedArg`, `expand_app`, `expand_args` — syntax → argument lists. No `Expr` work. |
| `crates/leanr_elab/src/app/state.rs` | `Context`, `State`, `AppElab`, and `fType` navigation (`f_type_is_forall`, `get_param_name/type/info`, `get_arg_expected_type`, `get_f_type`, `has_args_to_process`) |
| `crates/leanr_elab/src/app/args.rs` | the `main` loop and the parameter-kind arms (`process_explicit_arg`, `process_implicit_arg`, `process_strict_implicit_arg`, `add_new_arg`, `add_implicit_arg`, `add_eta_arg`, `elab_and_add_new_arg`) |
| `crates/leanr_elab/src/app/propagate.rs` | `propagate_expected_type`, `get_resulting_type`, `should_propagate_expected_type_for` |
| `crates/leanr_elab/src/app/finalize.rs` | `finalize` — eta-lambda wrap, expected-type propagation, the P2 instance-mvar seam |
| `crates/leanr_elab/src/app/head.rs` | `elab_app_fn`: resolve the application head (ident → `Expr.const` with fresh level mvars or an fvar; `@`; `.{u}`) — the logic retired from `builtin/ident.rs` |
| `crates/leanr_elab/src/app/overload.rs` | the single-candidate shape guard |
| `crates/leanr_elab/tests/app_smoke.rs` | Rust-level unit tests for the state machine (shapes and orderings the oracle corpus cannot distinguish) |

**Modified:**

| File | Change |
|---|---|
| `crates/leanr_meta/src/metactx.rs` | add `instantiate_beta_rev_range` (Task 1) |
| `crates/leanr_elab/src/lib.rs` | `pub mod app;` + update the deferral ledger in the module doc |
| `crates/leanr_elab/src/dispatch.rs` | register `Lean.Parser.Term.app`, re-point `<ident>`, add `Term.explicit` / `Term.explicitUniv`; update the deferral table |
| `crates/leanr_elab/src/error.rs` | new variants (Task 4, Task 8) |
| `tests/fixtures/elab/Elab0.lean` | add the corpus constants later tasks need (Task 7) |
| `tests/fixtures/elab/dump_elab.lean` | one new query list per corpus-bearing task |
| `tests/fixtures/elab/elab-queries.jsonl` | regenerated (never hand-edited) |
| `tests/fixtures/elab/Elab0.olean` | rebuilt when `Elab0.lean` changes |

**Deleted:**

| File | Reason |
|---|---|
| `crates/leanr_elab/src/builtin/ident.rs` | the oracle has no standalone ident elaborator; `elabIdent := elabAtom` (`App.lean:2246`). Its logic moves to `app/head.rs` (Task 4). |

---

### Task 1: `MetaCtx::instantiate_beta_rev_range`

The oracle's `State.getFType` is `s.fType.instantiateBetaRevRange 0 s.fArgs.size s.fArgs` (`App.lean:232-237`). `leanr_kernel::subst::instantiate_rev` is public, but the beta step needs `whnf.rs`'s `head_beta`, which is `pub(crate)` to `leanr_meta` — hence one additive accessor.

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs` (add a method next to `mk_let_expr`, which ends at line 635+)
- Test: `crates/leanr_meta/src/metactx.rs` (its existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Produces: `pub fn instantiate_beta_rev_range(&mut self, e: ExprId, args: &[ExprId]) -> Result<ExprId, MetaError>` on `MetaCtx`. `args` is innermost-first, matching `instantiate_rev`'s documented convention (`subst[len-1]` replaces `#0`).

- [ ] **Step 1: Write the failing test**

Add to the `#[cfg(test)] mod tests` block in `crates/leanr_meta/src/metactx.rs`:

```rust
/// `instantiate_beta_rev_range` on a forall BODY with one loose bvar:
/// substituting `Nat` for `#0` yields `Nat` itself. Mirrors what
/// `ElabAppArgs.State.getFType` does after one argument is consumed.
#[test]
fn instantiate_beta_rev_range_substitutes_loose_bvar() {
    let env = crate::test_support::env_nat_only();
    let view = env.view();
    let mut scratch = Store::scratch();
    let mut ctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        &[],
        &[],
        &[],
        &[],
        &[],
    );
    // `#0` — a loose bvar standing for the consumed argument.
    let bvar = ctx.store_mut().expr_bvar(None, 0).unwrap();
    let nat = crate::test_support::const_nat(&mut ctx);
    let got = ctx.instantiate_beta_rev_range(bvar, &[nat]).unwrap();
    assert_eq!(got, nat, "#0 must be replaced by the single argument");
}

/// The empty-args fast path is the identity, and must not re-intern.
#[test]
fn instantiate_beta_rev_range_empty_is_identity() {
    let env = crate::test_support::env_nat_only();
    let view = env.view();
    let mut scratch = Store::scratch();
    let mut ctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        &[],
        &[],
        &[],
        &[],
        &[],
    );
    let nat = crate::test_support::const_nat(&mut ctx);
    assert_eq!(ctx.instantiate_beta_rev_range(nat, &[]).unwrap(), nat);
}
```

If `crate::test_support` has no `env_nat_only` / `const_nat` helper with these exact names, use whichever fixture builder that module already exposes (read `crates/leanr_meta/src/test_support.rs` first) — do not add new helpers to it for this test.

- [ ] **Step 2: Run the test to verify it fails**

Run: `cargo test -p leanr_meta instantiate_beta_rev_range`
Expected: FAIL — `no method named instantiate_beta_rev_range found for struct MetaCtx`.

- [ ] **Step 3: Write the implementation**

Add to the `impl<'e> MetaCtx<'e>` block in `crates/leanr_meta/src/metactx.rs`, immediately after `mk_let_expr`:

```rust
/// oracle: `Expr.instantiateBetaRevRange 0 args.size args`, as used by
/// `ElabAppArgs.State.getFType` (`Lean/Elab/App.lean:232-237`) to
/// instantiate a partially-applied function type's loose bvars with the
/// arguments consumed so far. `args` is innermost-first — the same
/// convention `leanr_kernel::subst::instantiate_rev` documents
/// (`subst[len-1]` replaces `#0`).
///
/// Additive + behavior-neutral, and the reason it lives HERE rather than
/// in `leanr_elab`: the substitution half (`instantiate_rev`) is public
/// kernel API the elaborator could call itself, but the beta half
/// (`head_beta`, `whnf.rs:1767`) is `pub(crate)` to this crate. Exposes
/// no new capability, adds no state, changes no existing path.
pub fn instantiate_beta_rev_range(
    &mut self,
    e: ExprId,
    args: &[ExprId],
) -> Result<ExprId, MetaError> {
    if args.is_empty() {
        return Ok(e);
    }
    let inst = leanr_kernel::subst::instantiate_rev(
        self.scratch,
        Some(self.view.store),
        e,
        args,
        &mut self.guard,
    )?;
    self.head_beta(inst)
}
```

Check the `use` list at the top of `metactx.rs` — if `instantiate_rev` is not already imported there, call it fully qualified as written above rather than adding an import.

- [ ] **Step 4: Run the test to verify it passes**

Run: `cargo test -p leanr_meta instantiate_beta_rev_range`
Expected: PASS (2 tests).

- [ ] **Step 5: Confirm nothing else in leanr_meta moved**

Run: `cargo test -p leanr_meta`
Expected: PASS — this is an additive method; any other failure means something non-additive was touched.

- [ ] **Step 6: Format, lint, commit**

```bash
mise run fmt
mise run lint
git add crates/leanr_meta/src/metactx.rs
git commit -m "M4b-3 P1 task 1: MetaCtx::instantiate_beta_rev_range accessor"
```

---

### Task 2: `Arg` / `NamedArg` / `expand_app`

Split the `Term.app` syntax node into `(head, named_args, positional_args, ellipsis)`. Oracle: `expandApp` / `expandArgs` (`Lean/Elab/Arg.lean:62-84`) — `stx[0]` is the head, `stx[1].getArgs` are the arguments, a trailing `Term.ellipsis` sets the flag and is popped, a non-trailing `..` is an error, and `Term.namedArgument`'s `stx[1]` is the name with `stx[3]` the value.

**Files:**
- Create: `crates/leanr_elab/src/app/mod.rs`, `crates/leanr_elab/src/app/expand.rs`
- Modify: `crates/leanr_elab/src/lib.rs`
- Test: `crates/leanr_elab/tests/app_smoke.rs` (create)

**Interfaces:**
- Consumes: nothing from Task 1.
- Produces:
  - `pub enum Arg { Stx(SynElem), Expr(ExprId) }`
  - `pub struct NamedArg { pub name: String, pub val: Arg, pub num_implicit_params: usize }`
  - `pub fn expand_app(node: &SyntaxNode, kinds: &KindInterner) -> Result<(SynElem, Vec<NamedArg>, Vec<Arg>, bool), ElabError>`
  - `pub fn expand_args(items: &[SynElem], kinds: &KindInterner) -> Result<(Vec<NamedArg>, Vec<Arg>, bool), ElabError>`

`NamedArg::name` is a `String` (the identifier's raw source text) rather than a `NameId`: named-argument matching compares against a *binder* name read out of the function's type, and Task 3's comparison helper renders that binder name to text once. Interning would force a store round-trip on every comparison for no benefit.

- [ ] **Step 1: Write the tree-shape probe test**

The `Term.app` child layout in leanr's rowan tree must be confirmed, not assumed — M4b-1 hit exactly this with `typeAscription` (see `builtin/ascription.rs`'s module doc). Create `crates/leanr_elab/tests/app_smoke.rs`:

```rust
//! M4b-3 P1 unit tests: the application state machine's shapes and
//! orderings. These are the properties the hermetic oracle corpus
//! (`oracle_elab.rs`) cannot distinguish — tree layout, argument
//! partitioning, and seam messages — so they get direct tests here.
//! Same spirit as `binder_smoke.rs`.

use leanr_syntax::{builtin, parse_term, tree::NodeOrToken};

/// PROBE (delete once the shape below is encoded in `expand.rs`): dump
/// the real child layout of a `Term.app` node so `expand_app` navigates
/// by confirmed positions, not assumed ones.
#[test]
fn probe_app_tree_shape() {
    let snap = builtin::snapshot();
    for src in ["Nat.succ Nat.zero", "Nat.succ Nat.zero Nat.zero"] {
        let parsed = parse_term(src, &snap);
        assert!(parsed.errors.is_empty(), "{src}: {:?}", parsed.errors);
        let root = parsed.tree.root();
        let app = root
            .first_child()
            .unwrap_or_else(|| panic!("{src}: no app node"));
        eprintln!("--- {src}: root child kind = {}", parsed.tree.kinds.name(app.kind()));
        for (i, ch) in app.children_with_tokens().enumerate() {
            eprintln!(
                "  [{i}] kind={} text={:?}",
                parsed.tree.kinds.name(ch.kind()),
                match &ch {
                    NodeOrToken::Node(n) => n.text().to_string(),
                    NodeOrToken::Token(t) => t.text().to_string(),
                }
            );
        }
    }
}
```

- [ ] **Step 2: Run the probe and record the shape**

Run: `cargo test -p leanr_elab --test app_smoke probe_app_tree_shape -- --nocapture`
Expected: PASS, printing the child list. **Write the observed layout into a comment in `expand.rs`** (which index is the head, whether the argument list is a wrapping `KIND_NULL` node or inline siblings, and whether trivia appears between children). Use `dispatch::non_trivia_children` for navigation, as every existing builtin does.

- [ ] **Step 3: Write the failing partitioning tests**

Append to `crates/leanr_elab/tests/app_smoke.rs`:

```rust
use leanr_elab::app::expand::{expand_app, Arg};

fn app_node(src: &str) -> (leanr_syntax::tree::SyntaxNode, leanr_syntax::parse::Parsed) {
    let snap = builtin::snapshot();
    let parsed = parse_term(src, &snap);
    assert!(parsed.errors.is_empty(), "{src}: {:?}", parsed.errors);
    let node = parsed.tree.root().first_child().expect("app node");
    (node, parsed)
}

#[test]
fn expand_app_splits_head_and_positional_args() {
    let (node, parsed) = app_node("Nat.succ Nat.zero");
    let (head, named, args, ellipsis) = expand_app(&node, &parsed.tree.kinds).unwrap();
    assert_eq!(head.kind(), parsed.tree.kinds.id("<ident>").unwrap());
    assert!(named.is_empty());
    assert_eq!(args.len(), 1);
    assert!(matches!(args[0], Arg::Stx(_)));
    assert!(!ellipsis);
}

#[test]
fn expand_app_collects_named_args() {
    let (node, parsed) = app_node("Nat.succ (n := Nat.zero)");
    let (_head, named, args, _e) = expand_app(&node, &parsed.tree.kinds).unwrap();
    assert_eq!(named.len(), 1, "named args: {:?}", named.len());
    assert_eq!(named[0].name, "n");
    assert!(args.is_empty(), "a named arg is not positional");
}

#[test]
fn expand_app_pops_trailing_ellipsis() {
    let (node, parsed) = app_node("Nat.succ ..");
    let (_head, named, args, ellipsis) = expand_app(&node, &parsed.tree.kinds).unwrap();
    assert!(ellipsis, "trailing `..` sets the flag");
    assert!(named.is_empty() && args.is_empty(), "`..` is not an argument");
}

#[test]
fn expand_app_rejects_duplicate_named_arg() {
    let (node, parsed) = app_node("Nat.succ (n := Nat.zero) (n := Nat.zero)");
    match expand_app(&node, &parsed.tree.kinds) {
        Err(leanr_elab::ElabError::DuplicateNamedArg(n)) => assert_eq!(n, "n"),
        other => panic!("expected DuplicateNamedArg, got {other:?}"),
    }
}
```

If `parse_term` rejects any of these sources, record the parse error in a comment and drop that specific test rather than working around the parser — a missing surface is `leanr_syntax`'s slice, not this one. `kinds.id(..)` may have a different name on `KindInterner`; read `crates/leanr_syntax/src/kind.rs` and use the real lookup (comparing `kinds.name(head.kind()) == "<ident>"` is an acceptable substitute).

- [ ] **Step 4: Run the tests to verify they fail**

Run: `cargo test -p leanr_elab --test app_smoke expand_app`
Expected: FAIL — `unresolved import leanr_elab::app`.

- [ ] **Step 5: Implement `expand.rs`**

Create `crates/leanr_elab/src/app/expand.rs`:

```rust
//! Syntax → argument lists. Oracle: `expandApp`/`expandArgs`
//! (`Lean/Elab/Arg.lean:62-84`). Pure syntax navigation — no `Expr` is
//! built here, and nothing in this file touches `MetaCtx`.
//!
//! Confirmed `Term.app` child layout (probe, Task 2 step 2):
//! <PASTE THE OBSERVED LAYOUT HERE>

use crate::dispatch::{non_trivia_children, SynElem};
use crate::error::ElabError;
use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

/// oracle: `inductive Arg` (`Arg.lean:19-21`) — an argument is either
/// unelaborated syntax or an already-elaborated `Expr`. The `Expr` arm
/// has no P1 producer (it exists for dot-notation/`pipeProj` in M4b-4
/// and for `binop%`), but the type carries it so later slices need not
/// reshape the state machine.
#[derive(Debug, Clone)]
pub enum Arg {
    Stx(SynElem),
    Expr(ExprId),
}

/// oracle: `structure NamedArg` (`Arg.lean:34-45`).
#[derive(Debug, Clone)]
pub struct NamedArg {
    /// The identifier's raw source text (see the module doc on why this
    /// is not a `NameId`).
    pub name: String,
    pub val: Arg,
    /// oracle: `NamedArg.numImplicitParams` — overrides the binder info
    /// of the first N parameters to implicit. Only ever nonzero for
    /// structure-projection expansion (`f.val`), which is M4b-4, so
    /// every P1 producer sets 0. The field exists because
    /// `process_explicit_arg` branches on it.
    pub num_implicit_params: usize,
}

/// oracle: `expandApp` (`Arg.lean:82-84`).
pub fn expand_app(
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<(SynElem, Vec<NamedArg>, Vec<Arg>, bool), ElabError> {
    let ch = non_trivia_children(node);
    let head = ch
        .first()
        .cloned()
        .ok_or_else(|| ElabError::IllFormedSyntax("app: no function child".to_string()))?;
    // Argument items: whatever the probe showed — either the children of
    // a single wrapping node at index 1, or `ch[1..]` directly.
    let items: Vec<SynElem> = /* per the recorded layout */ ch[1..].to_vec();
    let (named, args, ellipsis) = expand_args(&items, kinds)?;
    Ok((head, named, args, ellipsis))
}

/// oracle: `expandArgs` (`Arg.lean:62-80`). Note the exact order: the
/// trailing `..` is popped FIRST (so a `..` anywhere else is the error
/// case), then each remaining item is classified.
pub fn expand_args(
    items: &[SynElem],
    kinds: &KindInterner,
) -> Result<(Vec<NamedArg>, Vec<Arg>, bool), ElabError> {
    let mut items = items.to_vec();
    let mut ellipsis = false;
    if let Some(last) = items.last() {
        if kinds.name(last.kind()) == "Lean.Parser.Term.ellipsis" {
            items.pop();
            ellipsis = true;
        }
    }
    let mut named: Vec<NamedArg> = Vec::new();
    let mut args: Vec<Arg> = Vec::new();
    for item in items {
        match kinds.name(item.kind()) {
            "Lean.Parser.Term.namedArgument" => {
                let node = item.as_node().ok_or_else(|| {
                    ElabError::IllFormedSyntax("namedArgument is not a node".to_string())
                })?;
                let nch = non_trivia_children(node);
                // oracle: `stx[1].getId` is the name, `stx[3]` the value.
                // Positions are over the trivia-stripped child list, the
                // same convention `non_trivia_children`'s doc describes.
                let name_tok = nch.get(1).ok_or_else(|| {
                    ElabError::IllFormedSyntax("namedArgument: no name".to_string())
                })?;
                let name = match name_tok {
                    leanr_syntax::tree::NodeOrToken::Token(t) => t.text().to_string(),
                    leanr_syntax::tree::NodeOrToken::Node(n) => n.text().to_string(),
                };
                let val = nch
                    .get(3)
                    .cloned()
                    .ok_or_else(|| {
                        ElabError::IllFormedSyntax("namedArgument: no value".to_string())
                    })?;
                // oracle: `addNamedArg` (`Arg.lean:55-59`) errors on a
                // repeated name rather than silently keeping one.
                if named.iter().any(|na| na.name == name) {
                    return Err(ElabError::DuplicateNamedArg(name));
                }
                named.push(NamedArg {
                    name,
                    val: Arg::Stx(val),
                    num_implicit_params: 0,
                });
            }
            "Lean.Parser.Term.ellipsis" => {
                // oracle: `throwErrorAt stx "unexpected '..'"` — only a
                // TRAILING `..` is legal, and that one was popped above.
                return Err(ElabError::IllFormedSyntax("unexpected '..'".to_string()));
            }
            _ => args.push(Arg::Stx(item)),
        }
    }
    Ok((named, args, ellipsis))
}
```

Adjust the `items` line and the `nch.get(1)`/`nch.get(3)` indices to the layout the probe actually printed; leave the recorded layout in the module doc.

Create `crates/leanr_elab/src/app/mod.rs`:

```rust
//! M4b-3 P1: the application elaborator. Oracle: `Lean/Elab/App.lean`'s
//! `ElabAppArgs` namespace. See
//! docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md
//! § P1 — the application machinery.
//!
//! NOT in this plan, each a named seam (never a silent fall-through):
//!   instance-implicit arguments + the synthetic-mvar fixpoint . P2
//!   num/char/scientific literals ......................... P3
//!   coercions (CoeT/CoeFun/CoeSort, mkCoe) ............... P4
//!   optParam defaults / autoParam / `..` ellipsis ........ P5
//!   implicit-lambda insertion ............................ P5
//!   overload resolution (candidates > 1) ................. resolve_global slice
//!   elabAsElim, dot notation, LVal machinery ............. M4b-4

pub mod expand;
```

Add `pub mod app;` to `crates/leanr_elab/src/lib.rs` (next to `pub mod builtin;`).

Add to `crates/leanr_elab/src/error.rs`'s `ElabError`:

```rust
    /// oracle: `addNamedArg`'s "Argument `x` was already set"
    /// (`Arg.lean:55-59`).
    DuplicateNamedArg(String),
    /// A syntax node whose shape contradicts the grammar (missing child,
    /// wrong node/token variant, a non-trailing `..`). Distinct from
    /// `UnsupportedSyntax`, which means "this construct's slice has not
    /// landed"; this means "this tree cannot be what it claims to be".
    IllFormedSyntax(String),
```

- [ ] **Step 6: Run the tests to verify they pass**

Run: `cargo test -p leanr_elab --test app_smoke expand_app`
Expected: PASS (4 tests).

- [ ] **Step 7: Delete the probe, format, lint, commit**

Remove `probe_app_tree_shape` (its output now lives in `expand.rs`'s module doc — M4b-1's "throwaway probe, never landed" precedent).

```bash
mise run fmt
mise run lint
cargo test -p leanr_elab
git add crates/leanr_elab/src/app crates/leanr_elab/src/lib.rs crates/leanr_elab/src/error.rs crates/leanr_elab/tests/app_smoke.rs
git commit -m "M4b-3 P1 task 2: Arg/NamedArg + expand_app argument partitioning"
```

---

### Task 3: `Context`, `State`, `AppElab`, and `fType` navigation

**Files:**
- Create: `crates/leanr_elab/src/app/state.rs`
- Modify: `crates/leanr_elab/src/app/mod.rs`
- Test: `crates/leanr_elab/tests/app_smoke.rs`

**Interfaces:**
- Consumes: `MetaCtx::instantiate_beta_rev_range` (Task 1); `Arg`/`NamedArg` (Task 2).
- Produces:
  - `pub struct Context { pub ellipsis: bool, pub explicit: bool, pub result_is_out_param_support: bool, pub num_implicit_params: usize }`
  - `pub struct State { pub f: ExprId, pub f_type: ExprId, pub f_args: Vec<ExprId>, pub args: Vec<Arg>, pub named_args: Vec<NamedArg>, pub expected_type: Option<ExprId>, pub eta_args: Vec<(Option<NameId>, ExprId)>, pub to_set_error_ctx: Vec<MVarId>, pub inst_mvars: Vec<MVarId>, pub propagate_expected: bool, pub result_type_out_param: Option<MVarId>, pub found_named_args: Vec<String> }`
  - `pub struct AppElab<'a, 'e> { pub ctx: Context, pub st: State, pub elab: &'a mut TermElabM<'e> }`
  - methods: `param_idx() -> usize`, `f_type_is_forall() -> Result<bool, ElabError>`, `get_param_name() -> Option<NameId>`, `get_param_type() -> Result<ExprId, ElabError>`, `get_param_info() -> Result<BinderInfo, ElabError>`, `get_arg_expected_type() -> Result<ExprId, ElabError>`, `get_f_type() -> Result<ExprId, ElabError>`, `has_args_to_process() -> bool`, `node(ExprId) -> Node`

**Every `State`/`Context` field is present from this task**, including ones no P1 arm drives (`inst_mvars`, `result_type_out_param`, `to_set_error_ctx`, `found_named_args`). A missing arm is a named seam; a missing field is a silent fidelity hole, because the oracle branches on these far from where they are set (spec § P1).

- [ ] **Step 1: Write the failing tests**

Append to `crates/leanr_elab/tests/app_smoke.rs`:

```rust
mod support;

use leanr_elab::app::state::{AppElab, Context, State};

/// `f_type_is_forall` must WHNF a non-forall `fType` into one and cache
/// the result (oracle: `fTypeIsForall`, `App.lean:238-249`), and report
/// false without mutating `fType` when it does not reduce to a forall.
#[test]
fn f_type_is_forall_whnfs_and_caches() {
    let mut h = support::app_harness("Nat.succ");
    // `Nat.succ : Nat -> Nat` is already a forall.
    assert!(h.app.f_type_is_forall().unwrap());
    let cached = h.app.st.f_type;
    assert!(h.app.f_type_is_forall().unwrap());
    assert_eq!(h.app.st.f_type, cached, "second call must not re-reduce");
}

#[test]
fn f_type_is_forall_false_for_non_function() {
    let mut h = support::app_harness("Nat.zero");
    assert!(
        !h.app.f_type_is_forall().unwrap(),
        "Nat.zero : Nat is not a function type"
    );
}

/// `get_param_info` reads the CURRENT parameter's binder info, and
/// `param_idx` tracks `f_args.len()` (oracle: `State.paramIdx`,
/// `App.lean:230`).
#[test]
fn param_idx_tracks_f_args_len() {
    let mut h = support::app_harness("Nat.succ");
    assert_eq!(h.app.param_idx(), 0);
    assert!(h.app.f_type_is_forall().unwrap());
    assert_eq!(
        h.app.get_param_info().unwrap(),
        leanr_kernel::BinderInfo::Default
    );
}
```

Create `crates/leanr_elab/tests/support/` usage: `crates/leanr_elab/tests/support/mod.rs` already exists (9 lines) and is shared by `oracle_elab.rs`. Add an `app_harness` there that builds the fixture env + `MetaCtx` + `TermElabM` + an `AppElab` whose head is the given source term:

```rust
/// Build an `AppElab` whose head is `head_src`, elaborated against the
/// committed `Elab0.olean` fixture env. Owns the env/store so the
/// borrows stay alive for the test's duration.
pub struct AppHarness<'a> {
    pub app: leanr_elab::app::state::AppElab<'a, 'a>,
}
```

Because `AppElab` borrows `TermElabM` which borrows the `Store`, a struct-returning harness needs the env/store to outlive it. The simplest shape that compiles is a closure-taking helper instead:

```rust
/// Run `k` with an `AppElab` whose head is `head_src`, elaborated
/// against the committed `Elab0.olean` fixture environment.
pub fn with_app_harness<R>(
    head_src: &str,
    k: impl FnOnce(&mut leanr_elab::app::state::AppElab) -> R,
) -> R;
```

Use the closure form and write the tests as `with_app_harness("Nat.succ", |app| { ... })`. Model the env/`MetaCtx`/`TermElabM` construction on `oracle_elab.rs:29-93` verbatim (`replay_fixture_in("elab", "Elab0.olean")`, `Store::scratch()`, `MetaCtx::new(..)`, `TermElabM::new(mctx, view)`), and build the head `Expr` by parsing `head_src` and calling `elab.elab_term(&elem, &kinds, None)` — which for a bare ident still routes to M4b-1's `builtin::ident` until Task 4 rewires it.

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_elab --test app_smoke f_type_is_forall`
Expected: FAIL — `unresolved import leanr_elab::app::state`.

- [ ] **Step 3: Implement `state.rs`**

Create `crates/leanr_elab/src/app/state.rs`:

```rust
//! `Context` + `State` + `AppElab`, and the `fType` navigation helpers.
//! Oracle: `App.lean:132-300`.
//!
//! Lean's `abbrev M := ReaderT Context (StateRefT State TermElabM)`
//! (`App.lean:229`) is ONE struct here, not a transformer stack: the
//! reader half is immutable after construction, the state half is
//! `&mut`, and each `private def foo : M α` becomes a method. Rust's
//! borrow checker then enforces exactly what `StateRefT` provides.

use leanr_kernel::bank::{ExprId, NameId, Node};
use leanr_kernel::BinderInfo;
use leanr_meta::MVarId;

use crate::app::expand::{Arg, NamedArg};
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `structure Context` (`App.lean:132-175`).
pub struct Context {
    /// `..` was used.
    pub ellipsis: bool,
    /// `@` was used.
    pub explicit: bool,
    /// Special support for applications whose result type is the
    /// `outParam` of a local instance (`App.lean:141-168`). The oracle
    /// computes it as `env.contains ``Lean.Internal.coeM && flag &&
    /// !explicit` (`App.lean:1355`) — coercions must be available for
    /// the feature to make sense. P1 computes it the SAME way, which
    /// makes it `false` throughout the hermetic fixture env (prelude-mode
    /// `Elab0` declares no `Lean.Internal.coeM`) with no special-casing.
    /// The consuming logic lands in P2 with the fixpoint.
    pub result_is_out_param_support: bool,
    /// oracle: `Context.numImplicitParams` — cached max over
    /// `namedArgs`; only nonzero for structure projections (M4b-4).
    pub num_implicit_params: usize,
}

/// oracle: `structure State` (`App.lean:178-227`). Every field the
/// oracle has is present, including those no P1 arm drives yet — see
/// this module's own doc and the design spec § P1.
pub struct State {
    pub f: ExprId,
    pub f_type: ExprId,
    pub f_args: Vec<ExprId>,
    pub args: Vec<Arg>,
    pub named_args: Vec<NamedArg>,
    pub expected_type: Option<ExprId>,
    /// oracle: `State.etaArgs` — `(binder name, fvar)` per eta-expanded
    /// parameter. Driven by Task 7.
    pub eta_args: Vec<(Option<NameId>, ExprId)>,
    /// oracle: `State.toSetErrorCtx`. Driven by Task 5.
    pub to_set_error_ctx: Vec<MVarId>,
    /// oracle: `State.instMVars` — instance-implicit argument mvars
    /// awaiting synthesis. NO P1 producer: `process_inst_implicit_arg`
    /// is P2's seam. `finalize` asserts it is empty (Task 4).
    pub inst_mvars: Vec<MVarId>,
    pub propagate_expected: bool,
    /// oracle: `State.resultTypeOutParam?`. No P1 producer (P2).
    pub result_type_out_param: Option<MVarId>,
    /// oracle: `State.foundNamedArgs` — valid named-argument names seen
    /// while walking the function's type; feeds the oracle's "invalid
    /// argument name" diagnostic. Driven by Task 7.
    pub found_named_args: Vec<String>,
}

pub struct AppElab<'a, 'e> {
    pub ctx: Context,
    pub st: State,
    pub elab: &'a mut TermElabM<'e>,
}

impl<'a, 'e> AppElab<'a, 'e> {
    /// Destructure an `ExprId`. `Store::expr_node` is already public
    /// (`leanr_kernel/src/bank/terms.rs:615`), so this needs no
    /// `leanr_meta` accessor — `mctx.store()` is the scratch store and
    /// `view.store` the persistent base, exactly the pairing every
    /// `base`-taking kernel method wants.
    pub fn node(&self, e: ExprId) -> Node {
        let base = self.elab.view.store;
        self.elab.mctx.store().expr_node(Some(base), e)
    }

    /// oracle: `State.paramIdx` (`App.lean:230`).
    pub fn param_idx(&self) -> usize {
        self.st.f_args.len()
    }

    /// oracle: `State.getFType` (`App.lean:232-237`) — `fType` with
    /// loose bvars instantiated by the arguments consumed so far.
    /// `f_args` is passed innermost-first, matching
    /// `instantiate_beta_rev_range`'s documented convention.
    pub fn get_f_type(&mut self) -> Result<ExprId, ElabError> {
        let f_type = self.st.f_type;
        let args = self.st.f_args.clone();
        let out = self
            .elab
            .mctx
            .instantiate_beta_rev_range(f_type, &args)?;
        self.st.f_type = out;
        Ok(out)
    }

    /// oracle: `fTypeIsForall` (`App.lean:238-249`). Returns true if
    /// `fType` is a function type, WHNF-ing and caching if needed, and
    /// guarantees the domain has no loose bvars.
    pub fn f_type_is_forall(&mut self) -> Result<bool, ElabError> {
        if let Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = self.node(self.st.f_type)
        {
            // oracle: instantiate the domain so `getParamType` is valid.
            // `has_loose_bvars` is not exposed; re-interning an
            // already-closed domain is a no-op on the hash-consed bank,
            // so instantiate unconditionally rather than adding an
            // accessor for the predicate.
            let args = self.st.f_args.clone();
            let d = self
                .elab
                .mctx
                .instantiate_beta_rev_range(binder_type, &args)?;
            if d != binder_type {
                let f_type = self
                    .elab
                    .mctx
                    .store_mut()
                    .expr_forall(None, binder_name, d, body, binder_info)
                    .map_err(leanr_meta::MetaError::from)?;
                self.st.f_type = f_type;
            }
            return Ok(true);
        }
        let f_type = self.get_f_type()?;
        let reduced = self.whnf_forall(f_type)?;
        self.st.f_type = reduced;
        Ok(matches!(self.node(reduced), Node::Forall { .. }))
    }

    /// oracle: `whnfForall` (`Lean/Meta/Basic.lean`) — WHNF, but keep the
    /// ORIGINAL term if the reduct is not a forall. Composed from the
    /// public `MetaCtx::whnf`; no accessor needed.
    fn whnf_forall(&mut self, e: ExprId) -> Result<ExprId, ElabError> {
        let r = self.elab.mctx.whnf(e)?;
        if matches!(self.node(r), Node::Forall { .. }) {
            Ok(r)
        } else {
            Ok(e)
        }
    }

    /// oracle: `getParamName` (`App.lean:251-255`). Valid only when
    /// `f_type_is_forall` returned true.
    pub fn get_param_name(&self) -> Option<NameId> {
        match self.node(self.st.f_type) {
            Node::Forall { binder_name, .. } => binder_name,
            _ => None,
        }
    }

    /// oracle: `getParamType` (`App.lean:257-261`).
    pub fn get_param_type(&self) -> Result<ExprId, ElabError> {
        match self.node(self.st.f_type) {
            Node::Forall { binder_type, .. } => Ok(binder_type),
            _ => Err(ElabError::IllFormedSyntax(
                "getParamType called on a non-forall fType".to_string(),
            )),
        }
    }

    /// oracle: `getParamInfo` (`App.lean:263-267`).
    pub fn get_param_info(&self) -> Result<BinderInfo, ElabError> {
        match self.node(self.st.f_type) {
            Node::Forall { binder_info, .. } => Ok(binder_info),
            _ => Err(ElabError::IllFormedSyntax(
                "getParamInfo called on a non-forall fType".to_string(),
            )),
        }
    }

    /// oracle: `getArgExpectedType` (`App.lean:269-273`) —
    /// `getParamType` with `consumeTypeAnnotations` applied, i.e. the
    /// `optParam`/`autoParam` wrapper stripped. P1 has no
    /// optParam/autoParam ARM (P5), but stripping here is not the arm:
    /// it is what makes the argument's expected type correct whenever a
    /// wrapper is present and the caller supplied the argument
    /// explicitly. Omitting it would silently elaborate the argument
    /// against `optParam α d` instead of `α`.
    pub fn get_arg_expected_type(&mut self) -> Result<ExprId, ElabError> {
        let t = self.get_param_type()?;
        self.consume_type_annotations(t)
    }

    /// oracle: `Expr.consumeTypeAnnotations` — strip `optParam _ _` and
    /// `autoParam _ _` wrappers from the head.
    fn consume_type_annotations(&mut self, mut t: ExprId) -> Result<ExprId, ElabError> {
        loop {
            let (f, arg0) = match self.app_fn_and_first_arg(t) {
                Some(pair) => pair,
                None => return Ok(t),
            };
            match self.node(f) {
                Node::Const { name: Some(n), .. } => {
                    let base = self.elab.view.store;
                    let rendered = self
                        .elab
                        .mctx
                        .store()
                        .to_name(Some(base), Some(n))
                        .map(|nm| nm.to_string())
                        .unwrap_or_default();
                    if rendered == "optParam" || rendered == "autoParam" {
                        t = arg0;
                        continue;
                    }
                    return Ok(t);
                }
                _ => return Ok(t),
            }
        }
    }

    /// The head and FIRST argument of an application spine, if any.
    fn app_fn_and_first_arg(&self, e: ExprId) -> Option<(ExprId, ExprId)> {
        let mut spine = Vec::new();
        let mut cur = e;
        while let Node::App { f, arg } = self.node(cur) {
            spine.push(arg);
            cur = f;
        }
        spine.pop().map(|first| (cur, first))
    }

    /// oracle: `hasArgsToProcess` (`App.lean:290-293`).
    pub fn has_args_to_process(&self) -> bool {
        !self.st.args.is_empty() || !self.st.named_args.is_empty()
    }
}
```

The `to_name` rendering in `consume_type_annotations` must match however `resolve.rs` renders a `NameId` today — read `crates/leanr_elab/src/resolve.rs` and reuse its exact idiom rather than inventing one; if it renders differently, compare against the interned `NameId` of `optParam`/`autoParam` instead of a string.

Add `pub mod state;` to `crates/leanr_elab/src/app/mod.rs`.

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p leanr_elab --test app_smoke`
Expected: PASS (all tests from Tasks 2 and 3).

- [ ] **Step 5: Format, lint, commit**

```bash
mise run fmt
mise run lint
cargo test -p leanr_elab
git add crates/leanr_elab/src/app crates/leanr_elab/tests
git commit -m "M4b-3 P1 task 3: Context/State/AppElab + fType navigation"
```

---

### Task 4: Explicit arguments end-to-end — head resolution, `main`, `finalize`, dispatch rewire

The first task with oracle coverage. Deliverable: `Nat.succ Nat.zero` elaborates to the oracle's `Expr`, **and every committed M4b-1 `ident` record still passes byte-for-byte** after `builtin/ident.rs` is deleted.

**Files:**
- Create: `crates/leanr_elab/src/app/args.rs`, `crates/leanr_elab/src/app/finalize.rs`, `crates/leanr_elab/src/app/head.rs`, `crates/leanr_elab/src/app/overload.rs`
- Modify: `crates/leanr_elab/src/app/mod.rs`, `crates/leanr_elab/src/dispatch.rs`, `crates/leanr_elab/src/error.rs`, `tests/fixtures/elab/dump_elab.lean`
- Delete: `crates/leanr_elab/src/builtin/ident.rs`
- Regenerate: `tests/fixtures/elab/elab-queries.jsonl`

**Interfaces:**
- Consumes: everything from Tasks 1-3.
- Produces:
  - `app::elab_app(elab: &mut TermElabM, node: &SyntaxNode, kinds: &KindInterner, expected: Option<ExprId>) -> Result<ExprId, ElabError>`
  - `app::elab_atom(elab: &mut TermElabM, elem: &SynElem, kinds: &KindInterner, expected: Option<ExprId>) -> Result<ExprId, ElabError>`
  - `app::head::elab_app_fn(elab, elem, kinds, explicit: bool) -> Result<Vec<ExprId>, ElabError>` — the candidate vector (see `overload.rs`)
  - `app::args::main(&mut AppElab) -> Result<ExprId, ElabError>`

- [ ] **Step 1: Add the corpus queries and regenerate**

Add to `tests/fixtures/elab/dump_elab.lean`, after `haveQueries`:

```lean
/-- M4b-3 P1 task 4: EXPLICIT-argument applications only. `Nat.succ`
takes one explicit `Nat` and no implicit/instance parameters, so these
exercise `ElabAppArgs.main`'s `processExplicitArg` arm, `addNewArg`, and
`finalize` with an empty `etaArgs`/`instMVars` — no implicit insertion
(task 5), no expected-type propagation (task 6), no instance synthesis
(P2). `app/nested` checks that the inner application elaborates through
the same path as an argument. -/
def appExplicitQueries : List (String × String) :=
  [ ("app/succZero",  "Nat.succ Nat.zero")
  , ("app/nested",    "Nat.succ (Nat.succ Nat.zero)")
  , ("app/ascribed",  "(Nat.succ Nat.zero : Nat)")
  ]
```

and add `++ appExplicitQueries` to the `for (id, src) in ...` list in `main`.

```bash
mise run elan:bootstrap        # once, if the toolchain is not installed
mise run fixtures:regen-elab
git diff --stat tests/fixtures/elab/elab-queries.jsonl
```

Expected: the diff shows **only three added lines** — the new `app/*` records. If any pre-existing record changed, STOP: the dumper's entry point or the fixture env moved, which this task must not do.

- [ ] **Step 2: Run the oracle gate to verify it fails**

Run: `cargo test -p leanr_elab --test oracle_elab`
Expected: FAIL with 3 divergences, each `app/...: leanr errored: UnsupportedSyntax("Lean.Parser.Term.app")`.

- [ ] **Step 3: Implement head resolution (`head.rs`)**

Move the body of `builtin/ident.rs` here, unchanged in behavior. Preserve **every** `base = Some(view.store)` / `base = None` decision and the doc comments explaining them — those comments record empirically-found bugs (scratch-vs-persistent `NameId` misrouting) and are not decoration.

```rust
//! `elabAppFn`: resolve the application head to a candidate list.
//! Oracle: `App.lean`'s `elabAppFn` ident case, which for a bare
//! identifier reduces to `resolveName`/`mkConsts`/`mkConst`
//! (`Lean/Elab/Term/TermElabM.lean:2117-2126`, `:2145`, `:2170`).
//!
//! This file is where M4b-1's `builtin/ident.rs` went. That module was
//! a SIMPLIFICATION, not a layer: `elabIdent := elabAtom`
//! (`App.lean:2246`), so a bare identifier is a zero-argument
//! application in the oracle and its implicit parameters are inserted
//! by `ElabAppArgs.main` like any other application's. Keeping a
//! separate leaf path would diverge on every polymorphic constant.
//!
//! Returns a Vec because the oracle's `elabAppFn` returns a candidate
//! ARRAY (overloaded names). Exactly-one is the only P1 shape; see
//! `overload.rs`.

use leanr_kernel::bank::{ExprId, NameId};
use leanr_syntax::kind::KindInterner;

use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::resolve::resolve_global;

pub fn elab_app_fn(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    explicit_levels: &[leanr_kernel::bank::LevelId],
) -> Result<Vec<ExprId>, ElabError> {
    match (kinds.name(elem.kind()), elem) {
        ("<ident>", leanr_syntax::tree::NodeOrToken::Token(tok)) => {
            Ok(vec![elab_ident_head(elab, tok.text(), explicit_levels)?])
        }
        (other, _) => Err(ElabError::UnsupportedSyntax(format!(
            "application head `{other}` — dot notation / LVal machinery is M4b-4"
        ))),
    }
}

/// The former `builtin::ident::elab_ident`, plus `explicit_levels`
/// (Task 8's `.{u}`): oracle `mkConst` creates fresh universe mvars only
/// for the levelParams NOT covered by explicit levels
/// (`TermElabM.lean:2117-2126`).
fn elab_ident_head(
    elab: &mut TermElabM,
    raw: &str,
    explicit_levels: &[leanr_kernel::bank::LevelId],
) -> Result<ExprId, ElabError> {
    // ... verbatim from builtin/ident.rs: intern_dotted, the
    // lctx_lookup_by_name shadowing check, resolve_global, then one
    // fresh level mvar per UNCOVERED levelParam, then expr_const with
    // `base = Some(view.store)`.
    todo!("move the body of builtin/ident.rs here, comments included")
}
```

Replace the `todo!` with the real moved body — the `todo!` above marks *where* the move lands, and must not survive the step. `intern_dotted` moves with it. When `explicit_levels` is non-empty and longer than `level_params`, error (oracle: "too many universe levels"); Task 8 adds the corpus entry for it, so in this task keep the check but no query.

- [ ] **Step 4: Implement `overload.rs`**

```rust
//! The overload shape guard. Oracle: `elabAppAux` (`App.lean:2202-2217`)
//! takes `candidates`, and with more than one runs `getSuccesses` /
//! ambiguity reporting / `mergeFailures`. That machinery is unreachable
//! while `resolve_global` resolves only exact names (no `open`, no
//! aliases, no `_root_`, no `choice` nodes), so it is NOT built
//! speculatively — the shape is asserted instead.

use leanr_kernel::bank::ExprId;

use crate::error::ElabError;

pub fn expect_single(candidates: Vec<ExprId>) -> Result<ExprId, ElabError> {
    match candidates.len() {
        1 => Ok(candidates.into_iter().next().expect("len == 1")),
        0 => Err(ElabError::IllFormedSyntax(
            "elab_app_fn returned no candidates".to_string(),
        )),
        n => Err(ElabError::UnsupportedSyntax(format!(
            "overloaded application ({n} candidates) requires namespace/alias \
             resolution — the slice that grows resolve_global owns this"
        ))),
    }
}
```

- [ ] **Step 5: Implement `main` (explicit arm only) in `args.rs`**

```rust
//! `ElabAppArgs.main` and the parameter-kind arms. Oracle:
//! `App.lean:730-951`.

use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;

use crate::app::expand::Arg;
use crate::app::state::AppElab;
use crate::error::ElabError;

/// oracle: `main` (`App.lean:926-951`).
pub fn main(app: &mut AppElab) -> Result<ExprId, ElabError> {
    loop {
        if app.f_type_is_forall()? {
            let binder_name = app.get_param_name();
            // Task 7 inserts the named-argument lookup here, BEFORE the
            // binder-info dispatch (the oracle checks `findNamedArg?`
            // first, `App.lean:930-938`).
            match app.get_param_info()? {
                BinderInfo::Default => {
                    if !process_explicit_arg(app, binder_name)? {
                        return crate::app::finalize::finalize(app);
                    }
                }
                bi @ (BinderInfo::Implicit | BinderInfo::StrictImplicit) => {
                    // Task 5.
                    return Err(ElabError::UnsupportedSyntax(format!(
                        "implicit argument insertion ({bi:?}) — M4b-3 P1 task 5"
                    )));
                }
                BinderInfo::InstImplicit => {
                    // oracle: `processInstImplicitArg` (`App.lean:900+`)
                    // creates an instance mvar and pushes it onto
                    // `instMVars` for `synthesizeAppInstMVars`. Both need
                    // the synthesis client and the fixpoint.
                    return Err(ElabError::UnsupportedSyntax(
                        "instance-implicit arguments require typeclass synthesis \
                         and the synthetic-mvar fixpoint — M4b-3 P2"
                            .to_string(),
                    ));
                }
            }
        } else if app.has_args_to_process() {
            // oracle: `synthesizePendingAndNormalizeFunType`
            // (`App.lean:372-404`) — synthesize pending instance mvars,
            // then re-WHNF; if `fType` is STILL not a forall it tries
            // `coerceToFunction?` and otherwise reports "function
            // expected". Both halves are later plans.
            return Err(ElabError::UnsupportedSyntax(
                "too many arguments: normalizing the function type needs pending-instance \
                 synthesis (M4b-3 P2) and CoeFun (M4b-3 P4)"
                    .to_string(),
            ));
        } else {
            return crate::app::finalize::finalize(app);
        }
    }
}

/// oracle: `processExplicitArg` (`App.lean:765-877`). Returns `false`
/// when the oracle's own control flow reaches `finalize` (no argument
/// left to consume and no eta/optParam path applies), so `main` can
/// finalize rather than looping.
fn process_explicit_arg(
    app: &mut AppElab,
    binder_name: Option<NameId>,
) -> Result<bool, ElabError> {
    if app.param_idx() < app.ctx.num_implicit_params {
        // Only reachable via structure-projection expansion (M4b-4),
        // which is the sole producer of `num_implicit_params > 0`.
        return Err(ElabError::UnsupportedSyntax(
            "numImplicitParams override (structure projection) — M4b-4".to_string(),
        ));
    }
    if !app.st.args.is_empty() {
        let arg = app.st.args.remove(0);
        // Task 6 inserts `propagate_expected_type(app, &arg)?` HERE —
        // the oracle propagates BEFORE elaborating the argument
        // (`App.lean:803-806`).
        elab_and_add_new_arg(app, binder_name, arg)?;
        return Ok(true);
    }
    // No positional argument left. The oracle now branches on ellipsis,
    // optParam, autoParam, named args, and eta — Tasks 7-8 and P5. With
    // none of those in P1, this is `finalize`.
    if app.ctx.ellipsis {
        return Err(ElabError::UnsupportedSyntax(
            "`..` ellipsis argument filling — M4b-3 P5".to_string(),
        ));
    }
    if !app.st.named_args.is_empty() {
        return Err(ElabError::UnsupportedSyntax(
            "named arguments with missing positional arguments (eta expansion) — \
             M4b-3 P1 task 7"
                .to_string(),
        ));
    }
    // oracle: the `optParam`/`autoParam` default-filling arms
    // (`App.lean:827-855`) live here. `get_arg_expected_type` already
    // STRIPS the wrapper (task 3), so an explicitly-supplied argument to
    // a wrapped parameter is handled above; only the DEFAULT path is
    // deferred. Detect it rather than finalizing a shorter application
    // than the oracle would build.
    if has_opt_or_auto_param(app)? {
        return Err(ElabError::UnsupportedSyntax(
            "optParam default / autoParam tactic argument — M4b-3 P5".to_string(),
        ));
    }
    Ok(false)
}

/// oracle: `hasOptAutoParams` (`App.lean:121-127`) restricted to the
/// CURRENT parameter — enough to detect the deferred default-filling
/// path without walking the whole remaining telescope (Task 7 widens
/// this to the oracle's full `forallTelescopeReducing` form, which the
/// eta decision needs).
fn has_opt_or_auto_param(app: &mut AppElab) -> Result<bool, ElabError> {
    let raw = app.get_param_type()?;
    let stripped = app.get_arg_expected_type()?;
    Ok(raw != stripped)
}

/// oracle: `addNewArg` (`App.lean:418-429`) — `f := f arg`, push onto
/// `fArgs`, and advance `fType` to its BINDING BODY (not a
/// re-instantiated type: the loose bvars are instantiated lazily by
/// `get_f_type`, which is what makes `paramIdx`/`fArgs` the single
/// source of truth).
pub fn add_new_arg(app: &mut AppElab, arg: ExprId) -> Result<(), ElabError> {
    let body = match app.node(app.st.f_type) {
        leanr_kernel::bank::Node::Forall { body, .. } => body,
        _ => {
            return Err(ElabError::IllFormedSyntax(
                "add_new_arg on a non-forall fType".to_string(),
            ))
        }
    };
    let f = app
        .elab
        .mctx
        .store_mut()
        .expr_app(None, app.st.f, arg)
        .map_err(leanr_meta::MetaError::from)?;
    app.st.f = f;
    app.st.f_args.push(arg);
    app.st.f_type = body;
    Ok(())
}

/// oracle: `elabAndAddNewArg` (`App.lean:431-441`) — elaborate the
/// argument against the parameter's expected type, `ensureArgType` it,
/// then `addNewArg`.
fn elab_and_add_new_arg(
    app: &mut AppElab,
    _binder_name: Option<NameId>,
    arg: Arg,
) -> Result<(), ElabError> {
    let expected = app.get_arg_expected_type()?;
    let val = match arg {
        Arg::Expr(e) => e,
        Arg::Stx(elem) => {
            let kinds = app.kinds_handle();
            app.elab.elab_term(&elem, kinds, Some(expected))?
        }
    };
    // oracle: `ensureArgType` = `ensureHasType expected val`
    // (coercion-inserting from P4 onward; here the M4b-1 behavior, which
    // ERRORS on a defeq mismatch).
    let inferred = app.elab.mctx.infer_type(val)?;
    if !app.elab.mctx.is_def_eq(inferred, expected)? {
        return Err(ElabError::TypeMismatch {
            expected,
            got: inferred,
        });
    }
    add_new_arg(app, val)
}
```

`app.kinds_handle()` does not exist — the `KindInterner` is passed per call, never stored (`elab.rs`'s module doc). Thread it through instead: add a `kinds: &'k KindInterner` field to `AppElab` with its own lifetime parameter, or pass `kinds` down through `main`/`process_explicit_arg`/`elab_and_add_new_arg` as an explicit argument. **Prefer threading it as a parameter** — storing a borrow in `AppElab` would fight the `&mut TermElabM` borrow. Update Task 3's signatures accordingly if you take the field route.

- [ ] **Step 6: Implement `finalize.rs`**

```rust
//! oracle: `finalize` (`App.lean:610-660`).

use leanr_kernel::bank::ExprId;

use crate::app::state::AppElab;
use crate::error::ElabError;

pub fn finalize(app: &mut AppElab) -> Result<ExprId, ElabError> {
    // oracle: `for mvarId in s.toSetErrorCtx do
    // registerMVarErrorImplicitArgInfo ..` — error CONTEXT only, never
    // part of the emitted `Expr`. The ladder field it writes into
    // arrives in P2; until then the collected ids are simply unused.
    let e = app.st.f;

    // oracle: `unless s.etaArgs.isEmpty do e ← mkLambdaFVars ..`
    // (Task 7 populates `eta_args`).
    if !app.st.eta_args.is_empty() {
        return Err(ElabError::UnsupportedSyntax(
            "eta-expanded application (mkLambdaFVars over etaArgs) — M4b-3 P1 task 7"
                .to_string(),
        ));
    }

    // oracle: the `resultTypeOutParam?` branch (`App.lean:637-648`).
    // `result_is_out_param_support` is false in the fixture env (no
    // `Lean.Internal.coeM`), so there is no P1 producer; guard anyway.
    if app.st.result_type_out_param.is_some() {
        return Err(ElabError::UnsupportedSyntax(
            "result-type outParam support requires default instances — M4b-3 P2".to_string(),
        ));
    }

    // oracle: `if let some expectedType := s.expectedType? then
    // trySynthesizeAppInstMVars; discard <| isDefEq expectedType eType`
    // — a FAILED unification here is deliberately ignored: the caller
    // (`ensureHasType`) handles the mismatch. Task 6 adds this.

    // oracle: `synthesizeAppInstMVars` (`App.lean:349-370`).
    if !app.st.inst_mvars.is_empty() {
        return Err(ElabError::UnsupportedSyntax(
            "pending instance-implicit mvars require typeclass synthesis — M4b-3 P2"
                .to_string(),
        ));
    }
    Ok(e)
}
```

- [ ] **Step 7: Wire `elab_app` / `elab_atom` in `mod.rs`**

```rust
/// oracle: `elabApp` (`App.lean:2238-2241`) — `universeConstraintsCheckpoint`
/// wraps the whole thing; that checkpoint maps onto leanr_meta's postponed
/// level-constraint queue and lands in P2 with `process_postponed`.
pub fn elab_app(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let (head, named_args, args, ellipsis) = expand::expand_app(node, kinds)?;
    elab_app_aux(elab, &head, kinds, named_args, args, ellipsis, false, expected)
}

/// oracle: `elabAtom` (`App.lean:2243-2244`) — a zero-argument
/// application. This is what `ident`, `@`, `.{u}`, `choice`, `proj` and
/// `dotIdent` all reduce to in the oracle; P1 routes the first three.
pub fn elab_atom(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    elab_app_aux(elab, elem, kinds, Vec::new(), Vec::new(), false, false, expected)
}
```

`elab_app_aux` builds the `Context`/`State` exactly as `elabAppArgs` does (`App.lean:1351-1394`): `f_type = instantiate_mvars(infer_type(f))`, `num_implicit_params = named_args.iter().map(|n| n.num_implicit_params).max().unwrap_or(0)`, `propagate_expected = true` (the oracle's `propagateExpectedTypeFor f` consults the `elab_without_expected_type` attribute, an extension leanr does not decode — Task 9 records that as a fixture-scoped seam), and

```rust
let result_is_out_param_support = env_contains_coe_m(elab) && !explicit;
```

where `env_contains_coe_m` looks `Lean.Internal.coeM` up through `elab.view` and returns false when absent — the oracle's own `App.lean:1355` condition, not a shortcut.

Also guard `elabAsElim?` (`App.lean:1374`): it consults the `@[elab_as_elim]` attribute, an extension leanr does not decode. Task 9 adds the fixture-source gate that keeps this inert; add a comment here pointing at it.

- [ ] **Step 8: Rewire dispatch and delete `builtin/ident.rs`**

In `crates/leanr_elab/src/dispatch.rs`:
- add `"Lean.Parser.Term.app" => Some("app")` to `elaborator_name_for`
- re-point the `("<ident>", NodeOrToken::Token(tok))` arm to `crate::app::elab_atom(elab, elem, kinds, expected)`
- add `("Lean.Parser.Term.app", NodeOrToken::Node(node)) => crate::app::elab_app(elab, node, kinds, expected)`
- update the deferral table comment: move `application, @, named/optional args` off the deferred list, and add the P2-P5 seams named in `app/mod.rs`

Then `git rm crates/leanr_elab/src/builtin/ident.rs` and remove `pub mod ident;` from `crates/leanr_elab/src/builtin/mod.rs`. Move `ident.rs`'s `#[cfg(test)] mod tests` (the `unknown_ident_via_real_scratch_pipeline` regression) into `head.rs`, retargeted at `elab_ident_head`. That test guards a real, empirically-found scratch-vs-persistent `NameId` bug — losing it in the move would be a regression in test coverage even though no behavior changed.

- [ ] **Step 9: Run the oracle gate to verify it passes**

Run: `cargo test -p leanr_elab --test oracle_elab`
Expected: PASS — 0 divergences, covering the 3 new `app/*` records **and** the pre-existing `ident/Nat` and `ident/List` records now flowing through `elab_atom`.

- [ ] **Step 10: Prove the ident records are byte-identical**

The rewiring must not change any committed record. The gate passing already proves leanr still matches the oracle; this step proves the *corpus* did not move under us:

```bash
mise run fixtures:regen-elab
git diff --exit-code tests/fixtures/elab/elab-queries.jsonl
```

Expected: exit 0 (no diff) — the regenerated corpus is identical to what Step 1 committed. If it differs, the dumper or fixture env changed; revert and investigate before proceeding.

- [ ] **Step 11: Full suite, format, lint, commit**

```bash
mise run fmt
mise run lint
cargo test --workspace
git add -A crates/leanr_elab tests/fixtures/elab
git commit -m "M4b-3 P1 task 4: explicit-argument applications; retire the leaf ident elaborator

elabIdent IS elabAppAux (App.lean:2246), so builtin/ident.rs is deleted and
its constant resolution moves to app/head.rs. Committed ident records verified
byte-identical across the rewiring."
```

---

### Task 5: Implicit and strict-implicit argument insertion

**Files:**
- Modify: `crates/leanr_elab/src/app/args.rs`, `tests/fixtures/elab/dump_elab.lean`
- Regenerate: `tests/fixtures/elab/elab-queries.jsonl`

**Interfaces:**
- Consumes: `add_new_arg`, `AppElab`, `Context`/`State` (Tasks 3-4).
- Produces: `add_implicit_arg(app, kinds, binder_name) -> Result<bool, ElabError>`, `process_implicit_arg`, `process_strict_implicit_arg`.

- [ ] **Step 1: Add the corpus queries and regenerate**

```lean
/-- M4b-3 P1 task 5: IMPLICIT argument insertion. `id {α : Sort u} (a :
α) : α` (Elab0's own `id`) is the minimal shape: elaborating `id
Nat.zero` inserts a fresh mvar for `α`, which the explicit argument's
`ensureArgType` then assigns — so the emitted term is `@id Nat
Nat.zero`, NOT `id Nat.zero`. `app/implicitBareIdent` is the case the
retired leaf `ident` elaborator got wrong by construction: a bare
polymorphic constant against an expected type gets its implicit
arguments inserted too. -/
def appImplicitQueries : List (String × String) :=
  [ ("app/implicitId",        "id Nat.zero")
  , ("app/implicitIdAscribed", "(id Nat.zero : Nat)")
  , ("app/implicitBareIdent", "(List.nil : List Nat)")
  ]
```

Add `++ appImplicitQueries` to `main`'s list, then `mise run fixtures:regen-elab`.

- [ ] **Step 2: Run the gate to verify it fails**

Run: `cargo test -p leanr_elab --test oracle_elab`
Expected: FAIL with 3 divergences, each `UnsupportedSyntax("implicit argument insertion (Implicit) — M4b-3 P1 task 5")`.

- [ ] **Step 3: Implement the arms**

Replace the `BinderInfo::Implicit | BinderInfo::StrictImplicit` seam in `main` with real dispatch, and add:

```rust
/// oracle: `addImplicitArg` (`App.lean:747-760`). Creates a fresh mvar
/// for the parameter, records it in `toSetErrorCtx` for error
/// attribution, and continues the loop.
fn add_implicit_arg(app: &mut AppElab, kinds: &KindInterner) -> Result<(), ElabError> {
    let arg_type = app.get_arg_expected_type()?;
    // oracle: the `isNextOutParamOfLocalInstanceAndResult` branch
    // (`App.lean:749-757`) sets `resultTypeOutParam?` and disables
    // propagation. It needs class outParam positions from the
    // `classExtension`, which leanr does not decode until P2; the
    // guarding flag (`result_is_out_param_support`) is false in the
    // fixture env, so the branch is inert here rather than skipped
    // silently. `finalize` re-checks `result_type_out_param` (task 4).
    if app.ctx.result_is_out_param_support {
        return Err(ElabError::UnsupportedSyntax(
            "local-instance outParam result type requires classExtension decode — M4b-3 P2"
                .to_string(),
        ));
    }
    let arg = app.elab.mk_fresh_expr_mvar(arg_type)?;
    if let leanr_kernel::bank::Node::MVar { id: Some(n) } = app.node(arg) {
        app.st.to_set_error_ctx.push(leanr_meta::MVarId(n));
    }
    crate::app::args::add_new_arg(app, arg)?;
    let _ = kinds;
    Ok(())
}

/// oracle: `processImplicitArg` (`App.lean:879-885`) — under `@`, an
/// implicit parameter is filled from the positional arguments exactly
/// like an explicit one.
fn process_implicit_arg(
    app: &mut AppElab,
    kinds: &KindInterner,
    binder_name: Option<NameId>,
) -> Result<bool, ElabError> {
    if app.ctx.explicit {
        process_explicit_arg(app, kinds, binder_name)
    } else {
        add_implicit_arg(app, kinds)?;
        Ok(true)
    }
}

/// oracle: `processStrictImplicitArg` (`App.lean:887-895`) — a strict
/// implicit is inserted ONLY when there is still an argument to
/// process; otherwise the application finalizes here. This is the one
/// arm whose difference from `processImplicitArg` is invisible on
/// single-argument corpus terms, so `app_smoke.rs` gets a direct test.
fn process_strict_implicit_arg(
    app: &mut AppElab,
    kinds: &KindInterner,
    binder_name: Option<NameId>,
) -> Result<bool, ElabError> {
    if app.ctx.explicit {
        process_explicit_arg(app, kinds, binder_name)
    } else if app.has_args_to_process() {
        add_implicit_arg(app, kinds)?;
        Ok(true)
    } else {
        Ok(false)
    }
}
```

`MVarId`'s constructor may not be a tuple struct from outside `leanr_meta` — check `crates/leanr_meta/src/mvar_ctx.rs`. If it is not constructible there, have `TermElabM::mk_fresh_expr_mvar` return the `MVarId` alongside the `ExprId` (an additive change to `elab.rs`, which this plan owns) rather than reconstructing it from the node.

- [ ] **Step 4: Add the strict-implicit unit test**

```rust
/// A strict-implicit parameter with NO remaining arguments finalizes
/// instead of inserting an mvar (oracle: `processStrictImplicitArg`,
/// `App.lean:887-895`). The corpus cannot show this: Elab0 declares no
/// strict-implicit constant, and the difference only appears at the end
/// of the argument list.
#[test]
fn strict_implicit_without_args_finalizes() {
    // Construct the State directly: f = `id`, f_type forced to a
    // strict-implicit forall, args empty. Assert `main` returns `f`
    // unchanged rather than an application carrying a fresh mvar.
    // (Build the strict-implicit forall with
    // `store_mut().expr_forall(None, name, dom, body,
    // BinderInfo::StrictImplicit)`.)
}
```

Fill in the body following `with_app_harness`'s construction; the assertion is `got == f_before` and `st.f_args.is_empty()`.

- [ ] **Step 5: Run both to verify they pass**

Run: `cargo test -p leanr_elab`
Expected: PASS — oracle gate 0 divergences, `app_smoke` green.

- [ ] **Step 6: Format, lint, commit**

```bash
mise run fmt
mise run lint
git add -A crates/leanr_elab tests/fixtures/elab
git commit -m "M4b-3 P1 task 5: implicit and strict-implicit argument insertion"
```

---

### Task 6: `propagateExpectedType`

The heuristic that unifies the expected type against the application's *resulting* type before the first explicit argument is elaborated. Without it, `(f x : T)` unifies in the wrong order and produces different mvar assignments — an oracle-visible divergence on trivial terms.

**Files:**
- Create: `crates/leanr_elab/src/app/propagate.rs`
- Modify: `crates/leanr_elab/src/app/args.rs`, `crates/leanr_elab/src/app/finalize.rs`, `crates/leanr_elab/src/app/mod.rs`, `tests/fixtures/elab/dump_elab.lean`

**Interfaces:**
- Produces: `propagate_expected_type(app, kinds, arg: &Arg) -> Result<(), ElabError>`, `get_resulting_type(app) -> Result<Option<ExprId>, ElabError>`, `should_propagate_expected_type_for(arg, kinds) -> bool`.

- [ ] **Step 1: Add the corpus queries and regenerate**

```lean
/-- M4b-3 P1 task 6: expected-type propagation
(`propagateExpectedType`, App.lean:563-609). The expected type reaches
the state machine through SOURCE ASCRIPTION — `(e : T)` — which is the
only way this dumper's pinned `expectedType? := none` entry point can
supply one (design spec § Verification). `app/propagatePi` is the shape
the heuristic exists for: the expected type determines an implicit
argument BEFORE the explicit argument is elaborated, so a divergence
here shows up as a different mvar assignment, not an error. -/
def appPropagateQueries : List (String × String) :=
  [ ("app/propagateId",   "(id Nat.zero : Nat)")
  , ("app/propagateCons", "(List.cons Nat.zero List.nil : List Nat)")
  , ("app/propagatePi",   "(id id : Nat -> Nat)")
  ]
```

`app/propagateId` duplicates Task 5's `app/implicitIdAscribed` source; drop whichever id is redundant after regenerating (two records with the same `src` but different `id` are noise, not coverage). Add `++ appPropagateQueries` to `main`'s list, then `mise run fixtures:regen-elab`.

- [ ] **Step 2: Run the gate to verify it fails**

Run: `cargo test -p leanr_elab --test oracle_elab`
Expected: FAIL. Record the exact failure: `app/propagateCons` and `app/propagatePi` will either error or produce a term whose mvar assignments differ from the oracle's. A *divergence* rather than an error is the expected RED signal here — that is precisely the "silently different term" this task prevents.

- [ ] **Step 3: Implement `propagate.rs`**

Transliterate `App.lean:449-609`:

- `should_propagate_expected_type_for(arg)` — false for `Arg::Expr`, and for `Arg::Stx` false when the kind is `Lean.Parser.Term.hole`, `Lean.Parser.Term.syntheticHole`, or `Lean.Parser.Term.byTactic` (`App.lean:516-523`).
- `get_resulting_type` — the `getResultingTypeCore?` walk (`App.lean:445-509`), which *simulates* `main` without elaborating: for each remaining forall, consume a matching named arg, skip implicits when not `explicit`, treat `paramIdx < numImplicitParams` as implicit, decrement the positional count, and return `None` (propagation postponed) when the resulting type still depends on un-elaborated arguments, when named args remain and eta args would be needed, or when opt/auto params remain. **Keep every postponement condition** — each one that is dropped turns into an over-eager unification that assigns an mvar the oracle leaves open.
- `propagate_expected_type` — the guard chain: skip when `!eta_args.is_empty()` or `!propagate_expected`; `None` expected type is a no-op; when the instantiated expected type `isProp`, set `propagate_expected = false` and return **without unifying** (`App.lean:594-597`, the `if-then-else`-as-`Bool` case); otherwise `is_def_eq(expected, resulting)` and set `propagate_expected = false` **only on success** (the oracle's own emphasised note, `App.lean:602`).

`isProp` is `infer_type(t)` reducing to `Sort 0` — compose it from public `MetaCtx::infer_type` + `whnf` rather than adding an accessor.

Call it from `process_explicit_arg` immediately before `elab_and_add_new_arg` (`App.lean:803-806`), and from the named-argument branch in Task 7.

Then implement `finalize`'s expected-type step (`App.lean:650-655`): infer `e`'s type and `discard <| is_def_eq(expected, e_type)` — **a failed unification here is deliberately ignored**; the caller handles the mismatch. Do not turn it into an error.

- [ ] **Step 4: Run the gate to verify it passes**

Run: `cargo test -p leanr_elab --test oracle_elab`
Expected: PASS, 0 divergences.

- [ ] **Step 5: Format, lint, commit**

```bash
mise run fmt
mise run lint
cargo test --workspace
git add -A crates/leanr_elab tests/fixtures/elab
git commit -m "M4b-3 P1 task 6: propagateExpectedType + getResultingType"
```

---

### Task 7: Named arguments and eta-expansion

**Files:**
- Modify: `crates/leanr_elab/src/app/args.rs`, `crates/leanr_elab/src/app/finalize.rs`, `crates/leanr_elab/src/app/state.rs`, `tests/fixtures/elab/Elab0.lean`, `tests/fixtures/elab/dump_elab.lean`
- Regenerate: `tests/fixtures/elab/Elab0.olean`, `tests/fixtures/elab/elab-queries.jsonl`

**Interfaces:**
- Produces: `find_named_arg`, `erase_named_arg`, `push_found_named_arg`, `find_named_arg_depends_on_current`, `add_eta_arg`, `has_opt_auto_params` (widened to the oracle's telescope form), and `finalize`'s `mkLambdaFVars` step.

- [ ] **Step 1: Extend the fixture environment**

Elab0 has no multi-explicit-argument function, so named-argument and eta coverage is impossible today. Add to `tests/fixtures/elab/Elab0.lean`, at the end:

```lean
-- === M4b-3 P1 task 7 corpus: named arguments and eta-expansion ===
--
-- `pick` is the minimal shape that makes eta-expansion observable: TWO
-- explicit parameters, so `pick (y := Nat.zero)` leaves `x` missing and
-- the oracle emits `fun x => pick x Nat.zero` (App.lean:206's own
-- worked example) rather than an application. `dep` makes a named
-- argument's DEPENDENCY on an earlier parameter reachable
-- (`findNamedArgDependsOnCurrent?`, App.lean:340), which turns the
-- missing parameter implicit instead of eta.
def pick (x : Nat) (y : Nat) : Nat := x
def dep (a : Type) (z : a) : a := z
```

```bash
sh -c 'cd tests/fixtures/elab && lean Elab0.lean -o Elab0.olean'
```

Run the gate immediately: `cargo test -p leanr_elab --test oracle_elab` must still PASS. A fixture env grows monotonically; if any existing record changed, the additions perturbed elaboration of an existing query and must be reworked.

- [ ] **Step 2: Add the corpus queries and regenerate**

```lean
/-- M4b-3 P1 task 7: named arguments and eta-expansion. `app/namedBoth`
supplies both parameters by name (no eta). `app/namedEta` supplies only
the LATER one, so the earlier missing parameter becomes an eta argument
and the result is a LAMBDA (App.lean:191-205). `app/namedDep` supplies
a named argument that depends on the missing parameter, which becomes
IMPLICIT instead of eta (findNamedArgDependsOnCurrent?,
App.lean:340-348) — the two paths emit structurally different terms, so
both are corpus entries, not one. -/
def appNamedQueries : List (String × String) :=
  [ ("app/namedBoth",  "pick (x := Nat.zero) (y := Nat.zero)")
  , ("app/namedFirst", "pick (x := Nat.zero) Nat.zero")
  , ("app/namedEta",   "pick (y := Nat.zero)")
  , ("app/namedDep",   "dep (z := Nat.zero)")
  ]
```

Add `++ appNamedQueries` to `main`'s list, then `mise run fixtures:regen-elab`. If the oracle rejects `app/namedDep` (the dependency may not be solvable without an expected type), record the oracle's error in a comment and drop that entry — a query the oracle itself cannot elaborate is not a differential test.

- [ ] **Step 3: Run the gate to verify it fails**

Run: `cargo test -p leanr_elab --test oracle_elab`
Expected: FAIL — the named-arg entries hit the `named arguments with missing positional arguments` seam from Task 4, and `app/namedBoth` hits the missing named-argument lookup in `main`.

- [ ] **Step 4: Implement named-argument matching in `main`**

Per `App.lean:930-941`, BEFORE the binder-info dispatch: look up the current binder name in `named_args`; on a hit, `propagate_expected_type` on its value, `erase_named_arg`, `elab_and_add_new_arg`, and continue. On a miss, `push_found_named_arg` (unless the binder name has macro scopes — leanr's binder names carry none, so record that in a comment rather than implementing scope stripping) and fall through to the binder-info dispatch.

Comparing a `NamedArg::name` (`String`) against a binder `NameId` needs one rendering per comparison; render the binder name once per loop iteration and compare to the string. The oracle's `findDeprecatedBinderName?` fallback (`App.lean:85-90`) needs the deprecation attribute, which leanr does not decode — make it a named seam comment, not a silent omission.

- [ ] **Step 5: Implement `add_eta_arg` and the eta branch**

`add_eta_arg` (`App.lean:730-740`): `get_arg_expected_type`, push a fresh local decl via `MetaCtx::push_local_decl` (M4b-2's accessor, as `builtin/binder.rs:192` uses it), record `(binder_name, fvar)` in `eta_args`, `add_new_arg(fvar)`, continue. The oracle uses `Core.mkFreshUserName argName` so remaining arguments cannot capture the parameter's name — mirror that with the fresh-name idiom already in `elab.rs` (`_leanr_elab_*` prefix + counter), and say so in a comment.

In `process_explicit_arg`'s no-positional-argument branch, replace the Task 4 seam with the oracle's exact chain (`App.lean:857-877`): ellipsis → `add_implicit_arg`; else named args remain → `find_named_arg_depends_on_current` → `add_implicit_arg` if some, `add_eta_arg` otherwise; else not `explicit` and `has_opt_auto_params(get_f_type())` → `add_eta_arg`; else `finalize`. Widen `has_opt_auto_params` to the oracle's `forallTelescopeReducing` form (`App.lean:121-127`) — the current-parameter-only version from Task 4 is not enough for this decision.

`find_named_arg_depends_on_current` (`App.lean:340-348`): return `None` when `named_args` is empty or `f_type` is a non-dependent arrow; otherwise find a named arg whose parameter's type mentions the current parameter.

In `finalize`, replace the eta seam with the real step: `MetaCtx::mk_lambda(&eta_fvars, e)` then apply the recorded binder names (`e.updateBinderNames`, `App.lean:623`). If no `update_binder_names` equivalent exists, the binder names come from `push_local_decl`'s own `name` argument — pass the intended user name there and drop the separate rename, noting the reasoning in a comment.

Bracket the whole `main` call in `elab_app_aux` with `lctx_checkpoint`/`lctx_restore` (M4b-2's `binder.rs:217,226` idiom) so eta fvars never leak into the ambient context.

- [ ] **Step 6: Run the gate to verify it passes**

Run: `cargo test -p leanr_elab --test oracle_elab`
Expected: PASS, 0 divergences.

- [ ] **Step 7: Format, lint, commit**

```bash
mise run fmt
mise run lint
cargo test --workspace
git add -A crates/leanr_elab tests/fixtures/elab
git commit -m "M4b-3 P1 task 7: named arguments, eta-expansion, and the finalize lambda wrap"
```

---

### Task 8: `@` explicit mode, `.{u}` explicit universes, and the remaining guards

**Files:**
- Modify: `crates/leanr_elab/src/app/mod.rs`, `crates/leanr_elab/src/app/head.rs`, `crates/leanr_elab/src/dispatch.rs`, `crates/leanr_elab/src/elab.rs`, `tests/fixtures/elab/dump_elab.lean`

**Interfaces:**
- Produces: dispatch arms for `Lean.Parser.Term.explicit` and `Lean.Parser.Term.explicitUniv`; `elab_explicit_univs`; the implicit-lambda guard in `elab_term`.

- [ ] **Step 1: Add the corpus queries and regenerate**

```lean
/-- M4b-3 P1 task 8: `@` and `.{u}`. Under `@`, implicit parameters are
supplied positionally (`processImplicitArg` delegates to
`processExplicitArg`, App.lean:879-885) and `resultIsOutParamSupport`
is forced off (App.lean:1355). `.{u}` supplies explicit universe levels
so `mkConst` mints FEWER fresh level mvars (TermElabM.lean:2117-2126) —
`app/univList` should carry a concrete `zero`, not an `lmvar`. -/
def appExplicitModeQueries : List (String × String) :=
  [ ("app/atId",     "@id Nat Nat.zero")
  , ("app/atBare",   "@Nat.succ")
  , ("app/univList", "List.{0}")
  ]
```

Add `++ appExplicitModeQueries` to `main`'s list, then `mise run fixtures:regen-elab`. If leanr's parser does not accept `List.{0}` in term position, drop that entry and note it — `explicitUniv` is registered in `leanr_syntax` (`builtin/term.rs:1177`), so verify with a parse test before dropping.

- [ ] **Step 2: Run the gate to verify it fails**

Run: `cargo test -p leanr_elab --test oracle_elab`
Expected: FAIL — `UnsupportedSyntax("Lean.Parser.Term.explicit")` / `("Lean.Parser.Term.explicitUniv")`.

- [ ] **Step 3: Implement the `@` arm**

Oracle `elabExplicit` (`App.lean:2260-2271`) has two behaviours by shape:
- `@ident`, `@ident.{us}`, `@(...).field` → `elab_atom` with `explicit = true`
- `@(t)` and `@t` for any other `t` → **not** explicit mode at all: it elaborates `t` with **implicit-lambda insertion disabled**

P1 implements the first family and seams the second, because implicit-lambda insertion is P5 and `@t` exists precisely to disable it:

```rust
"Lean.Parser.Term.explicit" => {
    // oracle: `elabExplicit` (App.lean:2260-2271). The `@(t)`/`@t`
    // forms do NOT enter explicit mode — they disable implicit-lambda
    // insertion, which P5 owns.
    let inner = /* the single non-trivia child after `@` */;
    match kinds.name(inner.kind()) {
        "<ident>" | "Lean.Parser.Term.explicitUniv" => {
            app::elab_atom_explicit(elab, &inner, kinds, expected)
        }
        other => Err(ElabError::UnsupportedSyntax(format!(
            "`@` applied to `{other}` disables implicit-lambda insertion — M4b-3 P5"
        ))),
    }
}
```

`elab_atom_explicit` is `elab_atom` with `explicit = true` threaded into `Context`. Note that `@` in an application head position is handled by `expand_app` returning the `Term.explicit` node as the head — so `elab_app_fn` must also accept it, recursing into the inner ident and reporting `explicit = true` upward. Implement that by having `elab_app_fn` return `(candidates, explicit_override)` or by peeling `@` in `elab_app_aux` before building `Context`; **prefer peeling in `elab_app_aux`**, which keeps `head.rs` about names only.

- [ ] **Step 4: Implement `.{u}`**

Oracle `elabExplicitUnivs` (`App.lean:1899`) elaborates each level syntax and passes the list to `mkConst`. `builtin/sort.rs` already has a level elaborator (`elab_level`) covering `Lean.Parser.Level.*` — reuse it; do not write a second one. Thread the resulting `Vec<LevelId>` into `elab_ident_head`'s `explicit_levels` (already a parameter from Task 4). Keep the "too many universe levels" error from Task 4 and add a unit test for it in `app_smoke.rs` (Elab0's `List` has exactly one level param, so `List.{0, 0}` is the case).

- [ ] **Step 5: Add the implicit-lambda guard**

`useImplicitLambda` (`TermElabM.lean:1743`, `1823-1880`) wraps a term in lambdas when the expected type is an implicit-`forall` and the term is not itself a lambda. This path becomes reachable the moment ascription supplies expected types (Task 6), so it needs a guard **now**, with the implementation in P5:

In `elab_term` (or `elab_term_ensuring_type`, wherever the expected type is first seen), before dispatch: if `expected` WHNFs to a `forall` whose `binder_info` is `Implicit`, `StrictImplicit` or `InstImplicit`, and the syntax kind is not one the oracle excludes (`fun`, `@`-disabled forms), return

```rust
Err(ElabError::UnsupportedSyntax(
    "implicit lambda insertion — M4b-3 P5".to_string(),
))
```

Read `TermElabM.lean:1743-1780` for the exact exclusion list and mirror it; a guard that fires too eagerly will break Task 5's `(List.nil : List Nat)` record, so run the full gate after adding it.

- [ ] **Step 6: Run the gate to verify it passes**

Run: `cargo test -p leanr_elab`
Expected: PASS — 0 divergences, all `app_smoke` tests green.

- [ ] **Step 7: Format, lint, commit**

```bash
mise run fmt
mise run lint
cargo test --workspace
git add -A crates/leanr_elab tests/fixtures/elab
git commit -m "M4b-3 P1 task 8: @ explicit mode, .{u} explicit universes, implicit-lambda guard"
```

---

### Task 9: Seam audit, undecoded-attribute gates, and documentation

Every deferral must be a *named* seam that a fresh reader can find. Two of P1's guards depend on env extensions leanr does not decode (`@[elab_as_elim]`, `@[elab_without_expected_type]`), which cannot be detected at runtime — so they get a fixture-source gate instead, and that limitation is written down rather than left implicit.

**Files:**
- Create: `crates/leanr_elab/tests/seam_audit.rs`
- Modify: `crates/leanr_elab/src/lib.rs`, `crates/leanr_elab/src/dispatch.rs`, `crates/leanr_elab/src/app/mod.rs`, `ARCHITECTURE.md`

- [ ] **Step 1: Write the seam audit test**

```rust
//! M4b-3 P1 seam audit (M4b-1 Task 7's precedent): every construct this
//! plan defers is reachable ONLY through a named `UnsupportedSyntax`
//! carrying the owning slice, never a panic and never a wrong `ExprId`.

use leanr_syntax::{builtin, parse_term};

/// Each source term below exercises one deferred path. The assertion is
/// deliberately on the ERROR SHAPE, not the message text, plus a
/// substring check on the slice name so a seam cannot be silently
/// re-pointed at the wrong owner.
#[test]
fn deferred_constructs_are_named_seams() {
    let cases: &[(&str, &str)] = &[
        // (source, expected slice marker in the message)
        ("Nat.succ ..", "P5"),
        ("(Nat.succ : Nat -> Nat) Nat.zero Nat.zero", "P2"),
    ];
    for (src, marker) in cases {
        // elaborate through the same entry point oracle_elab.rs uses,
        // and assert Err(UnsupportedSyntax(msg)) with msg containing
        // `marker`.
    }
}

/// The `@[elab_as_elim]` and `@[elab_without_expected_type]` attributes
/// change `elabAppArgs`'s control flow (`App.lean:1374`, `:1330-1333`),
/// and leanr decodes NEITHER extension — so their guards cannot be
/// runtime checks. They are inert only because no declaration in the
/// hermetic fixture carries them. This test is that invariant: it fails
/// the moment someone adds one to `Elab0.lean`, which is exactly when a
/// real guard (and an extension decode) becomes necessary.
#[test]
fn fixture_declares_no_undecoded_elab_attributes() {
    let src = std::fs::read_to_string(
        concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/fixtures/elab/Elab0.lean"),
    )
    .expect("committed fixture source");
    for attr in ["elab_as_elim", "elab_without_expected_type"] {
        assert!(
            !src.contains(attr),
            "Elab0.lean declares `@[{attr}]`, whose extension leanr does not decode: \
             elabAppArgs' control flow would diverge silently. Decode the extension \
             (M4b-4 owns elab_as_elim) before adding such a declaration."
        );
    }
}
```

Fill in the elaboration bodies using `oracle_elab.rs`'s construction. Verify each `cases` entry actually reaches the intended seam — if a source hits a *different* seam, use the message it really produces (a seam audit that asserts the wrong path is worse than none).

- [ ] **Step 2: Run the audit**

Run: `cargo test -p leanr_elab --test seam_audit`
Expected: PASS.

- [ ] **Step 3: Update the deferral ledgers**

Three places must agree, since a fresh reader may start at any of them:
- `crates/leanr_elab/src/lib.rs`'s module doc — move `application`, `@`, `named args` out of the deferred list; add the P2-P5 seams.
- `crates/leanr_elab/src/dispatch.rs`'s deferred table — same edit; add `Term.proj`/`pipeProj`/`dotIdent`/`namedPattern`/`choice` explicitly as M4b-4 (they route to `elabAtom` in the oracle but need the LVal machinery, so leanr must NOT route them yet).
- `crates/leanr_elab/src/app/mod.rs`'s seam list — reconcile against what actually shipped.

- [ ] **Step 4: Update `ARCHITECTURE.md`**

Add `leanr_elab/src/app/` to the crate-boundary description: one paragraph naming the module's responsibility and the `AppElab`-instead-of-monad-stack decision, pointing at the design spec. Follow the file's existing style; do not restructure it.

- [ ] **Step 5: Full CI**

Run: `mise run ci`
Expected: PASS — `cargo fmt --check`, clippy, and the whole workspace test suite including `oracle_elab`, `app_smoke`, `seam_audit`, `meta:fast`.

- [ ] **Step 6: Final corpus review and commit**

```bash
mise run fixtures:regen-elab
git diff --exit-code tests/fixtures/elab/elab-queries.jsonl
wc -l tests/fixtures/elab/elab-queries.jsonl
```

Expected: no diff; the corpus has grown from 54 records by the number of `app/*` entries actually landed. Then:

```bash
mise run fmt
git add -A
git commit -m "M4b-3 P1 task 9: seam audit, undecoded-attribute gate, deferral ledgers"
```

---

## Self-Review

**Spec coverage (§ P1 — the application machinery):**

| Spec requirement | Task |
|---|---|
| module layout `app/{expand,state,args,propagate,finalize,overload}.rs` | 2, 3, 4, 6 (+ `head.rs`, added here because the spec's "`elabAppFn`'s ident case" needs a home) |
| `AppElab` struct instead of a transformer stack | 3 |
| every `Context`/`State` field present from the start | 3 |
| `param_idx` / `get_f_type` via `instantiate_beta_rev_range` | 1, 3 |
| dispatch rewiring of `app` / `<ident>` / `explicit` / `explicitUniv` | 4, 8 |
| `builtin/ident.rs` deleted, logic moved, records byte-identical | 4 (steps 8, 10) |
| `proj`/`pipeProj`/`dotIdent`/`namedPattern`/`choice` NOT rewired | 9 (step 3) |
| overload single-candidate guard | 4 (step 4) |
| `propagateExpectedType` | 6 |
| `etaArgs` | 7 |
| implicit-lambda guard in P1, implementation in P5 | 8 (step 5) |
| P1 accessor ledger = `instantiate_beta_rev_range` only | 1 |
| expected types induced by source ascription; dumper entry point unchanged | 4-8 (every corpus step) |

**Placeholder scan:** the one `todo!()` in Task 4 step 3 is an explicit move-marker with instructions that it must not survive the step; the two "fill in the body" test stubs (Task 5 step 4, Task 9 step 1) name the exact assertion and construction helper. No "TBD", no "add error handling", no "similar to Task N".

**Type consistency:** `AppElab`/`Context`/`State` field names are used identically in Tasks 3-8. Two signature adjustments are called out where they arise rather than left to collide: `kinds` threading through `main`/`process_explicit_arg`/`elab_and_add_new_arg` (Task 4 step 5, with Task 3's signatures to be updated if the field route is taken), and `mk_fresh_expr_mvar` possibly returning `(ExprId, MVarId)` (Task 5 step 3). `add_new_arg` drops the oracle's `argName` parameter because its only use is `registerMVarArgName`, a P2 ladder field — noted in Task 4's code comment.

---

## Execution Handoff

Plan complete and saved to `docs/superpowers/plans/2026-07-25-m4b3-plan1-app-foundation.md`. Two execution options:

1. **Subagent-Driven (recommended)** — a fresh subagent per task, review between tasks, fast iteration.
2. **Inline Execution** — execute tasks in this session using executing-plans, batch execution with checkpoints.
