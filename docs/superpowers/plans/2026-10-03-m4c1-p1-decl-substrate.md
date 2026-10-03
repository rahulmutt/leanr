# M4c-1 P1 — declaration substrate — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** P2's command elaborator needs a set of kernel and `leanr_meta` primitives to turn an elaborated definition into kernel-checked declarations. This plan ports them:
- level-param collection and sorting
- `levelMVarToParam`
- `getMaxHeight`
- `Core.betaReduce` and `zetaReduce`
- the `Closure` builder
- `abstractNestedProofs`, which produces `_proof_N` aux theorems
- a kernel entry point that admits a declaration built in a caller's scratch store

**Architecture:** Each oracle function becomes a `MetaCtx` method, or a free function where the oracle function is pure, in a new focused `leanr_meta` file. Aux lemmas are **not** added to the environment during elaboration. Instead, `abstract_nested_proofs` records them in an `AuxLemmas` accumulator, and its pending names count as "already in the environment" for naming and triviality. The caller later commits them, in order, through the new `Environment::add_decl_in(&mut scratch, decl)`. A final integration test does exactly that over the Meta0 fixture.

**Tech Stack:** Rust (workspace crates `leanr_kernel`, `leanr_meta`); the oracle is `leanprover/lean4:v4.33.0-rc1` (sources under `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean`).

**Spec:** `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md`. Amendment 1 at the bottom of this plan lists the refinements made at plan time; the same text goes into the spec in Task 8.

## Global Constraints

- The pinned oracle is `leanprover/lean4:v4.33.0-rc1`. Every `oracle:` doc comment cites a `file:line` you have **opened**, because cites drift by 1-2 lines (memory: "oracle citations are unverified").
- `leanr_kernel` changes are additive and TCB-neutral: one new `pub fn` plus one visibility widening, with no change to checking logic.
- `leanr_meta` changes are additive. Each new file has one responsibility, and existing methods are only widened (`pub(crate)`/`pub`), never re-behaved.
- Every new public item P2 consumes is listed under **Interfaces → Produces** with its exact signature.
- Build only under `/workspace` (`target/`), never `/tmp`. `/tmp` is a 20Gi EmptyDir, and filling it evicts the pod.
- Before every push, run `mise run ci` and block on it. It covers fmt, clippy and tests. Never background it and end the turn.
- Every task's mutation list is executed for real: apply the mutation, run the named test, confirm it FAILS, then revert. Record the outcomes in the task's commit message body.
- Test style follows the existing `leanr_meta` unit tests: `#[cfg(test)] mod tests` at the bottom of the file, helpers from `crate::test_support`, and expected exprs built with the same helpers and compared by `ExprId` equality (hash-consing makes structural equality the same as id equality).

## Review Focus

These are the failure modes a P2 user is most likely to hit that no task's happy-path tests cover. Each one gets a test in the task that owns the code.

1. **Lexicographic `u_N` ordering:** `sortDeclLevelParams` sorts leftover params with `Name.lt`, so `u_10` sorts BEFORE `u_2`. A numeric-aware sort would silently reorder `levelParams`. → Task 2 test `sort_decl_level_params_sorts_leftovers_lexicographically`.
2. **Pending aux names:** a second abstracted proof in the same declaration must get `_proof_2`, not `_proof_1`, even though `_proof_1` is not in the env yet. → Task 7 test `distinct_proofs_get_distinct_indices`.
3. **Closure renames level params:** an aux lemma over a universe-polymorphic proof gets `u_1` in its own level params, and is applied to the ORIGINAL `u` (probe: `foo2._proof_1.{u_1}` applied as `foo2._proof_1.{u} α a`). → Task 6 test `closure_renames_level_params_to_u_n`.
4. **Trivial proofs stay inline:** `@rfl N n` (atomic args) must NOT be abstracted (probe: `foo5` has no aux). → Task 7 test `atomic_arg_proof_is_not_abstracted`.
5. **Rejected commit leaves no trace:** `add_decl_in` with an ill-typed declaration must leave `env.len()` unchanged. → Task 1 test `add_decl_in_rejection_leaves_env_unchanged`.

## Oracle probe facts (pinned at plan time)

These come from scratch `target/m4c1probe/Probe.lean` (`import Lean`, `inductive N`), checked with `pp.all`:

| source | result |
|---|---|
| `def foo1 (n : N) : PProd N (N.succ n = N.succ n) := ⟨n, rfl⟩` | `foo1._proof_1 : ∀ (n : N), @Eq.{1} N (N.succ n) (N.succ n) := fun (n : N) => @rfl.{1} N (N.succ n)`; value `fun n => @PProd.mk.{1,0} N (…) n (foo1._proof_1 n)`; hints `regular 1` |
| `def foo2.{u} (α : Sort u) (a : α) : PProd α (id a = id a) := ⟨a, rfl⟩` | `foo2._proof_1.[u_1] : ∀ (α : Sort u_1) (a : α), @Eq.{u_1} α (@id.{u_1} α a) (@id.{u_1} α a)`; used as `foo2._proof_1.{u} α a`; hints `regular 2` (`id` has height 1) |
| `foo3`: two identical proofs | one aux lemma used twice. In the probe the cache was **env-wide**, so `foo3` reused `foo1._proof_1` (an M4c-2 concern; see Amendment 1). |
| `foo4`: proofs over `N.succ n` and `N.succ (N.succ n)` | the first reused `foo1._proof_1` from the cache; the second became `foo4._proof_1` (fresh index for this declaration's prefix) |
| `def foo5 (n : N) : PProd N (n = n) := ⟨n, rfl⟩` | no aux: `@rfl.{1} N n` stays inline (trivial proof) |
| `def bar := @id` | `bar.[u_1] : {α : Sort u_1} → α → α`, hints `regular 2` |

Meta0 heights from `Meta0.olean` (`readModuleData`): `id` is `regular 1`, `count._sunfold` is `regular 2`, `count` is `regular 1`, and `Eq.ndrec`, `N.brecOn` and the other auxiliaries are `abbrev`.

## File Structure

| File | Responsibility |
|---|---|
| `crates/leanr_kernel/src/env.rs` (modify) | `Environment::add_decl_in` — check+admit a `Declaration` whose ids live in a caller-owned scratch `Store` |
| `crates/leanr_kernel/src/env/tests.rs` (modify) | tests for `add_decl_in` |
| `crates/leanr_kernel/src/local_ctx.rs` (modify) | widen `fresh_fvar_id` to `pub` (Task 6 needs an undeclared fresh fvar) |
| `crates/leanr_meta/src/level_params.rs` (create) | `name_cmp`, `append_index_after`, `CollectLevelParams`, `sort_decl_level_params`, `level_mvar_to_param` |
| `crates/leanr_meta/src/level.rs` (modify) | `update_level_succ/max/imax` (the oracle's `Level.update*!Impl` semantics) + `mk_level_imax_prime` |
| `crates/leanr_meta/src/max_height.rs` (create) | `get_max_height` |
| `crates/leanr_meta/src/transform.rs` (modify) | `core_transform` (loose-bvar traversal), `beta_reduce`, `transform_with`, `zeta_reduce` |
| `crates/leanr_meta/src/closure.rs` (create) | `mk_value_type_closure` (`zetaDelta := true` only) |
| `crates/leanr_meta/src/abstract_proofs.rs` (create) | `AuxLemmas`, `mk_aux_decl_name`, `mk_aux_lemma`, `mk_aux_theorem`, `is_non_trivial_proof`, `has_sorry`, `abstract_nested_proofs` |
| `crates/leanr_meta/src/test_support.rs` (modify) | `cu` (const with explicit levels), `lparam`, `lit_level` helpers |
| `crates/leanr_meta/tests/decl_substrate.rs` (create) | end-to-end: abstract + commit aux and main decls over Meta0 into an owned `Environment` |
| `crates/leanr_meta/src/lib.rs` (modify) | `mod` lines + `pub use` of the new public items |

---

### Task 1: `Environment::add_decl_in`

**Files:**
- Modify: `crates/leanr_kernel/src/env.rs:494-524` (`add_decl`)
- Test: `crates/leanr_kernel/src/env/tests.rs`

**Interfaces:**
- Consumes: `check_declaration(view, &mut Store, Declaration)` (`env.rs:199`), `add_core(&Store, ConstantInfo)` (`env.rs:547`).
- Produces: `pub fn add_decl_in(&mut self, scratch: &mut Store, d: Declaration) -> Result<(), KernelError>`. `add_decl(d)` becomes `self.add_decl_in(&mut Store::scratch(), d)`.

(Superseded by R5: `add_decl_in` DOES promote every id of `d` into `self.store` before checking; see Amendment 1 item 1. The paragraph below is the original, wrong claim.) Why no promote walk: `check_declaration` already resolves every id through `scratch.*(Some(view.store), …)`, so a declaration whose ids were minted in **this** scratch store checks correctly. Then `add_core` promotes each surviving `ConstantInfo` through `promote_constant_info`. The region contract in `add_decl`'s doc ("a freshly-created scratch cannot resolve a scratch id minted by some OTHER scratch store") is exactly what `add_decl_in` lifts.

- [ ] **Step 1: Write the failing tests** (append to `env/tests.rs`)

```rust
// ---- add_decl_in (M4c-1 P1 task 1) -------------------------------------

/// A declaration whose NAME (and type) live only in a caller-owned scratch
/// store is checked against that store and admitted with persistent ids.
#[test]
fn add_decl_in_admits_a_declaration_built_in_a_caller_scratch_store() {
    let mut env = mini::env();
    let len_before = env.len();
    let mut scratch = Store::scratch();
    let name = scratch
        .intern_name(Some(&env.store), &nm("scratchOnlyAx"))
        .unwrap()
        .unwrap();
    assert!(name.is_scratch(), "precondition: the name is new, so scratch-region");
    let ty = scratch.intern_expr(Some(&env.store), &mini::sort0()).unwrap();
    env.add_decl_in(
        &mut scratch,
        Declaration::Axiom(AxiomVal {
            val: ConstantVal { name, level_params: vec![], ty },
            is_unsafe: false,
        }),
    )
    .unwrap();
    assert_eq!(env.len(), len_before + 1);
    let persistent = nm_id(&mut env, "scratchOnlyAx");
    let ci = env.get(persistent).expect("admitted under its persistent id").clone();
    assert!(matches!(ci, ConstantInfo::Axiom(_)));
    assert_no_scratch_ids(&env.store, &ci);
}

/// Review Focus 5: a rejected scratch-built declaration leaves no trace.
#[test]
fn add_decl_in_rejection_leaves_env_unchanged() {
    let mut env = mini::env();
    let len_before = env.len();
    let mut scratch = Store::scratch();
    let name = scratch
        .intern_name(Some(&env.store), &nm("scratchBadThm"))
        .unwrap()
        .unwrap();
    // `theorem scratchBadThm : A := a` — `A : Sort 1`, not a Prop.
    let ty = scratch.intern_expr(Some(&env.store), &mini::cst("A", vec![])).unwrap();
    let value = scratch.intern_expr(Some(&env.store), &mini::cst("a", vec![])).unwrap();
    let r = env.add_decl_in(
        &mut scratch,
        Declaration::Thm(TheoremVal {
            val: ConstantVal { name, level_params: vec![], ty },
            value,
            all: vec![name],
        }),
    );
    assert!(r.is_err(), "a non-Prop theorem type is rejected");
    assert_eq!(env.len(), len_before);
}
```

Before relying on the second test, confirm that `mini`'s `A` is not a Prop: `rejects_theorem_not_prop` (`env/tests.rs:237`) uses the same constant. If it uses a different one, copy that test's type instead.

- [ ] **Step 2: Run the tests and verify they fail**

Run: `cargo test -p leanr_kernel add_decl_in -- --nocapture`
Expected: compile error `no method named add_decl_in`.

- [ ] **Step 3: Implement**

In `env.rs`, replace `add_decl`'s body and add `add_decl_in` directly below it, keeping `add_decl`'s doc comment:

```rust
    pub fn add_decl(&mut self, d: Declaration) -> Result<(), KernelError> {
        self.add_decl_in(&mut Store::scratch(), d)
    }

    /// [`Environment::add_decl`] over a CALLER-OWNED scratch store (M4c-1
    /// P1): `d`'s ids may be scratch-region ids minted in `scratch` itself
    /// (an elaborator's per-declaration store). `check_declaration`
    /// resolves every id through `scratch` with `self.store` as base, and
    /// `add_core` promotes each survivor (`promote_constant_info`), so no
    /// separate promote walk over `d` is needed. On any check failure the
    /// environment is left completely unchanged (`scratch` may have grown;
    /// it is the caller's to drop).
    pub fn add_decl_in(&mut self, scratch: &mut Store, d: Declaration) -> Result<(), KernelError> {
        let Admitted {
            survivors,
            quot_init,
        } = {
            let view = self.view();
            check_declaration(view, scratch, d)?
        };
        for ci in survivors {
            self.add_core(scratch, ci)?;
        }
        if quot_init {
            self.quot_initialized = true;
        }
        Ok(())
    }
```

- [ ] **Step 4: Run the tests and verify they pass**

Run: `cargo test -p leanr_kernel` (the whole crate, since `add_decl` now delegates)
Expected: PASS, including every pre-existing `env/tests.rs` and replay test.

- [ ] **Step 5: Mutations** (apply, run `cargo test -p leanr_kernel add_decl_in`, expect FAIL, revert)
  1. In `add_decl_in`, call `check_declaration(view, &mut Store::scratch(), d)`. Expected: the first test fails (the scratch name cannot be resolved).
  2. Skip `add_core`'s promotion by inserting `ci` unpromoted with `self.constants.insert(ci.name(), ci)`. Expected: the first test fails, either on `env.get(persistent)` being `None` or in `assert_no_scratch_ids`.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_kernel/src/env.rs crates/leanr_kernel/src/env/tests.rs
git commit -m "leanr_kernel: add_decl_in admits a declaration built in a caller scratch store"
```

---

### Task 2: level-param collection and sorting

**Files:**
- Create: `crates/leanr_meta/src/level_params.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (`mod level_params;` + `pub use level_params::{name_cmp, sort_decl_level_params, CollectLevelParams};`)
- Modify: `crates/leanr_meta/src/test_support.rs` (helpers below)

**Interfaces:**
- Consumes: `MetaCtx::{node, guarded, step}`, `Store::{level_row, name_row, str_at, nat_at, level_list_at}`.
- Produces:
  - `pub fn name_cmp(st: &Store, base: Option<&Store>, a: Option<NameId>, b: Option<NameId>) -> std::cmp::Ordering`. `None` is `Name.anonymous`.
  - `pub(crate) fn append_index_after(st: &mut Store, base: Option<&Store>, n: NameId, idx: u64) -> Result<NameId, MetaError>`.
  - `#[derive(Default)] pub struct CollectLevelParams { pub params: Vec<NameId>, visited_level: HashSet<LevelId>, visited_expr: HashSet<ExprId> }`.
  - `impl MetaCtx { pub fn collect_level_params(&mut self, s: &mut CollectLevelParams, e: ExprId) -> Result<(), MetaError> }`.
  - `pub fn sort_decl_level_params(st: &Store, base: Option<&Store>, scope_params: &[NameId], all_user_params: &[NameId], used_params: &[NameId]) -> Result<Vec<NameId>, NameId>`. `scope_params` and `all_user_params` are in **reverse declaration order** (head = last declared), exactly as the oracle. `Err(u)` is the unused universe parameter `u`.
  - test_support helpers:
    - `lparam(ctx, "u") -> LevelId`
    - `lit_level(ctx, n) -> LevelId` (`succ^n zero`)
    - `cu(ctx, "Eq.refl", &[LevelId]) -> ExprId` (a const with explicit levels; dotted names allowed)

The oracle code being ported:
- `Name.cmp` (`Lean/Data/Name.lean:67-80`), where `Name.lt a b` is `a.cmp b == .lt`.
- `Name.appendIndexAfter` (`Init/Meta/Defs.lean:322-325`). There are no macro scopes in leanr names, so `modifyBase` is the identity.
- `CollectLevelParams` (`Lean/Util/CollectLevelParams.lean:11-72`).
- `sortDeclLevelParams` (`Lean/Elab/DeclUtil.lean:79-88`).

- [ ] **Step 1: Add the test helpers** to `test_support.rs`, next to `c`:

```rust
/// `Level.param` for a root name.
pub(crate) fn lparam(ctx: &mut MetaCtx, name: &str) -> leanr_kernel::bank::LevelId {
    let base = Some(ctx.view.store);
    let s = ctx.scratch.intern_str(base, name).expect("intern");
    let n = ctx.scratch.name_str(base, None, s).expect("name");
    ctx.scratch.level_param(base, Some(n)).expect("level")
}

/// `succ^n zero`.
pub(crate) fn lit_level(ctx: &mut MetaCtx, n: u32) -> leanr_kernel::bank::LevelId {
    let base = Some(ctx.view.store);
    let mut l = ctx.scratch.level_zero(base).expect("level");
    for _ in 0..n {
        l = ctx.scratch.level_succ(base, l).expect("level");
    }
    l
}

/// `Expr.const` for a possibly dotted name with EXPLICIT universe levels
/// (unlike [`c`], which fills every level with `zero`).
pub(crate) fn cu(ctx: &mut MetaCtx, name: &str, levels: &[leanr_kernel::bank::LevelId]) -> ExprId {
    let base = Some(ctx.view.store);
    let mut n = None;
    for part in name.split('.') {
        let s = ctx.scratch.intern_str(base, part).expect("intern");
        n = Some(ctx.scratch.name_str(base, n, s).expect("name"));
    }
    let ls = ctx.scratch.intern_level_list(base, levels).expect("levels");
    ctx.scratch.expr_const(base, n, ls).expect("const")
}
```

- [ ] **Step 2: Write the failing tests** (`level_params.rs`, `#[cfg(test)] mod tests`)

```rust
use super::*;
use crate::test_support::{cu, lparam, with_ctx};

fn nm(ctx: &mut MetaCtx, s: &str) -> NameId {
    let base = Some(ctx.view.store);
    let mut n = None;
    for part in s.split('.') {
        let id = ctx.scratch.intern_str(base, part).unwrap();
        n = Some(ctx.scratch.name_str(base, n, id).unwrap());
    }
    n.unwrap()
}

#[test]
fn name_cmp_is_the_oracle_structural_order() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let (u, u_2, u_10, u_v) = (nm(ctx, "u"), nm(ctx, "u_2"), nm(ctx, "u_10"), nm(ctx, "u.v"));
        use std::cmp::Ordering::*;
        // String components compare lexicographically: "u_10" < "u_2".
        assert_eq!(name_cmp(ctx.scratch, base, Some(u_10), Some(u_2)), Less);
        // A prefix (shorter parent chain) sorts first: `u` < `u.v`.
        assert_eq!(name_cmp(ctx.scratch, base, Some(u), Some(u_v)), Less);
        assert_eq!(name_cmp(ctx.scratch, base, None, Some(u)), Less);
        assert_eq!(name_cmp(ctx.scratch, base, Some(u), Some(u)), Equal);
    });
}

#[test]
fn append_index_after_extends_the_last_string_component() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let proof = nm(ctx, "foo._proof");
        let got = append_index_after(ctx.scratch, base, proof, 1).unwrap();
        assert_eq!(got, nm(ctx, "foo._proof_1"));
    });
}

/// Visit order is the oracle's: forall/lam domain before body, app fn
/// before arg, const levels left to right; each param once.
#[test]
fn collect_level_params_visits_in_oracle_order_and_dedupes() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let (u, v, w) = (lparam(ctx, "u"), lparam(ctx, "v"), lparam(ctx, "w"));
        let f = cu(ctx, "F", &[v, u]); // F.{v,u}
        let sw = ctx.scratch.expr_sort(base, w).unwrap(); // Sort w
        let fu = app(ctx, f, sw); // F.{v,u} (Sort w)
        let uu = ctx.scratch.level_max(base, u, u).unwrap();
        let su = ctx.scratch.expr_sort(base, uu).unwrap(); // Sort (max u u)
        let e = app(ctx, fu, su);
        let mut s = CollectLevelParams::default();
        ctx.collect_level_params(&mut s, e).unwrap();
        assert_eq!(s.params, vec![nm(ctx, "v"), nm(ctx, "u"), nm(ctx, "w")]);
    });
}

/// Review Focus 1: user names first in user order, then the rest by
/// `Name.lt` — so `u_10` precedes `u_2`.
#[test]
fn sort_decl_level_params_sorts_leftovers_lexicographically() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let (u, v, u_2, u_10) = (nm(ctx, "u"), nm(ctx, "v"), nm(ctx, "u_2"), nm(ctx, "u_10"));
        // `.{u, v}` declared in that order → reverse order in the list.
        let all_user = [v, u];
        let used = [u_2, v, u_10, u];
        let got = sort_decl_level_params(ctx.scratch, base, &[], &all_user, &used).unwrap();
        assert_eq!(got, vec![u, v, u_10, u_2]);
    });
}

#[test]
fn sort_decl_level_params_rejects_an_unused_user_param_outside_the_scope() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let (u, w) = (nm(ctx, "u"), nm(ctx, "w"));
        assert_eq!(
            sort_decl_level_params(ctx.scratch, base, &[], &[w, u], &[u]),
            Err(w)
        );
        // In scope (`universe w`), an unused `w` is fine and is not listed.
        assert_eq!(
            sort_decl_level_params(ctx.scratch, base, &[w], &[w, u], &[u]),
            Ok(vec![u])
        );
    });
}
```

`app` is `crate::test_support::app`; import it too.

- [ ] **Step 3: Run the tests and verify they fail**

Run: `cargo test -p leanr_meta level_params`
Expected: compile errors (the module and functions don't exist yet).

- [ ] **Step 4: Implement `level_params.rs`**

```rust
//! oracle: universe-parameter bookkeeping for declarations (M4c-1 P1).
//! `Name.cmp` (`Lean/Data/Name.lean:67-80`), `Name.appendIndexAfter`
//! (`Init/Meta/Defs.lean:322-325`), `CollectLevelParams`
//! (`Lean/Util/CollectLevelParams.lean:11-72`), `sortDeclLevelParams`
//! (`Lean/Elab/DeclUtil.lean:79-88`) and `levelMVarToParam`
//! (`Lean/MetavarContext.lean:1426-1497`; Task 3).

use std::cmp::Ordering;
use std::collections::HashSet;

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::names::NameRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId, Store};

use crate::{MetaCtx, MetaError};

/// oracle: `Name.cmp` (`Name.lean:67-80`): parents first; `num < str`;
/// strings by `compare` (code-point lexicographic), nums numerically.
pub fn name_cmp(st: &Store, base: Option<&Store>, a: Option<NameId>, b: Option<NameId>) -> Ordering {
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(a), Some(b)) => match (st.name_row(base, a), st.name_row(base, b)) {
            (NameRow::Num { parent: p1, part: i1 }, NameRow::Num { parent: p2, part: i2 }) => {
                name_cmp(st, base, *p1, *p2).then_with(|| st.nat_at(base, *i1).cmp(st.nat_at(base, *i2)))
            }
            (NameRow::Num { .. }, NameRow::Str { .. }) => Ordering::Less,
            (NameRow::Str { .. }, NameRow::Num { .. }) => Ordering::Greater,
            (NameRow::Str { parent: p1, part: s1 }, NameRow::Str { parent: p2, part: s2 }) => {
                name_cmp(st, base, *p1, *p2).then_with(|| st.str_at(base, *s1).cmp(st.str_at(base, *s2)))
            }
        },
    }
}
```

Adapt the `NameRow` pattern to its real shape: `bank/names.rs` defines it, and `name_str`/`name_num` above show the `parent`/`part` fields. Rust's `str::cmp` compares bytes, which agrees with code-point order for UTF-8. `Nat` must implement `Ord`; if it doesn't, compare via its existing `cmp` helper (grep `impl Ord for Nat`).

```rust
/// oracle: `Name.appendIndexAfter` (`Defs.lean:322-325`): `str p s` →
/// `str p (s ++ "_" ++ idx)`; otherwise `str n ("_" ++ idx)`.
pub(crate) fn append_index_after(
    st: &mut Store,
    base: Option<&Store>,
    n: NameId,
    idx: u64,
) -> Result<NameId, MetaError> {
    let (parent, s) = match *st.name_row(base, n) {
        NameRow::Str { parent, part } => (parent, format!("{}_{idx}", st.str_at(base, part))),
        NameRow::Num { .. } => (Some(n), format!("_{idx}")),
    };
    let sid = st.intern_str(base, &s)?;
    Ok(st.name_str(base, parent, sid)?)
}

/// oracle: `CollectLevelParams.State` (`CollectLevelParams.lean:13-16`).
#[derive(Default)]
pub struct CollectLevelParams {
    pub params: Vec<NameId>,
    visited_level: HashSet<LevelId>,
    visited_expr: HashSet<ExprId>,
}

impl<'e> MetaCtx<'e> {
    /// oracle: `collectLevelParams` (`CollectLevelParams.lean:72`) and
    /// its `visitExpr`/`main`/`visitLevel`/`collect` (`:20-55`).
    pub fn collect_level_params(&mut self, s: &mut CollectLevelParams, e: ExprId) -> Result<(), MetaError> {
        if !self.data(e).has_level_param() || !s.visited_expr.insert(e) {
            return Ok(());
        }
        self.step()?;
        match self.node(e) {
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                self.guarded(|c| c.collect_level_params(s, structure))
            }
            Node::Forall { binder_type, body, .. } | Node::Lam { binder_type, body, .. } => self.guarded(|c| {
                c.collect_level_params(s, binder_type)?;
                c.collect_level_params(s, body)
            }),
            Node::LetE { ty, value, body, .. } => self.guarded(|c| {
                c.collect_level_params(s, ty)?;
                c.collect_level_params(s, value)?;
                c.collect_level_params(s, body)
            }),
            Node::App { f, a } => self.guarded(|c| {
                c.collect_level_params(s, f)?;
                c.collect_level_params(s, a)
            }),
            Node::MData { expr, .. } => self.guarded(|c| c.collect_level_params(s, expr)),
            Node::Const { levels, .. } => {
                let ls = self.scratch.level_list_at(Some(self.view.store), levels).to_vec();
                for l in ls {
                    self.collect_level(s, l);
                }
                Ok(())
            }
            Node::Sort { level } => {
                self.collect_level(s, level);
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// oracle: `visitLevel`/`collect` (`:20-30`).
    fn collect_level(&self, s: &mut CollectLevelParams, u: LevelId) {
        let base = Some(self.view.store);
        if self.scratch.level_flags(base, u) & 0b01 == 0 || !s.visited_level.insert(u) {
            return;
        }
        match *self.scratch.level_row(base, u) {
            LevelRow::Succ(v) => self.collect_level(s, v),
            LevelRow::Max(a, b) | LevelRow::IMax(a, b) => {
                self.collect_level(s, a);
                self.collect_level(s, b);
            }
            LevelRow::Param(Some(n)) => s.params.push(n),
            _ => {}
        }
    }
}

/// oracle: `sortDeclLevelParams` (`DeclUtil.lean:79-88`). `scope_params`
/// and `all_user_params` are in REVERSE declaration order. `Err(u)` is
/// the oracle's "unused universe parameter 'u'".
pub fn sort_decl_level_params(
    st: &Store,
    base: Option<&Store>,
    scope_params: &[NameId],
    all_user_params: &[NameId],
    used_params: &[NameId],
) -> Result<Vec<NameId>, NameId> {
    if let Some(&u) = all_user_params
        .iter()
        .find(|u| !used_params.contains(u) && !scope_params.contains(u))
    {
        return Err(u);
    }
    // foldl over the reversed list, consing → user order.
    let mut result: Vec<NameId> = all_user_params
        .iter()
        .rev()
        .copied()
        .filter(|u| used_params.contains(u))
        .collect();
    let mut remaining: Vec<NameId> = used_params
        .iter()
        .copied()
        .filter(|p| !all_user_params.contains(p))
        .collect();
    remaining.sort_by(|a, b| name_cmp(st, base, Some(*a), Some(*b)));
    result.extend(remaining);
    Ok(result)
}
```

Check the exact `Node` field names (`binder_type`, `body`, `ty`, `value`, `f`, `a`, `levels`, `level`, `expr`, `structure`) against `crates/leanr_kernel/src/bank/terms.rs:257-317` and rename to match. Also check that `self.data(e).has_level_param()` exists: `ExprData::has_level_param` is at `expr.rs:284`.

- [ ] **Step 5: Run the tests and verify they pass**

Run: `cargo test -p leanr_meta level_params`
Expected: 5 PASS.

- [ ] **Step 6: Mutations** (each one expected to FAIL the named test)
  1. Visit `body` before `binder_type` in the `Forall`/`Lam` arm → `collect_level_params_visits_in_oracle_order_and_dedupes`.
  2. Drop `visited_level.insert` dedupe (always recurse) → same test (duplicate `u`).
  3. In `sort_decl_level_params`, sort `remaining` by a numeric-suffix-aware key (e.g. `sort_by_key(|n| render(n).len())`) → `sort_decl_level_params_sorts_leftovers_lexicographically`.
  4. Drop the `.rev()` in the user-order fold → same test (`[v, u, …]`).
  5. Drop `&& !scope_params.contains(u)` → `sort_decl_level_params_rejects_an_unused_user_param_outside_the_scope`.

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_meta/src/level_params.rs crates/leanr_meta/src/lib.rs crates/leanr_meta/src/test_support.rs
git commit -m "leanr_meta: collectLevelParams, sortDeclLevelParams, Name.cmp ports"
```

---

### Task 3: `levelMVarToParam` and the `Level.update*!` helpers

**Files:**
- Modify: `crates/leanr_meta/src/level.rs` (helpers next to `mk_level_max_prime`, `:536-560`)
- Modify: `crates/leanr_meta/src/level_params.rs`

**Interfaces:**
- Consumes: Task 2's `append_index_after`; `MetavarContext::{level_assignment, assign_level, assignment}`; `MetaCtx::{instantiate_mvars, head_beta, fresh_level_mvar}`.
- Produces:
  - `pub(crate) fn update_level_succ(&mut self, orig: LevelId, a2: LevelId) -> Result<LevelId, MetaError>`
  - `pub(crate) fn update_level_max(&mut self, orig: LevelId, a2: LevelId, b2: LevelId) -> Result<LevelId, MetaError>`
  - `pub(crate) fn update_level_imax(&mut self, orig: LevelId, a2: LevelId, b2: LevelId) -> Result<LevelId, MetaError>`
  - `pub struct LevelMVarToParamResult { pub expr: ExprId, pub new_param_names: Vec<NameId>, pub next_param_idx: u64 }`
  - `pub fn level_mvar_to_param(&mut self, e: ExprId, already_used: &[NameId], next_param_idx: u64) -> Result<LevelMVarToParamResult, MetaError>`. The prefix is fixed at `u` and `except` is always `false`, which are the only settings `Term.levelMVarToParam` (`Elab/Term/TermElabM.lean:1059-1064`) passes. P2 owns the `levelNames` bookkeeping.

The oracle code being ported:
- `Level.update{Succ,Max,IMax}!Impl` (`Lean/Level.lean:564-595`). The compiled `implemented_by` versions are what runs. If both children are unchanged, the oracle uses `simpLevelMax'`/`simpLevelIMax'` with `orig` as the default; otherwise `mkLevelMax'`/`mkLevelIMax'` (`:518-554`). `succ` rebuilds only when changed.
- `LevelMVarToParam` (`MetavarContext.lean:1426-1497`):
  - `visitLevel`: an assigned level mvar is followed; an unassigned one gets `mkParamName`, skipping names in `already_used`, and is **assigned** to the new param.
  - `main`: skips terms with no mvars (`hasMVar` = expression or level mvar), caches per structure, and handles an app whose head is an assigned expr mvar with `instantiate` + `headBeta`.

Because ids are hash-consed, `ptrEq` becomes id equality. That is stronger than pointer equality, but it is observably the same here: when the children are structurally equal, `mkLevelMax'` and `simpLevelMax'` agree.

- [ ] **Step 1: Write the failing tests** (`level_params.rs` tests module)

```rust
use crate::test_support::lit_level;

fn sort_of(ctx: &mut MetaCtx, l: LevelId) -> ExprId {
    let base = Some(ctx.view.store);
    ctx.scratch.expr_sort(base, l).unwrap()
}

fn arrow(ctx: &mut MetaCtx, a: ExprId, b: ExprId) -> ExprId {
    ctx.mk_arrow(a, b).unwrap()
}

/// `Sort ?u → Sort ?v → Sort ?u` ↦ `Sort u_1 → Sort u_2 → Sort u_1`; the
/// mvars are ASSIGNED, so a second occurrence reuses the param.
#[test]
fn level_mvar_to_param_names_u_n_and_assigns() {
    with_ctx(|ctx| {
        let (mu, lu) = ctx.fresh_level_mvar().unwrap();
        let (_mv, lv) = ctx.fresh_level_mvar().unwrap();
        let (su, sv) = (sort_of(ctx, lu), sort_of(ctx, lv));
        let inner = arrow(ctx, sv, su);
        let e = arrow(ctx, su, inner);
        let r = ctx.level_mvar_to_param(e, &[], 1).unwrap();
        let (p1, p2) = (lparam(ctx, "u_1"), lparam(ctx, "u_2"));
        let (s1, s2) = (sort_of(ctx, p1), sort_of(ctx, p2));
        let inner2 = arrow(ctx, s2, s1);
        assert_eq!(r.expr, arrow(ctx, s1, inner2));
        assert_eq!(r.new_param_names, vec![nm(ctx, "u_1"), nm(ctx, "u_2")]);
        assert_eq!(r.next_param_idx, 3);
        assert_eq!(ctx.mctx().level_assignment(mu), Some(p1));
    });
}

#[test]
fn level_mvar_to_param_skips_already_used_names() {
    with_ctx(|ctx| {
        let (_m, l) = ctx.fresh_level_mvar().unwrap();
        let e = sort_of(ctx, l);
        let used = [nm(ctx, "u_1")];
        let r = ctx.level_mvar_to_param(e, &used, 1).unwrap();
        let p2 = lparam(ctx, "u_2");
        assert_eq!(r.expr, sort_of(ctx, p2));
        assert_eq!(r.new_param_names, vec![nm(ctx, "u_2")]);
    });
}

/// An assigned mvar is followed: `?w := succ ?u` gives `Sort (succ u_1)`.
#[test]
fn level_mvar_to_param_follows_level_assignments() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let (_mu, lu) = ctx.fresh_level_mvar().unwrap();
        let (mw, lw) = ctx.fresh_level_mvar().unwrap();
        let su = ctx.scratch.level_succ(base, lu).unwrap();
        ctx.mctx_mut().assign_level(mw, su).unwrap();
        let r = ctx.level_mvar_to_param(sort_of(ctx, lw), &[], 1).unwrap();
        let p1 = lparam(ctx, "u_1");
        let sp1 = ctx.scratch.level_succ(base, p1).unwrap();
        assert_eq!(r.expr, sort_of(ctx, sp1));
    });
}

/// `update_level_max` on CHANGED children uses `mkLevelMax'`, which
/// simplifies `max 1 0` to `1`; on UNCHANGED children it returns `orig`
/// unless `simpLevelMax'` fires.
#[test]
fn update_level_max_simplifies_like_mk_level_max_prime() {
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let (zero, one) = (lit_level(ctx, 0), lit_level(ctx, 1));
        let u = lparam(ctx, "u");
        let orig = ctx.scratch.level_max(base, u, zero).unwrap(); // max u 0
        assert_eq!(ctx.update_level_max(orig, one, zero).unwrap(), one);
        let v = lparam(ctx, "v");
        let uv = ctx.scratch.level_max(base, u, v).unwrap();
        assert_eq!(ctx.update_level_max(uv, u, v).unwrap(), uv);
    });
}
```

`mk_arrow` is `pub(crate)` (`metactx.rs:570`), which a crate-internal test can call. If `fresh_level_mvar` has a different return shape, follow `level.rs:798`.

- [ ] **Step 2: Run the tests and verify they fail**

Run: `cargo test -p leanr_meta level_mvar_to_param update_level_max`
Expected: compile errors.

- [ ] **Step 3: Implement the level helpers** (`level.rs`, after `mk_level_max_prime`)

First read `mk_level_max_prime` (`level.rs:536-560`). If its "core" (the oracle's `mkLevelMaxCore u v elseK`, `Level.lean:518-533`) is inline, refactor it into `fn mk_level_max_core(&mut self, u, v, else_k: impl FnOnce(&mut Self) -> Result<LevelId, MetaError>)`, so both `mkLevelMax'` (`else_k` = build `max u v`) and `simpLevelMax'` (`else_k` = return `orig`) share it. Then add:

```rust
    /// oracle: `mkLevelIMaxCore` + `mkLevelIMax'` (`Level.lean:542-551`).
    fn mk_level_imax_core(
        &mut self,
        u: LevelId,
        v: LevelId,
        else_k: impl FnOnce(&mut Self) -> Result<LevelId, MetaError>,
    ) -> Result<LevelId, MetaError> {
        let base = Some(self.view.store);
        if self.level_is_never_zero(v) {
            self.mk_level_max_prime(u, v)
        } else if matches!(*self.scratch.level_row(base, v), LevelRow::Zero) {
            Ok(v)
        } else if matches!(*self.scratch.level_row(base, u), LevelRow::Zero) || u == v {
            Ok(if u == v { u } else { v })
        } else {
            else_k(self)
        }
    }

    /// oracle: `Level.updateSucc!Impl` (`Level.lean:564-567`).
    pub(crate) fn update_level_succ(&mut self, orig: LevelId, a2: LevelId) -> Result<LevelId, MetaError> {
        let base = Some(self.view.store);
        match *self.scratch.level_row(base, orig) {
            LevelRow::Succ(a) if a == a2 => Ok(orig),
            _ => Ok(self.scratch.level_succ(base, a2)?),
        }
    }

    /// oracle: `Level.updateMax!Impl` (`Level.lean:575-578`).
    pub(crate) fn update_level_max(&mut self, orig: LevelId, a2: LevelId, b2: LevelId) -> Result<LevelId, MetaError> {
        let base = Some(self.view.store);
        match *self.scratch.level_row(base, orig) {
            LevelRow::Max(a, b) if a == a2 && b == b2 => self.mk_level_max_core(a2, b2, |_| Ok(orig)),
            _ => self.mk_level_max_prime(a2, b2),
        }
    }

    /// oracle: `Level.updateIMax!Impl` (`Level.lean:586-589`).
    pub(crate) fn update_level_imax(&mut self, orig: LevelId, a2: LevelId, b2: LevelId) -> Result<LevelId, MetaError> {
        let base = Some(self.view.store);
        match *self.scratch.level_row(base, orig) {
            LevelRow::IMax(a, b) if a == a2 && b == b2 => self.mk_level_imax_core(a2, b2, |_| Ok(orig)),
            _ => {
                let mk = |c: &mut Self| Ok(c.scratch.level_imax(Some(c.view.store), a2, b2)?);
                self.mk_level_imax_core(a2, b2, mk)
            }
        }
    }
```

Open `Level.lean:542-547` and copy the branch order exactly: `isNeverZero v` → `mkLevelMax'`, `isZero v` → `v`, `isZero u` → `v`, `u == v` → `u`, else. The `if/else` above must mirror it one-to-one. Split the combined branch into two if that reads clearer. `level_is_never_zero` must port `Level.isNeverZero` (`Level.lean`, grep `def isNeverZero`); reuse it if `level.rs` already has one (grep `never_zero`).

- [ ] **Step 4: Implement `level_mvar_to_param`** (`level_params.rs`)

```rust
/// oracle: `UnivMVarParamResult` (`MetavarContext.lean:1478-1482`).
pub struct LevelMVarToParamResult {
    pub expr: ExprId,
    pub new_param_names: Vec<NameId>,
    pub next_param_idx: u64,
}

struct L2P<'a> {
    already_used: &'a [NameId],
    next_idx: u64,
    names: Vec<NameId>,
    cache: std::collections::HashMap<ExprId, ExprId>,
}

impl<'e> MetaCtx<'e> {
    /// oracle: `MetavarContext.levelMVarToParam` (`:1484-1491`) as called
    /// by `Term.levelMVarToParam` (`Elab/Term/TermElabM.lean:1059-1064`):
    /// prefix `u`, `except := fun _ => false`.
    pub fn level_mvar_to_param(
        &mut self,
        e: ExprId,
        already_used: &[NameId],
        next_param_idx: u64,
    ) -> Result<LevelMVarToParamResult, MetaError> {
        let mut st = L2P { already_used, next_idx: next_param_idx, names: Vec::new(), cache: Default::default() };
        let expr = self.l2p_main(&mut st, e)?;
        Ok(LevelMVarToParamResult { expr, new_param_names: st.names, next_param_idx: st.next_idx })
    }

    /// oracle: `mkParamName` (`:1426-1435`).
    fn l2p_param_name(&mut self, st: &mut L2P) -> Result<NameId, MetaError> {
        let base = Some(self.view.store);
        let u_str = self.scratch.intern_str(base, "u")?;
        let u = self.scratch.name_str(base, None, u_str)?;
        loop {
            let n = append_index_after(self.scratch, base, u, st.next_idx)?;
            st.next_idx += 1;
            if !st.already_used.contains(&n) {
                st.names.push(n);
                return Ok(n);
            }
        }
    }

    /// oracle: `visitLevel` (`:1437-1453`).
    fn l2p_level(&mut self, st: &mut L2P, u: LevelId) -> Result<LevelId, MetaError> {
        let base = Some(self.view.store);
        match *self.scratch.level_row(base, u) {
            LevelRow::Succ(v) => {
                let v2 = self.guarded(|c| c.l2p_level(st, v))?;
                self.update_level_succ(u, v2)
            }
            LevelRow::Max(a, b) => {
                let a2 = self.guarded(|c| c.l2p_level(st, a))?;
                let b2 = self.guarded(|c| c.l2p_level(st, b))?;
                self.update_level_max(u, a2, b2)
            }
            LevelRow::IMax(a, b) => {
                let a2 = self.guarded(|c| c.l2p_level(st, a))?;
                let b2 = self.guarded(|c| c.l2p_level(st, b))?;
                self.update_level_imax(u, a2, b2)
            }
            LevelRow::Zero | LevelRow::Param(_) => Ok(u),
            LevelRow::MVar(name) => {
                let id = crate::LMVarId(name.ok_or_else(|| MetaError::MVar("anonymous level mvar".into()))?);
                match self.mctx.level_assignment(id) {
                    Some(v) => self.guarded(|c| c.l2p_level(st, v)),
                    None => {
                        let p = self.l2p_param_name(st)?;
                        let p = self.scratch.level_param(base, Some(p))?;
                        self.mctx.assign_level(id, p)?;
                        Ok(p)
                    }
                }
            }
        }
    }

    /// oracle: `main` + `visitApp` (`:1455-1476`).
    fn l2p_main(&mut self, st: &mut L2P, e: ExprId) -> Result<ExprId, MetaError> {
        let d = self.data(e);
        if !d.has_expr_mvar() && !d.has_level_mvar() {
            return Ok(e);
        }
        if let Some(&r) = st.cache.get(&e) {
            return Ok(r);
        }
        self.step()?;
        let base = Some(self.view.store);
        let r = match self.node(e) {
            Node::Proj { .. } | Node::ProjBig { .. } | Node::Forall { .. } | Node::Lam { .. }
            | Node::LetE { .. } | Node::MData { .. } => {
                // Structural rebuild of each child, via the same per-node
                // `update*` constructors `transform_children` uses
                // (`transform.rs`), each child through `l2p_main`.
                self.l2p_children(st, e)?
            }
            Node::App { .. } | Node::MVar { .. } => {
                let f = self.get_app_fn(e);
                let args = self.get_app_args(e);
                self.l2p_visit_app(st, f, &args)?
            }
            Node::Const { name, levels } => {
                let ls = self.scratch.level_list_at(base, levels).to_vec();
                let mut out = Vec::with_capacity(ls.len());
                for l in ls {
                    out.push(self.l2p_level(st, l)?);
                }
                let ls2 = self.scratch.intern_level_list(base, &out)?;
                self.scratch.expr_const(base, name, ls2)?
            }
            Node::Sort { level } => {
                let l2 = self.l2p_level(st, level)?;
                self.scratch.expr_sort(base, l2)?
            }
            _ => e,
        };
        st.cache.insert(e, r);
        Ok(r)
    }

    /// oracle: `visitApp` (`:1470-1476`): an assigned expr-mvar head is
    /// instantiated and head-beta'd; otherwise rebuild `f args`.
    fn l2p_visit_app(&mut self, st: &mut L2P, f: ExprId, args: &[ExprId]) -> Result<ExprId, MetaError> {
        if let Node::MVar { id: Some(n) } = self.node(f) {
            if let Some(v) = self.mctx.assignment(crate::MVarId(n)) {
                let vf = self.get_app_fn(v);
                let mut vargs = self.get_app_args(v);
                vargs.extend_from_slice(args);
                let r = self.guarded(|c| c.l2p_visit_app(st, vf, &vargs))?;
                return self.head_beta(r);
            }
            let mut out = Vec::with_capacity(args.len());
            for &a in args {
                out.push(self.guarded(|c| c.l2p_main(st, a))?);
            }
            return self.mk_app_spine(f, &out);
        }
        let f2 = self.guarded(|c| c.l2p_main(st, f))?;
        let mut out = Vec::with_capacity(args.len());
        for &a in args {
            out.push(self.guarded(|c| c.l2p_main(st, a))?);
        }
        self.mk_app_spine(f2, &out)
    }
}
```

Write `l2p_children` as a `match` mirroring `transform_children`'s `MData`/`Proj`/`ProjBig` arms (`transform.rs`), plus `Forall`/`Lam`/`LetE` arms. Those arms rebuild with `self.scratch.expr_forall`/`expr_lam`/`expr_let`, using the node's own binder name and binder info and each child mapped through `l2p_main`. **No binder opening:** the oracle's `main` walks loose bvars directly. The `expr_lam`/`expr_forall`/`expr_let` signatures are at `bank/terms.rs:455-534`. `head_beta` is `pub(crate)` (`whnf.rs:1796`).

- [ ] **Step 5: Run the tests and verify they pass**

Run: `cargo test -p leanr_meta level_params level::`
Expected: all PASS, with existing `level.rs` tests unchanged.

- [ ] **Step 6: Mutations**
  1. Don't `assign_level` in the `None` arm → `level_mvar_to_param_names_u_n_and_assigns` (the second `?u` becomes `u_3`).
  2. Ignore `already_used` → `level_mvar_to_param_skips_already_used_names`.
  3. In the `MVar` arm, treat assigned like unassigned → `level_mvar_to_param_follows_level_assignments`.
  4. `update_level_max` returns `self.scratch.level_max(...)` unsimplified → `update_level_max_simplifies_like_mk_level_max_prime`.

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_meta/src/level.rs crates/leanr_meta/src/level_params.rs
git commit -m "leanr_meta: levelMVarToParam + Level.update*! simplifying rebuilds"
```

---

### Task 4: `getMaxHeight`

**Files:**
- Create: `crates/leanr_meta/src/max_height.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (`mod max_height;`)

**Interfaces:**
- Consumes: `EnvView::get` (`tc.rs:296`), `ConstantInfo::Defn`, `ReducibilityHints::Regular`.
- Produces: `impl MetaCtx { pub fn get_max_height(&mut self, e: ExprId) -> Result<u32, MetaError> }`.

The oracle (`Lean/Environment.lean:2890-2901`) runs `e.foldConsts 0` and, for each constant that resolves to a definition with `.regular h` hints, takes the max. `defHeightOverrideExt` is a non-persistent extension that only structural recursion writes, so it is empty in M4c-1; that is a named seam in the doc comment. A name that is not in the environment contributes nothing, and that includes a pending aux lemma, which is a theorem anyway.

- [ ] **Step 1: Write the failing test** (`max_height.rs` tests module; Meta0 heights pinned above)

```rust
use crate::test_support::{app, c, with_meta0_ctx};

#[test]
fn max_height_takes_the_max_regular_hint_and_ignores_abbrev_and_theorems() {
    with_meta0_ctx(|ctx| {
        let id = c(ctx, "id"); // regular 1
        let sunfold = c(ctx, "count._sunfold"); // regular 2
        let ndrec = c(ctx, "Eq.ndrec"); // abbrev
        let thm = c(ctx, "twoZeroEqA"); // theorem
        let ctor = c(ctx, "N.zero"); // constructor
        assert_eq!(ctx.get_max_height(id).unwrap(), 1);
        let e = app(ctx, sunfold, id);
        assert_eq!(ctx.get_max_height(e).unwrap(), 2);
        let e = app(ctx, id, sunfold);
        assert_eq!(ctx.get_max_height(e).unwrap(), 2, "order-independent max");
        let e = app(ctx, ndrec, thm);
        let e = app(ctx, e, ctor);
        assert_eq!(ctx.get_max_height(e).unwrap(), 0);
    });
}
```

- [ ] **Step 2: Run the test and verify it fails**

Run: `cargo test -p leanr_meta max_height`
Expected: compile error.

- [ ] **Step 3: Implement**

```rust
//! oracle: `getMaxHeight` (`Lean/Environment.lean:2890-2901`). Seam:
//! `defHeightOverrideExt` (`:2880-2888`) is not modelled — only
//! structural recursion writes it, which M4c-1 does not elaborate.

use std::collections::HashSet;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::{ConstantInfo, ReducibilityHints};

use crate::{MetaCtx, MetaError};

impl<'e> MetaCtx<'e> {
    /// oracle: `getMaxHeight` — `foldConsts` visits every distinct
    /// subterm once; each `.const` resolving to a definition with
    /// `.regular h` hints raises the max.
    pub fn get_max_height(&mut self, e: ExprId) -> Result<u32, MetaError> {
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut stack = vec![e];
        let mut max = 0u32;
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            self.step()?;
            match self.node(x) {
                Node::Const { name: Some(n), .. } => {
                    if let Some(ConstantInfo::Defn(v)) = self.view.get(n) {
                        if let ReducibilityHints::Regular(h) = v.hints {
                            max = max.max(h);
                        }
                    }
                }
                Node::App { f, a } => stack.extend([f, a]),
                Node::Lam { binder_type, body, .. } | Node::Forall { binder_type, body, .. } => {
                    stack.extend([binder_type, body])
                }
                Node::LetE { ty, value, body, .. } => stack.extend([ty, value, body]),
                Node::MData { expr, .. } => stack.push(expr),
                Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => stack.push(structure),
                _ => {}
            }
        }
        Ok(max)
    }
}
```

Field names follow Task 2's `Node` check.

- [ ] **Step 4: Run the test and verify it passes**

Run: `cargo test -p leanr_meta max_height`
Expected: PASS.

- [ ] **Step 5: Mutations**
  1. `max = h` (last wins) → the `app(id, sunfold)`/`app(sunfold, id)` pair: one of them fails.
  2. Also count `ReducibilityHints::Abbrev` as height 1 → the `0` assert fails.
  3. Don't descend into `App` → the `2` assert fails.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_meta/src/max_height.rs crates/leanr_meta/src/lib.rs
git commit -m "leanr_meta: getMaxHeight"
```

---

### Task 5: `Core.betaReduce` and `zetaReduce`

**Files:**
- Modify: `crates/leanr_meta/src/transform.rs`

**Interfaces:**
- Consumes: `transform_visit` (existing), `head_beta`, `beta_rev` (`whnf.rs:1750`), `instantiate_mvars`, `local_entry`, `lctx.get`.
- Produces:
  - `pub fn beta_reduce(&mut self, e: ExprId) -> Result<ExprId, MetaError>`, which ports `Core.betaReduce` (`Transform.lean:75-76`) over `Core.transform` (`:43-72`). It never opens binders, and terms may contain loose bvars.
  - `pub fn zeta_reduce(&mut self, e: ExprId) -> Result<ExprId, MetaError>`, which ports `Meta.zetaReduce` at its defaults (`zetaDelta := true`, `zetaHave := true`, `beta := true`; `Transform.lean:198-209`).
  - `pub(crate) fn transform_with(&mut self, input: ExprId, pre: Pre<'_, 'e>, used_let_only: bool) -> Result<ExprId, MetaError>`. `transform` and `transform_used_let_only` become thin calls to it.

The oracle's `zetaReduce` unfolds an fvar head's value when `decl.value? (allowNondep := zetaHave && decl.index ≥ n)` returns one, where `n` is the number of local declarations when `zetaReduce` started. In other words:
- a `let` always unfolds (`zetaDelta := true`);
- a `have` (nondep) unfolds only if `transform` itself opened it.

It returns `.visit ((← instantiateMVars value).beta args)`.

- [ ] **Step 1: Write the failing tests** (`transform.rs` tests module, or create one)

```rust
use crate::test_support::{app, bvar, c, fresh_fvar, with_meta0_ctx};
use leanr_kernel::BinderInfo;

/// `fun (y : N) => (fun (x : N) => N.succ x) y` ↦ `fun y => N.succ y`, under
/// a binder: `Core.transform` does not open it, the body has a loose bvar.
#[test]
fn beta_reduce_reduces_under_binders_without_opening_them() {
    with_meta0_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let n = c(ctx, "N");
        let succ = c(ctx, "N.succ");
        let b0 = bvar(ctx, 0);
        let sx = app(ctx, succ, b0);
        let lam_x = ctx.scratch.expr_lam(base, None, n, sx, BinderInfo::Default).unwrap();
        let redex = app(ctx, lam_x, b0);
        let e = ctx.scratch.expr_lam(base, None, n, redex, BinderInfo::Default).unwrap();
        let want = ctx.scratch.expr_lam(base, None, n, sx, BinderInfo::Default).unwrap();
        assert_eq!(ctx.beta_reduce(e).unwrap(), want);
    });
}

/// A `let` in the ambient context unfolds; a pre-existing `have` does not.
#[test]
fn zeta_reduce_unfolds_ambient_lets_but_not_ambient_haves() {
    with_meta0_ctx(|ctx| {
        let n = c(ctx, "N");
        let zero = c(ctx, "N.zero");
        let succ = c(ctx, "N.succ");
        let a = ctx.push_let_decl(None, n, zero).unwrap(); // let a := N.zero
        let sa = app(ctx, succ, a);
        let want = app(ctx, succ, zero);
        assert_eq!(ctx.zeta_reduce(sa).unwrap(), want);
        let h = ctx.push_have_decl(None, n, zero).unwrap(); // have h := N.zero
        let sh = app(ctx, succ, h);
        assert_eq!(ctx.zeta_reduce(sh).unwrap(), sh);
    });
}

/// An inner `let b := N.zero; N.succ b` is opened by `transform`, unfolded,
/// and (usedLetOnly) dropped: result `N.succ N.zero`.
#[test]
fn zeta_reduce_inlines_and_drops_an_inner_let() {
    with_meta0_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let n = c(ctx, "N");
        let zero = c(ctx, "N.zero");
        let succ = c(ctx, "N.succ");
        let b0 = bvar(ctx, 0);
        let body = app(ctx, succ, b0);
        let e = ctx.scratch.expr_let(base, None, n, zero, body, false).unwrap();
        let want = app(ctx, succ, zero);
        assert_eq!(ctx.zeta_reduce(e).unwrap(), want);
    });
}
```

Two adaptations:
- Use the real `push_let_decl` signature (`metactx.rs:947`) and the real API for a nondep `have` push. Grep `nondep` in `metactx.rs`: `push_let_decl_with_kind` or a `have` variant. If no have-push exists, drop the `have` half and note it in the commit.
- `expr_let`'s argument order and `nondep` flag are at `bank/terms.rs:508`.

- [ ] **Step 2: Run the tests and verify they fail**

Run: `cargo test -p leanr_meta beta_reduce zeta_reduce`
Expected: compile errors.

- [ ] **Step 3: Implement**

1. Refactor: add `transform_with(input, pre, used_let_only)`, which builds `TransformSt { cache, used_let_only }` and calls `transform_visit`. Make `transform` and `transform_used_let_only` call it. This is behavior-neutral, so the existing `coe.rs` tests stay green.
2. Write `core_transform_visit(&mut self, e, pre: &mut dyn FnMut(&mut Self, ExprId) -> Result<TransformStep, MetaError>, cache: &mut HashMap<ExprId, ExprId>)`. It follows `Core.transform` (`Transform.lean:43-72`) with the default `post`:
   - check `cache`, then `step()`, then run `pre`;
   - `Done` → the term as given; `Visit(e2)` → recurse on `e2`;
   - `Continue(e2)` → rebuild the children **without opening binders**:
     - `Forall`/`Lam`: `binder_type`, `body`
     - `LetE`: `ty`, `value`, `body`, keeping `nondep`
     - `App`: the spine, `f` then each arg, rebuilt with `expr_app`
     - `MData`, `Proj`, `ProjBig`
     - anything else: unchanged
   - insert into `cache`.
3. `beta_reduce`:

```rust
    /// oracle: `Core.betaReduce` (`Transform.lean:75-76`):
    /// `transform e (pre := fun e => if e.isHeadBetaTarget then .visit e.headBeta else .continue)`.
    /// `isHeadBetaTarget` here models only a `Lam` head (the same
    /// narrowing `head_beta` documents, `whnf.rs:1790`).
    pub fn beta_reduce(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let mut cache = HashMap::new();
        let mut pre = |c: &mut MetaCtx<'e>, x: ExprId| -> Result<TransformStep, MetaError> {
            let is_target = matches!(c.node(x), Node::App { .. })
                && matches!(c.node(c.get_app_fn(x)), Node::Lam { .. });
            Ok(if is_target { TransformStep::Visit(c.head_beta(x)?) } else { TransformStep::Continue(None) })
        };
        self.core_transform_visit(e, &mut pre, &mut cache)
    }
```

4. `zeta_reduce`:

```rust
    /// oracle: `Meta.zetaReduce` (`Transform.lean:198-209`) at its
    /// defaults (`zetaDelta := true`, `zetaHave := true`, `beta := true`).
    /// `n` = local decls before the call; a decl at index ≥ n was opened
    /// by this `transform`, so its value is visible even if nondep.
    pub fn zeta_reduce(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let n = self.local_names.len();
        let mut pre = move |c: &mut MetaCtx<'e>, x: ExprId| -> Result<TransformStep, MetaError> {
            let f = c.get_app_fn(x);
            let Node::FVar { id: Some(fid) } = c.node(f) else {
                return Ok(TransformStep::Continue(None));
            };
            let Some(pos) = c.local_names.iter().position(|en| en.id == fid) else {
                return Ok(TransformStep::Continue(None));
            };
            let nondep = c.local_names[pos].nondep;
            let value = c.lctx.get(fid).and_then(|d| d.value);
            let value = match value {
                Some(v) if !nondep || pos >= n => v,
                _ => return Ok(TransformStep::Continue(None)),
            };
            let v = c.instantiate_mvars(value)?;
            let args = c.get_app_args(x);
            Ok(TransformStep::Visit(c.beta_rev(v, &args)?))
        };
        self.transform_with(e, &mut pre, true)
    }
```

Before relying on `beta_rev`, read `whnf.rs:1750` to confirm it takes args in application order, as `head_beta`'s call implies. If it takes them reversed, reverse `args`. The oracle's `Expr.beta f args` uses application order.

- [ ] **Step 4: Run the tests and verify they pass**

Run: `cargo test -p leanr_meta transform:: beta_reduce zeta_reduce coe::`
Expected: all PASS (`coe::` guards the refactor).

- [ ] **Step 5: Mutations**
  1. In `beta_reduce`'s pre, return `Continue` always → `beta_reduce_reduces_under_binders_without_opening_them`.
  2. In `zeta_reduce`, drop the `pos >= n` condition (never unfold nondep) → `zeta_reduce_inlines_and_drops_an_inner_let` still passes (the inner decl is a `let`). So also run: drop `!nondep ||` (unfold every have) → `zeta_reduce_unfolds_ambient_lets_but_not_ambient_haves` fails.
  3. `transform_with(e, &mut pre, false)` → `zeta_reduce_inlines_and_drops_an_inner_let` (the unused `let` stays).

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_meta/src/transform.rs
git commit -m "leanr_meta: Core.betaReduce + zetaReduce (transform_with)"
```

---

### Task 6: `Closure.mkValueTypeClosure` (`zetaDelta := true`)

**Files:**
- Create: `crates/leanr_meta/src/closure.rs`
- Modify: `crates/leanr_kernel/src/local_ctx.rs:80` (widen `fresh_fvar_id` to `pub`, add a one-line doc that the Closure port needs undeclared fvars), `crates/leanr_kernel/src/lib.rs` (`pub use` it if `local_ctx` is private), `crates/leanr_meta/src/lib.rs` (`mod closure;` + `pub use closure::ClosureResult;`)

**Interfaces:**
- Consumes: Task 3's `update_level_*`; `abstract_fvars` (`subst.rs:752`); `instantiate_mvars`; `fvar_gen`; `local_names`; `lctx.get`.
- Produces:

```rust
pub struct ClosureResult {
    pub level_params: Vec<NameId>,
    pub ty: ExprId,
    pub value: ExprId,
    pub level_args: Vec<LevelId>,
    pub expr_args: Vec<ExprId>,
}
impl MetaCtx {
    pub fn mk_value_type_closure(&mut self, ty: ExprId, value: ExprId) -> Result<ClosureResult, MetaError>;
}
```

This ports `Lean/Meta/Closure.lean:111-450`, with `zetaDelta := true` hard-wired (the only value `abstractProof` passes, `AbstractNestedProofs.lean:31`). Consequences:

- `preprocess` (`:155-162`) is just `instantiateMVars`: `check` runs only when `!zetaDelta`.
- **The `fvar` arm** (`:221-228`): an fvar whose `getValue?` returns a value (a `let`, not a nondep `have`) is replaced by `collect (preprocess value)`. Any other fvar gets a fresh undeclared fvar, recorded in `toProcess`.
- **Dependent lets never reach `process`:** `zetaDeltaFVarIds` stays empty because no `check` runs. So `process`'s `ldecl` arm always takes the "non-dependent" branch, and `newLetDecls` is always empty.
- **The `mvar` arm (`:186-219`) is a seam.** P2 calls this only after `ensureNoUnassignedMVars` and `instantiateMVars`, so no unassigned mvar can reach it. That means `sortDecls` (`:357-405`) receives no mvar decls and is the identity. The arm returns `MetaError::Unsupported("closure over a metavariable — M4c-1 seam (Closure.lean:186)")`.
- **Levels** (`:135-149`): every `param` (and every `mvar`) becomes a fresh `u_N` via `mkNewLevelParam` (`:126-130`). `level_args` collects the originals. Visits are memoized, and `succ`/`max`/`imax` rebuild through Task 3's `update_level_*`.
- **The expr walk** (`:164-230`) never opens binders. The visit cache keys on the expr, so the same fvar maps to the same new fvar. Terms with no level param, fvar or mvar are skipped (`visitExpr`, `:110-120`).
- **`pickNextToProcess?`** (`:236-257`) takes the element with the **greatest** lctx index. Here "index" is the position in `local_names`.
- **`process`** (`:270-300`): for a cdecl, it runs `pushLocalDecl(newFVarId, userName, type, bi)` (with the type collected first) and pushes the original fvar onto `exprFVarArgs`. A nondep ldecl is handled the same way, but with `.default` binder info.
- **Result** (`:407-424`): reverse `newLocalDecls` and `exprFVarArgs`, then `type := mkForall decls type` and `value := mkLambda decls value`. `mkBinding` (`:302-322`) abstracts **syntactically** with `abstract_fvars` over the new fvars: decl `i`'s type is abstracted over `xs[..i]`, the body over all `xs`.

- [ ] **Step 1: Write the failing tests** (`closure.rs` tests module, over Meta0)

```rust
use crate::test_support::{app, bvar, c, cu, lit_level, lparam, with_meta0_ctx};
use leanr_kernel::BinderInfo;

/// probe `foo1._proof_1`: closing `@rfl.{1} N (N.succ n)` over `n : N`.
#[test]
fn closure_abstracts_free_fvars_in_lctx_order() {
    with_meta0_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let one = lit_level(ctx, 1);
        let n_ty = c(ctx, "N");
        let succ = c(ctx, "N.succ");
        let n_name = { let s = ctx.scratch.intern_str(base, "n").unwrap(); ctx.scratch.name_str(base, None, s).unwrap() };
        let n = ctx.push_local_decl(Some(n_name), n_ty, BinderInfo::Default).unwrap();
        let sn = app(ctx, succ, n);
        let eq = cu(ctx, "Eq", &[one]);
        let rfl = cu(ctx, "rfl", &[one]);
        let ty = ctx.mk_app_spine(eq, &[n_ty, sn, sn]).unwrap();
        let val = ctx.mk_app_spine(rfl, &[n_ty, sn]).unwrap();
        let r = ctx.mk_value_type_closure(ty, val).unwrap();
        // ∀ (n : N), @Eq.{1} N (N.succ #0) (N.succ #0)
        let b0 = bvar(ctx, 0);
        let s0 = app(ctx, succ, b0);
        let ty_body = ctx.mk_app_spine(eq, &[n_ty, s0, s0]).unwrap();
        let want_ty = ctx.scratch.expr_forall(base, Some(n_name), n_ty, ty_body, BinderInfo::Default).unwrap();
        let val_body = ctx.mk_app_spine(rfl, &[n_ty, s0]).unwrap();
        let want_val = ctx.scratch.expr_lam(base, Some(n_name), n_ty, val_body, BinderInfo::Default).unwrap();
        assert_eq!(r.ty, want_ty);
        assert_eq!(r.value, want_val);
        assert_eq!(r.expr_args, vec![n]);
        assert!(r.level_params.is_empty() && r.level_args.is_empty());
    });
}

/// Review Focus 3 / probe `foo2._proof_1.{u_1}`: `u` becomes `u_1`, the
/// level arg is the original `u`; `α` is pulled in through `a`'s type.
#[test]
fn closure_renames_level_params_to_u_n() {
    with_meta0_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let u = lparam(ctx, "u");
        let sort_u = ctx.scratch.expr_sort(base, u).unwrap();
        let alpha = ctx.push_local_decl(None, sort_u, BinderInfo::Default).unwrap();
        let a = ctx.push_local_decl(None, alpha, BinderInfo::Default).unwrap();
        let id_u = cu(ctx, "id", &[u]);
        let ida = ctx.mk_app_spine(id_u, &[alpha, a]).unwrap();
        let eq_u = cu(ctx, "Eq", &[u]);
        let rfl_u = cu(ctx, "rfl", &[u]);
        let ty = ctx.mk_app_spine(eq_u, &[alpha, ida, ida]).unwrap();
        let val = ctx.mk_app_spine(rfl_u, &[alpha, ida]).unwrap();
        let r = ctx.mk_value_type_closure(ty, val).unwrap();
        assert_eq!(r.level_args, vec![u]);
        let u_1 = { let s = ctx.scratch.intern_str(base, "u_1").unwrap(); ctx.scratch.name_str(base, None, s).unwrap() };
        assert_eq!(r.level_params, vec![u_1]);
        assert_eq!(r.expr_args, vec![alpha, a], "α first: lower lctx index");
        // ∀ (α : Sort u_1) (a : α), @Eq.{u_1} α (@id.{u_1} α a) (@id.{u_1} α a)
        let p1 = lparam(ctx, "u_1");
        let sort_p1 = ctx.scratch.expr_sort(base, p1).unwrap();
        let (b0, b1) = (bvar(ctx, 0), bvar(ctx, 1));
        let id_p1 = cu(ctx, "id", &[p1]);
        let eq_p1 = cu(ctx, "Eq", &[p1]);
        let id_ba = ctx.mk_app_spine(id_p1, &[b1, b0]).unwrap();
        let body = ctx.mk_app_spine(eq_p1, &[b1, id_ba, id_ba]).unwrap();
        let inner = ctx.scratch.expr_forall(base, None, b0, body, BinderInfo::Default).unwrap();
        let want_ty = ctx.scratch.expr_forall(base, None, sort_p1, inner, BinderInfo::Default).unwrap();
        assert_eq!(r.ty, want_ty);
    });
}

/// zetaDelta: a `let m := N.succ n` occurring in the term is inlined; the
/// closure abstracts only `n`.
#[test]
fn closure_zeta_expands_let_fvars() {
    with_meta0_ctx(|ctx| {
        let n_ty = c(ctx, "N");
        let succ = c(ctx, "N.succ");
        let n = ctx.push_local_decl(None, n_ty, BinderInfo::Default).unwrap();
        let sn = app(ctx, succ, n);
        let m = ctx.push_let_decl(None, n_ty, sn).unwrap();
        let sm = app(ctx, succ, m);
        let r = ctx.mk_value_type_closure(n_ty, sm).unwrap();
        assert_eq!(r.expr_args, vec![n]);
        let base = Some(ctx.view.store);
        let b0 = bvar(ctx, 0);
        let s0 = app(ctx, succ, b0);
        let ss0 = app(ctx, succ, s0);
        let want = ctx.scratch.expr_lam(base, None, n_ty, ss0, BinderInfo::Default).unwrap();
        assert_eq!(r.value, want);
    });
}

#[test]
fn closure_over_an_unassigned_mvar_is_a_named_seam() {
    with_meta0_ctx(|ctx| {
        let n_ty = c(ctx, "N");
        let (m, _) = crate::test_support::fresh_mvar(ctx, n_ty);
        let err = ctx.mk_value_type_closure(n_ty, m).unwrap_err();
        assert!(matches!(err, MetaError::Unsupported(ref s) if s.contains("M4c-1 seam")), "{err:?}");
    });
}
```

The binder names in `want_ty` must be the original user names: `pushLocalDecl` copies `userName` from the original decl. Pass the same `name` you pushed with (`None` above, `Some(n_name)` in the first test).

- [ ] **Step 2: Run the tests and verify they fail**

Run: `cargo test -p leanr_meta closure`
Expected: compile error.

- [ ] **Step 3: Implement `closure.rs`**

The state struct mirrors `Closure.State` (`:91-106`):

```rust
struct ClosureSt {
    visited_level: HashMap<LevelId, LevelId>,
    visited_expr: HashMap<ExprId, ExprId>,
    level_params: Vec<NameId>,
    next_level_idx: u64,
    level_args: Vec<LevelId>,
    /// (new fvar, user name, collected type, binder info) — `newLocalDecls`.
    new_local_decls: Vec<(ExprId, Option<NameId>, ExprId, BinderInfo)>,
    next_expr_idx: u64,
    expr_fvar_args: Vec<ExprId>,
    /// (original fvar id, new fvar) — `toProcess`.
    to_process: Vec<(NameId, ExprId)>,
}
```

Write these methods, each with an `oracle:` doc citing the line ranges above:
- `closure_level`: `visitLevel` + `collectLevelAux`. If the level has neither param nor mvar (`level_flags & 0b11 == 0`), return it unchanged. Otherwise memoize. `Param`/`MVar` → `mkNewLevelParam`: the name is `append_index_after(u, next_level_idx)`; push it to `level_params`; push the **original** level to `level_args`; return `level_param(new)`. `Succ`/`Max`/`IMax` rebuild through `update_level_*`.
- `closure_expr`: `visitExpr` + `collectExprAux`. Return early if `!has_level_param && !has_fvar && !has_expr_mvar && !has_level_mvar`. Memoize. Then dispatch:
  - `Proj`, `Forall`, `Lam`, `LetE`, `App` (binary, `f` then `a`) and `MData`: rebuild the node over its collected children with `scratch.expr_*`, keeping binder names and info.
  - `Sort`/`Const`: map their levels through `closure_level`.
  - `MVar`: the seam error.
  - `FVar`: if `local_entry(fid)` is not nondep and `lctx.get(fid).value` is `Some(v)`, then `closure_expr(instantiate_mvars(v))`. Otherwise mint `new = fresh fvar`, push `(fid, new)` to `to_process`, and return `new`.
- `closure_fresh_fvar`: `leanr_kernel::fresh_fvar_id(&mut self.fvar_gen, self.scratch, base)`, then `expr_fvar`.
- `closure_pick_next`: pop the back, then scan the rest with `pickNextToProcessAux`'s swap semantics (`:236-248`). Keep the element whose `local_names` position is greatest, and put the displaced one back where the winner was.
- `closure_process`: loop until `to_process` is empty. Pick an element. Read its decl through `lctx.get(fid)`: type, `binder_name`, `binder_info`; a nondep ldecl uses `BinderInfo::Default`. Collect the type (`collectExpr` = `instantiate_mvars` + `closure_expr`), push to `new_local_decls`, and push the original fvar expr (`local_entry(fid).fvar`) to `expr_fvar_args`.
- `mk_value_type_closure`:
  - collect `ty` and then `value` (`mkValueTypeClosureAux`, `:332-337`), then `closure_process`;
  - reverse both vectors;
  - for each decl `i`, abstract its type over `xs[..i]` with `abstract_fvars`;
  - abstract each body over all `xs`;
  - fold right-to-left into `expr_forall` (for the type) or `expr_lam` (for the value), with the decl's name and binder info;
  - `debug_assert!(!has_fvar(value))` (`:419`).

- [ ] **Step 4: Run the tests and verify they pass**

Run: `cargo test -p leanr_meta closure && cargo test -p leanr_kernel`
Expected: all PASS.

- [ ] **Step 5: Mutations**
  1. In `closure_level`, return a `Param` unchanged (don't rename) → `closure_renames_level_params_to_u_n`.
  2. In `closure_pick_next`, pick the smallest index → `closure_renames_level_params_to_u_n` (`expr_args` order).
  3. In the `FVar` arm, ignore let values → `closure_zeta_expands_let_fvars`.
  4. Don't reverse `new_local_decls` → `closure_renames_level_params_to_u_n`.
  5. Abstract decl `i`'s type over all `xs` instead of `xs[..i]` → it should change nothing observable in tests 1-3 (a type can't mention later fvars). Record it as an EQUIVALENT mutant in the commit body. Don't add a test for it.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_meta/src/closure.rs crates/leanr_meta/src/lib.rs crates/leanr_kernel/src/local_ctx.rs crates/leanr_kernel/src/lib.rs
git commit -m "leanr_meta: Closure.mkValueTypeClosure (zetaDelta := true)"
```

---

### Task 7: `abstractNestedProofs` and the aux-lemma accumulator

**Files:**
- Create: `crates/leanr_meta/src/abstract_proofs.rs`
- Modify: `crates/leanr_meta/src/discr_path.rs:577` (move `is_proof` into `lazy_delta.rs` next to `is_prop` as `pub(crate) fn is_proof`; `discr_path` calls it)
- Modify: `crates/leanr_meta/src/lib.rs` (`mod abstract_proofs;` + `pub use abstract_proofs::AuxLemmas;`)

**Interfaces:**
- Consumes: Task 5 (`beta_reduce`, `zeta_reduce`), Task 6 (`mk_value_type_closure`), Task 2 (`append_index_after`), `infer_type`, `is_prop`, `mk_lambda`, `mk_forall`, `push_local_decl`, `instantiate_rev`.
- Produces:

```rust
/// Aux theorems minted while abstracting one declaration's value, in
/// creation order — the caller commits them, in order, BEFORE the main
/// declaration (`Environment::add_decl_in`).
pub struct AuxLemmas { /* decl_name, next_idx, cache, pending */ }
impl AuxLemmas {
    pub fn new(decl_name: NameId) -> Self;
    pub fn pending(&self) -> &[leanr_kernel::Declaration];
    pub fn into_pending(self) -> Vec<leanr_kernel::Declaration>;
}
impl MetaCtx {
    /// oracle: `Meta.abstractNestedProofs` (`AbstractNestedProofs.lean:111-117`), `cache := true`.
    pub fn abstract_nested_proofs(&mut self, aux: &mut AuxLemmas, e: ExprId) -> Result<ExprId, MetaError>;
}
```

The oracle code being ported:
- `Meta.abstractNestedProofs` (`:111-117`): if `isProof e`, return `e`; otherwise run `visit` with a fresh `ExprStructEq` cache.
- `visit` (`:66-107`):
  - **Atomic** (`isAtomic`: const, sort, bvar, lit, mvar, fvar): returned unchanged.
  - **The cache** applies to everything else.
  - **Non-trivial proof** without sorry → `abstractProof e cache visit`.
  - **`lam` / `letE`** → `lambdaLetTelescope`, then `visitBinders`, then `mkLambdaFVars (usedLetOnly := false) (generalizeNondepLet := false)`. In leanr, a `LetE` anywhere in the walk is a **seam**: `MetaError::Unsupported("abstractNestedProofs under let — letToHave follow-up (M4c-1 seam)")`. P2 rejects any `let` first (spec decision 5), so this arm is unreachable from the elaborator.
  - **`forallE`** → `forallTelescope`, then `visitBinders`, then `mkForallFVars`.
  - **`mdata` / `proj`** → update the child.
  - **`app`** → `withApp`, visiting `f` and each arg.
  - **Anything else** → `e`.
- `visitBinders` (`:72-84`) visits each binder's TYPE (and a let's value) in the opened context. leanr opens binder by binder, as `transform_lambda` does: instantiate the domain with the fvars so far, visit it, then push the local decl **with the visited type**. This is equivalent, because a binder type cannot mention later binders, and the shared cache makes the visits identical.
- `isNonTrivialProof` (`:40-62`):
  - `false` if `!isProof e`;
  - `false` if `e` is an app of `Grind.nestedProof` (compare the head const's name with the dotted name `Grind.nestedProof`);
  - otherwise, with `(f, args) := getLambdaBody(e).withApp`, return `!f.isAtomic || (f is a const NOT in the env) || args.any(!isAtomic)`.
  - **In leanr, "in the env" means `view.get(name).is_some() || aux.is_pending(name)`.** The oracle's aux lemmas *are* in the env at that point.
  - `getLambdaBody` strips `lam` only and leaves loose bvars; `withApp` on a term with loose bvars is purely syntactic.
- `abstractProof` (`:19-31`), with `postprocessType := visit`:
  1. `type ← inferType proof`, `betaReduce`, `zetaReduce`, then `visit type`;
  2. `cache := cache && !proof.hasSorry`;
  3. `mkAuxTheorem cache type proof (zetaDelta := true)`.
- `mkAuxTheorem` (`Closure.lean:457-461`): run `mkValueTypeClosure` and `mkAuxLemma result.levelParams result.type result.value`, then return `mkAppN (mkConst name levelArgs) exprArgs`.
- `mkAuxLemma` (`Tactic/AuxLemma.lean:43-81`):
  - **Cache lookup:** the key is `{type, isPrivate := false, defeq := false}`. Elab0 is not a module, so `isPrivate` is always false and the private-retry branch (`:73-76`) never fires. A hit is used only when its level params equal this call's.
  - **Miss:** `mkAuxDeclName (kind := _proof)`. If any constant in `type`/`value` is unsafe, the oracle builds an unsafe opaque `defnDecl`; that is a **seam** here, and it returns `Unsupported`, because `add_decl_in` rejects unsafe `Defn`. Otherwise it builds a `thmDecl {name, levelParams, type, value}` with **no `all` field override**: `TheoremVal.all` defaults to `[name]` (`Declaration.lean`, grep `structure TheoremVal`; confirm the default when you open it). The result is pushed to `pending` and inserted in the cache.
- `mkAuxDeclName` (`CoreM.lean:149-153`) uses `DeclNameGenerator.mkUniqueName` (`:102-125`). The prefix is the declaration name (`withDeclNameForAuxNaming`, `PreDefinition/Basic.lean:125`), and the base is `declName ++ _proof`. Starting from `idx` (initially 1), the candidate is `appendIndexAfter base idx`; while it conflicts (`view.get(candidate).is_some() || pending contains candidate`), `idx += 1`. Return the candidate **without** advancing past it. The next call then conflicts with the now-pending name and moves on, which is what produced `_proof_2` in the oracle.
- `hasSorry`: any `Const` named `sorryAx` in the term (grep `hasSorry` in `Lean/Expr.lean` to confirm it is a const scan, and cite it).

- [ ] **Step 1: Write the failing tests** (`abstract_proofs.rs` tests module, over Meta0)

Shared builder: `pprod_with_proof(ctx, proof_ty, proof) -> (value_body)` builds `@PProd.mk.{1,0} N proof_ty n proof` and similar. Write it once in the tests module:

```rust
use crate::test_support::{app, c, cu, lit_level, render_name, with_meta0_ctx};
use leanr_kernel::{BinderInfo, Declaration};

fn name(ctx: &mut MetaCtx, s: &str) -> NameId {
    let base = Some(ctx.view.store);
    let mut n = None;
    for part in s.split('.') {
        let id = ctx.scratch.intern_str(base, part).unwrap();
        n = Some(ctx.scratch.name_str(base, n, id).unwrap());
    }
    n.unwrap()
}

/// `fun (n : N) => @PProd.mk.{l1,l2} A B a b` with `n` bound; the closure
/// receives the opened `n` and returns (A, B, a, b).
fn lam_n_pprod(
    ctx: &mut MetaCtx,
    levels: (u32, u32),
    parts: impl FnOnce(&mut MetaCtx, ExprId) -> (ExprId, ExprId, ExprId, ExprId),
) -> ExprId {
    let n_ty = c(ctx, "N");
    let n_name = name(ctx, "n");
    let cp = ctx.lctx_checkpoint();
    let n = ctx.push_local_decl(Some(n_name), n_ty, BinderInfo::Default).unwrap();
    let (ta, tb, a, b) = parts(ctx, n);
    let (l1, l2) = (lit_level(ctx, levels.0), lit_level(ctx, levels.1));
    let mk = cu(ctx, "PProd.mk", &[l1, l2]);
    let body = ctx.mk_app_spine(mk, &[ta, tb, a, b]).unwrap();
    let r = ctx.mk_lambda(&[n], body).unwrap();
    ctx.lctx_restore(cp);
    r
}

/// `@Eq.{1} N x x` and `@rfl.{1} N x`.
fn eq_rfl(ctx: &mut MetaCtx, x: ExprId) -> (ExprId, ExprId) {
    let one = lit_level(ctx, 1);
    let n_ty = c(ctx, "N");
    let eq = cu(ctx, "Eq", &[one]);
    let rfl = cu(ctx, "rfl", &[one]);
    (ctx.mk_app_spine(eq, &[n_ty, x, x]).unwrap(), ctx.mk_app_spine(rfl, &[n_ty, x]).unwrap())
}

/// probe foo1: `⟨n, rfl⟩ : PProd N (N.succ n = N.succ n)` →
/// `foo1._proof_1 n`, one pending theorem.
#[test]
fn nested_proof_becomes_proof_1_applied_to_its_closure() {
    with_meta0_ctx(|ctx| {
        let foo1 = name(ctx, "foo1");
        let succ = c(ctx, "N.succ");
        let n_ty = c(ctx, "N");
        let e = lam_n_pprod(ctx, (1, 0), |ctx, n| {
            let sn = app(ctx, succ, n);
            let (ty, pf) = eq_rfl(ctx, sn);
            (n_ty, ty, n, pf)
        });
        let mut aux = AuxLemmas::new(foo1);
        let out = ctx.abstract_nested_proofs(&mut aux, e).unwrap();
        assert_eq!(aux.pending().len(), 1);
        let Declaration::Thm(t) = &aux.pending()[0] else { panic!("thmDecl expected") };
        assert_eq!(render_name(ctx, t.val.name), "foo1._proof_1");
        assert!(t.val.level_params.is_empty());
        // out = fun n => @PProd.mk.{1,0} N (Eq ..) n (foo1._proof_1 n)
        let p1 = cu(ctx, "foo1._proof_1", &[]);
        let want = lam_n_pprod(ctx, (1, 0), |ctx, n| {
            let sn = app(ctx, succ, n);
            let (ty, _) = eq_rfl(ctx, sn);
            let call = app(ctx, p1, n);
            (n_ty, ty, n, call)
        });
        assert_eq!(out, want);
    });
}

/// Review Focus 4 / probe foo5: `@rfl.{1} N n` has atomic args → kept.
#[test]
fn atomic_arg_proof_is_not_abstracted() {
    with_meta0_ctx(|ctx| {
        let foo5 = name(ctx, "foo5");
        let n_ty = c(ctx, "N");
        let e = lam_n_pprod(ctx, (1, 0), |ctx, n| {
            let (ty, pf) = eq_rfl(ctx, n);
            (n_ty, ty, n, pf)
        });
        let mut aux = AuxLemmas::new(foo5);
        assert_eq!(ctx.abstract_nested_proofs(&mut aux, e).unwrap(), e);
        assert!(aux.pending().is_empty());
    });
}

/// Two identical proofs in one declaration share one aux (cache).
#[test]
fn identical_proofs_share_one_aux() {
    with_meta0_ctx(|ctx| {
        let foo3 = name(ctx, "foo3");
        let succ = c(ctx, "N.succ");
        let e = lam_n_pprod(ctx, (0, 0), |ctx, n| {
            let sn = app(ctx, succ, n);
            let (ty, pf) = eq_rfl(ctx, sn);
            (ty, ty, pf, pf)
        });
        let mut aux = AuxLemmas::new(foo3);
        ctx.abstract_nested_proofs(&mut aux, e).unwrap();
        assert_eq!(aux.pending().len(), 1);
    });
}

/// Review Focus 2: two DISTINCT proofs → `_proof_1`, `_proof_2`, though
/// neither is in the env yet.
#[test]
fn distinct_proofs_get_distinct_indices() {
    with_meta0_ctx(|ctx| {
        let foo4 = name(ctx, "foo4");
        let succ = c(ctx, "N.succ");
        let e = lam_n_pprod(ctx, (0, 0), |ctx, n| {
            let sn = app(ctx, succ, n);
            let ssn = app(ctx, succ, sn);
            let (t1, p1) = eq_rfl(ctx, sn);
            let (t2, p2) = eq_rfl(ctx, ssn);
            (t1, t2, p1, p2)
        });
        let mut aux = AuxLemmas::new(foo4);
        ctx.abstract_nested_proofs(&mut aux, e).unwrap();
        let names: Vec<String> = aux
            .pending()
            .iter()
            .map(|d| match d { Declaration::Thm(t) => render_name(ctx, t.val.name), _ => panic!() })
            .collect();
        assert_eq!(names, vec!["foo4._proof_1", "foo4._proof_2"]);
    });
}

/// A value that is itself a proof is returned unchanged
/// (`AbstractNestedProofs.lean:112-114`).
#[test]
fn a_proof_value_is_not_abstracted_at_the_root() {
    with_meta0_ctx(|ctx| {
        let succ = c(ctx, "N.succ");
        let zero = c(ctx, "N.zero");
        let sz = app(ctx, succ, zero);
        let (_, pf) = eq_rfl(ctx, sz);
        let thm = name(ctx, "thm");
        let mut aux = AuxLemmas::new(thm);
        assert_eq!(ctx.abstract_nested_proofs(&mut aux, pf).unwrap(), pf);
        assert!(aux.pending().is_empty());
    });
}
```

`c(ctx, "N.succ")` fills levels with zero, and `N` has no level params, so that is correct. Universe-polymorphic coverage (`foo2`) lives in Task 6's closure test and in Task 8's integration test.

- [ ] **Step 2: Run the tests and verify they fail**

Run: `cargo test -p leanr_meta abstract_proofs`
Expected: compile error.

- [ ] **Step 3: Implement `abstract_proofs.rs`**, following the oracle notes above

The struct:

```rust
pub struct AuxLemmas {
    decl_name: NameId,
    /// `DeclNameGenerator.idx` for the `_proof` infix (starts at 1).
    next_idx: u64,
    /// `auxLemmasExt` key `type` → (name, levelParams). Per declaration
    /// in M4c-1 (see plan Amendment 1, item 2).
    cache: HashMap<ExprId, (NameId, Vec<NameId>)>,
    pending: Vec<Declaration>,
}
```

Other parts:
- `AuxLemmas::is_pending(&self, n: NameId) -> bool` scans `pending` names.
- `visit` uses a `HashMap<ExprId, ExprId>` cache that lives for one `abstract_nested_proofs` call. It is threaded through `abstractProof`'s `postprocessType`, which is the same `visit` with the same cache, as in the oracle's shared `MonadCacheT`.
- Binders follow the per-binder open/visit/push loop described above, under `lctx_checkpoint`/`lctx_restore`, like `transform_children` does.
- Rebuild with `mk_lambda`/`mk_forall`. For the `forall` case, the oracle's `mkForallFVars` uses the defaults, and so does `mk_forall`. For lambdas, `generalizeNondepLet := false` only matters for a `have` in the telescope, which cannot occur because `letE` is a seam. Note this in a comment.

- [ ] **Step 4: Run the tests and verify they pass**

Run: `cargo test -p leanr_meta abstract_proofs discr_path`
Expected: all PASS (`discr_path` guards the `is_proof` move).

- [ ] **Step 5: Mutations**
  1. `mk_aux_decl_name` ignores pending names (env conflict only) → `distinct_proofs_get_distinct_indices` (`_proof_1` twice).
  2. Disable the cache hit → `identical_proofs_share_one_aux`.
  3. `is_non_trivial_proof` drops the `args.any(!atomic)` clause → `nested_proof_becomes_proof_1_applied_to_its_closure` (no aux).
  4. `is_non_trivial_proof` returns `true` for every proof → `atomic_arg_proof_is_not_abstracted`.
  5. Remove the root `is_proof` early return → `a_proof_value_is_not_abstracted_at_the_root`.
  6. Advance `next_idx` past the returned candidate → nothing fails in this task; Task 8 is the gate. Record it as "killed in Task 8" once Task 8 exists, or as equivalent with the reason.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_meta/src/abstract_proofs.rs crates/leanr_meta/src/lazy_delta.rs crates/leanr_meta/src/discr_path.rs crates/leanr_meta/src/lib.rs
git commit -m "leanr_meta: abstractNestedProofs + AuxLemmas accumulator (mkAuxLemma/mkAuxTheorem)"
```

---

### Task 8: end-to-end commit over Meta0; spec amendment; close-out

**Files:**
- Create: `crates/leanr_meta/tests/decl_substrate.rs`
- Modify: `crates/leanr_meta/tests/support/mod.rs` only if a needed helper is missing; prefer local helpers in the test file
- Modify: `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md` (append Amendment 1 + `## Landed` › P1)

**Interfaces:**
- Consumes: everything above, through the crate's public API only (integration test): `MetaCtx::{new, push_local_decl, mk_lambda, mk_forall, abstract_nested_proofs, collect_level_params, get_max_height}`, `AuxLemmas`, `sort_decl_level_params`, `Environment::add_decl_in`, plus `replay_fixture_in` from `tests/support`.
- Produces: no new API. This is P1's gate, and P2's pipeline will follow the same shape.

The test is the **probe `foo2` shape end to end**. In a scope over a replayed Meta0 `Environment`:
1. Push `α : Sort u` and `a : α`. Build `value = fun α a => @PProd.mk.{u,0} α (@Eq.{u} α (id a) (id a)) a (@rfl.{u} α (id a))` and `type = ∀ α a, PProd.{u,0} α (Eq …)`.
2. `abstract_nested_proofs(&mut AuxLemmas::new(foo2), value)`.
3. `collect_level_params` over the type and the new value, then `sort_decl_level_params(&[], &[u], …)`. Expect `[u]`.
4. Build `Declaration::Defn { name: foo2, level_params, ty, value, hints: Regular(get_max_height(value) + 1), safety: Safe, all: [foo2] }`.
5. Drop the `MetaCtx`. **Collect the pending aux decls and the main decl before the borrow ends.**
6. `env.add_decl_in(&mut scratch, d)` for each pending aux decl, then for the main decl.

Then assert:
- `env.get(foo2._proof_1)` is a `Thm` with `level_params == [u_1]`;
- `env.get(foo2)` is a `Defn` with hints `Regular(2)` (probe: `foo2` is `regular 2`, since `id` is 1);
- the main declaration's value mentions `foo2._proof_1.{u}`. Check it by rendering the promoted value, or simply by the kernel having accepted it, which it would not have done without the aux being present.

A **negative control** in the same file commits the main decl WITHOUT its aux first and expects `Err(KernelError::UnknownConstant(..))` from `add_decl_in`. This proves the ordering matters, and it is the test that kills Task 7 mutation 6's sibling: a wrong aux name would make the kernel reject.

- [ ] **Step 1: Write the test** (complete file)

```rust
//! M4c-1 P1 gate: abstract + commit aux and main declarations over Meta0
//! (plan `docs/superpowers/plans/2026-10-03-m4c1-p1-decl-substrate.md`
//! Task 8). Mirrors the oracle probe `foo2` (plan § Oracle probe facts).

mod support;

use leanr_kernel::bank::{ExprId, NameId, Store};
use leanr_kernel::{
    BinderInfo, ConstantInfo, ConstantVal, Declaration, DefinitionSafety, DefinitionVal,
    ReducibilityHints,
};
use leanr_meta::{sort_decl_level_params, AuxLemmas, CollectLevelParams, Config, EnvExtensions, MetaCtx};

struct Built {
    decls: Vec<Declaration>,
}

fn nm(ctx: &mut MetaCtx, s: &str) -> NameId {
    let base = Some(ctx.view.store);
    let st = ctx.store_mut();
    let mut n = None;
    for part in s.split('.') {
        let id = st.intern_str(base, part).unwrap();
        n = Some(st.name_str(base, n, id).unwrap());
    }
    n.unwrap()
}

fn cu(ctx: &mut MetaCtx, s: &str, levels: &[leanr_kernel::bank::LevelId]) -> ExprId {
    let n = nm(ctx, s);
    let base = Some(ctx.view.store);
    let st = ctx.store_mut();
    let ls = st.intern_level_list(base, levels).unwrap();
    st.expr_const(base, Some(n), ls).unwrap()
}

/// Build `foo2` (with its aux) inside a `MetaCtx` over `env`; return the
/// declarations in commit order (aux first).
fn build_foo2(env: &leanr_kernel::Environment, scratch: &mut Store) -> Built {
    let view = env.view();
    let mut ctx = MetaCtx::new(view, scratch, Config::default(), EnvExtensions::default());
    let base = Some(view.store);
    let u_name = nm(&mut ctx, "u");
    let u = ctx.store_mut().level_param(base, Some(u_name)).unwrap();
    let zero = ctx.store_mut().level_zero(base).unwrap();
    let sort_u = ctx.store_mut().expr_sort(base, u).unwrap();
    let alpha_n = nm(&mut ctx, "α");
    let a_n = nm(&mut ctx, "a");
    let alpha = ctx.push_local_decl(Some(alpha_n), sort_u, BinderInfo::Default).unwrap();
    let a = ctx.push_local_decl(Some(a_n), alpha, BinderInfo::Default).unwrap();
    let id_u = cu(&mut ctx, "id", &[u]);
    let ida = ctx.store_mut().expr_app(base, id_u, alpha).unwrap();
    let ida = ctx.store_mut().expr_app(base, ida, a).unwrap();
    let eq_u = cu(&mut ctx, "Eq", &[u]);
    let rfl_u = cu(&mut ctx, "rfl", &[u]);
    let mut eq_ty = eq_u;
    for x in [alpha, ida, ida] {
        eq_ty = ctx.store_mut().expr_app(base, eq_ty, x).unwrap();
    }
    let mut pf = rfl_u;
    for x in [alpha, ida] {
        pf = ctx.store_mut().expr_app(base, pf, x).unwrap();
    }
    let pprod = cu(&mut ctx, "PProd", &[u, zero]);
    let mut ty_body = pprod;
    for x in [alpha, eq_ty] {
        ty_body = ctx.store_mut().expr_app(base, ty_body, x).unwrap();
    }
    let mk = cu(&mut ctx, "PProd.mk", &[u, zero]);
    let mut val_body = mk;
    for x in [alpha, eq_ty, a, pf] {
        val_body = ctx.store_mut().expr_app(base, val_body, x).unwrap();
    }
    let ty = ctx.mk_forall(&[alpha, a], ty_body).unwrap();
    let value = ctx.mk_lambda(&[alpha, a], val_body).unwrap();

    let foo2 = nm(&mut ctx, "foo2");
    let mut aux = AuxLemmas::new(foo2);
    let value = ctx.abstract_nested_proofs(&mut aux, value).unwrap();

    let mut s = CollectLevelParams::default();
    ctx.collect_level_params(&mut s, ty).unwrap();
    ctx.collect_level_params(&mut s, value).unwrap();
    let lps = sort_decl_level_params(ctx.store(), base, &[], &[u_name], &s.params).unwrap();
    assert_eq!(lps, vec![u_name]);
    let h = ctx.get_max_height(value).unwrap();

    let mut decls = aux.into_pending();
    decls.push(Declaration::Defn(DefinitionVal {
        val: ConstantVal { name: foo2, level_params: lps, ty },
        value,
        hints: ReducibilityHints::Regular(h + 1),
        safety: DefinitionSafety::Safe,
        all: vec![foo2],
    }));
    Built { decls }
}

fn persistent(env: &mut leanr_kernel::Environment, s: &str) -> NameId {
    env.store_mut()
        .intern_name(None, &leanr_kernel::Name::from_dotted(s))
        .unwrap()
        .unwrap()
}

#[test]
fn foo2_commits_its_aux_theorem_then_itself() {
    let mut env = support::replay_fixture_in("meta", "Meta0.olean").env;
    let mut scratch = Store::scratch();
    let Built { decls } = build_foo2(&env, &mut scratch);
    assert_eq!(decls.len(), 2, "one aux + the main decl");
    for d in decls {
        env.add_decl_in(&mut scratch, d).expect("kernel admits");
    }
    let aux = persistent(&mut env, "foo2._proof_1");
    let main = persistent(&mut env, "foo2");
    let u_1 = persistent(&mut env, "u_1");
    match env.get(aux) {
        Some(ConstantInfo::Thm(t)) => assert_eq!(t.val.level_params, vec![u_1]),
        other => panic!("foo2._proof_1: {other:?}"),
    }
    match env.get(main) {
        Some(ConstantInfo::Defn(d)) => assert_eq!(d.hints, ReducibilityHints::Regular(2)),
        other => panic!("foo2: {other:?}"),
    }
}

#[test]
fn the_main_decl_is_rejected_without_its_aux() {
    let mut env = support::replay_fixture_in("meta", "Meta0.olean").env;
    let mut scratch = Store::scratch();
    let Built { decls } = build_foo2(&env, &mut scratch);
    let main = decls.into_iter().last().unwrap();
    let err = env.add_decl_in(&mut scratch, main).unwrap_err();
    assert!(
        matches!(err, leanr_kernel::KernelError::UnknownConstant(_)),
        "{err:?}"
    );
}
```

Adapt to the real API:
- `ctx.view` may not be public outside the crate. If it isn't, take `base` from `env.view().store` before constructing `MetaCtx`, and pass it into the helpers explicitly.
- `Name::from_dotted` may not exist. Use whatever constructor `tests/support` uses: `decode_name` (memory: `name_id`-style helpers exist in the elab support).
- `ReducibilityHints` needs `PartialEq`, which `decl.rs:68` derives (`Copy, PartialEq, Eq` on the shared enums). Confirm it.
- Check that `support::replay_fixture_in` accepts `("meta", "Meta0.olean")` (`tests/support/mod.rs:65`).

- [ ] **Step 2: Run the test**

Run: `cargo test -p leanr_meta --test decl_substrate`
Expected: PASS once Tasks 1-7 are in. If it fails, debug with the systematic-debugging skill: first compare the aux type and value against the probe's `pp.all` output (plan § Oracle probe facts).

- [ ] **Step 3: Mutation sweep** (Task 7 mutation 6 and the cross-task ones)
  1. Task 7 mutation 6 (advance `next_idx` past the returned candidate) → no change for a single aux. Record it as equivalent for single-aux declarations, already covered by `distinct_proofs_get_distinct_indices` for multi-aux.
  2. Swap the commit order (main first) → `foo2_commits_its_aux_theorem_then_itself` fails (`UnknownConstant`).
  3. In `closure_level`, keep `u` (don't rename) → this test fails (`level_params == [u]`), and so does Task 6's test.

- [ ] **Step 4: Append the spec amendment and the P1 landing note**

Append the text of **Amendment 1** below to the spec verbatim, then a `## Landed › P1` section:
- the commit list (`git log --oneline main..HEAD`);
- each task's mutation outcomes;
- any `oracle:` cite corrected during the final sweep.

- [ ] **Step 5: Final citation sweep**

For every `oracle:` cite added on this branch (`git diff main..HEAD | grep -n "oracle:"`), open the cited line in the toolchain sources and fix off-by-N errors in the code comment, the plan and the spec together.

- [ ] **Step 6: Full CI, blocking**

Run: `mise run ci; echo CI_EXIT=$?`
Expected: `CI_EXIT=0` (fmt, clippy, all tests).

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_meta/tests/decl_substrate.rs docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md
git commit -m "leanr_meta: M4c-1 P1 gate — foo2 + aux committed over Meta0; spec amendment 1"
```

---

## Amendment 1 (plan-time refinements; append to the spec in Task 8)

1. **(Superseded by R5; see the spec's Amendment 1 item 1.)** ~~The kernel API is `add_decl_in(&mut self, scratch: &mut Store, d)`, with no separate promote walk.~~ The P1 gate showed this breaks cross-declaration references in one scratch store; `add_decl_in` now promotes first (`promote_declaration`).
   Original text: `check_declaration` already resolves ids through the caller's scratch store, and `add_core` already promotes each survivor (`promote_constant_info`). The spec's `add_decl_from_scratch` "promote, then `add_decl`" is replaced by this. The behavior is the same, and less code is involved.
2. **The aux-lemma cache is env-wide in the oracle.** In the probe, `foo3` reused `foo1._proof_1` from an earlier declaration. M4c-1's corpus resets the environment for each record, so a per-declaration cache (`AuxLemmas`) is observably identical there. M4c-2's file loop must lift the cache to `CommandElab` scope, keyed by type and level params, and must also keep the earlier declarations' aux names as conflicts.
3. **Pending aux names count as "in the environment"** in two places: `mkUniqueName`'s conflict check, and `isNonTrivialProof`'s "constant not in env" test. In the oracle both see aux lemmas that `mkAuxLemma` has already added.
4. **New named seams in P1:**
   - a `letE` reached by `abstractNestedProofs` (unreachable from P2, which rejects `let` first);
   - an unassigned mvar reached by the Closure walk (unreachable after `ensureNoUnassignedMVars`);
   - an aux lemma over unsafe constants (the oracle's unsafe `defnDecl` would be rejected by `add_decl_in`);
   - Closure with `zetaDelta := false` (`check` and dependent let-decls) is not ported, because no M4c-1 caller passes it.
5. **`levelMVarToParamHeaders` applies only to `theorem` or Prop-typed headers** (`MutualDef.lean:1148-1160`). Definition headers keep their level mvars until `levelMVarToParamTypesPreDecls` (`MutualDef.lean:1434`, `PreDefinition/Basic.lean:56-58`), which covers **types only**. A level mvar left in a value is an error (`ensureNoUnassignedLevelMVarsAtPreDef`, `PreDefinition/Main.lean:76-97`). This sharpens spec § The oracle model step 3, and P2's plan owns it.
