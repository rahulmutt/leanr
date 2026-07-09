# Term-Bank Kernel Migration Implementation Plan (compact Expr, phase 2 of 3)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Migrate the kernel — `subst`, `local_ctx`, `tc`, `quot`, `inductive`, `env`, `replay` — from `Arc<Expr>`/`Arc<Name>`/`Level` to the phase-1 bank's `ExprId`/`NameId`/`LevelId`, so every checker cache is structural, per-declaration transients free wholesale, and full `check --all` completes inside the 32 GiB pod limit — with zero verdict changes, proven by a dual-checker differential gate before the flip.

**Architecture:** Approach A from the spec (`docs/superpowers/specs/2026-07-06-term-bank-kernel-migration-design.md`): id-native modules grow as `bank/` siblings (`bank/decl.rs`, `bank/local_ctx.rs`, `bank/subst.rs`, `bank/tc.rs`, `bank/quot.rs`, `bank/inductive.rs`, `bank/env.rs`, `bank/replay.rs`), each landing green with the Arc kernel untouched. A dual-checker gate replays every fixture through both kernels and requires identical verdicts. The final flip `git mv`s the new modules over the old, rewires callers, and deletes the Arc checker + `intern.rs`.

**Tech Stack:** Rust, `leanr_kernel` (no new deps, no `unsafe`); dual-checker gate lives in `crates/leanr_olean/tests/` (the crate that can decode fixtures and drive the kernel).

## Global Constraints

- `leanr_kernel` depends on no workspace crate and gains no external deps. No `unsafe` anywhere.
- Untrusted-input discipline: no panics reachable from attacker data; recursion over attacker-depth structures uses explicit stacks or `RecGuard`; id/pool exhaustion returns `KernelError::BankExhausted`.
- The interning invariant (parent spec §1) — equal ids ⇔ structurally equal terms — is what makes id-keyed caches sound. Every ported cache cites it.
- Oracle citations: ported code keeps its oracle source-line comments verbatim. Porting is representation-only; any algorithmic drift is a bug.
- **Region discipline:** one scratch `Store` per declaration, owned by admission (`add_decl`), lent to every `TypeChecker` and admission step of that declaration; env values are persistent-region ids; kernel-generated survivors promote at `add_core`. Scratch ids must never be stored in the persistent env or in a `KernelError`.
- Store-access convention (phase-1): writable region first, `base: Option<&Store>` second — `f(st: &mut Store, base: Option<&Store>, ...)`. When `st` is the persistent store, `base` is `None`.
- Lint gate before every commit: `mise run lint`. Full gate where a task says so: `mise run ci`. Conventional-commit prefixes.
- The Arc kernel, its tests, and `crates/leanr_olean/tests/check_fixtures.rs` stay untouched and green until Task 8 (the flip).

## File Structure

- Create: `crates/leanr_kernel/src/bank/decl.rs` — id-twin declaration types + `ConstantInfo` bridges + id `constant_info_eq`.
- Create: `crates/leanr_kernel/src/bank/local_ctx.rs` — `LocalDecl`/`LocalContext`/`FVarIdGen` over ids.
- Create: `crates/leanr_kernel/src/bank/subst.rs` — the six subst operations over ids.
- Create: `crates/leanr_kernel/src/bank/quot_red.rs`, `crates/leanr_kernel/src/bank/tc.rs` + `crates/leanr_kernel/src/bank/tc/tests.rs` — the type checker.
- Create: `crates/leanr_kernel/src/bank/quot.rs`, `crates/leanr_kernel/src/bank/inductive.rs` + `crates/leanr_kernel/src/bank/inductive/tests.rs` — admission machinery.
- Create: `crates/leanr_kernel/src/bank/env.rs`, `crates/leanr_kernel/src/bank/used_consts.rs`, `crates/leanr_kernel/src/bank/replay.rs` (+ `tests.rs` submodules mirroring the old layout) — environment and replay.
- Create: `crates/leanr_olean/tests/dual_check.rs` — the pre-flip dual-checker gate.
- Modify: `crates/leanr_kernel/src/bank/mod.rs` (module decls), `crates/leanr_kernel/src/bank/scratch.rs` (public `promote_name`/`promote_level`), `crates/leanr_kernel/src/lib.rs` (Task 8 flip).
- Delete at flip: `subst.rs`, `local_ctx.rs`, `tc.rs` + `tc/`, `quot.rs`, `quot_red.rs`, `inductive.rs` + `inductive/`, `env.rs` + `env/`, `replay.rs` + `replay/`, `used_consts.rs`, `intern.rs`, `decl.rs` (replaced by moved bank twins).

Naming rule: **every id-twin type/function keeps the name of its Arc counterpart** (`ConstantInfo`, `TypeChecker`, `instantiate`, …), distinguished only by module path. Inside `bank/` files that bridge, alias the Arc types: `use crate::ConstantInfo as ArcConstantInfo;`. This makes the Task-8 flip a module swap, not a rename.

---

### Task 1: `bank/decl.rs` — id-twin declaration types, bridges, `constant_info_eq`

**Files:**
- Create: `crates/leanr_kernel/src/bank/decl.rs`
- Modify: `crates/leanr_kernel/src/bank/mod.rs` (add `pub mod decl;`)
- Test: inline `#[cfg(test)]` in `decl.rs`

**Interfaces:**
- Consumes: `Store` intern/bridge API (`intern_name`, `to_name`, `intern_level`, `to_level`, `intern_expr`, `to_expr`), id newtypes, `Nat`, `RecGuard`.
- Produces (all in `bank::decl`, mirroring `decl.rs` field-for-field, oracle citations copied):
  - `ConstantVal { name: NameId, level_params: Vec<NameId>, ty: ExprId }`
  - `ReducibilityHints`, `DefinitionSafety`, `QuotKind` contain no Arc types — do NOT duplicate them; re-export the existing ones: `pub use crate::{ReducibilityHints, DefinitionSafety, QuotKind};` (they survive the Task-8 flip unchanged).
  - `AxiomVal`, `DefinitionVal`, `TheoremVal`, `OpaqueVal`, `QuotVal`, `InductiveVal`, `ConstructorVal`, `RecursorRule`, `RecursorVal`, `ConstantInfo` (8-variant enum), `Declaration`, `InductiveType` — same shapes as `decl.rs` with `Arc<Name> → NameId`, `Arc<Expr> → ExprId`, `Vec<Arc<Name>> → Vec<NameId>`; scalar fields (`Nat`, `bool`, `u32`, hints, safety) unchanged.
  - `ConstantInfo::constant_val(&self) -> &ConstantVal`, `name(&self) -> NameId`, `kind(&self) -> &'static str` (byte-identical strings to the Arc version — the golden fixtures compare them).
  - Bridges (iterative where they walk exprs — they delegate to `intern_expr`/`to_expr` which already are):
    - `pub fn intern_constant_info(st: &mut Store, base: Option<&Store>, ci: &ArcConstantInfo) -> Result<ConstantInfo, KernelError>`
    - `pub fn to_constant_info(st: &Store, base: Option<&Store>, ci: &ConstantInfo, g: &mut RecGuard) -> Result<ArcConstantInfo, KernelError>`
    - `pub fn intern_declaration(st: &mut Store, base: Option<&Store>, d: &crate::Declaration) -> Result<Declaration, KernelError>`
  - `pub fn constant_info_eq(a: &ConstantInfo, b: &ConstantInfo) -> bool` — pure id/scalar comparisons (no `RecGuard`, no `Result`: by the interning invariant this IS the Arc version's guarded structural walk). Field coverage must be complete — copy the Arc version's field-enumeration doc comment and enumerate every field of every variant; a skipped field is a soundness hole in replay's postponed-constructor check.

- [ ] **Step 1: Write the failing tests.** Create `bank/decl.rs` with the test module only:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::bank::Store;
    use crate::testenv::{g, nm};
    use crate::ConstantInfo as ArcConstantInfo;

    // Build a small Arc-side ConstantInfo, bridge in, bridge out,
    // compare with the Arc structural equality.
    #[test]
    fn constant_info_round_trip() {
        let ci = crate::testenv::axiom_u(); // if absent, build inline:
        // ArcConstantInfo::Axiom(AxiomVal { val: ConstantVal { name: nm("A"),
        //   level_params: vec![nm("u")], ty: e::sort_u() }, is_unsafe: false })
        let mut st = Store::persistent();
        let id_ci = intern_constant_info(&mut st, None, &ci).unwrap();
        let back = to_constant_info(&st, None, &id_ci, &mut g()).unwrap();
        assert!(crate::constant_info_eq(&ci, &back, &mut g()).unwrap());
    }

    #[test]
    fn interning_twice_gives_equal_twins() {
        let ci = crate::testenv::axiom_u();
        let mut st = Store::persistent();
        let a = intern_constant_info(&mut st, None, &ci).unwrap();
        let b = intern_constant_info(&mut st, None, &ci).unwrap();
        assert!(constant_info_eq(&a, &b));
        assert_eq!(a.name(), b.name());
    }

    #[test]
    fn eq_distinguishes_every_field() {
        // For each ConstantInfo variant: intern a base value, then a copy
        // with exactly one field perturbed, assert !constant_info_eq.
        // Perturb: name, one level_param, ty, value, hints, safety, all,
        // cidx, num_params, num_fields, is_unsafe, induct, rules[0].rhs,
        // rules[0].nfields, k, num_motives, num_minors, num_indices,
        // num_nested, is_rec, is_reflexive, ctors, kind (Axiom vs Defn).
        // One assert per field — write them all out.
    }

    #[test]
    fn kind_strings_match_arc_kernel() {
        // For each of the 8 variants: bridge in, assert
        // id_ci.kind() == arc_ci.kind().
    }
}
```

If `testenv` lacks a `ConstantInfo` builder, add small `pub fn` builders to `testenv.rs` (test-only file) rather than duplicating literals — check `env/tests.rs` and `replay/tests.rs` first; they already construct `ConstantInfo`s and their helpers may just need `pub`.

- [ ] **Step 2: Run tests, verify they fail to compile** (types don't exist yet): `cargo test -p leanr_kernel bank::decl` — expect compile errors naming `intern_constant_info`.
- [ ] **Step 3: Implement the types.** Copy `decl.rs` top-to-bottom, applying the type mapping (`Arc<Name>`→`NameId`, `Arc<Expr>`→`ExprId`, drop the `use std::sync::Arc`), keeping every oracle citation and doc comment, deriving `Debug, Clone` (plus `Copy` where all fields are `Copy` — `QuotVal` is not: `ConstantVal` has a `Vec`).
- [ ] **Step 4: Implement the bridges.** Field-by-field: names via `st.intern_name(base, &arc_name)?` / `st.to_name(base, Some(id))`, exprs via `st.intern_expr(base, &e)?` / `st.to_expr(base, id, g)?`, scalars copied. `Option<NameId>` never appears here (declaration names are never anonymous — but do not assert: `intern_name` of `Name::Anonymous` returns whatever the phase-1 encoding does; store it as it comes. Check `intern_name`'s signature — it returns `Result<Option<NameId>, _>` if anonymous maps to `None`; mirror phase 1's `Const`/`FVar` handling: store `Option<NameId>` in `ConstantVal.name` **only if** phase-1 `intern_name` forces it; otherwise plain `NameId`. Whichever it is, `to_constant_info` must round-trip `Name::Anonymous` unchanged — add a round-trip test with an anonymous name to pin it).
- [ ] **Step 5: Implement `constant_info_eq`** as pure `==` over ids and scalars, every field enumerated.
- [ ] **Step 6: Run tests, verify green:** `cargo test -p leanr_kernel bank::decl` — PASS.
- [ ] **Step 7: Lint + commit:** `mise run lint`; `git add -A && git commit -m "feat: id-twin declaration types and ConstantInfo bridges (migration Task 1)"`

---

### Task 2: `bank/local_ctx.rs` — local contexts over ids

**Files:**
- Create: `crates/leanr_kernel/src/bank/local_ctx.rs`
- Modify: `crates/leanr_kernel/src/bank/mod.rs` (add `pub mod local_ctx;`)
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Consumes: `Store::expr_fvar`, `expr_forall`, `expr_lam`, `intern_name`, `name_num`/`name_str` (fresh-name minting), `bank/subst.rs` comes later — so `mk_pi`/`mk_lambda` need `abstract_fvars`; **check the Arc `local_ctx.rs:181-208`**: if `mk_pi`/`mk_lambda` call `subst::abstract_fvars`, move this task AFTER Task 3 or (better) keep task order and implement `mk_pi`/`mk_lambda` in Task 3's file as free functions taking `&LocalContext` — mirror whatever split the Arc kernel actually uses; the Interfaces block of Task 3 lists them again for that case.
- Produces (`bank::local_ctx`):
  - `LocalDecl { id: NameId, binder_name: Option<NameId>, ty: ExprId, binder_info: BinderInfo, value: Option<ExprId> }` (binder_name optionality: mirror phase-1's binder-name encoding — same choice as Task 1 Step 4).
  - `LocalContext { decls: Vec<LocalDecl>, index: HashMap<NameId, usize> }` with `mk_local_decl(&mut self, st: &mut Store, base: Option<&Store>, gen: &mut FVarIdGen, binder_name..., ty: ExprId, bi: BinderInfo) -> Result<ExprId, KernelError>` (returns the fvar ref), `mk_let_decl(...)`, `get(&self, fvar_id: NameId) -> Option<&LocalDecl>`, plus `mk_pi`/`mk_lambda` if they live here (see Consumes).
  - `FVarIdGen { next: u64 }` minting `_kernel_fresh.<n>` by interning `Name::Str(anon, "_kernel_fresh")` then `name_num` — the *same* name values as the Arc kernel (oracle: type_checker.cpp:24), so dual-checker traces stay comparable.

- [ ] **Step 1: Write failing tests** — port the Arc `local_ctx.rs` inline tests (find them: `grep -n "#\[cfg(test)\]" crates/leanr_kernel/src/local_ctx.rs`), mapping constructions through `Store` calls. Minimum set: fresh ids are `_kernel_fresh.0, .1, ...` (bridge out with `to_name`, compare against the Arc `FVarIdGen` output); `get` finds a pushed decl by id; `mk_local_decl` returns an `FVar` node wrapping the minted id.
- [ ] **Step 2: Run, verify failure:** `cargo test -p leanr_kernel bank::local_ctx` — compile error.
- [ ] **Step 3: Port the module** (mapping: `Arc<Name>`→`NameId` via intern, `Expr::fvar(id)`→`st.expr_fvar(base, ...)?`, every constructor call becomes fallible — thread `Result` up; keep oracle citations).
- [ ] **Step 4: Run, verify green.**
- [ ] **Step 5: Lint + commit:** `git commit -m "feat: id-based LocalContext and FVarIdGen (migration Task 2)"`

---

### Task 3: `bank/subst.rs` — substitution walkers over ids

**Files:**
- Create: `crates/leanr_kernel/src/bank/subst.rs`
- Modify: `crates/leanr_kernel/src/bank/mod.rs` (add `pub mod subst;`)
- Test: inline `#[cfg(test)]` — unit ports + a differential property suite

**Interfaces:**
- Consumes: `Store` node view (`expr_node`, `expr_data`), intern-constructors, `bank::local_ctx::LocalContext`.
- Produces — same six entry points as Arc `subst.rs`, same parameter lists with `Arc<Expr>`→`ExprId`, `&[Arc<Expr>]`→`&[ExprId]`, plus the leading store pair:
  - `pub fn instantiate_core(st: &mut Store, base: Option<&Store>, e: ExprId, subst: &[ExprId]) -> Result<ExprId, KernelError>` (mirror the exact Arc param list — read `subst.rs:73` first; if it takes an offset or `RecGuard`, keep it)
  - `instantiate`, `instantiate_rev`, `lift_loose_bvars`, `abstract_fvars`, `instantiate_level_params` — same rule.
  - If the Arc kernel's `LocalContext::mk_pi`/`mk_lambda` call `abstract_fvars` (Task 2's Consumes note), implement them here as free functions `pub fn mk_pi(st: &mut Store, base: Option<&Store>, lctx: &LocalContext, fvars: &[ExprId], e: ExprId) -> Result<ExprId, KernelError>` (mirror the Arc param list exactly) and the analogous `mk_lambda`; otherwise they already landed in Task 2.
  - Every walker keeps its memo, keyed by `(ExprId, offset)` instead of `(ptr, offset)` (`HashMap<(ExprId, u32), ExprId>`), and keeps the closed-subterm fast path via the cached loose-bvar range in `expr_data` (`bvar_loose_range`) — the Arc version's skip conditions port verbatim.

- [ ] **Step 1: Write the differential property suite first** (this is the task's real gate):

```rust
#[cfg(test)]
mod tests {
    use crate::bank::Store;
    use crate::testenv::g;

    /// Drive the SAME operation through both representations and
    /// bridge-compare. `gen_expr(seed)` is the phase-1 deterministic
    /// generator (bank/tests.rs) — reuse it, don't rewrite it; make it
    /// `pub(crate)` in bank/tests.rs if needed... it is cfg(test), so
    /// instead move the generator into a `#[cfg(test)] pub(crate) mod
    /// testgen;` under bank/ (mechanical move, do it as part of this
    /// step, keeping bank/tests.rs green).
    #[test]
    fn instantiate_matches_arc_kernel() {
        for seed in 0u64..500 {
            let (arc_e, arc_subst) = testgen::expr_and_closed_subst(seed);
            let mut st = Store::scratch();
            let base = Store::persistent();
            let e = st.intern_expr(Some(&base), &arc_e).unwrap();
            let subst: Vec<_> = arc_subst.iter()
                .map(|s| st.intern_expr(Some(&base), s).unwrap()).collect();
            let got = super::instantiate(&mut st, Some(&base), e, &subst).unwrap();
            let want = crate::instantiate(&arc_e, &arc_subst, &mut g()).unwrap();
            let got_arc = st.to_expr(Some(&base), got, &mut g()).unwrap();
            assert!(crate::Expr::structural_eq(&got_arc, &want, &mut g()).unwrap(),
                "seed {seed}");
        }
    }
    // Same shape for: instantiate_rev, instantiate_core,
    // lift_loose_bvars, abstract_fvars, instantiate_level_params
    // (generator variant that produces level params + level lists).
    // Mirror the Arc functions' exact signatures when calling them —
    // read subst.rs first; adjust the harness, not the property.
}
```

Plus port the Arc `subst.rs` inline unit tests (same mapping as Task 2).

- [ ] **Step 2: Run, verify compile failure.**
- [ ] **Step 3: Port the six walkers.** Mechanical mapping per function: pattern-match `st.expr_node(base, e)` instead of `e.node()`; rebuild with intern-constructors (`?` on each); memo `HashMap<(ExprId, u32), ExprId>`; the traversal skeleton (explicit stack or `RecGuard`d recursion) ports UNCHANGED — same frames, same order, same oracle citations.
- [ ] **Step 4: Run, verify green:** `cargo test -p leanr_kernel bank::subst`.
- [ ] **Step 5: Lint + commit:** `git commit -m "feat: id-based substitution walkers with differential property suite (migration Task 3)"`

---

### Task 4: `bank/quot_red.rs` + `bank/tc.rs` — the type checker

**Files:**
- Create: `crates/leanr_kernel/src/bank/quot_red.rs`, `crates/leanr_kernel/src/bank/tc.rs`, `crates/leanr_kernel/src/bank/tc/tests.rs`
- Modify: `crates/leanr_kernel/src/bank/mod.rs` (add `pub mod quot_red; pub mod tc;`)

**Interfaces:**
- Consumes: Tasks 1-3; `bank::env::EnvView` does NOT exist yet — so `TypeChecker` in this task is written against the trait-free view struct defined HERE and re-used by Task 6:
  - `pub struct EnvView<'a> { pub consts: &'a std::collections::HashMap<NameId, bank::decl::ConstantInfo>, pub extra: Option<&'a std::collections::HashMap<NameId, bank::decl::ConstantInfo>>, pub quot_initialized: bool, pub store: &'a Store }` with `pub fn get(&self, n: NameId) -> Option<&ConstantInfo>` (extra first, then consts) and `pub fn get_with(&self, n: NameId) -> Result<&ConstantInfo, KernelError>` (miss → `KernelError::UnknownConstant(store.to_name(None, Some(n)))`). Define `EnvView` in `bank/tc.rs`; Task 6's `Environment::view()` produces it.
- Produces (`bank::tc`):
  - `pub struct TypeChecker<'e> { view: EnvView<'e>, scratch: &'e mut Store, lctx: LocalContext, fvar_gen: FVarIdGen, infer_cache: [HashMap<ExprId, ExprId>; 2], whnf_cache: HashMap<ExprId, ExprId>, whnf_core_cache: HashMap<ExprId, ExprId>, eqv_cache: UnionFind, failure_cache: HashSet<(ExprId, ExprId)>, unfold_memo: HashMap<ExprId, ExprId>, ... }` — every remaining private field of Arc `tc.rs:312-380` carried over with `Arc<Expr>`→`ExprId`.
  - `pub fn new(view: EnvView<'e>, scratch: &'e mut Store) -> TypeChecker<'e>` — **the scratch store is borrowed, not owned** (Global Constraints: one scratch per declaration, several checkers).
  - `check`, `infer_type(&mut self, e: ExprId) -> Result<ExprId, KernelError>`, `ensure_sort`, `ensure_pi`, `is_prop`, `whnf`, `is_def_eq(&mut self, t: ExprId, s: ExprId) -> Result<bool, KernelError>`, `Lbool` — mirroring `tc.rs`'s public list exactly.
  - `UnionFind` over raw id bits: `index: HashMap<u32, usize>` (was `HashMap<ExprPtr, usize>`), insert with `id.bits()`. `ExprPtr` is not used anywhere in bank code.
  - `bank/quot_red.rs`: port of `quot_red.rs` (83 lines) with the same mapping.
  - The `to_name` bridge is the ONLY Arc construction allowed: error variants carrying `Arc<Name>` are built as `KernelError::UnknownConstant(self.store().to_name(...))` at the error site (cold path; keeps `KernelError` unchanged — spec §4 refined: no scratch id ever enters an error).

**Porting rules (apply uniformly; the traversals, cache-consult order, and oracle citations port verbatim):**

| Arc pattern | id pattern |
|---|---|
| `match e.node() { ExprNode::App { f, arg } => ...}` | `match self.node(e) { Node::App { f, arg } => ... }` where `fn node(&self, e: ExprId) -> Node { self.scratch.expr_node(Some(self.view.store), e) }` |
| `Expr::app(f, a)` | `self.scratch.expr_app(Some(self.view.store), f, a)?` |
| `cache.get(&ExprPtr(Arc::clone(e)))` | `cache.get(&e)` |
| `cache.insert(ExprPtr(...), Arc::clone(&r))` | `cache.insert(e, r)` |
| `Arc::ptr_eq(a, b)` fast path | `a == b` (now *structural* — strictly more hits, verdict-identical: cite the interning invariant where the Arc code cited pointer identity) |
| `Expr::structural_eq(a, b, g)?` | `a == b` (no guard, no Result — remove the `?` and the guard threading for these call sites only) |
| env lookup `self.env.get_with(name)?` | `self.view.get_with(name)?` (name is already `NameId` from the `Const` node) |
| `instantiate(e, subst, g)?` | `subst::instantiate(self.scratch, Some(self.view.store), e, subst)?` |
| unfold: `instantiate_level_params(val.value, params, levels)` | same via `bank::subst`, ids throughout; `unfold_memo` keyed by the `Const`'s `ExprId` |

Borrow-check note: methods that need `&mut self.scratch` and `self.view` simultaneously are fine (disjoint fields); methods that pattern-match a `Node` (a `Copy` value) and then intern do NOT hold a borrow across the intern — `Node` is `Copy`, bind it first.

- [ ] **Step 1: Port `bank/quot_red.rs`** (small, mechanical) with its inline tests; run `cargo test -p leanr_kernel bank::quot_red` green; commit `"feat: id-based quotient reduction (migration Task 4a)"`.
- [ ] **Step 2: Write the failing differential tests** in `bank/tc/tests.rs`. Port the Arc `tc/tests.rs` suite (919 lines) test-by-test: each test builds its environment with the existing Arc `testenv` helpers, then runs BOTH checkers and asserts identical results:

```rust
use crate::bank::{decl::intern_constant_info, tc::{EnvView, TypeChecker}, Store};

/// Bridge an Arc-kernel test env into (persistent store, consts map).
fn bridge_env(env: &crate::Environment)
    -> (Store, std::collections::HashMap<crate::bank::NameId, crate::bank::decl::ConstantInfo>) {
    let mut st = Store::persistent();
    let mut consts = std::collections::HashMap::new();
    for ci in env.iter() { // if Environment lacks iter(), add pub(crate) fn iter to env.rs (test-only accessor is fine as pub)
        let idci = intern_constant_info(&mut st, None, ci).unwrap();
        consts.insert(idci.name(), idci);
    }
    (st, consts)
}

/// The per-test harness: same input expr, both checkers, same verdict.
fn assert_infer_matches(env: &crate::Environment, e: &std::sync::Arc<crate::Expr>) {
    let arc_result = crate::TypeChecker::new(env).infer_type(e);
    let (st, consts) = bridge_env(env);
    let mut scratch = Store::scratch();
    let eid = scratch.intern_expr(Some(&st), e).unwrap();
    let view = EnvView { consts: &consts, extra: None,
        quot_initialized: env.quot_initialized(), store: &st };
    let id_result = TypeChecker::new(view, &mut scratch).infer_type(eid);
    match (arc_result, id_result) {
        (Ok(a), Ok(b)) => {
            let b = scratch.to_expr(Some(&st), b, &mut crate::testenv::g()).unwrap();
            assert!(crate::Expr::structural_eq(&a, &b, &mut crate::testenv::g()).unwrap());
        }
        (Err(a), Err(b)) => assert_eq!(a, b),
        (a, b) => panic!("verdict split: arc={a:?} id={b:?}"),
    }
}
```

Analogous harnesses for `whnf` and `is_def_eq` (bool compared directly). Every ported test calls the harness instead of asserting on one kernel.

- [ ] **Step 3: Run, verify compile failure:** `cargo test -p leanr_kernel bank::tc`.
- [ ] **Step 4: Port `tc.rs`** top-to-bottom with the porting rules. Do it in module order (helpers first, `infer` family, `whnf` family, `is_def_eq` family); the file stays non-compiling until done — that's fine within a task; do NOT commit mid-port.
- [ ] **Step 5: Run, verify green:** `cargo test -p leanr_kernel bank::tc` AND the whole crate `cargo test -p leanr_kernel` (nothing else may regress).
- [ ] **Step 6: Lint + commit:** `git commit -m "feat: id-based TypeChecker with structural id-keyed caches (migration Task 4)"`

---

### Task 5: `bank/quot.rs` + `bank/inductive.rs` — admission machinery

**Files:**
- Create: `crates/leanr_kernel/src/bank/quot.rs`, `crates/leanr_kernel/src/bank/inductive.rs`, `crates/leanr_kernel/src/bank/inductive/tests.rs`, `crates/leanr_kernel/src/bank/quot/tests.rs`
- Modify: `crates/leanr_kernel/src/bank/mod.rs`

**Interfaces:**
- Consumes: Tasks 1-4. The Arc versions' public entry points (read `quot.rs`, `inductive.rs` headers first) — typically `add_quot(...)` and the inductive admission entry called from `env.rs::add_decl`'s `Declaration::Inductive` arm; mirror those exact names/params with the store pair threaded.
- Produces: same entry points over ids, operating on a caller-supplied scratch `&mut Store` + `EnvView`-compatible inputs, returning the `ConstantInfo`s to admit (still scratch-region — Task 6's `add_core` promotes them).
- **Nested-inductive scratch env (spec §2):** where the Arc code clones the `Environment` and adds restored decls, the id code builds `extra: HashMap<NameId, ConstantInfo>` (values interned into the declaration's scratch store) and passes `EnvView { extra: Some(&extra), .. }`. No second-level region exists or is needed — transient decls and checking transients share the one scratch store and die together.

- [ ] **Step 1: Write failing tests** — port `inductive/tests.rs` (919 lines) and `quot/tests.rs` through the dual harness pattern from Task 4 Step 2 (admission tests assert both kernels produce the same admit/reject verdict and, on admit, `constant_info_eq`-equal outputs after bridging).
- [ ] **Step 2: Run, verify compile failure.**
- [ ] **Step 3: Port `bank/quot.rs`** (327 lines, mechanical; `check_eq_type` runs a `TypeChecker` — construct it with the caller's scratch).
- [ ] **Step 4: Port `bank/inductive.rs`** (2636 lines — the porting rules table from Task 4 applies verbatim; the nested-inductive env clone becomes the `extra` map per the Interfaces note).
- [ ] **Step 5: Run all crate tests green.**
- [ ] **Step 6: Lint + commit:** `git commit -m "feat: id-based quotient and inductive admission (migration Task 5)"`

---

### Task 6: `bank/env.rs` + `bank/used_consts.rs` + `bank/replay.rs` — environment and replay

**Files:**
- Create: `crates/leanr_kernel/src/bank/env.rs`, `crates/leanr_kernel/src/bank/used_consts.rs`, `crates/leanr_kernel/src/bank/replay.rs`, `crates/leanr_kernel/src/bank/env/tests.rs`, `crates/leanr_kernel/src/bank/replay/tests.rs`
- Modify: `crates/leanr_kernel/src/bank/mod.rs`; `crates/leanr_kernel/src/bank/scratch.rs` — make the name/level promotion helpers `pub` as `promote_name(base: &mut Store, scratch: &Store, id: NameId) -> Result<NameId, KernelError>` and `promote_level(...)` (they exist as internals of `promote`; if fused inline, extract them — behavior-preserving refactor covered by the existing bank tests).

**Interfaces:**
- Produces (`bank::env`):
  - `pub struct Environment { store: Store /* persistent */, constants: HashMap<NameId, ConstantInfo>, quot_initialized: bool }`
  - `pub fn from_modules<I>(modules: I) -> Result<Environment, EnvironmentError>` — same signature as Arc `env.rs:125`; interns each module's constants (`intern_constant_info(&mut self.store, None, ..)`), **dropping each module's Arc graph before pulling the next from the iterator** (the iterator is already lazy — just don't collect).
  - `pub fn intern_module(&mut self, module: Vec<crate::ConstantInfo>) -> Result<HashMap<NameId, ConstantInfo>, KernelError>` — the replay-input bridge: interns and returns id-form constants, consuming (dropping) the Arc module. Callers fold over decoded modules.
  - `get(&self, n: NameId) -> Option<&ConstantInfo>`, `get_with`, `is_structure_like`, `quot_initialized`, `len`, `is_empty` — ported; `view(&self) -> EnvView<'_>`.
  - `pub fn add_decl(&mut self, d: bank::decl::Declaration) -> Result<(), KernelError>` — creates `let mut scratch = Store::scratch();` for the declaration, runs the ported checking pipeline (Tasks 4-5), and admits via `add_core`.
  - `add_core` (private, the single admission choke point): for each `ConstantInfo` to admit, translate scratch ids → persistent via `promote` (exprs) / `promote_name` / `promote_level` field-by-field (write `fn promote_constant_info(store: &mut Store, scratch: &Store, ci: &ConstantInfo) -> Result<ConstantInfo, KernelError>` in `bank/env.rs` — every field enumerated like Task 1's bridges), then insert. Persistent-region ids pass through unchanged (already `promote`'s contract). The Arc kernel's `interner.intern_input`/`intern` calls in `add_core` have no id equivalent — deduplication already happened at interning; delete those lines in the port.
  - `Clone for Environment` is NOT implemented (the Arc version's clone existed only for the nested-inductive scratch env, replaced by `EnvView.extra` in Task 5 — nothing else clones; verify with `grep -rn "\.clone()" crates/leanr_kernel/src/inductive.rs crates/leanr_kernel/src/env.rs | grep -i env`).
  - `bank::used_consts::used_constants(st: &Store, base: Option<&Store>, info: &ConstantInfo) -> Vec<NameId>` — port of `used_consts.rs` walking id rows.
  - `bank::replay::replay(env: &mut Environment, constants: HashMap<NameId, ConstantInfo>) -> Result<ReplayStats, ReplayError>` — port of `replay.rs` with: input already id-form (callers bridge via `intern_module`); **the pre-intern block (`replay.rs:89-107`) deleted** — interning at input IS that pass; postponed ctor/recursor comparison via Task 1's `constant_info_eq` (id comparisons, no guard). `ReplayError { decl: Arc<Name>, error: KernelError }` keeps its shape — build `decl` via `to_name` (cold path).

- [ ] **Step 1: Write failing tests** — port `env/tests.rs` and `replay/tests.rs` through the dual harness (build Arc-side input, run Arc `replay` and id `replay` on bridged input, compare `ReplayStats` and verdicts; on success compare resulting env sizes via `len()` and spot-check `constant_info_eq` on bridged-out entries). Add one promotion-specific test: admit an inductive via id `add_decl`, assert every id reachable from the stored `ConstantInfo`s has `is_scratch() == false` (walk with `used_constants` + a row walk over `expr_node`).
- [ ] **Step 2: Run, verify compile failure.**
- [ ] **Step 3: Implement `bank/used_consts.rs`, then `bank/env.rs`, then `bank/replay.rs`** per the Interfaces block.
- [ ] **Step 4: Run all crate tests green** (`cargo test -p leanr_kernel`).
- [ ] **Step 5: Lint + commit:** `git commit -m "feat: id-based Environment with promote-at-add_core and replay without pre-intern (migration Task 6)"`

---

### Task 7: Dual-checker fixture gate

**Files:**
- Create: `crates/leanr_olean/tests/dual_check.rs`
- Modify: `crates/leanr_kernel/src/lib.rs` — export the bank kernel for external use: `pub use bank::{...}` is NOT the shape (names collide with the Arc exports); instead `pub mod bank;` already exists — just ensure the bank modules and their types are `pub` so `leanr_kernel::bank::env::Environment` etc. resolve from outside the crate.

**Interfaces:**
- Consumes: everything; `check_fixtures.rs`'s existing decode-and-replay plumbing (read it first and reuse its fixture-loading helpers — extract shared helpers into a `tests/common/mod.rs` if it doesn't already have one, keeping `check_fixtures.rs` byte-identical in behavior).
- Produces: the pre-flip gate. For EVERY fixture module set that `check_fixtures.rs` replays (including every hermetic mutation fixture):
  1. Decode once.
  2. Arc path: exactly what `check_fixtures.rs` does today → verdict A (Ok(stats) or the specific error).
  3. Id path: `bank::env::Environment` + `intern_module` fold + `bank::replay::replay` → verdict B.
  4. Assert: both Ok with equal `checked`/`skipped_unsafe` counts, or both Err with `assert_eq!(a.error, b.error)` (same `KernelError` variant AND payload — `KernelError: PartialEq`) and same failing `decl` name (bridge B's out via `to_name` comparison... `ReplayError.decl` is already `Arc<Name>` on both sides; `assert_eq!` directly).

- [ ] **Step 1: Write the gate** (it "fails" only if verdicts split — write it, run it, and treat any split as a bug in Tasks 1-6 to be fixed via superpowers:systematic-debugging before proceeding).
- [ ] **Step 2: Run:** `cargo test -p leanr_olean --test dual_check -- --nocapture`. Expected: PASS over all fixtures. Record runtime; if the doubled replay is slow, that's acceptable — this test runs until Task 8 deletes the Arc side, then IT becomes redundant and is deleted in the same commit that ports `check_fixtures.rs`.
- [ ] **Step 3: Full gate:** `mise run ci` — everything green.
- [ ] **Step 4: Commit:** `git commit -m "test: dual-checker fixture gate — id kernel verdict-identical to Arc kernel (migration Task 7)"`

---

### Task 8: The flip

**Files:**
- Modify: `crates/leanr_kernel/src/lib.rs`, `crates/leanr_kernel/src/bank/mod.rs`
- Move: `bank/decl.rs`→`decl.rs`, `bank/local_ctx.rs`→`local_ctx.rs`, `bank/subst.rs`→`subst.rs`, `bank/quot_red.rs`→`quot_red.rs`, `bank/tc.rs`+`bank/tc/`→`tc.rs`+`tc/`, `bank/quot.rs`+`bank/quot/`→`quot.rs`+`quot/`, `bank/inductive.rs`+`bank/inductive/`→`inductive.rs`+`inductive/`, `bank/env.rs`+`bank/env/`→`env.rs`+`env/`, `bank/replay.rs`+`bank/replay/`→`replay.rs`+`replay/`, `bank/used_consts.rs`→`used_consts.rs` (each `git mv -f` over its predecessor)
- Delete: `intern.rs`; `crates/leanr_olean/tests/dual_check.rs`
- Keep: `expr.rs`, `name.rs`, `level.rs`, `syntax.rs`, `num.rs`, `guard.rs` (decoder-boundary types + bridges), `testenv.rs` (bridged harnesses still use it)
- Modify: every caller in `crates/leanr_olean`, `crates/leanr_query`, `crates/leanr_cli` (find them: `grep -rn "TypeChecker\|replay\|Environment\|from_modules\|add_decl" crates/leanr_olean/src crates/leanr_query/src crates/leanr_cli/src crates/leanr_olean/tests`), plus `crates/leanr_kernel/tests/env.rs` and `crates/leanr_olean/tests/check_fixtures.rs` (port to id kernel: decode → `intern_module` per module, **dropping each decoded module before the next** — this is the memory-win line; same fixtures, same expected verdicts)

**Interfaces:**
- Produces: the id kernel IS the kernel. `lib.rs` exports: `Environment`, `TypeChecker`, `replay`, `ConstantInfo` (id form) etc. from the moved modules; `bank` keeps exporting `Store`, ids, bridges. The Arc `Expr`/`Name`/`Level`/`Syntax` types stay exported (decoder boundary). `constant_info_eq` export switches to the id version (Arc callers are gone). CLI behavior: `leanr check` output strings unchanged (errors carry the same `Arc<Name>` payloads).

- [ ] **Step 1: `git mv` the modules over their predecessors**, fix `lib.rs`/`bank/mod.rs` module decls and exports.
- [ ] **Step 2: Chase compile errors across the workspace** (`cargo check --workspace`) — every fix is mechanical rewiring per the Interfaces block; no logic changes. The old Arc-kernel-only tests that tested deleted code (e.g. `intern.rs` tests) are deleted; dual harnesses in the moved tests now compare against... nothing — strip the dual harness back to direct assertions on the id kernel (the harness pattern makes this mechanical: keep the id path, inline the expected values the Arc path produced).
- [ ] **Step 3: Port `check_fixtures.rs`** per the Files note (per-module intern + drop).
- [ ] **Step 4: Run the full gate:** `mise run ci`. Everything green — same fixture verdicts as before the flip (the dual gate in Task 7 already proved equality; this step proves the rewiring didn't change inputs).
- [ ] **Step 5: Update docs:** `ARCHITECTURE.md` (bank is no longer "standalone, not wired in" — it is the kernel representation; Arc types are the decoder boundary until phase 3), `AGENTS.md` if it names files that moved.
- [ ] **Step 6: Commit:** `git commit -m "feat!: flip kernel to id-based term-bank representation; delete Arc checker and interner (migration Task 8)"`

---

### Task 9: Acceptance

**Files:** none (controller-run measurements; record results in the PR description and `docs/superpowers/specs/2026-07-06-term-bank-kernel-migration-design.md` under a new "## Results" section)

- [ ] **Step 1: Canary.** Run with a watchdog and memory cap: `/usr/bin/time -v cargo run --release -p leanr_cli -- check Init.Data.Char.Ordinal` (use the repo's actual check invocation — see `mise tasks` for the canonical run task). Expected: exit 0; record "Maximum resident set size". Must be far below the pod limit (the old behavior was a >25 GiB kill on one declaration).
- [ ] **Step 2: Full sweep.** `mise run sweep:stdlib` equivalent for check (find the task: `mise tasks | grep -i check`); expected: exit 0, `checked 2433 modules, ...`, peak RSS **< 32 GiB** (record exact peak, wall-clock, declaration count). ≤ 6 GiB is phase 3's bar — record the number either way; if it already lands ≤ 6 GiB, phase 3's scope shrinks to the decoder rewrite alone.
- [ ] **Step 3: Append the Results section to the spec, commit:** `git commit -m "docs: phase-2 acceptance results (canary + full sweep peak RSS)"`
- [ ] **Step 4: Finish the branch** — use superpowers:finishing-a-development-branch (PR against main, like phase 1's PR #1).
