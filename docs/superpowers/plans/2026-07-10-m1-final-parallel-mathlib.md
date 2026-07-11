# M1-final — Parallel Checking + Mathlib-Scale Sweep — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `leanr check` a multi-threaded checker that re-checks all of pinned Mathlib green, faster than `lean4checker`'s best run, within 32 GiB — with verdict semantics provably identical to sequential `replay()`.

**Architecture:** After the closure is decoded once into the persistent bank, the bank is frozen and shared read-only. Decoded constants become a gated table (`CheckedConstants`): each entry carries an `AtomicBool` admitted flag, and the type checker's `EnvView` consults the table so a check sees only its already-admitted dependencies. A new `leanr_check` crate builds a dependency DAG (via the existing `used_constants`) and drives a std-thread worker pool over it. Def/axiom/theorem/opaque checks are fully lock-free; inductive/quotient blocks serialize behind one promotion mutex to canonicalize their regenerated survivors into the persistent store and compare them against the decoded twins with the existing `constant_info_eq`.

**Tech Stack:** Rust (edition 2021, rustc 1.96.1), `std::thread` + `std::sync` (atomics, `Mutex`, channels) — no rayon, no new external deps. `clap` (CLI). Mathlib via `elan`/`lake`. `lean4checker` as the benchmark oracle.

**Spec:** `docs/superpowers/specs/2026-07-10-m1-final-parallel-mathlib-design.md`

## Global Constraints

- `leanr_kernel` depends on **no** workspace crate and **no** new external dep (std atomics/Mutex only). It is the TCB.
- `.olean`-derived values are untrusted: no `panic!`/`unwrap`/`expect`/indexing on untrusted-derived values; no unguarded recursion (use `RecGuard`); no deadlock or livelock on hostile graphs; allocation bounded by input size.
- Verdict semantics are defined by sequential `replay()` (`crate::replay`, oracle `src/Lean/Replay.lean`); any divergence is a correctness bug.
- The Mathlib commit pin is a project constant, revisited only at a milestone boundary.
- Per commit: `mise run lint` (`cargo fmt --all --check` + `cargo clippy --workspace --all-targets -- -D warnings`) must pass. Where a task says so: `mise run ci` (adds `test`, `lint:deps`, `scan:secrets`).
- Conventional-commit prefixes (`feat:`, `refactor:`, `test:`, `docs:`, `chore:`, `feat!:`/`refactor!:` for breaking).
- New public kernel APIs get rustdoc citing the oracle/spec line they mirror, matching the density of surrounding code.

---

## File Structure

**`leanr_kernel` (modified):**
- Create `crates/leanr_kernel/src/checked.rs` — `ConstSource<'a>` enum + `CheckedConstants` gated table. The only new kernel data structure.
- Modify `crates/leanr_kernel/src/tc.rs` — `EnvView.consts` becomes `ConstSource`; derive `Clone, Copy` on `EnvView`; `EnvView::get` matches the enum.
- Modify `crates/leanr_kernel/src/env.rs` — extract `check_declaration` + `Admitted`; `add_decl` becomes check+commit; `view()` wraps `consts` in `ConstSource::Plain`.
- Modify `crates/leanr_kernel/src/inductive.rs` — `extend_view` propagates `ConstSource`.
- Modify `crates/leanr_kernel/src/lib.rs` — export `checked::{CheckedConstants, ConstSource}`, `env::{check_declaration, Admitted}`.

**`leanr_check` (new crate):**
- Create `crates/leanr_check/Cargo.toml`, `crates/leanr_check/src/lib.rs` — public entry `check_parallel`.
- Create `crates/leanr_check/src/graph.rs` — `DepGraph`, `Task`, `TaskKind`, block grouping (single-threaded, deterministic).
- Create `crates/leanr_check/src/schedule.rs` — worker pool, ready queue, cancellation, promotion mutex, stats.
- Create `crates/leanr_check/tests/graph_tests.rs`, `crates/leanr_check/tests/schedule_tests.rs`.

**`leanr_cli` (modified):**
- Modify `crates/leanr_cli/src/main.rs` — `--jobs N`; route `check` through `leanr_check`; progress counter.
- Modify `crates/leanr_cli/Cargo.toml` — add `leanr_check` dep.

**Repo:**
- Create `mathlib-pin` (repo root).
- Modify `mise.toml` — `mathlib:fetch`, `check:mathlib`, `bench:mathlib`.
- Create `scripts/bench-mathlib.sh`.
- Modify `Cargo.toml` (workspace members), `ARCHITECTURE.md`, `docs/THREAT_MODEL.md`.

---

## Task 1: Generalize `EnvView` over its constant source

Pure refactor — no behavior change. Introduces the `ConstSource` seam the gated table will plug into, keeping all existing tests green (everything uses the `Plain` variant).

**Files:**
- Create: `crates/leanr_kernel/src/checked.rs`
- Modify: `crates/leanr_kernel/src/tc.rs:287-299` (`EnvView` struct + `get`)
- Modify: `crates/leanr_kernel/src/inductive.rs:750-755` (`extend_view`)
- Modify: `crates/leanr_kernel/src/env.rs:331-338` (`view`)
- Modify: `crates/leanr_kernel/src/lib.rs` (module + re-export)

**Interfaces:**
- Produces: `ConstSource<'a>` (`Copy`) with `Plain(&'a HashMap<NameId, ConstantInfo>)` and `Gated(&'a CheckedConstants)` variants and `fn get(&self, NameId) -> Option<&'a ConstantInfo>`. `EnvView<'a>` becomes `Copy` with `consts: ConstSource<'a>`.

- [ ] **Step 1: Create `checked.rs` with `ConstSource` (gated variant stubbed)**

Create `crates/leanr_kernel/src/checked.rs`:

```rust
//! The gated declaration table (`CheckedConstants`) and the `ConstSource`
//! seam the checker's `EnvView` consults. Spec:
//! docs/superpowers/specs/2026-07-10-m1-final-parallel-mathlib-design.md
//! (§Components, §Key enabling observation). `CheckedConstants` is
//! populated in Task 2; this task only introduces the enum so `EnvView`
//! can be generalized without a behavior change.

use std::collections::HashMap;

use crate::bank::NameId;
use crate::ConstantInfo;

/// Where an `EnvView` resolves a `NameId` to a `ConstantInfo`.
/// `Plain` is the sequential environment's plain map (identical behavior
/// to the pre-refactor `&HashMap`); `Gated` is the parallel driver's
/// admitted-flag-gated table (Task 2).
#[derive(Clone, Copy)]
pub enum ConstSource<'a> {
    Plain(&'a HashMap<NameId, ConstantInfo>),
    Gated(&'a CheckedConstants),
}

impl<'a> ConstSource<'a> {
    pub fn get(&self, n: NameId) -> Option<&'a ConstantInfo> {
        match self {
            ConstSource::Plain(m) => m.get(&n),
            ConstSource::Gated(c) => c.get(n),
        }
    }
}

/// Placeholder filled in by Task 2. Present now only so `ConstSource`'s
/// `Gated` variant type-checks.
pub struct CheckedConstants {
    map: HashMap<NameId, ConstantInfo>,
}

impl CheckedConstants {
    pub fn get(&self, n: NameId) -> Option<&ConstantInfo> {
        self.map.get(&n)
    }
}
```

- [ ] **Step 2: Register the module and re-export**

In `crates/leanr_kernel/src/lib.rs`, add `pub mod checked;` next to the other `pub mod` lines, and add to the exports:

```rust
pub use checked::{CheckedConstants, ConstSource};
```

- [ ] **Step 3: Generalize `EnvView` (tc.rs:287-299)**

Replace the struct + `get` with:

```rust
/// The environment view the checker consults (brief's Task 4 interface).
#[derive(Clone, Copy)]
pub struct EnvView<'a> {
    pub consts: crate::ConstSource<'a>,
    pub extra: Option<&'a std::collections::HashMap<NameId, ConstantInfo>>,
    pub quot_initialized: bool,
    pub store: &'a Store,
}

impl<'a> EnvView<'a> {
    pub fn get(&self, n: NameId) -> Option<&'a ConstantInfo> {
        self.extra
            .and_then(|e| e.get(&n))
            .or_else(|| self.consts.get(n))
    }
```

(Leave `get_with` and every other method below unchanged.)

- [ ] **Step 4: Update the two production construction sites**

`crates/leanr_kernel/src/env.rs`, `view()` (around line 332): change `consts: &self.constants,` to `consts: crate::ConstSource::Plain(&self.constants),`.

`crates/leanr_kernel/src/inductive.rs`, `extend_view` (around line 751): it currently sets `consts: view.consts`. Since `EnvView` is now `Copy` and `consts` is `ConstSource` (also `Copy`), `consts: view.consts` still compiles unchanged — verify it reads `consts: view.consts,` and leave it.

- [ ] **Step 5: Update in-crate test construction sites**

Search and fix every remaining `EnvView {` literal:

Run: `grep -rn "EnvView {" crates/leanr_kernel/src/`

For each `consts: &<map>,` in a test, change to `consts: leanr_kernel::ConstSource::Plain(&<map>),` (or `crate::ConstSource::Plain` for in-crate `#[cfg(test)]` modules).

- [ ] **Step 6: Build and run the full kernel suite — expect PASS (no behavior change)**

Run: `cargo test -p leanr_kernel`
Expected: PASS — same counts as before this task.

- [ ] **Step 7: Lint**

Run: `mise run lint`
Expected: clean.

- [ ] **Step 8: Commit**

```bash
git add crates/leanr_kernel/src/checked.rs crates/leanr_kernel/src/tc.rs crates/leanr_kernel/src/env.rs crates/leanr_kernel/src/inductive.rs crates/leanr_kernel/src/lib.rs
git commit -m "refactor(kernel): generalize EnvView over a ConstSource seam"
```

---

## Task 2: `CheckedConstants` gated table

**Files:**
- Modify: `crates/leanr_kernel/src/checked.rs`
- Test: `crates/leanr_kernel/src/checked.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `ConstSource::Gated(&CheckedConstants)` (Task 1).
- Produces:
  - `CheckedConstants::new(map: HashMap<NameId, ConstantInfo>) -> CheckedConstants`
  - `fn get(&self, n: NameId) -> Option<&ConstantInfo>` — admitted-gated (`Acquire`).
  - `fn get_decoded(&self, n: NameId) -> Option<&ConstantInfo>` — ungated (dependency pass / structural compare).
  - `fn admit(&self, n: NameId)` — sets the flag (`Release`); `&self`.
  - `fn contains(&self, n: NameId) -> bool` — ungated key check.
  - `fn iter_decoded(&self) -> impl Iterator<Item = (&NameId, &ConstantInfo)>`
  - `fn len(&self) -> usize`
  - `CheckedConstants: Sync` (std atomics only).

- [ ] **Step 1: Write the failing tests**

Replace the placeholder `mod tests` slot at the end of `checked.rs` with:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::bank::Store;

    // Build a table with two axioms `A`, `B` interned into a persistent store.
    fn table() -> (CheckedConstants, NameId, NameId) {
        let mut st = Store::persistent();
        let a = st.intern_name(None, &crate::Name::mk_str("A")).unwrap().unwrap();
        let b = st.intern_name(None, &crate::Name::mk_str("B")).unwrap().unwrap();
        let ty = st.expr_sort_zero(None).unwrap();
        let mk = |n: NameId| {
            ConstantInfo::Axiom(crate::AxiomVal {
                val: crate::ConstantVal { name: n, level_params: vec![], ty },
                is_unsafe: false,
            })
        };
        let mut map = std::collections::HashMap::new();
        map.insert(a, mk(a));
        map.insert(b, mk(b));
        (CheckedConstants::new(map), a, b)
    }

    #[test]
    fn unadmitted_is_invisible_to_gated_get() {
        let (t, a, _b) = table();
        assert!(t.get(a).is_none());
        assert!(t.get_decoded(a).is_some());
        assert!(t.contains(a));
    }

    #[test]
    fn admit_makes_gated_get_visible() {
        let (t, a, b) = table();
        t.admit(a);
        assert!(t.get(a).is_some());
        assert!(t.get(b).is_none());
    }

    #[test]
    fn unknown_name_never_visible() {
        let (t, _a, _b) = table();
        let mut other = Store::persistent();
        let z = other.intern_name(None, &crate::Name::mk_str("Z")).unwrap().unwrap();
        assert!(t.get(z).is_none());
        t.admit(z); // no-op, must not panic
        assert!(t.get(z).is_none());
    }
}
```

If `Name::mk_str` / `Store::expr_sort_zero` / `Store::persistent` have different exact names in this crate, adjust to the real constructors (grep `impl Name`, `impl Store`); the test's intent is a two-entry table.

- [ ] **Step 2: Run — expect FAIL (compile error: `new`/`admit`/`get_decoded`/`contains` missing)**

Run: `cargo test -p leanr_kernel checked::tests`
Expected: FAIL to compile.

- [ ] **Step 3: Implement `CheckedConstants`**

Replace the placeholder struct/impl in `checked.rs` with:

```rust
use std::sync::atomic::{AtomicBool, Ordering};

/// The parallel driver's declaration table: every decoded constant of the
/// check closure, each gated by an admitted flag. The `map` is immutable
/// after `new`; only the flags flip (false -> true, once). `Sync` by
/// construction (std atomics), so `&CheckedConstants` crosses threads.
/// A `get` returns an entry only once its flag is set, so a checker
/// consulting it (via `ConstSource::Gated`) sees exactly the admitted
/// prefix — spec §Key enabling observation.
pub struct CheckedConstants {
    map: HashMap<NameId, ConstantInfo>,
    admitted: HashMap<NameId, AtomicBool>,
}

impl CheckedConstants {
    pub fn new(map: HashMap<NameId, ConstantInfo>) -> CheckedConstants {
        let admitted = map.keys().map(|&n| (n, AtomicBool::new(false))).collect();
        CheckedConstants { map, admitted }
    }

    /// Admitted-gated lookup (`Acquire` pairs with `admit`'s `Release`).
    pub fn get(&self, n: NameId) -> Option<&ConstantInfo> {
        match self.admitted.get(&n) {
            Some(flag) if flag.load(Ordering::Acquire) => self.map.get(&n),
            _ => None,
        }
    }

    /// Ungated lookup — the decoded constant regardless of admission.
    /// Used by the dependency pass and the decoded-vs-regenerated compare.
    pub fn get_decoded(&self, n: NameId) -> Option<&ConstantInfo> {
        self.map.get(&n)
    }

    pub fn contains(&self, n: NameId) -> bool {
        self.map.contains_key(&n)
    }

    /// Set `n`'s admitted flag. A name not in the table is a no-op (the
    /// caller only ever admits names it took from the table). `&self`:
    /// the flag is the only mutable state and it is atomic.
    pub fn admit(&self, n: NameId) {
        if let Some(flag) = self.admitted.get(&n) {
            flag.store(true, Ordering::Release);
        }
    }

    pub fn iter_decoded(&self) -> impl Iterator<Item = (&NameId, &ConstantInfo)> {
        self.map.iter()
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}
```

- [ ] **Step 4: Run — expect PASS**

Run: `cargo test -p leanr_kernel checked::tests`
Expected: PASS.

- [ ] **Step 5: Assert `Sync` at compile time**

Add to `checked.rs` (outside the test module):

```rust
const _: fn() = || {
    fn assert_sync<T: Sync>() {}
    assert_sync::<CheckedConstants>();
};
```

Run: `cargo build -p leanr_kernel`
Expected: compiles (proves `CheckedConstants: Sync`).

- [ ] **Step 6: Lint + commit**

Run: `mise run lint`

```bash
git add crates/leanr_kernel/src/checked.rs
git commit -m "feat(kernel): CheckedConstants admitted-flag-gated declaration table"
```

---

## Task 3: Split `add_decl` into `check_declaration` + commit

**Files:**
- Modify: `crates/leanr_kernel/src/env.rs:366-487` (`add_decl`)
- Modify: `crates/leanr_kernel/src/lib.rs` (export `check_declaration`, `Admitted`)
- Test: `crates/leanr_kernel/src/env/tests.rs`

**Interfaces:**
- Consumes: `EnvView` (Task 1, now `Copy`), `Store`, `Declaration`.
- Produces:
  - `pub struct Admitted { pub survivors: Vec<ConstantInfo>, pub quot_init: bool }` — `survivors` are scratch-region `ConstantInfo`s the caller must promote; `quot_init` true iff the declaration was `Declaration::Quot`.
  - `pub fn check_declaration(view: EnvView, scratch: &mut Store, d: Declaration) -> Result<Admitted, KernelError>` — everything `add_decl` did except the `add_core` promotion + the `quot_initialized` write.

- [ ] **Step 1: Write the failing test**

In `crates/leanr_kernel/src/env/tests.rs`, add (adapt the fixture helper to the file's existing ones for building a trusted base env + a checkable `Declaration` — reuse whatever `nat_decl`/`testenv` helper the file already uses):

```rust
#[test]
fn check_declaration_returns_survivor_without_mutating_env() {
    // A trusted base env with `Nat` admitted, and a simple axiom decl
    // referencing only already-admitted constants.
    let mut env = /* existing helper that yields an Environment with deps */;
    let before = env.len();
    let d: Declaration = /* existing helper: a checkable axiom Declaration */;

    let mut scratch = crate::bank::Store::scratch();
    let admitted = crate::check_declaration(env.view(), &mut scratch, d).unwrap();

    assert_eq!(admitted.survivors.len(), 1);
    assert!(!admitted.quot_init);
    // check_declaration must NOT have inserted anything into env.
    assert_eq!(env.len(), before);
}
```

- [ ] **Step 2: Run — expect FAIL (compile error: `check_declaration` missing)**

Run: `cargo test -p leanr_kernel check_declaration_returns_survivor -- --nocapture`
Expected: FAIL to compile.

- [ ] **Step 3: Add `Admitted` and `check_declaration`, rewrite `add_decl`**

In `env.rs`, above `add_decl`, add:

```rust
/// What `check_declaration` produces: the survivor `ConstantInfo`(s) to
/// promote+insert (scratch-region ids), and whether the declaration
/// initialized quotients. Splitting the check from the commit lets the
/// parallel driver (`leanr_check`) run the check half against a frozen
/// store and admit via flag flips instead of mutating a shared env.
pub struct Admitted {
    pub survivors: Vec<ConstantInfo>,
    pub quot_init: bool,
}
```

Convert the current `add_decl` **body** into a free function `check_declaration`. Mechanically: take the existing `add_decl`'s `let mut scratch = Store::scratch();` out, and move the `let info = { match d { ... } };` block into the new function, applying exactly these three edits to the match's exit points:

1. The `Declaration::Quot` arm currently ends:
   ```rust
       for ci in admitted { self.add_core(&scratch, ci)?; }
       self.quot_initialized = true;
       return Ok(());
   ```
   becomes:
   ```rust
       return Ok(Admitted { survivors: admitted, quot_init: true });
   ```
2. The `Declaration::Inductive { .. }` arm currently ends:
   ```rust
       for ci in admitted { self.add_core(&scratch, ci)?; }
       return Ok(());
   ```
   becomes:
   ```rust
       return Ok(Admitted { survivors: admitted, quot_init: false });
   ```
3. The single-info fall-through currently ends (after the match):
   ```rust
       };
       self.add_core(&scratch, info)?;
       Ok(())
   ```
   becomes:
   ```rust
       };
       Ok(Admitted { survivors: vec![info], quot_init: false })
   ```

Inside the moved arms replace every `self.view()` with the `view` parameter (it is `Copy`, so pass it by value where `TypeChecker::new` consumes it and by `&view` / `view` where `check_constant_val_pre` wants `&EnvView`), and every `&mut scratch` / `&scratch` with the `scratch` parameter (a `&mut Store`; use `&*scratch` where an immutable `&Store` is wanted). The resulting signature:

```rust
/// The check half of `Environment::add_decl` (oracle: environment.cpp
/// per-kind add_* ). Runs every kernel check against `view` + a caller-
/// owned per-declaration `scratch` store, and returns the survivor
/// `ConstantInfo`(s) to admit — WITHOUT promoting them or touching any
/// environment state. `Environment::add_decl` is the check+commit
/// wrapper; `leanr_check` calls this directly.
pub fn check_declaration(
    view: EnvView,
    scratch: &mut Store,
    d: Declaration,
) -> Result<Admitted, KernelError> {
    let info = {
        match d {
            // ... moved arms, per the three edits above ...
        }
    };
    Ok(Admitted { survivors: vec![info], quot_init: false })
}
```

Then rewrite `Environment::add_decl` as the thin wrapper:

```rust
pub fn add_decl(&mut self, d: Declaration) -> Result<(), KernelError> {
    let mut scratch = Store::scratch();
    let Admitted { survivors, quot_init } = {
        let view = self.view();
        check_declaration(view, &mut scratch, d)?
    };
    for ci in survivors {
        self.add_core(&scratch, ci)?;
    }
    if quot_init {
        self.quot_initialized = true;
    }
    Ok(())
}
```

- [ ] **Step 4: Export the new API**

In `lib.rs`, add to the `pub use env::{...}` line: `check_declaration, Admitted`.

- [ ] **Step 5: Run the new test + full kernel suite — expect PASS**

Run: `cargo test -p leanr_kernel`
Expected: PASS — `add_decl`'s behavior is unchanged, so `replay`/`check_fixtures` and every existing test stay green; the new test passes.

- [ ] **Step 6: Lint + commit**

Run: `mise run lint`

```bash
git add crates/leanr_kernel/src/env.rs crates/leanr_kernel/src/env/tests.rs crates/leanr_kernel/src/lib.rs
git commit -m "refactor(kernel): split add_decl into check_declaration + commit"
```

---

## Task 4: `leanr_check` crate + dependency graph (single-threaded)

Build the DAG and task grouping deterministically, with no threads yet. This task's deliverable is a graph whose task set matches what `replay()` admits.

**Files:**
- Create: `crates/leanr_check/Cargo.toml`
- Create: `crates/leanr_check/src/lib.rs`
- Create: `crates/leanr_check/src/graph.rs`
- Create: `crates/leanr_check/tests/graph_tests.rs`
- Modify: `Cargo.toml` (workspace members)

**Interfaces:**
- Consumes: `leanr_kernel::{CheckedConstants, ConstantInfo, used_constants, bank::NameId, ...}`.
- Produces (in `graph.rs`):
  - `type TaskId = usize;`
  - `enum TaskKind { Simple(NameId), InductiveBlock { members: Vec<NameId>, ctors: Vec<NameId> }, Quot { names: Vec<NameId>, eq: NameId } }`
  - `struct Task { pub id: TaskId, pub kind: TaskKind, pub deps: Vec<TaskId> }`
  - `struct DepGraph { pub tasks: Vec<Task>, pub name_to_task: HashMap<NameId, TaskId> }`
  - `fn build_graph(store: &Store, table: &CheckedConstants) -> Result<DepGraph, KernelError>`

- [ ] **Step 1: Create the crate manifest and register it**

Create `crates/leanr_check/Cargo.toml`:

```toml
[package]
name = "leanr_check"
version.workspace = true
edition.workspace = true
license.workspace = true

[dependencies]
leanr_kernel = { version = "0.1.0", path = "../leanr_kernel" }

[dev-dependencies]
leanr_kernel = { version = "0.1.0", path = "../leanr_kernel" }
```

In the root `Cargo.toml`, add `"crates/leanr_check"` to `members`.

- [ ] **Step 2: Write the failing graph tests**

Create `crates/leanr_check/tests/graph_tests.rs`. Build a small `CheckedConstants` by hand (mirror the kernel's `env::tests`/`testenv` fixture style — a chain `A : Sort`, `B : A-referencing`, plus one inductive with a constructor) and assert:

```rust
use leanr_check::graph::{build_graph, TaskKind};

// Helper builds a CheckedConstants with: axiom A, axiom B (uses A),
// inductive Foo with ctor Foo.mk, and returns (store, table, names).
mod fixture; // small module in tests/ that hand-builds the table

#[test]
fn simple_dependency_becomes_an_edge() {
    let (store, table, n) = fixture::chain_a_b();
    let g = build_graph(&store, &table).unwrap();
    let ta = g.name_to_task[&n.a];
    let tb = g.name_to_task[&n.b];
    assert!(g.tasks[tb].deps.contains(&ta));
    assert!(!g.tasks[ta].deps.contains(&tb));
}

#[test]
fn inductive_block_groups_type_and_ctor_into_one_task() {
    let (store, table, n) = fixture::inductive_foo();
    let g = build_graph(&store, &table).unwrap();
    let tfoo = g.name_to_task[&n.foo];
    // The constructor maps to the SAME task as its inductive.
    assert_eq!(g.name_to_task[&n.foo_mk], tfoo);
    match &g.tasks[tfoo].kind {
        TaskKind::InductiveBlock { members, ctors } => {
            assert!(members.contains(&n.foo));
            assert!(ctors.contains(&n.foo_mk));
        }
        _ => panic!("expected an inductive block task"),
    }
}

#[test]
fn missing_dependency_is_an_error() {
    let (store, table) = fixture::dangling_ref(); // B references absent C
    let err = build_graph(&store, &table).unwrap_err();
    assert!(matches!(err, leanr_kernel::KernelError::MissingConstant(_)));
}
```

- [ ] **Step 3: Run — expect FAIL (compile error: `leanr_check` empty)**

Run: `cargo test -p leanr_check --test graph_tests`
Expected: FAIL to compile.

- [ ] **Step 4: Implement `graph.rs`**

Create `crates/leanr_check/src/graph.rs`:

```rust
//! Dependency DAG over a frozen `CheckedConstants`, grouping mutual
//! inductive blocks (and their constructors + recursors) into single
//! tasks — the same admission units `crate::replay` processes. Spec
//! §Architecture Workstream 1 step 4. Built single-threaded and
//! deterministically (names sorted) so the task set is reproducible.

use std::collections::HashMap;

use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{used_constants, CheckedConstants, ConstantInfo, KernelError, RecGuard};

pub type TaskId = usize;

pub enum TaskKind {
    Simple(NameId),
    InductiveBlock { members: Vec<NameId>, ctors: Vec<NameId> },
    Quot { names: Vec<NameId>, eq: NameId },
}

pub struct Task {
    pub id: TaskId,
    pub kind: TaskKind,
    /// Names this task admits (flags to flip on success): for Simple, the
    /// one name; for InductiveBlock, members + ctors + recursors; for
    /// Quot, every quotient constant.
    pub admits: Vec<NameId>,
    pub deps: Vec<TaskId>,
}

pub struct DepGraph {
    pub tasks: Vec<Task>,
    pub name_to_task: HashMap<NameId, TaskId>,
}

pub fn build_graph(store: &Store, table: &CheckedConstants) -> Result<DepGraph, KernelError> {
    // Deterministic iteration: sort names by raw bits.
    let mut names: Vec<NameId> = table.iter_decoded().map(|(&n, _)| n).collect();
    names.sort_by_key(|n| n.bits());

    // 1. Assign every name to exactly one task, grouping inductive blocks.
    //    `name_to_task` maps members, ctors, AND recursors to their block.
    let mut name_to_task: HashMap<NameId, TaskId> = HashMap::new();
    let mut tasks: Vec<Task> = Vec::new();
    let mut g = RecGuard::new();

    for &n in &names {
        if name_to_task.contains_key(&n) {
            continue; // already claimed by an inductive block
        }
        let ci = table.get_decoded(n).expect("name came from the table");
        match ci {
            ConstantInfo::Induct(iv) => {
                let id = tasks.len();
                // Gather block members (iv.val.all) and their ctors.
                let mut members: Vec<NameId> = Vec::new();
                let mut ctors: Vec<NameId> = Vec::new();
                for &m in &iv.all {
                    members.push(m);
                    let ConstantInfo::Induct(miv) = table
                        .get_decoded(m)
                        .ok_or_else(|| KernelError::MissingConstant(store.to_name(None, Some(m))))?
                    else {
                        return Err(KernelError::MissingConstant(store.to_name(None, Some(m))));
                    };
                    ctors.extend_from_slice(&miv.ctors);
                }
                let mut admits = members.clone();
                admits.extend_from_slice(&ctors);
                // Recursors: a recursor references its inductive in its
                // type, so any decoded Rec whose used_constants meets this
                // block's member set belongs here. Claimed below in pass 1b.
                for &nm in members.iter().chain(ctors.iter()) {
                    name_to_task.insert(nm, id);
                }
                tasks.push(Task { id, kind: TaskKind::InductiveBlock { members, ctors }, admits, deps: Vec::new() });
            }
            ConstantInfo::Ctor(_) => {
                // Claimed by its inductive's block once that block is built;
                // if we reach it first, force its block by visiting induct.
                // (Handled by pass ordering: see below.)
                continue;
            }
            ConstantInfo::Rec(_) => continue, // claimed in pass 1b
            ConstantInfo::Quot(_) => {
                let id = tasks.len();
                // `Eq` = Name::Str { parent: Anonymous, part: "Eq" } — the
                // same name replay.rs::eq_name() builds.
                let eq_name = std::sync::Arc::new(leanr_kernel::Name::Str {
                    parent: std::sync::Arc::new(leanr_kernel::Name::Anonymous),
                    part: "Eq".to_string(),
                });
                let eq = store.intern_name(None, &eq_name)?.ok_or(KernelError::BankExhausted)?;
                // All quotient constants share one task.
                let quot_names: Vec<NameId> = names
                    .iter()
                    .copied()
                    .filter(|&q| matches!(table.get_decoded(q), Some(ConstantInfo::Quot(_))))
                    .collect();
                for &q in &quot_names {
                    name_to_task.insert(q, id);
                }
                tasks.push(Task { id, kind: TaskKind::Quot { names: quot_names.clone(), eq }, admits: quot_names, deps: Vec::new() });
            }
            _ => {
                let id = tasks.len();
                name_to_task.insert(n, id);
                tasks.push(Task { id, kind: TaskKind::Simple(n), admits: vec![n], deps: Vec::new() });
            }
        }
    }

    // Pass 1b: claim any not-yet-claimed ctor/rec by resolving to a block.
    for &n in &names {
        if name_to_task.contains_key(&n) {
            continue;
        }
        let ci = table.get_decoded(n).expect("name from table");
        let block = resolve_block(store, table, &name_to_task, n, ci, &mut g)?;
        name_to_task.insert(n, block);
        // Also record it in the block's `admits` so its flag is set.
        tasks[block].admits.push(n);
    }

    // 2. Edges: for every name, its used_constants → the owning task.
    for &n in &names {
        let ci = table.get_decoded(n).expect("name from table");
        let owner = name_to_task[&n];
        for dep in used_constants(store, None, ci) {
            let Some(&dep_task) = name_to_task.get(&dep) else {
                return Err(KernelError::MissingConstant(store.to_name(None, Some(dep))));
            };
            if dep_task != owner && !tasks[owner].deps.contains(&dep_task) {
                tasks[owner].deps.push(dep_task);
            }
        }
    }

    Ok(DepGraph { tasks, name_to_task })
}

/// Resolve a stray constructor/recursor to its inductive block: its
/// `used_constants` intersect the members of exactly one block.
fn resolve_block(
    store: &Store,
    _table: &CheckedConstants,
    name_to_task: &HashMap<NameId, TaskId>,
    n: NameId,
    ci: &ConstantInfo,
    _g: &mut RecGuard,
) -> Result<TaskId, KernelError> {
    match ci {
        ConstantInfo::Ctor(cv) => name_to_task
            .get(&cv.induct)
            .copied()
            .ok_or_else(|| KernelError::MissingConstant(store.to_name(None, Some(cv.induct)))),
        ConstantInfo::Rec(_) => {
            for dep in used_constants(store, None, ci) {
                if let Some(&t) = name_to_task.get(&dep) {
                    return Ok(t); // first inductive-owned dep is its block
                }
            }
            Err(KernelError::MissingConstant(store.to_name(None, Some(n))))
        }
        _ => Err(KernelError::MissingConstant(store.to_name(None, Some(n)))),
    }
}
```

Note the pass-ordering subtlety: pass 1 may hit a `Ctor`/`Rec` before its inductive. `continue` leaves it unclaimed; pass 1b resolves it. But a `Ctor` needs its inductive's task to exist first — pass 1 always creates the block when it reaches the `Induct` (which it will, since the block's members include an `Induct`), and pass 1b runs after all blocks exist. For `resolve_block`'s `Rec` case to find an inductive-owned dep, blocks must be built — they are (pass 1b is strictly after pass 1). If `NameId::raw()` isn't the accessor name, use the real one (grep `impl NameId`). If `Name::mk_str` differs, use the real constructor from Task 2.

- [ ] **Step 5: Create `lib.rs` exposing the module**

Create `crates/leanr_check/src/lib.rs`:

```rust
//! Parallel kernel-check driver over a frozen `CheckedConstants`.
//! Spec: docs/superpowers/specs/2026-07-10-m1-final-parallel-mathlib-design.md
pub mod graph;
```

- [ ] **Step 6: Run the graph tests — expect PASS**

Run: `cargo test -p leanr_check --test graph_tests`
Expected: PASS.

- [ ] **Step 7: Lint + commit**

Run: `mise run lint`

```bash
git add crates/leanr_check Cargo.toml
git commit -m "feat(check): leanr_check crate + dependency DAG with inductive-block grouping"
```

---

## Task 5: Worker-pool scheduler + serialized promote-and-compare

**Files:**
- Create: `crates/leanr_check/src/schedule.rs`
- Modify: `crates/leanr_check/src/lib.rs` (add `mod schedule;` + public `check_parallel`)
- Test: `crates/leanr_check/tests/schedule_tests.rs`

**Interfaces:**
- Consumes: `DepGraph` (Task 4), `check_declaration`/`Admitted` (Task 3), `CheckedConstants` (Task 2), `constant_info_eq`, `promote_constant_info` — **note:** `promote_constant_info` is currently `pub(crate)` in `env.rs`; this task promotes survivors into the shared store, so add a kernel entry point for it (Step 3a).
- Produces:
  - `struct CheckStats { pub checked: usize, pub skipped_unsafe: usize }`
  - `struct CheckFailure { pub decl: NameId, pub error: KernelError }`
  - `fn check_parallel(store: Arc<Store>, table: Arc<CheckedConstants>, graph: DepGraph, jobs: usize, progress: impl Fn(usize) + Send + Sync) -> Result<CheckStats, CheckFailure>`

- [ ] **Step 1: Add a kernel entry point for promotion + a parallel-admit helper**

The parallel driver needs to, under a mutex: promote an inductive/quot block's scratch survivors into the shared persistent store and compare each against its decoded twin. Add to `env.rs` a small free function (keeps promotion logic in the TCB):

```rust
/// Promote a checked survivor into `store` (canonicalizing its ids) and
/// return the persistent-region `ConstantInfo`. The parallel driver calls
/// this under its promotion mutex for inductive/quotient survivors, then
/// compares the result against the decoded twin with `constant_info_eq`
/// (both now persistent-region, so id equality is structural equality).
/// Mirrors `add_core`'s promote step without the env insert.
pub fn promote_into(store: &mut Store, scratch: &Store, ci: &ConstantInfo) -> Result<ConstantInfo, KernelError> {
    promote_constant_info(store, scratch, ci)
}
```

Export it in `lib.rs` (`pub use env::{check_declaration, Admitted, promote_into};`).

Run: `cargo build -p leanr_kernel` → compiles.

- [ ] **Step 2: Write the failing scheduler tests (synthetic DAGs)**

Create `crates/leanr_check/tests/schedule_tests.rs`. These test the scheduler's ordering/liveness independent of the kernel by running `check_parallel` over hand-built graphs of `Simple` tasks whose "check" trivially succeeds (axioms over already-admitted deps):

```rust
use std::sync::Arc;
use leanr_check::{check_parallel, graph::build_graph};

mod fixture; // reuse Task 4's fixture module (copy or share)

#[test]
fn diamond_admits_shared_dep_once_and_all_four() {
    // A ; B<-A ; C<-A ; D<-B,C  (axioms)
    let (store, table, _n) = fixture::diamond();
    let g = build_graph(&store, &table).unwrap();
    let stats = check_parallel(Arc::new(store), Arc::new(table), g, 4, |_| {}).unwrap();
    assert_eq!(stats.checked, 4);
}

#[test]
fn cycle_reports_error_not_hang() {
    // Hand-forge a DepGraph with a 2-cycle (bypass build_graph).
    let (store, table, g) = fixture::forged_cycle();
    let res = check_parallel(Arc::new(store), Arc::new(table), g, 2, |_| {});
    assert!(res.is_err(), "a dependency cycle must be reported, not hang");
}

#[test]
fn single_worker_matches_multi_worker_count() {
    let (store, table, _n) = fixture::wide_fanout(64);
    let g1 = build_graph(&store, &table).unwrap();
    let s = Arc::new(store);
    let t = Arc::new(table);
    let a = check_parallel(s.clone(), t.clone(), g1, 1, |_| {}).unwrap();
    let (store2, table2, _n2) = fixture::wide_fanout(64);
    let g8 = build_graph(&store2, &table2).unwrap();
    let b = check_parallel(Arc::new(store2), Arc::new(table2), g8, 8, |_| {}).unwrap();
    assert_eq!(a.checked, b.checked);
}
```

The `cycle_reports_error_not_hang` test MUST complete quickly; guard the whole test with a wall-clock assertion is unnecessary if the scheduler's drain-detection is correct, but keep the DAG tiny.

- [ ] **Step 3: Run — expect FAIL (compile error: `check_parallel` missing)**

Run: `cargo test -p leanr_check --test schedule_tests`
Expected: FAIL to compile.

- [ ] **Step 4: Implement `schedule.rs`**

Create `crates/leanr_check/src/schedule.rs`:

```rust
//! Worker-pool scheduler over a `DepGraph`. Def/axiom/theorem/opaque
//! tasks run lock-free; inductive/quotient tasks take one shared
//! promotion mutex to canonicalize their regenerated survivors into the
//! frozen store and compare against the decoded twins. Spec §Architecture
//! Workstream 1 step 5, §Error handling. Untrusted input: no panic, no
//! unbounded wait — a drained queue with unfinished tasks is a cycle and
//! is reported, never a hang.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;

use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{
    check_declaration, constant_info_eq, promote_into, Admitted, CheckedConstants, ConstSource,
    ConstantInfo, EnvView, KernelError,
};

use crate::graph::{DepGraph, Task, TaskId, TaskKind};

pub struct CheckStats {
    pub checked: usize,
    pub skipped_unsafe: usize,
}

pub struct CheckFailure {
    pub decl: NameId,
    pub error: KernelError,
}

pub fn check_parallel(
    store: Arc<Store>,
    table: Arc<CheckedConstants>,
    graph: DepGraph,
    jobs: usize,
    progress: impl Fn(usize) + Send + Sync,
) -> Result<CheckStats, CheckFailure> {
    let n_tasks = graph.tasks.len();

    // Per-task remaining-dependency counter; a task is ready at 0.
    let pending: Vec<AtomicUsize> =
        graph.tasks.iter().map(|t| AtomicUsize::new(t.deps.len())).collect();
    // Reverse adjacency: task -> tasks that depend on it.
    let mut dependents: Vec<Vec<TaskId>> = vec![Vec::new(); n_tasks];
    for t in &graph.tasks {
        for &d in &t.deps {
            dependents[d].push(t.id);
        }
    }

    let shared = Arc::new(Shared {
        tasks: graph.tasks,
        pending,
        dependents,
        ready: Mutex::new(ReadyState { queue: Vec::new(), in_flight: 0, done: 0 }),
        cv: Condvar::new(),
        cancel: AtomicBool::new(false),
        failure: Mutex::new(None),
        checked: AtomicUsize::new(0),
        promote_lock: Mutex::new(()),
        store,
        table,
    });

    // Seed ready queue with zero-dependency tasks.
    {
        let mut r = shared.ready.lock().unwrap();
        for (id, p) in shared.pending.iter().enumerate() {
            if p.load(Ordering::Relaxed) == 0 {
                r.queue.push(id);
            }
        }
        shared.cv.notify_all();
    }

    let progress = Arc::new(progress);
    let jobs = jobs.max(1);
    thread::scope(|scope| {
        for _ in 0..jobs {
            let shared = Arc::clone(&shared);
            let progress = Arc::clone(&progress);
            scope.spawn(move || worker(&shared, &*progress));
        }
    });

    if let Some(f) = shared.failure.lock().unwrap().take() {
        return Err(f);
    }
    // Drained with no failure but not all tasks done ⇒ dependency cycle.
    let done = shared.ready.lock().unwrap().done;
    if done != n_tasks {
        // Name any member of an unfinished task for the error.
        let stuck = (0..n_tasks)
            .find(|&i| shared.pending[i].load(Ordering::Relaxed) != 0)
            .and_then(|i| shared.tasks[i].admits.first().copied());
        let decl = stuck.unwrap_or_else(|| NameId::from_index(0, false).unwrap());
        return Err(CheckFailure {
            decl,
            error: KernelError::DependencyCycle(shared.store.to_name(None, Some(decl))),
        });
    }
    Ok(CheckStats {
        checked: shared.checked.load(Ordering::Relaxed),
        skipped_unsafe: 0, // filled by the caller (unsafe/partial are excluded before the table)
    })
}

struct Shared {
    tasks: Vec<Task>,
    pending: Vec<AtomicUsize>,
    dependents: Vec<Vec<TaskId>>,
    ready: Mutex<ReadyState>,
    cv: Condvar,
    cancel: AtomicBool,
    failure: Mutex<Option<CheckFailure>>,
    checked: AtomicUsize,
    promote_lock: Mutex<()>,
    store: Arc<Store>,
    table: Arc<CheckedConstants>,
}

struct ReadyState {
    queue: Vec<TaskId>,
    in_flight: usize,
    done: usize,
}

fn worker(shared: &Shared, progress: &(impl Fn(usize) + ?Sized)) {
    loop {
        // Acquire a ready task, or exit when the run is over.
        let task_id = {
            let mut r = shared.ready.lock().unwrap();
            loop {
                if shared.cancel.load(Ordering::Acquire) {
                    return;
                }
                if let Some(id) = r.queue.pop() {
                    r.in_flight += 1;
                    break id;
                }
                // No ready work: if nothing is in flight, no new work can
                // appear (queue drained). Exit so the scope can join.
                if r.in_flight == 0 {
                    shared.cv.notify_all();
                    return;
                }
                r = shared.cv.wait(r).unwrap();
            }
        };

        let result = run_task(shared, task_id);

        let mut r = shared.ready.lock().unwrap();
        r.in_flight -= 1;
        match result {
            Ok(()) => {
                r.done += 1;
                // Release dependents whose counter hits zero.
                for &dep in &shared.dependents[task_id] {
                    if shared.pending[dep].fetch_sub(1, Ordering::AcqRel) == 1 {
                        r.queue.push(dep);
                    }
                }
                shared.cv.notify_all();
                drop(r);
                progress(shared.checked.load(Ordering::Relaxed));
            }
            Err(f) => {
                let mut slot = shared.failure.lock().unwrap();
                if slot.is_none() {
                    *slot = Some(f);
                }
                shared.cancel.store(true, Ordering::Release);
                shared.cv.notify_all();
                return;
            }
        }
    }
}

fn run_task(shared: &Shared, id: TaskId) -> Result<(), CheckFailure> {
    let task = &shared.tasks[id];
    let view = EnvView {
        consts: ConstSource::Gated(&shared.table),
        extra: None,
        quot_initialized: false, // quot task sets its own view; see below
        store: &shared.store,
    };
    match &task.kind {
        TaskKind::Simple(n) => {
            let ci = shared.table.get_decoded(*n).expect("task name in table");
            let d = declaration_of(ci); // reconstruct a Declaration from the decoded ci
            let mut scratch = Store::scratch();
            check_declaration(view, &mut scratch, d).map_err(|error| CheckFailure { decl: *n, error })?;
            // Survivor is the decoded ci already in the table — just admit.
            shared.checked.fetch_add(1, Ordering::Relaxed);
            shared.table.admit(*n);
            Ok(())
        }
        TaskKind::InductiveBlock { members, ctors } => {
            run_block(shared, id, members, ctors)
        }
        TaskKind::Quot { names, eq } => {
            run_quot(shared, id, names, *eq)
        }
    }
}
```

Then implement `run_block` and `run_quot` (both take the promotion mutex to canonicalize survivors and compare):

```rust
fn run_block(
    shared: &Shared,
    _id: TaskId,
    members: &[NameId],
    ctors: &[NameId],
) -> Result<(), CheckFailure> {
    // Build the inductive Declaration from the decoded members, exactly as
    // replay::replay_inductive does (members' InductiveVal + ctor types).
    let decl = inductive_declaration(shared, members).map_err(|(decl, error)| CheckFailure { decl, error })?;
    let view = EnvView {
        consts: ConstSource::Gated(&shared.table),
        extra: None,
        quot_initialized: false,
        store: &shared.store,
    };
    let mut scratch = Store::scratch();
    let Admitted { survivors, .. } =
        check_declaration(view, &mut scratch, decl).map_err(|error| CheckFailure { decl: members[0], error })?;

    // Serialized promote-and-compare: canonicalize each regenerated
    // survivor into the frozen store and compare against its decoded twin.
    // SAFETY of the &mut: the promotion mutex makes this the sole writer of
    // `store` after freeze. `Arc::get_mut` is unavailable (multiple Arcs),
    // so route promotion through a store handle that permits interior
    // mutation under the lock — see note below.
    {
        let _guard = shared.promote_lock.lock().unwrap();
        let store = store_writer(&shared.store); // see Step 4a
        for surv in &survivors {
            let promoted = promote_into(store, &scratch, surv)
                .map_err(|error| CheckFailure { decl: surv.name(), error })?;
            let decoded = shared
                .table
                .get_decoded(promoted.name())
                .ok_or_else(|| CheckFailure {
                    decl: promoted.name(),
                    error: KernelError::MissingConstant(shared.store.to_name(None, Some(promoted.name()))),
                })?;
            if !constant_info_eq(decoded, &promoted) {
                return Err(CheckFailure {
                    decl: promoted.name(),
                    error: KernelError::ConstructorMismatch(shared.store.to_name(None, Some(promoted.name()))),
                });
            }
        }
    }

    shared.checked.fetch_add(1, Ordering::Relaxed);
    for &m in members.iter().chain(ctors.iter()) {
        shared.table.admit(m);
    }
    for surv in &survivors {
        shared.table.admit(surv.name()); // recursors + regenerated members/ctors
    }
    Ok(())
}
```

`run_quot` follows the same shape but builds `Declaration::Quot`, admits `Eq` first (its task edge guarantees `Eq` is already admitted), and admits every quotient name.

**Step 4a — the shared-store write.** Promotion needs `&mut Store`, but the store is behind `Arc<Store>` shared with all workers. The promotion mutex guarantees a unique writer, but `Arc` won't hand out `&mut`. Resolve this in the kernel, NOT with `unsafe` in the driver: give `Store` an interior-mutable persistent-intern path usable behind `&self` under the caller's external lock — i.e. add `Store::promote_locked(&self, scratch: &Store, ci: &ConstantInfo, _guard: &PromoteGuard) -> Result<ConstantInfo, KernelError>` where the persistent segment's growable arenas sit behind the store's own `Mutex`/`UnsafeCell` with a documented single-writer contract. **This is a kernel-TCB change and must be its own committed step with its own test** (two threads promoting distinct terms under the lock never corrupt the store; property test in `leanr_kernel`). If that is larger than budgeted, the fallback that keeps the driver simple is: build the persistent store as `Arc<Mutex<Store>>` for the *whole* run and have every worker's scratch read through a short-lived lock when resolving persistent ids — but that reintroduces contention on the hot path and is explicitly NOT the chosen design. Prefer the interior-mutable promote path.

> Implementer note: this step is the one place the plan cannot fully pin the code without the store's arena internals in front of you. Read `crates/leanr_kernel/src/bank/terms.rs` + `names.rs` + `levels.rs` + `pools.rs` growth paths first, then choose the minimal interior-mutability boundary. Keep it behind a `PromoteGuard` token so the type system records that promotion happens under the mutex.

- [ ] **Step 5: Wire `lib.rs` and helpers**

Add to `crates/leanr_check/src/lib.rs`:

```rust
pub mod schedule;
pub use schedule::{check_parallel, CheckFailure, CheckStats};
```

Implement the small reconstruction helpers used above — `declaration_of(&ConstantInfo) -> Declaration`, `inductive_declaration(...)`, and the `KernelError::DependencyCycle` variant — mirroring `replay.rs`'s arms (`Declaration::Axiom/Defn/Thm/Opaque` from the matching `*Val`; the inductive block builder is a direct copy of `replay::replay_inductive`'s `types`/`ctor_pairs` construction). Add `KernelError::DependencyCycle(Arc<Name>)` to `error.rs` with a `Display` line `dependency cycle involving '<name>'`.

- [ ] **Step 6: Run the scheduler tests under the thread sanitizer**

Run: `cargo test -p leanr_check --test schedule_tests`
Expected: PASS.

Then, with the nightly used for fuzzing (`.mise.toml` fuzz task documents `nightly-2026-07-01`):

Run: `RUSTFLAGS="-Zsanitizer=thread" cargo +nightly-2026-07-01 test -p leanr_check --test schedule_tests --target x86_64-unknown-linux-gnu`
Expected: PASS, no TSan data-race reports.

If the nightly/target isn't provisioned, record that the TSan run is a controller step and keep the plain run green.

- [ ] **Step 7: Lint + commit**

Run: `mise run lint`

```bash
git add crates/leanr_check crates/leanr_kernel/src/env.rs crates/leanr_kernel/src/error.rs crates/leanr_kernel/src/lib.rs crates/leanr_kernel/src/bank
git commit -m "feat(check): worker-pool scheduler with serialized promote-and-compare"
```

---

## Task 6: CLI `--jobs` + full-stdlib differential gate

**Files:**
- Modify: `crates/leanr_cli/src/main.rs` (`Check` args + `check` fn)
- Modify: `crates/leanr_cli/Cargo.toml` (add `leanr_check`)
- Create: `crates/leanr_cli/tests/parallel_differential.rs`
- Modify: `mise.toml` (`check:stdlib:differential`)

**Interfaces:**
- Consumes: `leanr_check::check_parallel`, `leanr_kernel::replay` (reference).

- [ ] **Step 1: Add `leanr_check` to the CLI manifest**

In `crates/leanr_cli/Cargo.toml` `[dependencies]`, add:

```toml
leanr_check = { version = "0.1.0", path = "../leanr_check" }
```

- [ ] **Step 2: Add `--jobs` and route `check` through the parallel driver**

In `main.rs`, add to the `Check` variant:

```rust
        /// Worker threads (default: available parallelism).
        #[arg(long)]
        jobs: Option<usize>,
        /// Use the sequential reference checker (crate::replay) instead of
        /// the parallel driver. Differential-testing / debugging only.
        #[arg(long)]
        sequential: bool,
```

Thread `jobs`/`sequential` through `check(...)`. After the existing decode + union-fold (which already builds `constants: HashMap<NameId, ConstantInfo>` and `owner`), split:

```rust
    // Exclude unsafe/partial exactly as replay does, before building the table.
    let mut skipped_unsafe = 0usize;
    let mut table_map: HashMap<NameId, ConstantInfo> = HashMap::new();
    for (name, ci) in constants {
        if leanr_kernel::is_unsafe_or_partial(&ci) {
            skipped_unsafe += 1;
        } else {
            table_map.insert(name, ci);
        }
    }

    if sequential {
        // unchanged: fold back and call replay (kept for the differential gate)
        // ... existing replay path ...
        return /* existing */;
    }

    let jobs = jobs.unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1));
    let store = std::sync::Arc::new(std::mem::take(env.store_mut())); // freeze
    let table = std::sync::Arc::new(leanr_kernel::CheckedConstants::new(table_map));
    let graph = match leanr_check::graph::build_graph(&store, &table) {
        Ok(g) => g,
        Err(err) => { eprintln!("error: {err}"); return ExitCode::FAILURE; }
    };
    let counter = std::sync::atomic::AtomicUsize::new(0);
    match leanr_check::check_parallel(store.clone(), table, graph, jobs, |done| {
        // periodic progress (throttled): print every ~1000 decls
        if done % 1000 == 0 { eprintln!("checked {done} declarations"); }
        let _ = &counter;
    }) {
        Ok(stats) => {
            println!("checked {n} modules, {} declarations (skipped {} unsafe/partial)", stats.checked, skipped_unsafe);
            ExitCode::SUCCESS
        }
        Err(f) => {
            let module = owner.get(&f.decl).map(|m| m.to_string()).unwrap_or_else(|| "?".to_string());
            eprintln!("error: {module}: while replaying '{}': {}", store.to_name(None, Some(f.decl)), f.error);
            ExitCode::FAILURE
        }
    }
```

Expose `is_unsafe_or_partial` from the kernel (small pub wrapper over `replay.rs`'s existing `is_unsafe`/`is_partial`). Keep the **final stats line format byte-identical** to today so goldens/`assert_cmd` expectations survive.

- [ ] **Step 3: Write the differential integration test**

Create `crates/leanr_cli/tests/parallel_differential.rs`. Using the existing `Prelude0.olean`/`ModPriv.olean` fixtures (hermetic, no toolchain needed — same ones `leanr_olean/tests/check_fixtures.rs` uses), decode, build both a `constants` map (for `replay`) and a `CheckedConstants` (for `check_parallel`), and assert identical verdicts and identical `checked`/`skipped` counts:

```rust
#[test]
fn parallel_matches_sequential_on_fixture() {
    // Decode Prelude0 into an env; build the union map.
    let (mut env, constants, skipped) = decode_prelude0(); // helper mirroring cli::check's fold
    // Sequential reference.
    let seq = leanr_kernel::replay(&mut env_clone(&env), clone_map(&constants));
    // Parallel, jobs=1 and jobs=4.
    for jobs in [1usize, 4] {
        let store = std::sync::Arc::new(take_store(&mut env_clone(&env)));
        let table = std::sync::Arc::new(leanr_kernel::CheckedConstants::new(clone_map(&constants)));
        let g = leanr_check::graph::build_graph(&store, &table).unwrap();
        let par = leanr_check::check_parallel(store, table, g, jobs, |_| {});
        match (&seq, &par) {
            (Ok(s), Ok(p)) => assert_eq!((s.checked, skipped), (p.checked, skipped)),
            (Err(_), Err(_)) => {} // both reject — acceptable for a differential
            _ => panic!("verdict mismatch seq vs parallel jobs={jobs}"),
        }
    }
}
```

(If cloning an `Environment`/store for the reference run is awkward — `Environment` deliberately isn't `Clone` — decode twice instead; the fixture is tiny.)

- [ ] **Step 4: Run — expect PASS**

Run: `cargo test -p leanr_cli --test parallel_differential`
Expected: PASS.

- [ ] **Step 5: Add the differential mise task (controller-run over full stdlib)**

In `mise.toml`:

```toml
[tasks."check:stdlib:differential"]
description = "Full-stdlib verdict-equivalence gate: parallel --jobs 1/8 vs sequential replay (local; needs toolchain)"
depends = ["elan:bootstrap"]
run = "scripts/check-differential.sh"
```

Create `scripts/check-differential.sh` that runs `leanr check --all --sequential`, then `--all --jobs 1` and `--all --jobs 8`, and asserts the three "checked N modules, M declarations (skipped K …)" lines are byte-identical.

- [ ] **Step 6: Full `mise run ci` + commit**

Run: `mise run ci`
Expected: PASS.

```bash
git add crates/leanr_cli mise.toml scripts/check-differential.sh
git commit -m "feat(cli): parallel check --jobs + full-stdlib differential gate"
```

- [ ] **Step 7: Controller acceptance — differential over the real stdlib**

Run (controller, needs toolchain): `mise run check:stdlib:differential`
Expected: three identical stats lines; exit 0. Record the line in the spec's Acceptance section. **Do not proceed to Task 7 until this is green.**

---

## Task 7: Make parallel the default; retire the differential path

**Files:**
- Modify: `crates/leanr_cli/src/main.rs`
- Modify: `mise.toml` (`check:stdlib` uses parallel; keep `--sequential` reachable for debugging or delete `check:stdlib:differential`)
- Modify: `ARCHITECTURE.md`, `docs/THREAT_MODEL.md`

- [ ] **Step 1: Confirm parallel is already the default**

Task 6 made the parallel path the default (`--sequential` opt-in). Verify `check:stdlib` (which runs `check --all` with no flag) now uses the parallel driver.

- [ ] **Step 2: Update ARCHITECTURE.md**

Add `leanr_check` to the crate map (between `leanr_olean` and `leanr_cli`): one paragraph — "the parallel kernel-check driver: dependency DAG + worker pool over a frozen `CheckedConstants`; def/thm checks lock-free, inductive/quot serialized behind a promotion mutex; verdict-equivalent to sequential `replay`."

- [ ] **Step 3: Update THREAT_MODEL.md**

Add a short subsection under resource bounds: the parallel driver's cycle/starvation surface — a hostile `.olean` whose declaration graph is cyclic cannot hang the checker; a drained ready queue with unfinished tasks is detected and reported as `DependencyCycle`; per-worker scratch is dropped per task so scratch can't accumulate; the promotion mutex bounds concurrent persistent-store writers to one.

- [ ] **Step 4: Decide the differential task's fate**

Keep `check:stdlib:differential` as a permanent regression gate (recommended — it's cheap insurance and the spec's "twin of the phase-3 differential gate" is only *deleted* per that phase's discipline once the flip is trusted). If keeping, leave `--sequential` in the CLI. If deleting per the spec's Sequencing step 7, remove the task, `scripts/check-differential.sh`, and the `--sequential` flag + the retained `replay` call path in one commit — but `crate::replay` itself STAYS (kernel reference + unit-test twin).

Recommendation: keep the task and the flag; they cost nothing and guard every future kernel change. Note the choice in the commit message.

- [ ] **Step 5: Lint + commit**

Run: `mise run lint`

```bash
git add crates/leanr_cli/src/main.rs mise.toml ARCHITECTURE.md docs/THREAT_MODEL.md
git commit -m "feat!: parallel check is the default; document driver + threat surface"
```

---

## Task 8: Mathlib pin, fetch, benchmark, acceptance sweep

**Files:**
- Create: `mathlib-pin`
- Modify: `mise.toml` (`mathlib:fetch`, `check:mathlib`, `bench:mathlib`)
- Create: `scripts/bench-mathlib.sh`
- Modify: `docs/superpowers/specs/2026-07-10-m1-final-parallel-mathlib-design.md` (Acceptance figures)

- [ ] **Step 1: Choose and record the Mathlib pin**

Find the Mathlib commit whose `lean-toolchain` equals this repo's `lean-toolchain` (the pinned version Mathlib itself used). Record it:

Create `mathlib-pin` (repo root):

```
# Mathlib commit whose lean-toolchain matches ./lean-toolchain.
# Revisit only at a milestone boundary (AGENTS.md oracle discipline).
<40-hex-commit-sha>
```

Determine the SHA by checking the Mathlib history for the tag/commit matching our `lean-toolchain` string (controller step with network; do not guess a SHA — resolve it against the real repo).

- [ ] **Step 2: Add the fetch task**

In `mise.toml`:

```toml
[tasks."mathlib:fetch"]
description = "One-time: clone Mathlib at ./mathlib-pin and `lake exe cache get` its prebuilt .oleans (network; local only)"
depends = ["elan:bootstrap"]
run = "scripts/mathlib-fetch.sh"
```

Create `scripts/mathlib-fetch.sh`: clone `https://github.com/leanprover-community/mathlib4` into `.mathlib/` (gitignored), `git checkout $(sed -n '3p' mathlib-pin)` (skip comment lines), verify `.mathlib/lean-toolchain` matches `./lean-toolchain` (abort with a clear error if not), then `cd .mathlib && lake exe cache get`. Add `.mathlib/` to `.gitignore`.

- [ ] **Step 3: Add the check + benchmark tasks**

```toml
[tasks."check:mathlib"]
description = "Kernel-check all of pinned Mathlib in parallel (needs mathlib:fetch first)"
depends = ["elan:bootstrap"]
run = "sh -c 'cargo run --release -p leanr_cli -- check --all --path .mathlib/.lake/build/lib'"

[tasks."bench:mathlib"]
description = "Benchmark leanr vs lean4checker over pinned Mathlib on this pod (needs mathlib:fetch)"
depends = ["elan:bootstrap"]
run = "scripts/bench-mathlib.sh"
```

(Confirm the real olean output dir under `.mathlib/.lake/`; adjust the `--path`.)

- [ ] **Step 4: Write the benchmark script**

Create `scripts/bench-mathlib.sh`: build `lean4checker` at the pinned toolchain (clone `leanprover/lean4checker` at the tag matching `lean-toolchain`, `lake build`), then time both checkers over the same Mathlib tree on the same pod, recording wall-clock (`/usr/bin/time -v`) and peak RSS for each:
- leanr: `scripts/mem-watchdog.sh 30 sh -c 'cargo run --release -p leanr_cli -- check --all --path <oleans> --jobs $(nproc)'`
- lean4checker: its best-configured invocation over all of Mathlib (its native multi-threaded mode).

Print a two-row table (checker, wall, peak RSS). The script only measures — the pass/fail bar (leanr green, faster, ≤ 32 GiB) is asserted by the controller reading the output.

- [ ] **Step 5: Controller acceptance runs**

These are controller-run (need toolchain + network + a full Mathlib build cache), under the watchdog:

1. `mise run mathlib:fetch` — succeeds; toolchain match verified.
2. `mise run check:mathlib` — exit 0, prints `checked <N> modules, <M> declarations (skipped <K> unsafe/partial)`; peak RSS ≤ 32 GiB.
3. `mise run bench:mathlib` — leanr wall-clock < lean4checker's best; both RSS recorded.
4. Canary: `cargo run --release -p leanr_cli -- check Init.Data.Char.Ordinal --jobs $(nproc)` — exit 0, bounded.

- [ ] **Step 6: Record figures and close acceptance**

Fill the spec's Acceptance section with the recorded numbers (module/declaration counts, leanr vs lean4checker wall-clock, both peak RSS, `--jobs` used, pod core count). Commit:

```bash
git add mathlib-pin mise.toml scripts/mathlib-fetch.sh scripts/bench-mathlib.sh .gitignore docs/superpowers/specs/2026-07-10-m1-final-parallel-mathlib-design.md
git commit -m "feat: Mathlib pin + parallel sweep + lean4checker benchmark (M1-final acceptance)"
```

---

## Self-Review

**Spec coverage:**
- Parallel replay over frozen bank → Tasks 1–5. ✓
- `CheckedConstants` gated table → Task 2. ✓
- `check_declaration` split → Task 3. ✓
- Dependency pass + block grouping → Task 4. ✓
- DAG scheduler + cancellation + lock-free majority + serialized inductive/quot promote-and-compare → Task 5. ✓
- The one new check (decoded-vs-regenerated inductive info via `constant_info_eq`) → Task 5 `run_block`. ✓
- CLI `--jobs` + differential gate → Task 6. ✓
- Flip default; keep `replay` as reference → Task 7. ✓
- Mathlib pin + fetch + `check:mathlib` + `bench:mathlib` vs lean4checker → Task 8. ✓
- Error handling (blame, MissingConstant early, cycle→reported) → Tasks 4 (missing dep), 5 (cycle/blame). ✓
- THREAT_MODEL update → Task 7. ✓
- Acceptance (canary, stdlib sweep, Mathlib sweep+bench, ≤ 32 GiB) → Task 8. ✓

**Known soft spot (flagged, not hidden):** Task 5 Step 4a — the shared persistent-store write under the promotion mutex — cannot be pinned to exact code without the bank arena internals in hand. The plan names the required kernel change (an interior-mutable, mutex-guarded promote path behind a `PromoteGuard` token), makes it a separately-committed and separately-tested step, and states the explicit fallback. The executing engineer must read `bank/{terms,names,levels,pools}.rs` growth paths before implementing it.

**Placeholder scan:** No "TBD"/"handle later"; the one irreducible unknown (arena mutability boundary) is called out with the reading list and decision criteria rather than left blank.

**Type consistency:** `CheckedConstants::{new,get,get_decoded,admit,contains,iter_decoded,len}`, `ConstSource::{Plain,Gated}`, `EnvView.consts: ConstSource`, `check_declaration(view: EnvView, scratch: &mut Store, d) -> Admitted`, `Admitted{survivors,quot_init}`, `promote_into`, `build_graph -> DepGraph`, `Task{id,kind,admits,deps}`, `check_parallel(Arc<Store>, Arc<CheckedConstants>, DepGraph, usize, Fn) -> Result<CheckStats, CheckFailure>` — names used consistently across Tasks 2–6. `KernelError::DependencyCycle` introduced in Task 5, used in Task 7's threat doc. ✓

---

## RESUME NOTES — session handoff (2026-07-11)

Branch `m1-final-parallel-mathlib` (local only, ahead of `origin/main`). Executed via subagent-driven-development. The `.superpowers/sdd/progress.md` ledger has blow-by-blow detail but is **gitignored** — this section is the durable handoff.

### Status: Tasks 1–7 DONE + reviewed clean. Task 8 (acceptance) IN PROGRESS.

**Key design change (user-approved) vs. this plan's Task 5:** Step 4a's promotion-mutex + interior-mutable store write was SUPERSEDED. Analysis found it had a real concurrent-read-during-append data race and was unnecessary. Replaced with **read-only "resolve-or-reject"**: the frozen store is never written during checking; inductive/quot survivors are compared by looking their ids up read-only in the frozen store (`leanr_kernel::resolve_constant_info`) + `constant_info_eq`. Result: fully **lock-free, `unsafe`-free, TSan-clean**. See the dated "Amendment (2026-07-10, execution)" block in the design spec §"Key enabling observation".

**Correctness is PROVEN** (stdlib differential gate green earlier): `leanr check --all` `--sequential` == `--jobs 1` == `--jobs 8`, byte-identical: `checked 2433 modules, 203134 declarations (skipped 3611 unsafe/partial)`.

### Commits (branch tip = latest listed):
- `6e59823` fix(kernel): memoize visited ExprIds in used_constants (O(DAG))  ← latest
- `11c93f2` fix(bench): derive --jobs from cgroup cpu.max, not nproc
- `16af7f2` fix(check): dedup build_graph edges globally by (owner,dep)
- `60a1763` fix(check): linear-time build_graph edge dedup + phase timing
- `2053415` fix(bench): measure leanchecker via mem-watchdog (no /usr/bin/time)
- `475090a` chore: Mathlib pin + fetch/check/bench scaffolding
- `614ff2e` feat!: parallel default + docs (Task 7)
- `8d80eec` fix(check): count each quotient constant in checked (Task 6 gate finding)
- `d2fd0cf` feat(cli): parallel check --jobs + differential gate (Task 6)
- ...(Tasks 1–5 below that; see `git log`)

### THREE bugs the Mathlib acceptance uncovered (all fixed, RED-verified, NONE soundness):
1. **Quot count** (`8d80eec`): stdlib gate caught parallel undercounting by 3. Scheduler counted `checked=done` (task count); replay counts per-add_decl and calls add_decl once per quotient constant (all 4). Fix: Quot task contributes `names.len()`.
2. **build_graph O(deps²)** (`60a1763`+`16af7f2`): first Mathlib sweep hung ~10h single-threaded. Pass-2 edge dedup used `Vec::contains`. Fix: global `HashSet<(owner,dep)>`. (v1 `60a1763` had a per-name-clear bug that duplicated block/quot deps; v2 `16af7f2` fixed it.)
3. **used_constants exponential** (`6e59823`): second sweep stalled in build_graph pass 2. `collect_expr_consts` walked the hash-consed DAG as a tree (no ExprId memo) → exponential on Mathlib's shared proof terms. Fix: `HashSet<ExprId>` visited-set. Output byte-identical.

### TO CLOSE TASK 8 — do these, in order:
1. **Rebuild release:** `cargo build --release -p leanr_cli`.
2. **Re-run stdlib differential gate** (REQUIRED — 2 output-identical kernel/graph changes landed since the last gate; verify no verdict perturbation): `mise run check:stdlib:differential` (~13 min). Expect three byte-identical `checked 2433 modules, 203134 declarations (skipped 3611 unsafe/partial)` lines, exit 0.
3. **Re-run Mathlib sweep** with BOTH perf fixes (never yet completed past decode): `LEAN_PATH="$(cd .mathlib && lake env printenv LEAN_PATH)" scripts/mem-watchdog.sh 40 sh -c 'cargo run --release -p leanr_cli -- check --all --jobs 8'`. Confirm exit 0, a `checked N modules, M declarations (skipped K …)` line, peak RSS ≤ 32 GiB. **Watch the `build_graph:` phase-timing lines on stderr** — pass2 must now complete in seconds. **OPEN RISK: we never got a clean run past decode+build_graph, so a THIRD single-threaded bottleneck (e.g. the CLI fold, or something in the parallel-check phase) may still surface. If it stalls again: check `pgrep -x leanr` thread count (1=pre-check single-threaded phase, 8=parallel check), RSS trend (flat+1 core = stuck in a call), and the last `build_graph:` timing line.**
4. **Benchmark:** `mise run bench:mathlib` (leanr vs bundled `leanchecker`, both under the 8-CPU cgroup budget via the fixed script). leanr must be green + faster than leanchecker + ≤ 32 GiB.
5. **Canary:** `LEAN_PATH=... cargo run --release -p leanr_cli -- check <one Mathlib module> --jobs 8` — exit 0.
6. **Record figures** in the design spec's "## Acceptance" section (module/decl counts, leanr vs leanchecker wall + peak RSS, jobs=8, 8-CPU pod) and commit `feat: Mathlib pin + parallel sweep + lean4checker benchmark (M1-final acceptance)`.
7. **Final whole-branch review** (superpowers:requesting-code-review, most capable model, MERGE_BASE `git merge-base main HEAD`..HEAD) — then finishing-a-development-branch.

### ENVIRONMENT specifics (this pod; a fresh pod may differ — re-probe):
- **CPU: cgroup v2 `cpu.max = 800000 100000` = 8 CPUs.** `nproc` misreports 24. USE `--jobs 8` (bench script auto-derives from cpu.max). Oversubscribing throttles + skews the benchmark.
- Mathlib already fetched at `./.mathlib` (gitignored), pin `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` (Mathlib toolchain == ours `leanprover/lean4:v4.32.0-rc1`, verified). `lake exe cache get` done (11007 oleans; full closure = Mathlib + ~15 deps + stdlib). If starting fresh: `mise run mathlib:fetch`.
- Module set is via `lake env printenv LEAN_PATH` (run inside `.mathlib`), NOT a single `--path` (Mathlib deps build to separate dirs; oleans at `<pkg>/.lake/build/lib/lean`).
- **`/usr/bin/time` absent, no root** — peak RSS comes from `scripts/mem-watchdog.sh` (prints `peak RSS N GiB (kB)` on exit); bench script already adapted.
- **lean4checker is deprecated/merged into Lean core as bundled `leanchecker`** (`~/.elan/bin/leanchecker`); no separate repo/tag. Bench targets it, run from inside `.mathlib`.
- RAM 125 GB (watchdog cap 40 GiB used for headroom; acceptance bar is ≤ 32 GiB). Decode is sequential single-threaded (~5-10 min, the Amdahl floor per spec §out-of-scope).
