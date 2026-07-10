# Direct-to-id Decode (Term-bank Phase 3) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `leanr_olean` decodes `.olean` bytes directly into term-bank ids; the Arc decoder-boundary machinery (Arc declaration family, both bridges, Arc decode path) is deleted or demoted to test support, with the verdict surface proven unchanged by an id-for-id differential gate.

**Architecture:** Build an id-emitting interpreter (`InterpId`) beside the existing Arc one, sharing the Arc interpreter for the surviving `Syntax` positions. Prove both paths produce id-for-id identical constants in a single store (interning is canonical, so id equality ⇔ structural equality), over all fixtures and one full-stdlib run. Then flip every consumer to the id path and delete the Arc path. Spec: `docs/superpowers/specs/2026-07-10-direct-to-id-decode-design.md`.

**Tech Stack:** Rust (mise-pinned 1.96.1), cargo workspace crates `leanr_kernel` / `leanr_olean` / `leanr_cli`, mise tasks for all workflows.

## Global Constraints

- `leanr_kernel` must depend on no other workspace crate (TCB rule, AGENTS.md).
- `.olean` bytes are untrusted: no code path may panic on arbitrary input (`docs/THREAT_MODEL.md`); recursion over attacker-shaped data is explicit-stack or `RecGuard`-bounded.
- Golden fixture `.txt` files must stay byte-identical — never regenerate them for this work; only the renderer's input representation changes.
- `tests/check_fixtures.rs` (verdict suite incl. mutation-differential harness) must stay green "unmodified in spirit": re-plumb representations, never weaken an assertion.
- `Syntax` stays an Arc tree with documented ptr-eq semantics; do not migrate it to ids (spec non-goal).
- No new external dependencies.
- Run `mise run test` (workspace tests) and `mise run lint` before every commit.
- Every conversion in the new decoder keeps its oracle citation comment (same citations as the Arc version it mirrors).

## File Structure

- `crates/leanr_kernel/src/bank/mod.rs` — add `Store::intern_kvmap_rows` (id-native kvmap intern; `intern_kvmap` refactors onto it).
- `crates/leanr_kernel/src/env.rs` — add `Environment::{store, store_mut, admit_unchecked}`; later delete `from_modules`, demote `intern_module`/`intern_declaration`.
- `crates/leanr_olean/src/lib.rs` — new `OleanError::Kernel` variant; `mod interp_id;` and export of the id module type.
- `crates/leanr_olean/src/interp_id.rs` — NEW: the id-emitting interpreter + the differential gate tests (gate tests deleted in Task 8).
- `crates/leanr_olean/src/interp.rs` — helper visibility widened to `pub(crate)`; Arc decode functions deleted in Task 8 (Name/Syntax decode survives).
- `crates/leanr_olean/src/module_data.rs` — `ModuleDataId` (id-native module: `parse`, `parse_parts`); renamed to `ModuleData` in Task 8 when the Arc struct is deleted.
- `crates/leanr_olean/src/loader.rs` — `load_closure` gains a `&mut Store` parameter; `ModuleSource::load` becomes `&mut self`.
- `crates/leanr_cli/src/main.rs` — `olean decls` and `check` flip to the id path.
- `crates/leanr_olean/tests/{module_data,check_fixtures,check_sweep,stdlib_sweep}.rs` — re-plumbed to id forms.
- `mise.toml` — temporary `gate:direct-decode` task (added Task 5, deleted Task 8).

---

### Task 1: Kernel support API

`InterpId` needs an id-native kvmap intern; the post-flip drivers need store access on `Environment` and a trusted-import insert (the `from_modules` loop body without the Arc bridge).

**Files:**
- Modify: `crates/leanr_kernel/src/bank/mod.rs` (around `intern_kvmap`, line ~630)
- Modify: `crates/leanr_kernel/src/env.rs` (in `impl Environment`, after `Default`)
- Test: in-file `#[cfg(test)]` additions in both files' existing test modules (`bank/tests.rs` has the bank suite; env tests live in `env.rs`'s tests or `bank/env/`— put the new tests where the sibling tests of the function you touch live)

**Interfaces:**
- Produces: `Store::intern_kvmap_rows(&mut self, base: Option<&Store>, entries: Vec<(Option<NameId>, DataValueRow)>) -> Result<KVMapId, KernelError>`
- Produces: `Environment::store(&self) -> &Store`, `Environment::store_mut(&mut self) -> &mut Store`, `Environment::admit_unchecked(&mut self, ci: ConstantInfo) -> Result<(), EnvironmentError>`
- Consumes: existing `pools::DataValueRow`, `KVMapRow`, `kvmap_row_hash` (all already visible inside the crate; `bank::pools` is already `pub mod`, so external code can name `leanr_kernel::bank::pools::DataValueRow`)

- [ ] **Step 1: Write the failing tests**

In the test module nearest `intern_kvmap`'s existing tests (`crates/leanr_kernel/src/bank/tests.rs`):

```rust
/// Interning a kvmap via pre-built rows must hit the same canonical
/// KVMapId as the Arc-bridge `intern_kvmap` on the same logical map —
/// this equivalence is what makes the phase-3 direct decoder's kvmaps
/// id-identical to the bridge's.
#[test]
fn kvmap_rows_and_arc_bridge_agree() {
    use crate::{DataValue, KVMap, Nat};
    let mut st = Store::persistent();
    let name = st.intern_name(None, &nm("k")).unwrap();
    let map = KVMap(vec![(nm("k"), DataValue::OfNat(Nat::from(7u64)))]);
    let via_arc = st.intern_kvmap(None, &map).unwrap();
    let nat = st.intern_nat(None, &Nat::from(7u64)).unwrap();
    let via_rows = st
        .intern_kvmap_rows(None, vec![(name, pools::DataValueRow::Nat(nat))])
        .unwrap();
    assert_eq!(via_arc, via_rows);
}
```

(`nm` is the existing test helper building `Arc<Name>` — reuse whatever the sibling tests in that file use; if the file has no `nm`, use `crate::testenv::nm`.)

In `env.rs`'s test module:

```rust
#[test]
fn admit_unchecked_inserts_and_rejects_duplicates() {
    let mut env = Environment::default();
    let arc_ci = crate::testenv::axiom_u();
    let ci = crate::decl::intern_constant_info(env.store_mut(), None, &arc_ci).unwrap();
    let name = ci.name();
    env.admit_unchecked(ci.clone()).unwrap();
    assert!(env.get(name).is_some());
    assert!(matches!(
        env.admit_unchecked(ci),
        Err(EnvironmentError::DuplicateName(_))
    ));
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_kernel kvmap_rows_and_arc_bridge_agree admit_unchecked -- --nocapture`
Expected: FAIL to compile — `intern_kvmap_rows`, `store_mut`, `admit_unchecked` not found.

- [ ] **Step 3: Implement**

In `bank/mod.rs`, refactor `intern_kvmap` (line ~630) into two functions:

```rust
    /// Id-native kvmap intern (phase 3, direct decode): the caller has
    /// already interned every entry's leaves and hands the finished
    /// rows. `intern_kvmap` (the Arc bridge) reduces to leaf-bridging
    /// plus this.
    pub fn intern_kvmap_rows(
        &mut self,
        base: Option<&Store>,
        entries: Vec<(Option<NameId>, DataValueRow)>,
    ) -> Result<KVMapId, KernelError> {
        let row = KVMapRow(entries.into_boxed_slice());
        let h = kvmap_row_hash(&row);
        if let Some(b) = base {
            if let Some(bits) = b.kvmaps.lookup(h, |t| *t == row) {
                return KVMapId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        let bits = self
            .kvmaps
            .intern(h, |t| *t == row, || row.clone(), kvmap_row_hash)?;
        KVMapId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }
```

and shrink `intern_kvmap` to build `entries` (its existing leaf-bridging loop, unchanged) then `self.intern_kvmap_rows(base, entries)`.

In `env.rs`, inside `impl Environment`:

```rust
    /// The persistent store, read-only (rendering ids for output).
    pub fn store(&self) -> &Store {
        &self.store
    }

    /// The persistent store, mutable — the direct-to-id decoder's
    /// intern target (phase 3). Interning cannot violate any kernel
    /// invariant: ids are minted canonically and `constants` is only
    /// written through checked/trusted insert paths.
    pub fn store_mut(&mut self) -> &mut Store {
        &mut self.store
    }

    /// Trusted-import insert (the decode path's replacement for the
    /// Arc-era `from_modules` loop body): duplicate-check + insert,
    /// no type checking. `ci`'s ids must live in `self.store` —
    /// i.e. it was decoded/interned against `self.store_mut()`.
    pub fn admit_unchecked(&mut self, ci: ConstantInfo) -> Result<(), EnvironmentError> {
        let name = ci.name();
        if self.constants.contains_key(&name) {
            let dup = self.store.to_name(None, Some(name));
            return Err(EnvironmentError::DuplicateName(dup));
        }
        self.constants.insert(name, ci);
        Ok(())
    }
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p leanr_kernel` — the two new tests pass, everything else stays green.

- [ ] **Step 5: Lint and commit**

```bash
mise run lint && mise run test
git add -A
git commit -m "feat(kernel): direct-decode support API — intern_kvmap_rows, Environment store accessors + admit_unchecked"
```

---

### Task 2: Id-emitting interpreter + fixture-level differential gate

The heart of the phase: `InterpId` mirrors `interp.rs` conversion-for-conversion but calls the store's typed intern-constructors. The failing test written first is the differential gate itself, at fixture level.

**Files:**
- Create: `crates/leanr_olean/src/interp_id.rs`
- Modify: `crates/leanr_olean/src/lib.rs` (`OleanError::Kernel` variant; `mod interp_id;`; export `ModuleDataId`)
- Modify: `crates/leanr_olean/src/interp.rs` (helper visibility; `reducibility` becomes a free fn)
- Modify: `crates/leanr_olean/src/module_data.rs` (`ModuleDataId` struct + `parse`)

**Interfaces:**
- Consumes: Task 1's `Store::intern_kvmap_rows`, `Environment::{store, store_mut}`; existing `Store::{intern_str, intern_nat, intern_int, name_str, name_num, level_zero, level_succ, level_max, level_imax, level_param, level_mvar, intern_level_list, expr_bvar, expr_fvar, expr_mvar, expr_sort, expr_const, expr_app, expr_lam, expr_forall, expr_let, expr_lit_nat, expr_lit_str, expr_mdata, expr_proj}`; `leanr_kernel::constant_info_eq`; `Environment::intern_module` (bridge side of the gate; still alive pre-flip).
- Produces: `pub(crate) struct InterpId<'s>` with `new(st: &'s mut Store)`, `with_arc(st: &'s mut Store, arc: Interp)`, `pub(crate) fn module_data(&mut self, root: &Raw) -> Result<ModuleDataId, OleanError>`.
- Produces: `pub struct ModuleDataId { pub is_module: bool, pub imports: Vec<Import>, pub const_names: Vec<NameId>, pub constants: Vec<ConstantInfo>, pub extra_const_names: Vec<NameId>, pub num_entries: usize }` with `pub fn parse(bytes: &[u8], st: &mut Store) -> Result<ModuleDataId, OleanError>`.
- Produces: `OleanError::Kernel(KernelError)` with `impl From<KernelError> for OleanError` (thiserror `#[from]` — `KernelError` implements `std::error::Error`, verified at `error.rs:116`).

- [ ] **Step 1: Preparatory visibility changes in `interp.rs` and `lib.rs`**

In `interp.rs`, widen to `pub(crate)`: `type Raw`, `fn key`, `fn bad`, `fn ctor`, `fn boolean`, `fn nat`, `fn int`, `fn string`, `fn list`, `fn array`, `fn substring`, `fn source_info`, `struct Interp`'s `fn new`, `fn name`, `fn syntax`. Move the `reducibility` method out of `impl Interp` into a free function (it uses no interpreter state):

```rust
/// ReducibilityHints (Declaration.lean:46-50). Representation-agnostic
/// (returns a plain enum) — shared by the Arc and id decode paths.
pub(crate) fn reducibility(r: &Raw) -> Result<ReducibilityHints, OleanError> {
    // body identical to the current method (interp.rs:598-614), minus `&mut self`
}
```

and change its one call site (`constant_info`, `hints: self.reducibility(&f[2])?`) to `hints: reducibility(&f[2])?`.

In `lib.rs`, add to `OleanError` (after `DeepRecursion`):

```rust
    /// Interning into the term bank failed while decoding directly to
    /// ids (phase 3) — e.g. a bank's u32 id space exhausted
    /// (`KernelError::BankExhausted`). Not reachable from legitimate
    /// files; incompleteness, never unsoundness.
    #[error("olean decode: kernel interning failed: {0}")]
    Kernel(#[from] leanr_kernel::KernelError),
```

(`KernelError` is `PartialEq, Eq`, so `OleanError`'s derives keep compiling.) Also add `mod interp_id;` next to `mod interp;` and `pub use module_data::ModuleDataId;` next to the existing `ModuleData` export.

Run: `cargo build -p leanr_olean` — fails only on the missing `interp_id.rs` / `ModuleDataId`; that's next.

- [ ] **Step 2: Write the failing gate test**

Create `crates/leanr_olean/src/interp_id.rs` containing (for now) only the test module — the gate, written against the not-yet-existing `InterpId`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::interp::Interp;
    use leanr_kernel::{constant_info_eq, Environment};
    use std::path::PathBuf;
    use std::sync::Arc;

    fn fixture(name: &str) -> Vec<u8> {
        std::fs::read(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../../tests/fixtures")
                .join(name),
        )
        .unwrap()
    }

    /// The phase-3 differential gate, single-store exact form (spec:
    /// 2026-07-10-direct-to-id-decode-design.md, "Differential gate"):
    /// Arc-decode-then-bridge and direct-decode into the SAME store
    /// must yield id-for-id identical constants. The Arc interpreter
    /// is handed on to the id interpreter so `Syntax` payloads are
    /// pointer-identical — kvmap rows compare `Syntax` by ptr-eq, so
    /// without sharing, syntax-bearing mdata would spuriously mint
    /// distinct KVMapIds. Returns the constant count for sweep totals.
    pub(super) fn assert_paths_agree(bytes: &[u8]) -> usize {
        let root = crate::raw::parse_bytes(bytes).expect("raw parses");

        // Arc path first (populates the shared syntax/name memos).
        let mut arc_interp = Interp::new();
        let arc_md = arc_interp.module_data(&root).expect("arc decodes");
        let arc_names: Vec<Arc<leanr_kernel::Name>> = arc_md
            .constants
            .iter()
            .map(|c| Arc::clone(c.name()))
            .collect();

        let mut env = Environment::default();
        let bridged = env
            .intern_module(arc_md.constants)
            .expect("bridge interns");

        // Direct path, same store, shared Arc interpreter.
        let direct = {
            let mut interp = InterpId::with_arc(env.store_mut(), arc_interp);
            interp.module_data(&root).expect("direct decodes")
        };

        assert_eq!(
            direct.constants.len(),
            arc_names.len(),
            "constant counts differ between decode paths"
        );
        for (ci, arc_name) in direct.constants.iter().zip(&arc_names) {
            let expect_name = env
                .store_mut()
                .intern_name(None, arc_name)
                .expect("name interns")
                .expect("declaration names are never anonymous");
            assert_eq!(
                ci.name(),
                expect_name,
                "constant order/name differs: {arc_name}"
            );
            let b = bridged
                .get(&ci.name())
                .unwrap_or_else(|| panic!("{arc_name} missing from bridged map"));
            assert!(
                constant_info_eq(ci, b),
                "constant {arc_name} differs id-for-id between decode paths"
            );
        }
        // const_names must be the constants' names, same order/ids.
        for (n, c) in direct.const_names.iter().zip(direct.constants.iter()) {
            assert_eq!(*n, c.name(), "const_names not shared with constants");
        }
        direct.constants.len()
    }

    #[test]
    fn prelude0_paths_agree() {
        assert!(assert_paths_agree(&fixture("Prelude0.olean")) >= 3);
    }

    #[test]
    fn sample_paths_agree() {
        assert!(assert_paths_agree(&fixture("Sample.olean")) > 0);
    }

    #[test]
    fn sample_rich_paths_agree() {
        assert!(assert_paths_agree(&fixture("SampleRich.olean")) > 0);
    }

    #[test]
    fn mutbase_paths_agree() {
        assert!(assert_paths_agree(&fixture("MutBase.olean")) > 0);
    }

    #[test]
    fn mutations0_paths_agree() {
        assert!(assert_paths_agree(&fixture("Mutations0.olean")) > 0);
    }
}
```

- [ ] **Step 3: Run the gate to verify it fails**

Run: `cargo test -p leanr_olean --lib paths_agree`
Expected: FAIL to compile — `InterpId` not defined.

- [ ] **Step 4: Implement `InterpId`**

Fill in `interp_id.rs` above the test module. Every conversion mirrors `interp.rs` line-for-line in shape logic (same tags, field counts, scalar offsets, oracle citations); only the outputs are ids. Full code:

```rust
//! Phase B, id-emitting (term-bank phase 3): interpret the validated
//! [`RawValue`] DAG directly into term-bank ids. Mirrors `interp.rs`
//! conversion-for-conversion (same oracle citations, same shape
//! checks); only the output representation differs — decoding IS
//! interning, with per-type memos mapping one file offset to one id.
//! `Syntax` subtrees remain Arc trees (opaque kernel payload, ptr-eq
//! semantics — spec non-goal) and are decoded by the embedded Arc
//! [`Interp`].

use std::collections::HashMap;

use leanr_kernel::bank::pools::DataValueRow;
use leanr_kernel::bank::{ExprId, KVMapId, LevelId, NameId, Store};
use leanr_kernel::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety,
    DefinitionVal, InductiveVal, OpaqueVal, QuotKind, QuotVal, RecursorRule, RecursorVal,
    TheoremVal,
};

use crate::interp::{
    array, bad, boolean, ctor, int, key, list, nat, reducibility, string, Interp, Raw,
};
use crate::raw::RawValue;
use crate::OleanError;

pub(crate) struct InterpId<'s> {
    st: &'s mut Store,
    /// Arc-side interpreter for the surviving Arc-tree positions:
    /// `Syntax` payloads (opaque, ptr-eq) and `Import.module` names
    /// (the loader keys its DFS and file resolution on `Arc<Name>`).
    arc: Interp,
    names: HashMap<*const RawValue, Option<NameId>>,
    levels: HashMap<*const RawValue, LevelId>,
    exprs: HashMap<*const RawValue, ExprId>,
}

impl<'s> InterpId<'s> {
    pub(crate) fn new(st: &'s mut Store) -> InterpId<'s> {
        InterpId::with_arc(st, Interp::new())
    }

    /// Differential-gate constructor: adopt an Arc interpreter whose
    /// memos are already populated, so `Syntax` payloads are the SAME
    /// `Arc`s the Arc path produced (kvmap rows compare `Syntax` by
    /// ptr-eq — required for exact id-for-id equality in the gate).
    pub(crate) fn with_arc(st: &'s mut Store, arc: Interp) -> InterpId<'s> {
        InterpId {
            st,
            arc,
            names: HashMap::new(),
            levels: HashMap::new(),
            exprs: HashMap::new(),
        }
    }

    /// Name (Init/Prelude.lean:4693-4717): same iterative chain walk as
    /// `Interp::name`; `None` = anonymous (the bank has no row for it).
    fn name(&mut self, r: &Raw) -> Result<Option<NameId>, OleanError> {
        let mut chain: Vec<&Raw> = Vec::new();
        let mut cur = r;
        let mut built: Option<NameId> = loop {
            if let RawValue::Scalar(0) = &**cur {
                break None;
            }
            if let Some(&n) = self.names.get(&key(cur)) {
                break n;
            }
            match &**cur {
                RawValue::Ctor {
                    tag: 1 | 2, fields, ..
                } if fields.len() == 2 => {
                    chain.push(cur);
                    cur = &fields[0];
                }
                _ => return Err(bad("Name")),
            }
        };
        for node in chain.into_iter().rev() {
            let RawValue::Ctor { tag, fields, .. } = &**node else {
                unreachable!()
            };
            let id = match tag {
                1 => {
                    let part = self.st.intern_str(None, &string(&fields[1])?)?;
                    self.st.name_str(None, built, part)?
                }
                2 => {
                    let part = self.st.intern_nat(None, &nat(&fields[1])?)?;
                    self.st.name_num(None, built, part)?
                }
                _ => unreachable!(),
            };
            built = Some(id);
            self.names.insert(key(node), built);
        }
        Ok(built)
    }

    /// Declaration-position name: never anonymous in legitimate data
    /// (same posture as `decl.rs`'s `intern_name_req` — reject, don't
    /// assert).
    fn name_req(&mut self, r: &Raw) -> Result<NameId, OleanError> {
        self.name(r)?.ok_or_else(|| bad("non-anonymous Name"))
    }

    fn sub_level(&mut self, r: &Raw) -> Result<LevelId, OleanError> {
        if let RawValue::Scalar(0) = &**r {
            return Ok(self.st.level_zero(None)?);
        }
        self.levels
            .get(&key(r))
            .copied()
            .ok_or_else(|| bad("Level subterm"))
    }

    /// Level (Level.lean:90-103): explicit-stack post-order, identical
    /// shape/tag validation to `Interp::level`.
    fn level(&mut self, root: &Raw) -> Result<LevelId, OleanError> {
        enum Step<'r> {
            Visit(&'r Raw),
            Build(&'r Raw),
        }
        let mut stack = vec![Step::Visit(root)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Visit(r) => {
                    if matches!(&**r, RawValue::Scalar(0)) || self.levels.contains_key(&key(r)) {
                        continue;
                    }
                    let RawValue::Ctor { tag, fields, .. } = &**r else {
                        return Err(bad("Level"));
                    };
                    let n_level_children = match tag {
                        1 => 1,     // succ
                        2 | 3 => 2, // max, imax
                        4 | 5 => 0, // param, mvar (Name field)
                        _ => return Err(bad("Level tag")),
                    };
                    let expected_fields = if *tag == 1 {
                        1
                    } else if *tag <= 3 {
                        2
                    } else {
                        1
                    };
                    if fields.len() != expected_fields {
                        return Err(bad("Level fields"));
                    }
                    stack.push(Step::Build(r));
                    for f in &fields[..n_level_children] {
                        stack.push(Step::Visit(f));
                    }
                }
                Step::Build(r) => {
                    let RawValue::Ctor { tag, fields, .. } = &**r else {
                        unreachable!()
                    };
                    let id = match tag {
                        1 => {
                            let a = self.sub_level(&fields[0])?;
                            self.st.level_succ(None, a)?
                        }
                        2 => {
                            let a = self.sub_level(&fields[0])?;
                            let b = self.sub_level(&fields[1])?;
                            self.st.level_max(None, a, b)?
                        }
                        3 => {
                            let a = self.sub_level(&fields[0])?;
                            let b = self.sub_level(&fields[1])?;
                            self.st.level_imax(None, a, b)?
                        }
                        4 => {
                            let n = self.name(&fields[0])?;
                            self.st.level_param(None, n)?
                        }
                        5 => {
                            let n = self.name(&fields[0])?;
                            self.st.level_mvar(None, n)?
                        }
                        _ => unreachable!(),
                    };
                    self.levels.insert(key(r), id);
                }
            }
        }
        self.sub_level(root)
    }

    fn sub_expr(&self, r: &Raw) -> Result<ExprId, OleanError> {
        self.exprs
            .get(&key(r))
            .copied()
            .ok_or_else(|| bad("Expr subterm"))
    }

    /// Expr (Expr.lean:321-471): explicit-stack post-order over the
    /// Expr-typed fields; same SHAPES table as `Interp::expr`.
    fn expr(&mut self, root: &Raw) -> Result<ExprId, OleanError> {
        enum Step<'r> {
            Visit(&'r Raw),
            Build(&'r Raw),
        }
        // (field count, indices of Expr-typed fields) per ctor tag.
        const SHAPES: [(usize, &[usize]); 12] = [
            (1, &[]),        // 0 bvar(Nat)
            (1, &[]),        // 1 fvar(Name)
            (1, &[]),        // 2 mvar(Name)
            (1, &[]),        // 3 sort(Level)
            (2, &[]),        // 4 const(Name, List Level)
            (2, &[0, 1]),    // 5 app
            (3, &[1, 2]),    // 6 lam
            (3, &[1, 2]),    // 7 forallE
            (4, &[1, 2, 3]), // 8 letE
            (1, &[]),        // 9 lit
            (2, &[1]),       // 10 mdata
            (3, &[2]),       // 11 proj
        ];
        let mut stack = vec![Step::Visit(root)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Visit(r) => {
                    if self.exprs.contains_key(&key(r)) {
                        continue;
                    }
                    let RawValue::Ctor { tag, fields, .. } = &**r else {
                        return Err(bad("Expr"));
                    };
                    let (nfields, expr_children) =
                        SHAPES.get(*tag as usize).ok_or_else(|| bad("Expr tag"))?;
                    if fields.len() != *nfields {
                        return Err(bad("Expr fields"));
                    }
                    stack.push(Step::Build(r));
                    for &i in *expr_children {
                        stack.push(Step::Visit(&fields[i]));
                    }
                }
                Step::Build(r) => {
                    let e = self.build_expr(r)?;
                    self.exprs.insert(key(r), e);
                }
            }
        }
        self.sub_expr(root)
    }

    fn build_expr(&mut self, r: &Raw) -> Result<ExprId, OleanError> {
        let RawValue::Ctor {
            tag,
            fields,
            scalars,
        } = &**r
        else {
            unreachable!()
        };
        // Scalar area: computed `data` u64 first (ignored; the bank's
        // row constructors recompute an equivalent `ExprData`), then
        // u8 flags (kernel/expr.h:265 proves the order).
        let expr: ExprId = match tag {
            0 => self.st.expr_bvar(None, &nat(&fields[0])?)?,
            1 => {
                let n = self.name(&fields[0])?;
                self.st.expr_fvar(None, n)?
            }
            2 => {
                let n = self.name(&fields[0])?;
                self.st.expr_mvar(None, n)?
            }
            3 => {
                let l = self.level(&fields[0])?;
                self.st.expr_sort(None, l)?
            }
            4 => {
                let n = self.name(&fields[0])?;
                let levels = list(&fields[1])?
                    .into_iter()
                    .map(|l| self.level(l))
                    .collect::<Result<Vec<_>, _>>()?;
                let ls = self.st.intern_level_list(None, &levels)?;
                self.st.expr_const(None, n, ls)?
            }
            5 => {
                let f = self.sub_expr(&fields[0])?;
                let arg = self.sub_expr(&fields[1])?;
                self.st.expr_app(None, f, arg)?
            }
            6 | 7 => {
                let binder_info = match scalars.get(8).copied() {
                    Some(0) => BinderInfo::Default,
                    Some(1) => BinderInfo::Implicit,
                    Some(2) => BinderInfo::StrictImplicit,
                    Some(3) => BinderInfo::InstImplicit,
                    _ => return Err(bad("BinderInfo")),
                };
                let binder_name = self.name(&fields[0])?;
                let binder_type = self.sub_expr(&fields[1])?;
                let body = self.sub_expr(&fields[2])?;
                if *tag == 6 {
                    self.st
                        .expr_lam(None, binder_name, binder_type, body, binder_info)?
                } else {
                    self.st
                        .expr_forall(None, binder_name, binder_type, body, binder_info)?
                }
            }
            8 => {
                let decl_name = self.name(&fields[0])?;
                let ty = self.sub_expr(&fields[1])?;
                let value = self.sub_expr(&fields[2])?;
                let body = self.sub_expr(&fields[3])?;
                let non_dep = boolean(scalars.get(8), "letE nondep")?;
                self.st
                    .expr_let(None, decl_name, ty, value, body, non_dep)?
            }
            9 => match &*fields[0] {
                RawValue::Ctor {
                    tag: 0, fields: lf, ..
                } if lf.len() == 1 => self.st.expr_lit_nat(None, &nat(&lf[0])?)?,
                RawValue::Ctor {
                    tag: 1, fields: lf, ..
                } if lf.len() == 1 => self.st.expr_lit_str(None, &string(&lf[0])?)?,
                _ => return Err(bad("Literal")),
            },
            10 => {
                let data = self.kvmap(&fields[0])?;
                let sub = self.sub_expr(&fields[1])?;
                self.st.expr_mdata(None, data, sub)?
            }
            11 => {
                let type_name = self.name(&fields[0])?;
                let idx = nat(&fields[1])?;
                let structure = self.sub_expr(&fields[2])?;
                self.st.expr_proj(None, type_name, &idx, structure)?
            }
            _ => unreachable!("tag checked in Visit"),
        };
        Ok(expr)
    }

    /// KVMap ≅ List (Name × DataValue) (Data/KVMap.lean:71-73).
    fn kvmap(&mut self, r: &Raw) -> Result<KVMapId, OleanError> {
        let mut entries: Vec<(Option<NameId>, DataValueRow)> = Vec::new();
        for pair in list(r)? {
            let (fields, _) = ctor(pair, 0, 2, "Prod")?;
            let n = self.name(&fields[0])?;
            let v = self.data_value(&fields[1])?;
            entries.push((n, v));
        }
        Ok(self.st.intern_kvmap_rows(None, entries)?)
    }

    /// DataValue (Data/KVMap.lean:18-25). `OfSyntax` stays an Arc tree
    /// decoded by the embedded Arc interpreter (opaque payload,
    /// ptr-eq semantics).
    fn data_value(&mut self, r: &Raw) -> Result<DataValueRow, OleanError> {
        match &**r {
            RawValue::Ctor { tag: 0, fields, .. } if fields.len() == 1 => Ok(DataValueRow::Str(
                self.st.intern_str(None, &string(&fields[0])?)?,
            )),
            RawValue::Ctor {
                tag: 1,
                fields,
                scalars,
            } if fields.is_empty() => Ok(DataValueRow::Bool(boolean(
                scalars.first(),
                "DataValue bool",
            )?)),
            RawValue::Ctor { tag: 2, fields, .. } if fields.len() == 1 => {
                Ok(DataValueRow::Name(self.name(&fields[0])?))
            }
            RawValue::Ctor { tag: 3, fields, .. } if fields.len() == 1 => Ok(DataValueRow::Nat(
                self.st.intern_nat(None, &nat(&fields[0])?)?,
            )),
            RawValue::Ctor { tag: 4, fields, .. } if fields.len() == 1 => Ok(DataValueRow::Int(
                self.st.intern_int(None, &int(&fields[0])?)?,
            )),
            RawValue::Ctor { tag: 5, fields, .. } if fields.len() == 1 => {
                Ok(DataValueRow::Syntax(self.arc.syntax(&fields[0])?))
            }
            _ => Err(bad("DataValue")),
        }
    }

    fn names(&mut self, items: Vec<&Raw>) -> Result<Vec<NameId>, OleanError> {
        items.into_iter().map(|n| self.name_req(n)).collect()
    }

    /// ConstantVal (Declaration.lean:95-99).
    fn constant_val(&mut self, r: &Raw) -> Result<ConstantVal, OleanError> {
        let (fields, _) = ctor(r, 0, 3, "ConstantVal")?;
        Ok(ConstantVal {
            name: self.name_req(&fields[0])?,
            level_params: self.names(list(&fields[1])?)?,
            ty: self.expr(&fields[2])?,
        })
    }

    /// ConstantInfo (Declaration.lean:429-437) and its Val payloads —
    /// arm-for-arm the same shapes as `Interp::constant_info`.
    fn constant_info(&mut self, r: &Raw) -> Result<ConstantInfo, OleanError> {
        let RawValue::Ctor { tag, fields, .. } = &**r else {
            return Err(bad("ConstantInfo"));
        };
        if fields.len() != 1 {
            return Err(bad("ConstantInfo payload"));
        }
        let v = &fields[0];
        Ok(match tag {
            0 => {
                let (f, s) = ctor(v, 0, 1, "AxiomVal")?;
                ConstantInfo::Axiom(AxiomVal {
                    val: self.constant_val(&f[0])?,
                    is_unsafe: boolean(s.first(), "AxiomVal.isUnsafe")?,
                })
            }
            1 => {
                let (f, s) = ctor(v, 0, 4, "DefinitionVal")?;
                ConstantInfo::Defn(DefinitionVal {
                    val: self.constant_val(&f[0])?,
                    value: self.expr(&f[1])?,
                    hints: reducibility(&f[2])?,
                    safety: match s.first().copied() {
                        Some(0) => DefinitionSafety::Unsafe,
                        Some(1) => DefinitionSafety::Safe,
                        Some(2) => DefinitionSafety::Partial,
                        _ => return Err(bad("DefinitionSafety")),
                    },
                    all: self.names(list(&f[3])?)?,
                })
            }
            2 => {
                let (f, _) = ctor(v, 0, 3, "TheoremVal")?;
                ConstantInfo::Thm(TheoremVal {
                    val: self.constant_val(&f[0])?,
                    value: self.expr(&f[1])?,
                    all: self.names(list(&f[2])?)?,
                })
            }
            3 => {
                let (f, s) = ctor(v, 0, 3, "OpaqueVal")?;
                ConstantInfo::Opaque(OpaqueVal {
                    val: self.constant_val(&f[0])?,
                    value: self.expr(&f[1])?,
                    is_unsafe: boolean(s.first(), "OpaqueVal.isUnsafe")?,
                    all: self.names(list(&f[2])?)?,
                })
            }
            4 => {
                let (f, s) = ctor(v, 0, 1, "QuotVal")?;
                ConstantInfo::Quot(QuotVal {
                    val: self.constant_val(&f[0])?,
                    kind: match s.first().copied() {
                        Some(0) => QuotKind::Type,
                        Some(1) => QuotKind::Ctor,
                        Some(2) => QuotKind::Lift,
                        Some(3) => QuotKind::Ind,
                        _ => return Err(bad("QuotKind")),
                    },
                })
            }
            5 => {
                let (f, s) = ctor(v, 0, 6, "InductiveVal")?;
                ConstantInfo::Induct(InductiveVal {
                    val: self.constant_val(&f[0])?,
                    num_params: nat(&f[1])?,
                    num_indices: nat(&f[2])?,
                    all: self.names(list(&f[3])?)?,
                    ctors: self.names(list(&f[4])?)?,
                    num_nested: nat(&f[5])?,
                    is_rec: boolean(s.first(), "InductiveVal.isRec")?,
                    is_unsafe: boolean(s.get(1), "InductiveVal.isUnsafe")?,
                    is_reflexive: boolean(s.get(2), "InductiveVal.isReflexive")?,
                })
            }
            6 => {
                let (f, s) = ctor(v, 0, 5, "ConstructorVal")?;
                ConstantInfo::Ctor(ConstructorVal {
                    val: self.constant_val(&f[0])?,
                    induct: self.name_req(&f[1])?,
                    cidx: nat(&f[2])?,
                    num_params: nat(&f[3])?,
                    num_fields: nat(&f[4])?,
                    is_unsafe: boolean(s.first(), "ConstructorVal.isUnsafe")?,
                })
            }
            7 => {
                let (f, s) = ctor(v, 0, 7, "RecursorVal")?;
                let mut rules = Vec::new();
                for rule in list(&f[6])? {
                    let (rf, _) = ctor(rule, 0, 3, "RecursorRule")?;
                    rules.push(RecursorRule {
                        ctor: self.name_req(&rf[0])?,
                        nfields: nat(&rf[1])?,
                        rhs: self.expr(&rf[2])?,
                    });
                }
                ConstantInfo::Rec(RecursorVal {
                    val: self.constant_val(&f[0])?,
                    all: self.names(list(&f[1])?)?,
                    num_params: nat(&f[2])?,
                    num_indices: nat(&f[3])?,
                    num_motives: nat(&f[4])?,
                    num_minors: nat(&f[5])?,
                    rules,
                    k: boolean(s.first(), "RecursorVal.k")?,
                    is_unsafe: boolean(s.get(1), "RecursorVal.isUnsafe")?,
                })
            }
            _ => return Err(bad("ConstantInfo tag")),
        })
    }

    /// Import (Setup.lean:25-32). `Import.module` stays `Arc<Name>`:
    /// the loader keys its DFS and file resolution on it.
    fn import(&mut self, r: &Raw) -> Result<crate::Import, OleanError> {
        let (f, s) = ctor(r, 0, 1, "Import")?;
        Ok(crate::Import {
            module: self.arc.name(&f[0])?,
            import_all: boolean(s.first(), "Import.importAll")?,
            is_exported: boolean(s.get(1), "Import.isExported")?,
            is_meta: boolean(s.get(2), "Import.isMeta")?,
        })
    }

    /// ModuleData (Environment.lean:109-129).
    pub(crate) fn module_data(&mut self, root: &Raw) -> Result<crate::ModuleDataId, OleanError> {
        let (f, s) = ctor(root, 0, 5, "ModuleData")?;
        Ok(crate::ModuleDataId {
            is_module: boolean(s.first(), "ModuleData.isModule")?,
            imports: array(&f[0])?
                .iter()
                .map(|i| self.import(i))
                .collect::<Result<_, _>>()?,
            const_names: array(&f[1])?
                .iter()
                .map(|n| self.name_req(n))
                .collect::<Result<_, _>>()?,
            constants: array(&f[2])?
                .iter()
                .map(|c| self.constant_info(c))
                .collect::<Result<_, _>>()?,
            extra_const_names: array(&f[3])?
                .iter()
                .map(|n| self.name_req(n))
                .collect::<Result<_, _>>()?,
            num_entries: array(&f[4])?.len(),
        })
    }
}
```

In `module_data.rs`, add (below the Arc `ModuleData`):

```rust
/// The id-native decoded module (term-bank phase 3): what `ModuleData`
/// becomes once the Arc decode path is deleted. Ids live in the
/// `&mut Store` handed to `parse`/`parse_parts` — the caller's
/// `Environment::store_mut()` in the check pipeline, or a standalone
/// `Store::persistent()` for inspection commands.
pub struct ModuleDataId {
    pub is_module: bool,
    pub imports: Vec<Import>,
    pub const_names: Vec<NameId>,
    pub constants: Vec<ConstantInfo>,
    pub extra_const_names: Vec<NameId>,
    /// Environment-extension entries are validated by phase A but kept
    /// opaque (spec: interpreted by the elaborator in M4).
    pub num_entries: usize,
}

impl ModuleDataId {
    /// Decode a whole single-region `.olean` file directly into `st`.
    /// `bytes` is untrusted input; every failure mode is an
    /// `OleanError`, never a panic. A failed decode may leave
    /// already-interned rows in `st` — sound (interning is append-only
    /// and canonical; unreachable ids are inert) and decode failure is
    /// fatal for the run.
    pub fn parse(bytes: &[u8], st: &mut Store) -> Result<ModuleDataId, OleanError> {
        let root = raw::parse_bytes(bytes)?;
        InterpId::new(st).module_data(&root)
    }
}
```

with the imports this needs (`use leanr_kernel::bank::{NameId, Store};`, `use leanr_kernel::ConstantInfo;`, `use crate::interp_id::InterpId;`). The Arc `ModuleData` and its imports stay untouched.

- [ ] **Step 5: Run the gate to verify it passes**

Run: `cargo test -p leanr_olean --lib paths_agree -- --nocapture`
Expected: all five gate tests PASS. If a fixture disagrees, that is a real finding — diagnose which constant and which field before touching anything (the gate exists to catch decode-fidelity bugs; do not weaken the comparison).

- [ ] **Step 6: Run the full suite, lint, commit**

```bash
mise run lint && mise run test
git add -A
git commit -m "feat(olean): id-emitting decoder (InterpId) + fixture-level differential gate"
```

---

### Task 3: Id-native `parse_parts` (multi-region modules)

**Files:**
- Modify: `crates/leanr_olean/src/module_data.rs` (add `ModuleDataId::parse_parts`)
- Test: `#[cfg(test)]` module in `module_data.rs` (in-crate — it needs fixtures and `Environment`)

**Interfaces:**
- Consumes: `InterpId` (Task 2), `raw::parse_parts_bytes`, `Environment::{store_mut, admit_unchecked}` — wait, no: this task only decodes; replay uses `leanr_kernel::replay` with the constants map.
- Produces: `ModuleDataId::parse_parts(parts: &[(PartKind, &[u8])], st: &mut Store) -> Result<ModuleDataId, OleanError>` — same part-merge semantics as the Arc version (`.private` > `.server` > base; shadowed duplicates must share `type` + `levelParams`).

- [ ] **Step 1: Write the failing tests**

In `module_data.rs`'s (new) `#[cfg(test)] mod tests`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use leanr_kernel::bank::NameId;
    use leanr_kernel::{ConstantInfo, Environment};
    use std::collections::HashMap;
    use std::path::PathBuf;

    fn fixture(name: &str) -> Vec<u8> {
        std::fs::read(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../../tests/fixtures")
                .join(name),
        )
        .unwrap()
    }

    /// Id-path mirror of `check_fixtures.rs`'s
    /// `modpriv_parts_replay_from_empty_env`: multi-region merge on the
    /// id path — `.private` wins over the base axiom stub, the private
    /// helper is present, and the merged set replays clean.
    #[test]
    fn modpriv_parts_id_decode_and_replay() {
        let base = fixture("ModPriv.olean");
        let server = fixture("ModPriv.olean.server");
        let private = fixture("ModPriv.olean.private");

        let mut env = Environment::default();
        let md = ModuleDataId::parse_parts(
            &[
                (PartKind::Base, &base),
                (PartKind::Server, &server),
                (PartKind::Private, &private),
            ],
            env.store_mut(),
        )
        .expect("parts decode");
        assert!(md.is_module);
        assert!(md.imports.is_empty());

        let render =
            |env: &Environment, n: NameId| env.store().to_name(None, Some(n)).to_string();
        assert!(
            md.constants
                .iter()
                .any(|c| render(&env, c.name()) == "_private.ModPriv.0.secret"),
            "private helper missing from merged constants"
        );
        let bump = md
            .constants
            .iter()
            .find(|c| render(&env, c.name()) == "bump")
            .expect("bump present");
        assert_eq!(bump.kind(), "def", "bump must be the private def, not an axiom stub");

        let constants: HashMap<NameId, ConstantInfo> =
            md.constants.into_iter().map(|c| (c.name(), c)).collect();
        let stats = leanr_kernel::replay(&mut env, constants).expect("replays clean");
        assert!(stats.checked >= 5, "expected >= 5 checked, got {}", stats.checked);
        assert_eq!(stats.skipped_unsafe, 0);
    }

    #[test]
    fn parse_parts_requires_exactly_one_base() {
        let base = fixture("ModPriv.olean");
        let mut env = Environment::default();
        let err = ModuleDataId::parse_parts(
            &[(PartKind::Private, &base)],
            env.store_mut(),
        )
        .expect_err("no base part");
        assert!(matches!(err, OleanError::BadShape { .. }));
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_olean --lib modpriv_parts_id parse_parts_requires`
Expected: FAIL to compile — `ModuleDataId::parse_parts` not found.

- [ ] **Step 3: Implement `parse_parts`**

In `module_data.rs`, inside `impl ModuleDataId`. Same structure as the Arc `ModuleData::parse_parts` (whose doc comment explains the authority order and the shadowed-duplicate guard — keep a pointer to it, and move that doc wholesale onto this function in Task 8 when the Arc version is deleted). The id representation makes the duplicate check guard-free: id equality IS structural equality.

```rust
    /// Decode a module split across its ordered companion parts —
    /// id-native twin of `ModuleData::parse_parts` (see its doc comment
    /// for the oracle rationale on part authority and the
    /// shadowed-duplicate guard; semantics are identical).
    pub fn parse_parts(
        parts: &[(PartKind, &[u8])],
        st: &mut Store,
    ) -> Result<ModuleDataId, OleanError> {
        let base_positions: Vec<usize> = parts
            .iter()
            .enumerate()
            .filter(|(_, (k, _))| *k == PartKind::Base)
            .map(|(i, _)| i)
            .collect();
        let [base_idx] = base_positions[..] else {
            return Err(OleanError::BadShape {
                expected: "exactly one Base part in parse_parts",
            });
        };

        let byte_slices: Vec<&[u8]> = parts.iter().map(|(_, b)| *b).collect();
        let roots = raw::parse_parts_bytes(&byte_slices)?;

        // One shared interpreter: objects shared across parts decode to
        // the same id (memos keyed by raw node address, exactly like
        // the Arc version). The block scopes the &mut Store borrow so
        // `st` is usable for error rendering below.
        let mut modules: Vec<ModuleDataId> = {
            let mut interp = InterpId::new(st);
            roots
                .iter()
                .map(|r| interp.module_data(r))
                .collect::<Result<_, _>>()?
        };

        // Most-authoritative first: `.private` > `.server` > base.
        let authority = |k: PartKind| match k {
            PartKind::Private => 0,
            PartKind::Server => 1,
            PartKind::Base => 2,
        };
        let mut order: Vec<usize> = (0..modules.len()).collect();
        order.sort_by_key(|&i| authority(parts[i].0));

        let mut const_names: Vec<NameId> = Vec::new();
        let mut constants: Vec<ConstantInfo> = Vec::new();
        let mut seen: std::collections::HashMap<NameId, usize> =
            std::collections::HashMap::new();
        for &i in &order {
            for c in &modules[i].constants {
                let name = c.name();
                match seen.get(&name) {
                    None => {
                        seen.insert(name, constants.len());
                        const_names.push(name);
                        constants.push(c.clone());
                    }
                    Some(&existing) => {
                        // Shadowed duplicate must share `type` +
                        // `levelParams` with the kept version. By the
                        // interning invariant id equality IS the Arc
                        // version's guarded structural_eq, so this is
                        // plain `==` — no RecGuard, no DeepRecursion.
                        let kept = constants[existing].constant_val();
                        let dup = c.constant_val();
                        let compatible =
                            kept.level_params == dup.level_params && kept.ty == dup.ty;
                        if !compatible {
                            return Err(OleanError::DuplicateConstant {
                                name: st.to_name(None, Some(name)).to_string(),
                            });
                        }
                    }
                }
            }
        }

        // Extra const names: union preserving first-seen order.
        let mut extra_seen: std::collections::HashSet<NameId> =
            std::collections::HashSet::new();
        let mut extra_const_names: Vec<NameId> = Vec::new();
        for &i in &order {
            for &n in &modules[i].extra_const_names {
                if extra_seen.insert(n) {
                    extra_const_names.push(n);
                }
            }
        }

        let base = &mut modules[base_idx];
        Ok(ModuleDataId {
            is_module: base.is_module,
            imports: std::mem::take(&mut base.imports),
            const_names,
            constants,
            extra_const_names,
            num_entries: base.num_entries,
        })
    }
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p leanr_olean --lib modpriv_parts_id parse_parts_requires`
Expected: PASS.

- [ ] **Step 5: Lint and commit**

```bash
mise run lint && mise run test
git add -A
git commit -m "feat(olean): id-native parse_parts — multi-region merge on the id path"
```

---

### Task 4: Full-stdlib differential gate — run and record

The pre-flip acceptance evidence: every base `.olean` in the pinned toolchain decodes id-for-id identically via both paths. Needs the toolchain locally (`mise run elan:bootstrap` provides it).

**Files:**
- Modify: `crates/leanr_olean/src/interp_id.rs` (add the `#[ignore]` stdlib gate test to the existing test module)
- Modify: `mise.toml` (temporary task)
- Modify: `docs/superpowers/specs/2026-07-10-direct-to-id-decode-design.md` (record the run under Acceptance)

**Interfaces:**
- Consumes: `assert_paths_agree` (Task 2's test helper — already `pub(super)`-reachable inside the test module).

- [ ] **Step 1: Add the stdlib gate test**

In `interp_id.rs`'s test module:

```rust
    fn collect_oleans(dir: &std::path::Path, out: &mut Vec<PathBuf>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                collect_oleans(&path, out);
            } else if path.extension().is_some_and(|e| e == "olean") {
                // Base parts only: `.olean.server`/`.olean.private`
                // have extension "server"/"private". Companion parts
                // are not self-contained regions, so the single-file
                // gate covers base parts; the parts MERGE is covered
                // by the id parse_parts tests + ModPriv replay.
                out.push(path);
            }
        }
    }

    /// TEMPORARY (phase 3): the full-stdlib id-for-id differential
    /// gate. Deleted, along with the Arc decode path it compares
    /// against, once the flip lands. Run via
    /// `mise run gate:direct-decode`.
    #[test]
    #[ignore = "phase-3 pre-flip gate; needs the pinned toolchain (LEANR_SWEEP_DIR)"]
    fn stdlib_paths_agree() {
        let dir = std::env::var("LEANR_SWEEP_DIR")
            .expect("LEANR_SWEEP_DIR must point at the toolchain lib/lean dir");
        let mut files = Vec::new();
        collect_oleans(std::path::Path::new(&dir), &mut files);
        files.sort();
        assert!(
            files.len() > 1000,
            "suspiciously few .olean files ({}) under {dir} — wrong directory?",
            files.len()
        );
        let mut constants = 0usize;
        for path in &files {
            let bytes = std::fs::read(path).unwrap();
            constants += assert_paths_agree(&bytes);
        }
        println!(
            "gate: {} modules, {} constants id-for-id identical across decode paths",
            files.len(),
            constants
        );
    }
```

(Each `assert_paths_agree` call builds its own `Environment`, so memory stays flat across the sweep.)

- [ ] **Step 2: Add the temporary mise task**

In `mise.toml`, after `sweep:stdlib`:

```toml
[tasks."gate:direct-decode"]
description = "TEMPORARY (term-bank phase 3): id-for-id differential decode gate over every stdlib .olean (local; needs toolchain). Deleted with the Arc decode path."
depends = ["elan:bootstrap"]
run = "sh -c 'LEANR_SWEEP_DIR=\"$(lean --print-libdir)\" cargo test --release --package leanr_olean --lib -- --ignored --nocapture stdlib_paths_agree'"
```

- [ ] **Step 3: Run the gate**

Run: `mise run gate:direct-decode`
Expected: exit 0; the `gate: 2433 modules, … constants id-for-id identical` line (module count matches the recorded sweep figure; expect roughly the sweep's constant total). Budget ~15–30 min wall (every module decodes twice + bridges). Any disagreement is a REAL FINDING: record the module/constant, diagnose the decode divergence, fix `InterpId` (never the comparison), re-run.

- [ ] **Step 4: Record the result in the spec**

In `docs/superpowers/specs/2026-07-10-direct-to-id-decode-design.md`, under "Acceptance" item 1, append a dated record: module count, constant count, wall time, exit status.

- [ ] **Step 5: Lint and commit**

```bash
mise run lint && mise run test
git add -A
git commit -m "test(olean): full-stdlib direct-decode differential gate — green over 2433 modules (recorded)"
```

---

### Task 5: Flip the parse-only consumers

The consumers that call `ModuleData::parse` directly (no loader): the `olean decls` CLI subcommand, the golden decls tests, and the decode-only stdlib sweep. Golden `.txt` fixtures are the gate — they must stay byte-identical.

**Files:**
- Modify: `crates/leanr_cli/src/main.rs` (`olean_decls`, line ~87)
- Modify: `crates/leanr_olean/tests/module_data.rs`
- Modify: `crates/leanr_olean/tests/stdlib_sweep.rs`

**Interfaces:**
- Consumes: `ModuleDataId::parse` (Task 2), `Store::persistent()`, `Store::to_name(None, Some(NameId)) -> Arc<Name>` (Display-able), `ConstantInfo::{kind, name}`.

- [ ] **Step 1: Flip `olean_decls`**

```rust
fn olean_decls(path: &std::path::Path) -> ExitCode {
    let bytes = match std::fs::read(path) {
        Ok(bytes) => bytes,
        Err(err) => {
            eprintln!("error: cannot read {}: {err}", path.display());
            return ExitCode::FAILURE;
        }
    };
    let mut store = leanr_kernel::bank::Store::persistent();
    match leanr_olean::ModuleDataId::parse(&bytes, &mut store) {
        Ok(module) => {
            // Same line format as the oracle-side dump script
            // (tests/fixtures/dump_decls.lean) — golden-compared in CI.
            let mut out = String::new();
            for c in &module.constants {
                out.push_str(&format!(
                    "{} {}\n",
                    c.kind(),
                    store.to_name(None, Some(c.name()))
                ));
            }
            print!("{out}");
            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("error: {}: {err}", path.display());
            ExitCode::FAILURE
        }
    }
}
```

- [ ] **Step 2: Flip `tests/module_data.rs`**

```rust
use std::path::PathBuf;

use leanr_kernel::bank::Store;
use leanr_olean::{ModuleDataId, OleanError};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

fn parse_fixture(name: &str) -> (Store, ModuleDataId) {
    let mut st = Store::persistent();
    let md = ModuleDataId::parse(&std::fs::read(fixture(name)).unwrap(), &mut st).unwrap();
    (st, md)
}

fn decls_lines(st: &Store, md: &ModuleDataId) -> Vec<String> {
    md.constants
        .iter()
        .map(|c| format!("{} {}", c.kind(), st.to_name(None, Some(c.name()))))
        .collect()
}

fn golden_lines(name: &str) -> Vec<String> {
    std::fs::read_to_string(fixture(name))
        .unwrap()
        .lines()
        .map(str::to_string)
        .collect()
}

#[test]
fn sample_constants_match_the_oracle_dump() {
    let (st, md) = parse_fixture("Sample.olean");
    assert_eq!(decls_lines(&st, &md), golden_lines("Sample.decls.txt"));
}

#[test]
fn sample_rich_constants_match_the_oracle_dump() {
    let (st, md) = parse_fixture("SampleRich.olean");
    assert_eq!(decls_lines(&st, &md), golden_lines("SampleRich.decls.txt"));
}

#[test]
fn imports_and_metadata_decode() {
    let (_, md) = parse_fixture("Sample.olean");
    assert!(
        md.imports.iter().any(|i| i.module.to_string() == "Init"),
        "non-prelude modules implicitly import Init, got {:?}",
        md.imports
            .iter()
            .map(|i| i.module.to_string())
            .collect::<Vec<_>>()
    );
    assert_eq!(md.const_names.len(), md.constants.len());
}

/// The spec's sharing guarantee, id form: `constNames` is built by the
/// oracle as `constants.map (·.name)` — one file offset, one id, so
/// the ids must be EQUAL (the interning invariant upgrades the Arc
/// version's ptr-eq assertion to plain equality).
#[test]
fn decoding_preserves_object_sharing() {
    let (_, md) = parse_fixture("SampleRich.olean");
    for (n, c) in md.const_names.iter().zip(md.constants.iter()) {
        assert_eq!(*n, c.name(), "constNames entry not shared with ConstantVal.name");
    }
}

#[test]
fn garbage_still_fails_cleanly() {
    let mut st = Store::persistent();
    assert!(matches!(
        ModuleDataId::parse(b"definitely not an olean", &mut st),
        Err(OleanError::Truncated(_))
    ));
}
```

- [ ] **Step 3: Flip `tests/stdlib_sweep.rs`**

In `every_stdlib_olean_decodes`, replace the parse call (a fresh store per module keeps the decode-only sweep's memory profile flat, matching the old per-module Arc drop):

```rust
    for path in &files {
        let bytes = std::fs::read(path).unwrap();
        let mut st = leanr_kernel::bank::Store::persistent();
        match leanr_olean::ModuleDataId::parse(&bytes, &mut st) {
            Ok(md) => constants += md.constants.len(),
            Err(err) => failures.push(format!("{}: {err}", path.display())),
        }
    }
```

(adjust the file's imports accordingly; the rest of the test is unchanged).

- [ ] **Step 4: Verify goldens byte-identical, run suite**

Run: `cargo test -p leanr_olean --test module_data && mise run test`
Expected: PASS with the golden `.txt` files untouched (`git status` shows no fixture changes).

- [ ] **Step 5: Commit**

```bash
mise run lint
git add -A
git commit -m "feat!: flip parse-path consumers (olean decls, goldens, decode sweep) to direct-to-id decode"
```

---

### Task 6: Flip the loader and the check pipeline

`load_closure` decodes into the caller's store; `leanr check`, the check sweep, and the whole verdict suite (including the mutation-differential harness) move to id forms.

**Files:**
- Modify: `crates/leanr_olean/src/loader.rs`
- Modify: `crates/leanr_cli/src/main.rs` (the `check` fn)
- Modify: `crates/leanr_olean/tests/check_sweep.rs`
- Modify: `crates/leanr_olean/tests/check_fixtures.rs`

**Interfaces:**
- Produces: `pub fn load_closure(sp: &SearchPath, targets: &[Arc<Name>], st: &mut Store) -> Result<Vec<(Arc<Name>, ModuleDataId)>, LoadError>`
- Consumes: `ModuleDataId::{parse, parse_parts}`, `Environment::{store, store_mut, admit_unchecked, get, add_decl, intern_... none}`, `leanr_kernel::{replay, Declaration, ConstantInfo}`.

- [ ] **Step 1: Rewire the loader**

In `loader.rs`:
- `trait ModuleSource`: `fn load(&mut self, module: &Name) -> Result<Self::Module, LoadError>;` (was `&self`).
- `struct FileSource<'a> { search_path: &'a SearchPath, st: &'a mut Store }` with

```rust
impl ModuleSource for FileSource<'_> {
    type Module = ModuleDataId;

    fn load(&mut self, module: &Name) -> Result<ModuleDataId, LoadError> {
        let path = self
            .search_path
            .find(module)
            .ok_or_else(|| LoadError::ModuleNotFound(module.to_string()))?;
        load_module_at(&path, self.st)
    }

    fn imports(module: &ModuleDataId) -> Vec<Arc<Name>> {
        module
            .imports
            .iter()
            .map(|i| Arc::clone(&i.module))
            .collect()
    }
}
```

- `fn load_module_at(base: &Path, st: &mut Store) -> Result<ModuleDataId, LoadError>` — body unchanged except `ModuleData::parse(&base_bytes)` → `ModuleDataId::parse(&base_bytes, st)` and `ModuleData::parse_parts(&parts)` → `ModuleDataId::parse_parts(&parts, st)`.
- `pub fn load_closure(sp: &SearchPath, targets: &[Arc<Name>], st: &mut Store) -> Result<LoadedModules<ModuleDataId>, LoadError> { load_closure_with(&mut FileSource { search_path: sp, st }, targets) }`
- `fn load_closure_with<S: ModuleSource>(src: &mut S, targets: &[Arc<Name>]) -> …` — change the parameter to `&mut S` and every `src.load(...)` call site accordingly; the walk logic is untouched.
- In-file loader tests: in-memory `ModuleSource` impls change `fn load(&self` → `fn load(&mut self`; tests calling `load_closure_with` pass `&mut src`; the find→read→parse test gains `let mut st = Store::persistent();` and threads `&mut st` (or uses the in-memory source unchanged if it never touches files).

- [ ] **Step 2: Rewire `leanr check`**

In `main.rs`'s `check` fn, replace the load + intern section (env is created BEFORE loading — the loader decodes straight into its store; the per-module Arc transient and the bridge walk are gone):

```rust
    let sp = SearchPath::new(roots);
    let mut env = Environment::default();
    let loaded = match leanr_olean::load_closure(&sp, &targets, env.store_mut()) {
        Ok(loaded) => loaded,
        Err(err) => {
            eprintln!("error: {err}");
            return ExitCode::FAILURE;
        }
    };

    // Per-module progress (stderr) while folding the union of constants
    // to replay, and the module that first supplies each constant (so a
    // replay failure can be attributed back to its module). Decoding
    // already interned everything (phase 3, direct-to-id decode) — this
    // loop just builds maps of ids.
    let n = loaded.len();
    let mut constants: HashMap<NameId, ConstantInfo> = HashMap::new();
    let mut owner: HashMap<NameId, Arc<Name>> = HashMap::new();
    for (i, (mod_name, md)) in loaded.into_iter().enumerate() {
        eprintln!("checking {mod_name} ({}/{n})", i + 1);
        for ci in md.constants {
            let name = ci.name();
            owner.entry(name).or_insert_with(|| Arc::clone(&mod_name));
            constants.entry(name).or_insert(ci);
        }
    }

    match leanr_kernel::replay(&mut env, constants) {
        Ok(stats) => {
            println!(
                "checked {n} modules, {} declarations (skipped {} unsafe/partial)",
                stats.checked, stats.skipped_unsafe
            );
            ExitCode::SUCCESS
        }
        Err(err) => {
            // `ReplayError.decl` is an Arc<Name> render; map it back to
            // an id to look up the owning module.
            let module = env
                .store_mut()
                .intern_name(None, &err.decl)
                .ok()
                .flatten()
                .and_then(|id| owner.get(&id))
                .map(|m| m.to_string())
                .unwrap_or_else(|| "?".to_string());
            eprintln!(
                "error: {module}: while replaying '{}': {}",
                err.decl, err.error
            );
            ExitCode::FAILURE
        }
    }
```

- [ ] **Step 3: Rewire `tests/check_sweep.rs`**

Replace its load + intern section with the same pattern (env first, `load_closure(&sp, &targets, env.store_mut())`, then fold `md.constants` into the `HashMap<NameId, ConstantInfo>` by `ci.name()` with `or_insert` — first-seen wins, same as before). Delete the bridge-intern comment block; note the decode-is-interning line instead.

- [ ] **Step 4: Rewire `tests/check_fixtures.rs`**

Top-of-file imports become `use leanr_kernel::bank::NameId; use leanr_kernel::{ConstantInfo, Declaration, Environment, Name};` plus `use leanr_olean::{load_closure, ModuleDataId, PartKind, SearchPath};`. The three replay tests re-plumb mechanically:

- `prelude0_replays_from_empty_env`:

```rust
    let bytes = std::fs::read(fixture_path("Prelude0.olean")).unwrap();
    let mut env = Environment::default();
    let m = ModuleDataId::parse(&bytes, env.store_mut()).unwrap();
    assert!(m.imports.is_empty(), "Prelude0 imports nothing");
    let constants: HashMap<NameId, ConstantInfo> =
        m.constants.into_iter().map(|c| (c.name(), c)).collect();
    let stats = leanr_kernel::replay(&mut env, constants).unwrap();
    // assertions unchanged
```

- `check_library_path_replays_prelude0_from_explicit_root` and `fixture_modules_replay_clean_with_closure`: create `env` first, call `load_closure(&sp, &targets, env.store_mut())`, then fold constants by `ci.name()` exactly as in Step 3.
- `modpriv_parts_replay_from_empty_env`: `ModuleDataId::parse_parts(&[...], env.store_mut())`; name assertions render via `env.store().to_name(None, Some(c.name())).to_string()`.

The mutation-differential harness restructures around one principle: per-mutant isolation is preserved by REBUILDING the env per mutant from bytes (ids are store-relative, so a fresh env means a fresh decode — the Arc version rebuilt from decoded Arc values instead; behaviorally identical, decode is re-run per mutant):

```rust
/// A committed mutant is always a def or theorem; turn its decoded
/// id `ConstantInfo` into the `Declaration` the oracle handed to
/// `addDeclCore`.
fn mutant_to_declaration(ci: &ConstantInfo, env: &Environment) -> Declaration {
    match ci {
        ConstantInfo::Defn(v) => Declaration::Defn(v.clone()),
        ConstantInfo::Thm(v) => Declaration::Thm(v.clone()),
        other => panic!(
            "mutant {} is {}, not a def/thm",
            env.store().to_name(None, Some(other.name())),
            other.kind()
        ),
    }
}

/// The differential core (id form). Per-mutant isolation: each verdict
/// line gets a FRESH `Environment`, into which `build_base` decodes and
/// trust-admits the import closure and `mutant_bytes` decodes the
/// mutant set — ids are store-relative, so isolation means re-decoding
/// (the Arc version re-bridged pre-decoded values; same semantics,
/// re-run decode). Acceptable for a differential test over a handful
/// of mutants.
fn assert_verdicts_match(
    build_base: impl Fn(&mut Environment),
    mutant_bytes: &[u8],
    text: &str,
) {
    let verdicts = parse_verdicts(text);
    assert!(!verdicts.is_empty(), "no mutant verdict lines in jsonl");

    let mut accepts = 0usize;
    let mut rejects = 0usize;
    let mut disagreements: Vec<String> = Vec::new();
    for (name, oracle) in &verdicts {
        let mut env = Environment::default();
        build_base(&mut env);
        let mutants = ModuleDataId::parse(mutant_bytes, env.store_mut())
            .expect("mutants decode")
            .constants;
        let ci = mutants
            .iter()
            .find(|c| env.store().to_name(None, Some(c.name())).to_string() == *name)
            .unwrap_or_else(|| panic!("mutant {name} is in the jsonl but missing from the olean"));
        let decl = mutant_to_declaration(ci, &env);
        let leanr = match env.add_decl(decl) {
            Ok(()) => "accept",
            Err(_) => "reject",
        };
        match oracle.as_str() {
            "accept" => accepts += 1,
            "reject" => rejects += 1,
            other => panic!("mutant {name}: unknown oracle verdict {other:?}"),
        }
        if leanr != oracle {
            disagreements.push(format!("  {name}: leanr={leanr} oracle={oracle}"));
        }
    }

    assert!(
        disagreements.is_empty(),
        "leanr disagreed with the oracle kernel on {} mutant(s):\n{}",
        disagreements.len(),
        disagreements.join("\n")
    );
    assert!(accepts >= 5, "harness needs >= 5 accepts, got {accepts}");
    assert!(rejects >= 5, "harness needs >= 5 rejects, got {rejects}");
}
```

with the two callers:

```rust
#[test]
fn mutation_verdicts_hermetic() {
    let base_bytes = std::fs::read(fixture_path("MutBase.olean"))
        .expect("MutBase.olean missing — run `mise run fixtures:mutations`");
    let mut_bytes = std::fs::read(fixture_path("Mutations0.olean"))
        .expect("Mutations0.olean missing — run `mise run fixtures:mutations`");
    let text = std::fs::read_to_string(fixture_path("mutations0-verdicts.jsonl"))
        .expect("mutations0-verdicts.jsonl missing — run `mise run fixtures:mutations`");

    assert_verdicts_match(
        |env| {
            let base = ModuleDataId::parse(&base_bytes, env.store_mut())
                .expect("MutBase decodes")
                .constants;
            for ci in base {
                env.admit_unchecked(ci).expect("base admits");
            }
        },
        &mut_bytes,
        &text,
    );
}

#[test]
#[ignore = "needs the pinned toolchain (LEANR_SWEEP_DIR); the hermetic variant is the CI acceptance"]
fn mutation_verdicts_toolchain() {
    let dir = std::env::var("LEANR_SWEEP_DIR")
        .expect("LEANR_SWEEP_DIR must point at the toolchain lib/lean dir");
    let mut_bytes = std::fs::read(fixture_path("Mutations.olean"))
        .expect("Mutations.olean missing — run `mise run fixtures:mutations`");
    let text = std::fs::read_to_string(fixture_path("mutations-verdicts.jsonl"))
        .expect("mutations-verdicts.jsonl missing — run `mise run fixtures:mutations`");

    let sp = SearchPath::new(vec![PathBuf::from(&dir)]);
    assert_verdicts_match(
        |env| {
            // Trusted import closure, decoded fresh per mutant (see
            // assert_verdicts_match's isolation note; local-only test,
            // wall clock over correctness). First-seen wins on the rare
            // cross-module duplicate, matching the old HashSet dedup.
            let modules = load_closure(&sp, &[name("Init.Core")], env.store_mut())
                .expect("Init.Core closure loads");
            for (_, md) in modules {
                for ci in md.constants {
                    if env.get(ci.name()).is_none() {
                        env.admit_unchecked(ci).expect("base admits");
                    }
                }
            }
        },
        &mut_bytes,
        &text,
    );
}
```

(`Environment::get(NameId)` is existing public API, env.rs:~244.) Delete the now-unused `ArcConstantInfo`/`ArcDeclaration`/`HashSet`/`Arc` imports and the old header comment about bridge-interning; update the file doc comment to say decode is interning (phase 3).

- [ ] **Step 5: Run the verdict suite and everything else**

Run: `cargo test -p leanr_olean && mise run test`
Expected: PASS — in particular `mutation_verdicts_hermetic` (the hard verdict gate) and the two `#[ignore]`d toolchain tests still compile.

- [ ] **Step 6: Commit**

```bash
mise run lint
git add -A
git commit -m "feat!: flip loader and check pipeline to direct-to-id decode"
```

---

### Task 7: Delete the Arc decode path; demote the Arc declaration machinery

Nothing outside tests reaches the Arc path anymore. Delete it, rename `ModuleDataId` → `ModuleData`, and demote the kernel's Arc declaration family to test support per the spec's deletion rule ("any Arc-side item unreachable from non-test code after the flip is deleted; test-only survivors are demoted").

**Files:**
- Modify: `crates/leanr_olean/src/interp.rs` (delete Arc decode fns; keep Name/Syntax decode)
- Modify: `crates/leanr_olean/src/interp_id.rs` (delete the gate test module's Arc-path pieces; rename references)
- Modify: `crates/leanr_olean/src/module_data.rs` (delete Arc `ModuleData`, rename `ModuleDataId` → `ModuleData`)
- Modify: `crates/leanr_olean/src/lib.rs`, `crates/leanr_olean/src/loader.rs`, `crates/leanr_cli/src/main.rs`, `crates/leanr_olean/tests/*.rs` (rename fallout)
- Modify: `crates/leanr_kernel/src/decl.rs`, `crates/leanr_kernel/src/env.rs`, `crates/leanr_kernel/src/lib.rs` (demotion)
- Modify: `mise.toml` (delete `gate:direct-decode`)

- [ ] **Step 1: Delete the gate and the Arc decode path in `leanr_olean`**

- `interp_id.rs`: delete `assert_paths_agree`, the five fixture gate tests, `collect_oleans`, and `stdlib_paths_agree` (the per-conversion logic keeps no gate residue). Keep `with_arc`? No — its only caller was the gate; delete it and inline `Interp::new()` into `InterpId::new`.
- `mise.toml`: delete the `gate:direct-decode` task.
- `interp.rs`: delete `sub_level`, `level`, `sub_expr`, `expr`, `build_expr`, `literal`, `kvmap`, `data_value`, `constant_val`, `constant_info`, `import`, `module_data`, `names`; delete the `levels`/`exprs`/`zero`/`guard` fields from `Interp` (and the now-dead imports: the `Arc*` decl aliases, `Expr`, `Level`, `Literal`, `KVMap`, `DataValue`, `BinderInfo`, `DefinitionSafety`, `ReducibilityHints` re-export stays only if `reducibility` needs it, `RecGuard`, `num_bigint` if unused). `Interp` keeps: `names`, `syntaxes`, `anonymous`, `missing`; fns `new`, `name`, `sub_syntax`, `syntax`, `build_syntax`, `preresolved`; free helpers and `reducibility` stay. Update the module doc: this file now decodes only the surviving Arc-tree positions (Syntax family + names for it and for `Import.module`); the id decoder in `interp_id.rs` is the main path. The four existing syntax tests stay as-is.
- `module_data.rs`: delete the Arc `ModuleData` struct and its `parse`/`parse_parts` (moving the `parse_parts` oracle-rationale doc comment onto the id version wholesale, as flagged in Task 3); rename `ModuleDataId` → `ModuleData` here and at every use site (`lib.rs` exports only the one name now; `interp_id.rs`, `loader.rs`, CLI, all four integration test files). `Import` struct is unchanged.
- If `OleanError::DeepRecursion` now has no constructor site (its only producers were the Arc `Expr::sort`/`Expr::const_` calls), delete the variant; `grep -rn "DeepRecursion" crates/` first — `parse_parts`'s Arc duplicate check was the other producer and is gone too.

- [ ] **Step 2: Demote the kernel's Arc declaration machinery**

Ground truth is reachability, so verify before gating (`--all-targets` builds tests too — use a plain build for the non-test view):

```bash
grep -rn "ArcConstantInfo\|ArcDeclaration\|intern_constant_info\|intern_declaration\|intern_module\|from_modules\|to_constant_info\|arc_constant_info_eq\|intern_expr\|to_expr" crates/*/src --include=*.rs | grep -v "^.*tests" 
```

Expected reachability after Task 6 (verify, then act):
- `Environment::from_modules` — no callers left anywhere: DELETE.
- `Environment::intern_module`, `Environment::intern_declaration` — callers only in `replay/tests.rs` and kernel test modules: gate each with `#[cfg(test)]`.
- `decl.rs` Arc section (the `Arc*` types, `intern_*` bridges, `to_*` bridges, `arc_constant_info_eq`) — callers only in kernel test code (`testenv`, `replay/tests.rs`, `decl.rs` tests, bank tests): gate the whole Arc section with `#[cfg(test)]` (one `#[cfg(test)]` on a `mod` wrapper re-exported via `#[cfg(test)] pub use`, or per-item — pick whichever keeps the diff smallest) and move the corresponding `pub use decl::{Arc…, arc_constant_info_eq, to_constant_info}` exports in `lib.rs` under `#[cfg(test)]`.
- `Store::intern_expr` / `Store::to_expr` and the tree `Expr` type: these are used by the (now test-gated) bridges AND possibly by non-test kernel internals — check the grep output. If non-test callers remain (e.g. error rendering), they stay ungated; record what stayed and why in the commit message. Do NOT delete `expr.rs`'s tree type if the bank property tests use it as the shadow reference — that is the spec's "demote to test support" case; a `#[cfg(test)]` on the type itself is only possible if no non-test code names it, otherwise leave it with a doc comment stating its remaining roles.
- Update `decl.rs`'s module doc: the boundary sentence ("They remain the decoder boundary until phase 3") is now historical — rewrite to say the Arc twins are test support for the kernel's own suites; the decoder is id-native.

- [ ] **Step 3: Full verification**

```bash
cargo build --workspace            # non-test build: proves nothing non-test reaches deleted/gated items
mise run lint && mise run test     # clippy -D warnings + full suite
```

Expected: clean build, all green, golden fixtures untouched.

- [ ] **Step 4: Commit**

```bash
git add -A
git commit -m "refactor!: delete Arc decode path and differential gate; demote Arc decl family to kernel test support"
```

---

### Task 8: Acceptance sweep, docs, and disposition close-out

**Files:**
- Modify: `docs/superpowers/specs/2026-07-10-direct-to-id-decode-design.md` (Acceptance records)
- Modify: `docs/superpowers/specs/2026-07-06-compact-expr-term-bank-design.md` (§4/phase-3 disposition note)
- Modify: `ARCHITECTURE.md` (decoder paragraph)
- Modify: `docs/THREAT_MODEL.md` (direct-interning posture paragraph)

- [ ] **Step 1: Run the post-flip acceptance sweep**

Run: `mise run check:stdlib:watched`
Expected: exit 0, `checked 2433 modules, 203134 declarations (skipped 3611 unsafe/partial)` (same coverage figures as the recorded baseline). Record peak RSS and wall clock from the watchdog output; the standard is flat-or-better vs 2 GiB / 367.62 s — a small regression is tolerable only under the pod limit (spec), but investigate anything notable before accepting.

- [ ] **Step 2: Record acceptance in the spec**

Fill the spec's Acceptance section items 2 and 3 with dated results: sweep figures + peak RSS + wall clock; deletion verification (one-line summary of what was deleted vs demoted, from Task 7's step 2 findings).

- [ ] **Step 3: Close the parent spec's phase-3 disposition**

In `2026-07-06-compact-expr-term-bank-design.md`, add a short dated note under §4 (or the sequencing section): phase 3 landed per `2026-07-10-direct-to-id-decode-design.md`, decoder is id-native, Arc boundary deleted/demoted, figures as recorded.

- [ ] **Step 4: Update `ARCHITECTURE.md` and `docs/THREAT_MODEL.md`**

- `ARCHITECTURE.md`, `leanr_kernel`/`leanr_olean` bullets: replace the "Arc… remain as the decoder-boundary types … that boundary lifts in phase 3" sentences with the landed state: `leanr_olean` decodes straight into the caller's term-bank store (`interp` keeps only the Syntax-family Arc decode); the Arc declaration family survives solely as kernel test support.
- `docs/THREAT_MODEL.md`: add a paragraph under the `.olean` trust-boundary section making the spec's argument explicit: untrusted bytes now drive interning directly into the kernel's persistent store; the raw phase remains the entire untrusted-bytes surface (fuzzed); the bank's interning API is panic-free, bounds-checked, `unsafe`-free, and mints ids only canonically; the decode walk is explicit-stack; partial-decode residue is inert.

- [ ] **Step 5: Final suite + commit**

```bash
mise run lint && mise run test
git add -A
git commit -m "docs: phase-3 acceptance — direct-to-id decode landed, sweep figures recorded, disposition closed"
```

---

## Self-Review Notes (resolved during planning)

- **Syntax ptr-eq vs the gate:** kvmap rows compare `Syntax` payloads by `Arc::ptr_eq`, so two independent decoders would spuriously disagree on syntax-bearing mdata. Resolved by the gate's shared-Arc-interpreter construction (`InterpId::with_arc`), which makes the comparison exact rather than relaxed. The stdlib sweep found real `ofSyntax` constants, so this is load-bearing, not theoretical.
- **Parts gate coverage:** companion parts are not self-contained regions, so the single-file gate cannot decode them standalone. The parts path is covered by (a) per-part decode equivalence via the single-file gate, (b) the id `parse_parts` merge tests + ModPriv replay, (c) the post-flip full check sweep, which loads every module-system module through `parse_parts`.
- **Mutation-harness isolation:** ids are store-relative, so the Arc version's rebuild-from-decoded-values isolation becomes rebuild-by-re-decoding. Hermetic variant: trivial cost. Toolchain variant: per-mutant closure re-decode, slow but local-only and `#[ignore]`d; semantics preserved exactly.
- **`Environment::from_modules` cannot survive:** id constants only make sense in the store they were interned into; its replacement is decode-into-`store_mut` + `admit_unchecked`.
