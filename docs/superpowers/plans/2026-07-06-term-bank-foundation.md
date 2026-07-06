# Term-Bank Foundation Implementation Plan (compact Expr, phase 1 of 3)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the complete, standalone index-based term bank (`ExprId`/`NameId`/`LevelId` stores, dedup probe table, intern-constructors, scratch region, promotion, and `Arc<Expr>` bridges) inside `leanr_kernel`, fully tested against the existing representation — without touching any production code path.

**Architecture:** One `Store` struct per region (persistent vs scratch, distinguished by the top bit of every id). All sub-banks (strings, nats, ints, names, levels, level-lists, kvmaps, LetE spills, expr rows) live inside `Store` and dedup through one hand-rolled open-addressing `IdTable` that rehashes rows from the arrays (no key duplication). A scratch `Store` consults the persistent one on every intern, so an id is equal iff the terms are structurally equal — across regions. Bridges to/from today's `Arc<Expr>` make the whole thing differentially testable now and drive the phase-2 migration and phase-3 decoder.

**Tech Stack:** Rust, `leanr_kernel` only (no new dependencies, no `unsafe`). Spec: `docs/superpowers/specs/2026-07-06-compact-expr-term-bank-design.md`.

## Global Constraints

- `leanr_kernel` depends on no workspace crate and gains no external deps.
- No `unsafe` anywhere, including the probe table.
- Untrusted-input discipline: no panics reachable from attacker data; recursion over attacker-depth structures uses explicit stacks (bridges/promotion) — never native recursion; id/pool exhaustion returns `KernelError::BankExhausted`, never a panic.
- The interning invariant (spec §1) is the contract every task serves: **equal ids ⇔ structurally equal terms** (today's `structural_eq` relation, including binder names, `BinderInfo`, `non_dep`, `KVMap` with its `OfSyntax` ptr-eq rule).
- Lint gate before every commit: `mise run lint`. Conventional-commit prefixes.
- Region bit: `REGION_BIT = 1 << 31` on the raw bits of **every** id type; persistent region = 0, scratch = 1.

## File Structure

- Create `crates/leanr_kernel/src/bank/mod.rs` — id newtypes, `Store`, region constants, module docs.
- Create `crates/leanr_kernel/src/bank/probe.rs` — `IdTable`.
- Create `crates/leanr_kernel/src/bank/pools.rs` — generic `ValuePool<T>` + row types for kvmaps/spills.
- Create `crates/leanr_kernel/src/bank/names.rs` — `NameBank`.
- Create `crates/leanr_kernel/src/bank/levels.rs` — `LevelBank`.
- Create `crates/leanr_kernel/src/bank/terms.rs` — `TermBank` (expr rows), `Node` view, intern-constructors, `Arc<Expr>` bridges.
- Create `crates/leanr_kernel/src/bank/scratch.rs` — cross-region views + `promote`.
- Create `crates/leanr_kernel/src/bank/tests.rs` — property/differential suite (unit tests live inline in each file).
- Modify `crates/leanr_kernel/src/lib.rs` — `pub mod bank;`.
- Modify `crates/leanr_kernel/src/error.rs` — add `KernelError::BankExhausted`.
- Modify `crates/leanr_kernel/src/expr.rs` — `pub(crate)` on data-word helpers (no behavior change).

---

### Task 1: Id types, `KernelError::BankExhausted`, module scaffolding, probe table

**Files:**
- Create: `crates/leanr_kernel/src/bank/mod.rs`, `crates/leanr_kernel/src/bank/probe.rs`
- Modify: `crates/leanr_kernel/src/lib.rs` (add `pub mod bank;` after the existing `mod expr;` line), `crates/leanr_kernel/src/error.rs`
- Test: inline `#[cfg(test)]` in `probe.rs` and `mod.rs`

**Interfaces:**
- Consumes: `KernelError` (error.rs).
- Produces: `REGION_BIT: u32`; id newtypes `ExprId, NameId, LevelId, StrId, NatId, IntId, LevelsId, KVMapId, SpillId` each with `from_index(index: u32, scratch: bool) -> Option<Self>`, `index(self) -> usize`, `is_scratch(self) -> bool`, `bits(self) -> u32`, `from_bits(bits: u32) -> Option<Self>`; `IdTable` with `new()`, `len() -> u32`, `lookup(&self, hash: u64, eq: impl FnMut(u32) -> bool) -> Option<u32>`, `insert(&mut self, hash: u64, bits: u32, rehash: impl FnMut(u32) -> u64)`.

- [ ] **Step 1: Write the failing tests.** Create `crates/leanr_kernel/src/bank/probe.rs` containing ONLY the test module for now:

```rust
//! Open-addressing id table (spec §1 "dedup at construction").
//!
//! Stores raw id *bits* (`u32`, nonzero — id encodings guarantee this)
//! in power-of-two slot arrays; `0` is the empty-slot sentinel. Keys are
//! never stored: the caller rehashes/compares rows straight from its
//! bank arrays, so the table costs ~4-8 bytes per entry at 50% max load.
//! Safe code only.

#[cfg(test)]
mod tests {
    use super::IdTable;

    #[test]
    fn insert_then_lookup_finds_bits() {
        let mut t = IdTable::new();
        t.insert(42, 7, |_| unreachable!("no growth at one entry"));
        assert_eq!(t.lookup(42, |bits| bits == 7), Some(7));
        assert_eq!(t.len(), 1);
    }

    #[test]
    fn lookup_misses_on_eq_false() {
        let mut t = IdTable::new();
        t.insert(42, 7, |_| unreachable!());
        // Same hash, eq rejects: a collision that is not the same row.
        assert_eq!(t.lookup(42, |_| false), None);
    }

    #[test]
    fn colliding_hashes_coexist() {
        let mut t = IdTable::new();
        // All the same hash — forces probe chains.
        for id in 1..=100u32 {
            t.insert(5, id, |bits| if bits <= 100 { 5 } else { unreachable!() });
        }
        for id in 1..=100u32 {
            assert_eq!(t.lookup(5, |bits| bits == id), Some(id), "id {id}");
        }
        assert_eq!(t.len(), 100);
    }

    #[test]
    fn growth_preserves_entries() {
        let mut t = IdTable::new();
        // Distinct hashes, enough to force several doublings; rehash
        // callback recomputes each entry's hash (here: identity of bits).
        for id in 1..=10_000u32 {
            t.insert(id as u64, id, |bits| bits as u64);
        }
        for id in (1..=10_000u32).step_by(97) {
            assert_eq!(t.lookup(id as u64, |bits| bits == id), Some(id));
        }
        assert_eq!(t.len(), 10_000);
    }
}
```

- [ ] **Step 2: Run to verify failure.** Add `pub mod bank;` to `crates/leanr_kernel/src/lib.rs` (directly after `mod expr;`), create `crates/leanr_kernel/src/bank/mod.rs` with just `pub mod probe;`, then:

Run: `cargo test -p leanr_kernel bank::probe 2>&1 | tail -5`
Expected: compile error — `IdTable` not found.

- [ ] **Step 3: Implement `IdTable`** (above the test module in `probe.rs`):

```rust
pub struct IdTable {
    /// Power-of-two slot array; 0 = empty (id bits are never 0).
    slots: Vec<u32>,
    len: u32,
}

impl Default for IdTable {
    fn default() -> Self {
        Self::new()
    }
}

impl IdTable {
    pub fn new() -> IdTable {
        IdTable {
            slots: vec![0; 16],
            len: 0,
        }
    }

    pub fn len(&self) -> u32 {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Triangular probing over a power-of-two table visits every slot.
    fn probe_start(&self, hash: u64) -> usize {
        // Fold the high bits in so low-entropy hashes still spread.
        ((hash ^ (hash >> 32)) as usize) & (self.slots.len() - 1)
    }

    /// Find an entry whose stored bits satisfy `eq` under `hash`.
    /// `eq` receives candidate id bits and must compare the actual rows.
    pub fn lookup(&self, hash: u64, mut eq: impl FnMut(u32) -> bool) -> Option<u32> {
        let mask = self.slots.len() - 1;
        let mut i = self.probe_start(hash);
        let mut step = 0usize;
        loop {
            let bits = self.slots[i];
            if bits == 0 {
                return None;
            }
            if eq(bits) {
                return Some(bits);
            }
            step += 1;
            if step > self.slots.len() {
                return None; // table full of non-matches (cannot happen below max load)
            }
            i = (i + step) & mask;
        }
    }

    /// Insert `bits` under `hash`. The caller has already checked the
    /// entry is absent (`lookup` returned `None`). Grows at 50% load;
    /// `rehash` recomputes the hash of an existing entry from its bits.
    pub fn insert(&mut self, hash: u64, bits: u32, mut rehash: impl FnMut(u32) -> u64) {
        debug_assert_ne!(bits, 0);
        if (self.len as usize + 1) * 2 > self.slots.len() {
            let old = std::mem::replace(&mut self.slots, vec![0; self.slots.len() * 2]);
            for b in old {
                if b != 0 {
                    let h = rehash(b);
                    self.place(h, b);
                }
            }
        }
        self.place(hash, bits);
        self.len += 1;
    }

    fn place(&mut self, hash: u64, bits: u32) {
        let mask = self.slots.len() - 1;
        let mut i = self.probe_start(hash);
        let mut step = 0usize;
        while self.slots[i] != 0 {
            step += 1;
            i = (i + step) & mask;
        }
        self.slots[i] = bits;
    }
}
```

- [ ] **Step 4: Run probe tests.**

Run: `cargo test -p leanr_kernel bank::probe 2>&1 | tail -3`
Expected: `4 passed`

- [ ] **Step 5: Add `KernelError::BankExhausted`.** In `crates/leanr_kernel/src/error.rs`, append to the `KernelError` enum (keep alphabetical/grouped placement natural to the file):

```rust
    /// The term bank's 2³¹-per-region id space (or a side pool) is
    /// exhausted. Ids are minted once per *distinct* interned row, so
    /// reaching this bound requires input of comparable size —
    /// rejection is incompleteness on absurd input, never unsoundness
    /// (same posture as `DeepRecursion`).
    BankExhausted,
```

and add the matching `Display` arm next to `DeepRecursion`'s (mirror its phrasing style):

```rust
            KernelError::BankExhausted => write!(f, "term bank id space exhausted"),
```

- [ ] **Step 6: Write id-type tests in `mod.rs`:**

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn id_roundtrips_index_and_region() {
        let p = ExprId::from_index(0, false).unwrap();
        assert_eq!(p.index(), 0);
        assert!(!p.is_scratch());
        let s = ExprId::from_index(12345, true).unwrap();
        assert_eq!(s.index(), 12345);
        assert!(s.is_scratch());
        assert_eq!(ExprId::from_bits(s.bits()), Some(s));
    }

    #[test]
    fn id_max_index_is_bounded() {
        assert!(ExprId::from_index(MAX_INDEX, false).is_some());
        assert!(ExprId::from_index(MAX_INDEX + 1, false).is_none());
    }

    #[test]
    fn zero_bits_is_no_id() {
        assert_eq!(ExprId::from_bits(0), None);
    }
}
```

- [ ] **Step 7: Implement the id machinery in `mod.rs`:**

```rust
//! Index-based term bank (spec:
//! docs/superpowers/specs/2026-07-06-compact-expr-term-bank-design.md).
//!
//! Phase 1: standalone next to the `Arc<Expr>` representation; nothing
//! in the production kernel path uses this module yet. Every id type
//! carries a region bit (persistent env bank vs per-declaration
//! scratch); raw bits are never 0, so probe tables can use 0 as the
//! empty sentinel.

pub mod levels;
pub mod names;
pub mod pools;
pub mod probe;
pub mod scratch;
pub mod terms;

use std::num::NonZeroU32;

/// Top bit of every id: set ⇒ the row lives in the scratch region.
pub const REGION_BIT: u32 = 1 << 31;
/// Largest storable row index per region: bits = index + 1 must stay
/// below `REGION_BIT`.
pub const MAX_INDEX: u32 = REGION_BIT - 2;

macro_rules! id_type {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name(NonZeroU32);

        impl $name {
            pub fn from_index(index: u32, scratch: bool) -> Option<$name> {
                if index > MAX_INDEX {
                    return None;
                }
                let bits = (index + 1) | if scratch { REGION_BIT } else { 0 };
                NonZeroU32::new(bits).map($name)
            }
            pub fn from_bits(bits: u32) -> Option<$name> {
                NonZeroU32::new(bits).map($name)
            }
            pub fn bits(self) -> u32 {
                self.0.get()
            }
            pub fn index(self) -> usize {
                ((self.0.get() & !REGION_BIT) - 1) as usize
            }
            pub fn is_scratch(self) -> bool {
                self.0.get() & REGION_BIT != 0
            }
        }
    };
}

id_type!(/** Expression row id. */ ExprId);
id_type!(/** Hierarchical name id (`None` = anonymous). */ NameId);
id_type!(/** Universe level id. */ LevelId);
id_type!(/** String-pool id. */ StrId);
id_type!(/** Nat (bignum) pool id. */ NatId);
id_type!(/** Int (bignum) pool id. */ IntId);
id_type!(/** Level-list pool id (Const's levels). */ LevelsId);
id_type!(/** KVMap pool id. */ KVMapId);
id_type!(/** LetE spill pool id. */ SpillId);
```

(`Store` is added in Task 2; `pub mod` lines for not-yet-created files are added task by task — at this point keep only `pub mod probe;` plus the id machinery, and add each module line when its file is created.)

- [ ] **Step 8: Run tests + lint.**

Run: `cargo test -p leanr_kernel bank:: 2>&1 | tail -3` → all pass.
Run: `mise run lint` → clean.
Run: `cargo test -p leanr_kernel 2>&1 | grep "test result: ok" | head -2` → existing suite untouched.

- [ ] **Step 9: Commit.**

```bash
git add crates/leanr_kernel/src/bank crates/leanr_kernel/src/lib.rs crates/leanr_kernel/src/error.rs
git commit -m "feat: term-bank ids, region bit, and dedup probe table (bank phase 1, Task 1)"
```

---

### Task 2: Generic `ValuePool` + leaf pools + `Store` shell

**Files:**
- Create: `crates/leanr_kernel/src/bank/pools.rs`
- Modify: `crates/leanr_kernel/src/bank/mod.rs` (add `pub mod pools;`, add `Store`)
- Test: inline in `pools.rs`

**Interfaces:**
- Consumes: `IdTable`, id types, `KernelError::BankExhausted`; `Nat`/`Int` (num.rs, both derive `Eq + Hash`).
- Produces:
  - `ValuePool<T>` with `new(region: u32)`, `len()`, `get(index: usize) -> Option<&T>`, `lookup(&self, hash: u64, eq: impl FnMut(&T) -> bool) -> Option<u32>` (returns bits), `intern(&mut self, hash: u64, eq: impl FnMut(&T) -> bool, make: impl FnOnce() -> T, rehash: impl FnMut(&T) -> u64) -> Result<u32, KernelError>` (returns bits of the existing-or-new row).
  - `Store` shell holding `pub strs: ValuePool<Box<str>>, pub nats: ValuePool<Nat>, pub ints: ValuePool<Int>` plus `region: u32`, `Store::persistent()`, `Store::scratch()`, and hash helpers `pub(crate) fn sip(x: &impl std::hash::Hash) -> u64`.
  - `Store::intern_str(&mut self, base: Option<&Store>, s: &str) -> Result<StrId, KernelError>`, `Store::intern_nat(&mut self, base: Option<&Store>, n: &Nat) -> Result<NatId, KernelError>`, `Store::intern_int(&mut self, base: Option<&Store>, i: &Int) -> Result<IntId, KernelError>`, and read accessors `str_at(&self, base: Option<&Store>, id: StrId) -> &str`, `nat_at(...) -> &Nat`, `int_at(...) -> &Int` (these take the *pair* and route on the region bit; callers of a persistent-only store pass `None`).

- [ ] **Step 1: Failing tests** (in `pools.rs`):

```rust
#[cfg(test)]
mod tests {
    use crate::bank::{Store, REGION_BIT};
    use crate::Nat;

    #[test]
    fn str_pool_dedups() {
        let mut s = Store::persistent();
        let a = s.intern_str(None, "hello").unwrap();
        let b = s.intern_str(None, "hello").unwrap();
        let c = s.intern_str(None, "world").unwrap();
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(s.str_at(None, a), "hello");
    }

    #[test]
    fn nat_pool_dedups_by_value() {
        let mut s = Store::persistent();
        let a = s.intern_nat(None, &Nat::from(7u64)).unwrap();
        let b = s.intern_nat(None, &Nat::from(7u64)).unwrap();
        assert_eq!(a, b);
        assert_eq!(s.nat_at(None, a), &Nat::from(7u64));
    }

    #[test]
    fn scratch_consults_base_first() {
        let mut base = Store::persistent();
        let pa = base.intern_str(None, "shared").unwrap();
        let mut scr = Store::scratch();
        let sa = scr.intern_str(Some(&base), "shared").unwrap();
        // Structurally equal ⇒ the persistent id, not a new scratch row.
        assert_eq!(sa, pa);
        assert!(!sa.is_scratch());
        // A genuinely new string goes to scratch with the region bit.
        let sb = scr.intern_str(Some(&base), "fresh").unwrap();
        assert!(sb.is_scratch());
        assert_eq!(sb.bits() & REGION_BIT, REGION_BIT);
        assert_eq!(scr.str_at(Some(&base), sb), "fresh");
        // Resolving a base id through the pair still works.
        assert_eq!(scr.str_at(Some(&base), pa), "shared");
    }
}
```

- [ ] **Step 2: Run to verify failure.** `cargo test -p leanr_kernel bank::pools 2>&1 | tail -3` → compile error (`Store` unknown).

- [ ] **Step 3: Implement.** `pools.rs`:

```rust
//! Deduplicated value pools (spec §1 "side pools"). One `ValuePool<T>`
//! = `Vec<T>` rows + an `IdTable` that rehashes rows from the vec, so
//! values are stored exactly once.

use super::probe::IdTable;
use super::{KernelErrorExt, MAX_INDEX};
use crate::KernelError;

pub struct ValuePool<T> {
    items: Vec<T>,
    table: IdTable,
    region: u32,
}

impl<T> ValuePool<T> {
    pub fn new(region: u32) -> ValuePool<T> {
        ValuePool {
            items: Vec::new(),
            table: IdTable::new(),
            region,
        }
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.items.get(index)
    }

    fn row_of_bits(&self, bits: u32) -> &T {
        // bits produced by this pool: strip region, -1.
        &self.items[((bits & !super::REGION_BIT) - 1) as usize]
    }

    /// Probe for an existing row (read-only; used cross-region).
    pub fn lookup(&self, hash: u64, mut eq: impl FnMut(&T) -> bool) -> Option<u32> {
        self.table.lookup(hash, |bits| eq(self.row_of_bits(bits)))
    }

    /// Intern: return existing bits or append a new row.
    pub fn intern(
        &mut self,
        hash: u64,
        eq: impl FnMut(&T) -> bool,
        make: impl FnOnce() -> T,
        mut rehash: impl FnMut(&T) -> u64,
    ) -> Result<u32, KernelError> {
        if let Some(bits) = self.lookup(hash, eq) {
            return Ok(bits);
        }
        let index = u32::try_from(self.items.len()).map_err(|_| KernelError::BankExhausted)?;
        if index > MAX_INDEX {
            return Err(KernelError::BankExhausted);
        }
        self.items.push(make());
        let bits = (index + 1) | self.region;
        // Rehash borrows rows immutably; split via a local closure over
        // the (already pushed) items.
        let items = &self.items;
        self.table.insert(hash, bits, |b| {
            rehash(&items[((b & !super::REGION_BIT) - 1) as usize])
        });
        Ok(bits)
    }
}
```

`mod.rs` additions (below the id macros):

```rust
use crate::{Int, KernelError, Nat};
use pools::ValuePool;

/// Marker trait so pools.rs can name the error without a cycle.
pub(crate) trait KernelErrorExt {}

/// Stable sip-style hash for pool values (DefaultHasher is fine: hashes
/// never persist and only feed in-process probe tables).
pub(crate) fn sip<T: std::hash::Hash + ?Sized>(x: &T) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut h = DefaultHasher::new();
    x.hash(&mut h);
    h.finish()
}

/// One region's complete storage (spec §2). The persistent `Store` is
/// phase 2's `Environment` bank; a scratch `Store` is a per-declaration
/// overlay whose intern methods consult `base` first.
pub struct Store {
    pub region: u32,
    pub strs: ValuePool<Box<str>>,
    pub nats: ValuePool<Nat>,
    pub ints: ValuePool<Int>,
    // Extended by Tasks 3-6: names, levels, level_lists, kvmaps,
    // spills, terms.
}

impl Store {
    pub fn persistent() -> Store {
        Store::new(0)
    }
    pub fn scratch() -> Store {
        Store::new(REGION_BIT)
    }
    fn new(region: u32) -> Store {
        Store {
            region,
            strs: ValuePool::new(region),
            nats: ValuePool::new(region),
            ints: ValuePool::new(region),
        }
    }

    /// Route an id to the store owning its region. `base` is `None`
    /// only when `self` IS the persistent store.
    fn store_for(&self, base: Option<&Store>, scratch_bit: bool) -> &Store {
        if scratch_bit {
            self
        } else {
            base.unwrap_or(self)
        }
    }

    pub fn intern_str(&mut self, base: Option<&Store>, s: &str) -> Result<StrId, KernelError> {
        let h = sip(s);
        if let Some(b) = base {
            if let Some(bits) = b.strs.lookup(h, |t| &**t == s) {
                return StrId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        let bits = self
            .strs
            .intern(h, |t| &**t == s, || s.into(), |t| sip(&**t))?;
        StrId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }

    pub fn str_at<'a>(&'a self, base: Option<&'a Store>, id: StrId) -> &'a str {
        self.store_for(base, id.is_scratch())
            .strs
            .get(id.index())
            .map(|b| &**b)
            .expect("StrId minted by intern ⇒ valid")
    }

    pub fn intern_nat(&mut self, base: Option<&Store>, n: &Nat) -> Result<NatId, KernelError> {
        let h = sip(n);
        if let Some(b) = base {
            if let Some(bits) = b.nats.lookup(h, |t| t == n) {
                return NatId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        let bits = self.nats.intern(h, |t| t == n, || n.clone(), sip)?;
        NatId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }

    pub fn nat_at<'a>(&'a self, base: Option<&'a Store>, id: NatId) -> &'a Nat {
        self.store_for(base, id.is_scratch())
            .nats
            .get(id.index())
            .expect("NatId minted by intern ⇒ valid")
    }

    pub fn intern_int(&mut self, base: Option<&Store>, i: &Int) -> Result<IntId, KernelError> {
        let h = sip(i);
        if let Some(b) = base {
            if let Some(bits) = b.ints.lookup(h, |t| t == i) {
                return IntId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        let bits = self.ints.intern(h, |t| t == i, || i.clone(), sip)?;
        IntId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }

    pub fn int_at<'a>(&'a self, base: Option<&'a Store>, id: IntId) -> &'a Int {
        self.store_for(base, id.is_scratch())
            .ints
            .get(id.index())
            .expect("IntId minted by intern ⇒ valid")
    }
}
```

Note on the `expect`s: they are unreachable for ids minted by these interns (the only constructors); this is an internal-invariant assert on *our* code, not on attacker data — attacker data can only produce ids through interning. Keep the message text as written so the invariant is searchable.

- [ ] **Step 4: Run tests.** `cargo test -p leanr_kernel bank:: 2>&1 | tail -3` → all pass (Task 1's too).

- [ ] **Step 5: Lint + commit.**

```bash
mise run lint
git add crates/leanr_kernel/src/bank
git commit -m "feat: generic dedup ValuePool and Store shell with str/nat/int pools (bank Task 2)"
```

---

### Task 3: `NameBank`

**Files:**
- Create: `crates/leanr_kernel/src/bank/names.rs`
- Modify: `crates/leanr_kernel/src/bank/mod.rs` (add `pub mod names;`, add `names: NameBank` field to `Store` + `Store` methods)
- Test: inline in `names.rs`

**Interfaces:**
- Consumes: `ValuePool`-style pattern, `StrId`/`NatId` interns, `Arc<Name>` (name.rs: `Name::{Anonymous, Str{parent, part}, Num{parent, part}}`, manual iterative `Eq`/`Hash`).
- Produces: `NameRow { Str { parent: Option<NameId>, part: StrId }, Num { parent: Option<NameId>, part: NatId } }` (`Option<NameId>` `None` = anonymous parent; the anonymous name itself is `Option<NameId>::None` at use sites); `NameBank { rows, hashes, table, region }` with `row(&self, index) -> &NameRow` and `hash_of(&self, index) -> u64`; `Store::name_str(&mut self, base, parent: Option<NameId>, part: StrId) -> Result<NameId, KernelError>`, `Store::name_num(&mut self, base, parent: Option<NameId>, part: NatId) -> Result<NameId, KernelError>`, `Store::name_row(&self, base, id: NameId) -> &NameRow`, and bridges `Store::intern_name(&mut self, base, n: &Arc<Name>) -> Result<Option<NameId>, KernelError>` (iterative: walks the parent chain with an explicit `Vec`, no recursion; `None` for `Name::Anonymous`), `Store::to_name(&self, base, id: Option<NameId>) -> Arc<Name>` (iterative rebuild).

Row hash recurrence (bottom-up, mix-based — internal to the bank, no oracle-parity requirement): `hash(Str) = mix(1, mix(parent_hash_or_0, sip(part_str)))`, `hash(Num) = mix(2, mix(parent_hash_or_0, sip(part_nat)))` where `mix` is `expr.rs`'s (made `pub(crate)` in this task) and `parent_hash_or_0` is the stored hash of the parent row (0 for anonymous).

- [ ] **Step 1: Failing tests** (in `names.rs`):

```rust
#[cfg(test)]
mod tests {
    use crate::bank::Store;
    use crate::Name;
    use std::sync::Arc;

    fn nm(parts: &[&str]) -> Arc<Name> {
        let mut n = Arc::new(Name::Anonymous);
        for p in parts {
            n = Arc::new(Name::Str { parent: n, part: p.to_string() });
        }
        n
    }

    #[test]
    fn name_interns_dedup_across_trees() {
        let mut s = Store::persistent();
        let a = s.intern_name(None, &nm(&["Foo", "bar"])).unwrap();
        let b = s.intern_name(None, &nm(&["Foo", "bar"])).unwrap();
        let c = s.intern_name(None, &nm(&["Foo", "baz"])).unwrap();
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert!(a.is_some());
    }

    #[test]
    fn anonymous_is_none() {
        let mut s = Store::persistent();
        assert_eq!(s.intern_name(None, &Arc::new(Name::Anonymous)).unwrap(), None);
    }

    #[test]
    fn name_roundtrips() {
        let mut s = Store::persistent();
        let orig = nm(&["Init", "Data", "Char"]);
        let id = s.intern_name(None, &orig).unwrap();
        let back = s.to_name(None, id);
        assert_eq!(&back, &orig);
    }

    #[test]
    fn shared_prefix_shares_rows() {
        let mut s = Store::persistent();
        let a = s.intern_name(None, &nm(&["Foo", "bar"])).unwrap().unwrap();
        let b = s.intern_name(None, &nm(&["Foo", "baz"])).unwrap().unwrap();
        // Both rows' parents are the same "Foo" id.
        let pa = match s.name_row(None, a) { crate::bank::names::NameRow::Str { parent, .. } => *parent, _ => panic!() };
        let pb = match s.name_row(None, b) { crate::bank::names::NameRow::Str { parent, .. } => *parent, _ => panic!() };
        assert_eq!(pa, pb);
    }
}
```

- [ ] **Step 2: Run to verify failure.** `cargo test -p leanr_kernel bank::names 2>&1 | tail -3` → compile error.

- [ ] **Step 3: Implement.** First make `expr.rs`'s `fn mix` `pub(crate)` (change `fn mix(` to `pub(crate) fn mix(` — no other edits). Then `names.rs`:

```rust
//! Hierarchical name bank (spec §1: `NameId`). The anonymous name is
//! `Option<NameId>::None` everywhere, so every stored row is a real
//! `Str`/`Num` component.

use super::probe::IdTable;
use super::{sip, NameId, NatId, Store, StrId, MAX_INDEX};
use crate::expr_hash::mix; // adjust to the actual re-export path chosen below
use crate::{KernelError, Name, Nat};
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NameRow {
    Str { parent: Option<NameId>, part: StrId },
    Num { parent: Option<NameId>, part: NatId },
}

pub struct NameBank {
    rows: Vec<NameRow>,
    hashes: Vec<u64>,
    table: IdTable,
    region: u32,
}

impl NameBank {
    pub fn new(region: u32) -> NameBank {
        NameBank { rows: Vec::new(), hashes: Vec::new(), table: IdTable::new(), region }
    }
    pub fn len(&self) -> usize { self.rows.len() }
    pub fn is_empty(&self) -> bool { self.rows.is_empty() }
    pub fn row(&self, index: usize) -> Option<&NameRow> { self.rows.get(index) }
    pub fn hash_of(&self, index: usize) -> u64 { self.hashes[index] }
    pub fn lookup(&self, hash: u64, row: &NameRow) -> Option<u32> {
        self.table.lookup(hash, |bits| {
            self.rows[((bits & !super::REGION_BIT) - 1) as usize] == *row
        })
    }
    fn insert(&mut self, hash: u64, row: NameRow) -> Result<u32, KernelError> {
        let index = u32::try_from(self.rows.len()).map_err(|_| KernelError::BankExhausted)?;
        if index > MAX_INDEX { return Err(KernelError::BankExhausted); }
        self.rows.push(row);
        self.hashes.push(hash);
        let bits = (index + 1) | self.region;
        let hashes = &self.hashes;
        self.table.insert(hash, bits, |b| hashes[((b & !super::REGION_BIT) - 1) as usize]);
        Ok(bits)
    }
}
```

`Store` methods in `mod.rs` (add `pub names: names::NameBank` to the struct and `names: names::NameBank::new(region)` to `Store::new`):

```rust
    fn name_hash_of(&self, base: Option<&Store>, id: Option<NameId>) -> u64 {
        match id {
            None => 0,
            Some(id) => self
                .store_for(base, id.is_scratch())
                .names
                .hash_of(id.index()),
        }
    }

    fn name_intern_row(
        &mut self,
        base: Option<&Store>,
        hash: u64,
        row: names::NameRow,
    ) -> Result<NameId, KernelError> {
        if let Some(b) = base {
            if let Some(bits) = b.names.lookup(hash, &row) {
                return NameId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        if let Some(bits) = self.names.lookup(hash, &row) {
            return NameId::from_bits(bits).ok_or(KernelError::BankExhausted);
        }
        let bits = self.names.insert(hash, row)?;
        NameId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }

    pub fn name_str(
        &mut self,
        base: Option<&Store>,
        parent: Option<NameId>,
        part: StrId,
    ) -> Result<NameId, KernelError> {
        let ph = self.name_hash_of(base, parent);
        let sh = sip(self.str_at(base, part));
        let h = crate::expr::mix(1, crate::expr::mix(ph, sh));
        self.name_intern_row(base, h, names::NameRow::Str { parent, part })
    }

    pub fn name_num(
        &mut self,
        base: Option<&Store>,
        parent: Option<NameId>,
        part: NatId,
    ) -> Result<NameId, KernelError> {
        let ph = self.name_hash_of(base, parent);
        let nh = sip(self.nat_at(base, part));
        let h = crate::expr::mix(2, crate::expr::mix(ph, nh));
        self.name_intern_row(base, h, names::NameRow::Num { parent, part })
    }

    pub fn name_row<'a>(&'a self, base: Option<&'a Store>, id: NameId) -> &'a names::NameRow {
        self.store_for(base, id.is_scratch())
            .names
            .row(id.index())
            .expect("NameId minted by intern ⇒ valid")
    }

    /// Bridge: intern an `Arc<Name>` chain (iterative — parent chains
    /// are attacker-depth).
    pub fn intern_name(
        &mut self,
        base: Option<&Store>,
        n: &Arc<Name>,
    ) -> Result<Option<NameId>, KernelError> {
        // Collect components root-last, then intern root-first.
        let mut chain: Vec<&Name> = Vec::new();
        let mut cur: &Name = n;
        loop {
            match cur {
                Name::Anonymous => break,
                Name::Str { parent, .. } | Name::Num { parent, .. } => {
                    chain.push(cur);
                    cur = parent;
                }
            }
        }
        let mut id: Option<NameId> = None;
        for comp in chain.into_iter().rev() {
            id = Some(match comp {
                Name::Str { part, .. } => {
                    let s = self.intern_str(base, part)?;
                    self.name_str(base, id, s)?
                }
                Name::Num { part, .. } => {
                    let p = self.intern_nat(base, part)?;
                    self.name_num(base, id, p)?
                }
                Name::Anonymous => unreachable!("filtered above"),
            });
        }
        Ok(id)
    }

    /// Bridge: rebuild an `Arc<Name>` (iterative).
    pub fn to_name(&self, base: Option<&Store>, id: Option<NameId>) -> Arc<Name> {
        let mut chain: Vec<NameId> = Vec::new();
        let mut cur = id;
        while let Some(c) = cur {
            chain.push(c);
            cur = match self.name_row(base, c) {
                names::NameRow::Str { parent, .. } | names::NameRow::Num { parent, .. } => *parent,
            };
        }
        let mut out = Arc::new(Name::Anonymous);
        for c in chain.into_iter().rev() {
            out = match *self.name_row(base, c) {
                names::NameRow::Str { part, .. } => Arc::new(Name::Str {
                    parent: out,
                    part: self.str_at(base, part).to_string(),
                }),
                names::NameRow::Num { part, .. } => Arc::new(Name::Num {
                    parent: out,
                    part: self.nat_at(base, part).clone(),
                }),
            };
        }
        out
    }
```

Path note: the plan text uses `crate::expr::mix`. `expr` is a private module of the crate — `pub(crate) fn mix` inside it is reachable as `crate::expr::mix` from bank code (same crate). Use that path; delete the placeholder `use crate::expr_hash::mix` line from the `names.rs` skeleton above (row hashing happens in `mod.rs`, so `names.rs` needs no `mix` import at all — trim unused imports until `mise run lint` is clean).

- [ ] **Step 4: Run tests.** `cargo test -p leanr_kernel bank:: 2>&1 | tail -3` → all pass.

- [ ] **Step 5: Lint + commit.**

```bash
mise run lint
git add crates/leanr_kernel/src/bank crates/leanr_kernel/src/expr.rs
git commit -m "feat: NameBank with Arc<Name> bridges (bank Task 3)"
```

---

### Task 4: `LevelBank` + level-list pool

**Files:**
- Create: `crates/leanr_kernel/src/bank/levels.rs`
- Modify: `crates/leanr_kernel/src/bank/mod.rs` (add `pub mod levels;`, `Store` fields `levels: LevelBank`, `level_lists: ValuePool<Box<[LevelId]>>` + methods)
- Test: inline in `levels.rs`

**Interfaces:**
- Consumes: `NameId` interning; `Level` (level.rs enum: `Zero, Succ, Max, IMax, Param(Arc<Name>), MVar(Arc<Name>)`), `Level::structural_eq` for test oracles.
- Produces: `LevelRow { Zero, Succ(LevelId), Max(LevelId, LevelId), IMax(LevelId, LevelId), Param(NameId), MVar(NameId) }` (names here are never anonymous — decoded params/mvars always have real names; enforce with `KernelError::BankExhausted`? No — anonymous param names are representable in `Level` via `Arc<Name>`, so `Param(Option<NameId>)`/`MVar(Option<NameId>)` it is); per-row `hash: u64` and `flags: u8` (`bit0 = has_param`, `bit1 = has_mvar`), both computed bottom-up O(1); `Store::{level_zero, level_succ, level_max, level_imax, level_param, level_mvar}` intern-constructors, `Store::level_row/level_hash/level_flags` accessors, `Store::intern_level(&mut self, base, l: &Arc<Level>) -> Result<LevelId, KernelError>` and `Store::to_level(&self, base, id) -> Arc<Level>` bridges (both iterative, explicit stacks), `Store::intern_level_list(&mut self, base, ids: &[LevelId]) -> Result<LevelsId, KernelError>` + `Store::level_list_at`.

Row hash recurrence: `Zero → 11`, `Succ(a) → mix(12, h(a))`, `Max(a,b) → mix(13, mix(h(a), h(b)))`, `IMax(a,b) → mix(14, mix(h(a), h(b)))`, `Param(n) → mix(15, name_hash_or_0)`, `MVar(n) → mix(16, name_hash_or_0)`. Flags: `Zero → 0`; `Succ/Max/IMax` OR the children; `Param → bit0`; `MVar → bit1`.

- [ ] **Step 1: Failing tests:**

```rust
#[cfg(test)]
mod tests {
    use crate::bank::Store;
    use crate::{Level, Name, RecGuard};
    use std::sync::Arc;

    fn lp(s: &str) -> Arc<Level> {
        Arc::new(Level::Param(Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: s.to_string(),
        })))
    }

    #[test]
    fn level_interns_dedup() {
        let mut s = Store::persistent();
        let a = s.intern_level(None, &Arc::new(Level::Succ(Arc::new(Level::Zero)))).unwrap();
        let b = s.intern_level(None, &Arc::new(Level::Succ(Arc::new(Level::Zero)))).unwrap();
        assert_eq!(a, b);
        let c = s.intern_level(None, &Arc::new(Level::Zero)).unwrap();
        assert_ne!(a, c);
    }

    #[test]
    fn level_flags_track_param_and_mvar() {
        let mut s = Store::persistent();
        let p = s.intern_level(None, &lp("u")).unwrap();
        assert_eq!(s.level_flags(None, p), 0b01);
        let m = s
            .intern_level(None, &Arc::new(Level::MVar(Arc::new(Name::Anonymous))))
            .unwrap();
        assert_eq!(s.level_flags(None, m), 0b10);
        let mx = s
            .intern_level(None, &Arc::new(Level::Max(lp("u"), Arc::new(Level::Zero))))
            .unwrap();
        assert_eq!(s.level_flags(None, mx), 0b01);
    }

    #[test]
    fn level_roundtrips_structurally() {
        let mut s = Store::persistent();
        let mut g = RecGuard::new();
        let orig = Arc::new(Level::IMax(lp("u"), Arc::new(Level::Succ(lp("v")))));
        let id = s.intern_level(None, &orig).unwrap();
        let back = s.to_level(None, id);
        assert!(Level::structural_eq(&orig, &back, &mut g).unwrap());
    }

    #[test]
    fn deep_level_chain_is_iterative() {
        let mut s = Store::persistent();
        let mut l = Arc::new(Level::Zero);
        for _ in 0..100_000 {
            l = Arc::new(Level::Succ(l));
        }
        // Must not overflow the stack; dedup makes the second intern id-equal.
        let a = s.intern_level(None, &l).unwrap();
        let b = s.intern_level(None, &l).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn level_list_pool_dedups() {
        let mut s = Store::persistent();
        let u = s.intern_level(None, &lp("u")).unwrap();
        let z = s.intern_level(None, &Arc::new(Level::Zero)).unwrap();
        let a = s.intern_level_list(None, &[u, z]).unwrap();
        let b = s.intern_level_list(None, &[u, z]).unwrap();
        let c = s.intern_level_list(None, &[z, u]).unwrap();
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(s.level_list_at(None, a), &[u, z]);
    }
}
```

- [ ] **Step 2: Verify failure.** `cargo test -p leanr_kernel bank::levels 2>&1 | tail -3` → compile error.

- [ ] **Step 3: Implement** `levels.rs` — same bank skeleton as `NameBank` (`rows: Vec<LevelRow>`, `hashes: Vec<u64>`, `flags: Vec<u8>`, `table: IdTable`, `region`, `lookup`/`insert` identical in shape). `Store` gains:

```rust
    pub fn level_zero(&mut self, base: Option<&Store>) -> Result<LevelId, KernelError> {
        self.level_intern_row(base, 11, 0, levels::LevelRow::Zero)
    }

    pub fn level_succ(&mut self, base: Option<&Store>, a: LevelId) -> Result<LevelId, KernelError> {
        let h = crate::expr::mix(12, self.level_hash(base, a));
        let f = self.level_flags(base, a);
        self.level_intern_row(base, h, f, levels::LevelRow::Succ(a))
    }

    pub fn level_max(&mut self, base: Option<&Store>, a: LevelId, b: LevelId) -> Result<LevelId, KernelError> {
        let h = crate::expr::mix(13, crate::expr::mix(self.level_hash(base, a), self.level_hash(base, b)));
        let f = self.level_flags(base, a) | self.level_flags(base, b);
        self.level_intern_row(base, h, f, levels::LevelRow::Max(a, b))
    }

    pub fn level_imax(&mut self, base: Option<&Store>, a: LevelId, b: LevelId) -> Result<LevelId, KernelError> {
        let h = crate::expr::mix(14, crate::expr::mix(self.level_hash(base, a), self.level_hash(base, b)));
        let f = self.level_flags(base, a) | self.level_flags(base, b);
        self.level_intern_row(base, h, f, levels::LevelRow::IMax(a, b))
    }

    pub fn level_param(&mut self, base: Option<&Store>, n: Option<NameId>) -> Result<LevelId, KernelError> {
        let h = crate::expr::mix(15, self.name_hash_of(base, n));
        self.level_intern_row(base, h, 0b01, levels::LevelRow::Param(n))
    }

    pub fn level_mvar(&mut self, base: Option<&Store>, n: Option<NameId>) -> Result<LevelId, KernelError> {
        let h = crate::expr::mix(16, self.name_hash_of(base, n));
        self.level_intern_row(base, h, 0b10, levels::LevelRow::MVar(n))
    }
```

with `level_intern_row` mirroring `name_intern_row` (base lookup → own lookup → insert; the bank's `insert` pushes row+hash+flags). Bridges (iterative post-order with an in-call memo keyed by `Arc::as_ptr` — sound for the call duration exactly as intern.rs documents):

```rust
    pub fn intern_level(&mut self, base: Option<&Store>, l: &Arc<Level>) -> Result<LevelId, KernelError> {
        use std::collections::HashMap;
        enum Frame<'a> { Enter(&'a Arc<Level>), Exit(&'a Arc<Level>) }
        let mut memo: HashMap<usize, LevelId> = HashMap::new();
        let mut out: Vec<LevelId> = Vec::new();
        let mut stack = vec![Frame::Enter(l)];
        while let Some(fr) = stack.pop() {
            match fr {
                Frame::Enter(l) => {
                    if let Some(&id) = memo.get(&(Arc::as_ptr(l) as usize)) {
                        out.push(id);
                        continue;
                    }
                    match l.as_ref() {
                        Level::Zero | Level::Param(_) | Level::MVar(_) => stack.push(Frame::Exit(l)),
                        Level::Succ(a) => {
                            stack.push(Frame::Exit(l));
                            stack.push(Frame::Enter(a));
                        }
                        Level::Max(a, b) | Level::IMax(a, b) => {
                            stack.push(Frame::Exit(l));
                            stack.push(Frame::Enter(b));
                            stack.push(Frame::Enter(a));
                        }
                    }
                }
                Frame::Exit(l) => {
                    let id = match l.as_ref() {
                        Level::Zero => self.level_zero(base)?,
                        Level::Succ(_) => {
                            let a = out.pop().expect("child pushed by Enter");
                            self.level_succ(base, a)?
                        }
                        Level::Max(_, _) => {
                            let b = out.pop().expect("child");
                            let a = out.pop().expect("child");
                            self.level_max(base, a, b)?
                        }
                        Level::IMax(_, _) => {
                            let b = out.pop().expect("child");
                            let a = out.pop().expect("child");
                            self.level_imax(base, a, b)?
                        }
                        Level::Param(n) => {
                            let n = self.intern_name(base, n)?;
                            self.level_param(base, n)?
                        }
                        Level::MVar(n) => {
                            let n = self.intern_name(base, n)?;
                            self.level_mvar(base, n)?
                        }
                    };
                    memo.insert(Arc::as_ptr(l) as usize, id);
                    out.push(id);
                }
            }
        }
        Ok(out.pop().expect("root"))
    }
```

`to_level` uses the same two-phase stack in reverse (memo keyed by `LevelId`), building `Arc<Level>` bottom-up. `intern_level_list`:

```rust
    pub fn intern_level_list(&mut self, base: Option<&Store>, ids: &[LevelId]) -> Result<LevelsId, KernelError> {
        let h = sip(&ids.iter().map(|i| i.bits()).collect::<Vec<u32>>());
        if let Some(b) = base {
            if let Some(bits) = b.level_lists.lookup(h, |t| {
                t.len() == ids.len() && t.iter().zip(ids).all(|(a, b)| a == b)
            }) {
                return LevelsId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        let bits = self.level_lists.intern(
            h,
            |t| t.len() == ids.len() && t.iter().zip(ids).all(|(a, b)| a == b),
            || ids.to_vec().into_boxed_slice(),
            |t| sip(&t.iter().map(|i| i.bits()).collect::<Vec<u32>>()),
        )?;
        LevelsId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }
```

(This is sound cross-region because `LevelId`s themselves are globally canonical — same reasoning as expr rows.)

- [ ] **Step 4: Run tests.** `cargo test -p leanr_kernel bank:: 2>&1 | tail -3` → all pass, including the 100k-deep chain.

- [ ] **Step 5: Lint + commit.**

```bash
mise run lint
git add crates/leanr_kernel/src/bank
git commit -m "feat: LevelBank with cached flags/hash, level-list pool, bridges (bank Task 4)"
```

---

### Task 5: KVMap and LetE-spill pools

**Files:**
- Modify: `crates/leanr_kernel/src/bank/pools.rs` (row types), `crates/leanr_kernel/src/bank/mod.rs` (`Store` fields `kvmaps: ValuePool<KVMapRow>`, `spills: ValuePool<SpillRow>` + methods), `crates/leanr_kernel/src/expr.rs` (make `kvmap_eq` and `data_value_eq` `pub(crate)`)
- Test: inline in `pools.rs`

**Interfaces:**
- Consumes: `KVMap`, `DataValue` (expr.rs), `Syntax` (syntax.rs); name/nat/int/str interns.
- Produces:
  - `DataValueRow { Str(StrId), Bool(bool), Name(Option<NameId>), Nat(NatId), Int(IntId), Syntax(std::sync::Arc<crate::Syntax>) }` with a manual `PartialEq` whose `Syntax` arm is `Arc::ptr_eq` — mirroring `data_value_eq`'s documented ptr-eq rule so the interning invariant matches today's `structural_eq` exactly.
  - `KVMapRow(pub Box<[(Option<NameId>, DataValueRow)]>)` (order-sensitive, like `kvmap_eq`).
  - `SpillRow { pub name: Option<NameId>, pub body_or_aux: u32 }` — phase 1 stores the LetE spill as `(decl_name, body ExprId bits)`; `terms.rs` (Task 6) is the only writer.
  - `Store::intern_kvmap(&mut self, base, m: &KVMap) -> Result<KVMapId, KernelError>` (bridging each `DataValue`), `Store::kvmap_at`, `Store::to_kvmap(&self, base, id) -> KVMap`; `Store::intern_spill(&mut self, base, name: Option<NameId>, body_bits: u32) -> Result<SpillId, KernelError>`, `Store::spill_at`.
  - Hashing: `DataValueRow::Syntax` hashes by `Arc::as_ptr` (consistent with its ptr-eq), everything else by id bits/value via `sip`.

- [ ] **Step 1: Failing tests:**

```rust
    #[test]
    fn kvmap_pool_dedups_and_roundtrips() {
        use crate::expr::{DataValue, KVMap};
        let mut s = Store::persistent();
        let nm = std::sync::Arc::new(crate::Name::Str {
            parent: std::sync::Arc::new(crate::Name::Anonymous),
            part: "k".to_string(),
        });
        let m = KVMap(vec![(nm.clone(), DataValue::OfBool(true))]);
        let a = s.intern_kvmap(None, &m).unwrap();
        let b = s.intern_kvmap(None, &KVMap(vec![(nm.clone(), DataValue::OfBool(true))])).unwrap();
        assert_eq!(a, b);
        let back = s.to_kvmap(None, a);
        assert!(crate::expr::kvmap_eq(&back, &m));
    }

    #[test]
    fn spill_pool_dedups() {
        let mut s = Store::persistent();
        let a = s.intern_spill(None, None, 42).unwrap();
        let b = s.intern_spill(None, None, 42).unwrap();
        let c = s.intern_spill(None, None, 43).unwrap();
        assert_eq!(a, b);
        assert_ne!(a, c);
    }
```

(`KVMap`/`DataValue`/`kvmap_eq` need `pub(crate)`-reachable paths: `KVMap`/`DataValue` are already `pub` re-exports in lib.rs; change `fn kvmap_eq(` → `pub(crate) fn kvmap_eq(` and `fn data_value_eq(` → `pub(crate) fn data_value_eq(` in expr.rs.)

- [ ] **Step 2: Verify failure.** `cargo test -p leanr_kernel bank::pools 2>&1 | tail -3` → compile error.

- [ ] **Step 3: Implement** the row types in `pools.rs` and the `Store` methods in `mod.rs`, following exactly the `intern_str`/`intern_nat` pattern (base lookup → own intern). `intern_kvmap` maps each `(Arc<Name>, DataValue)` entry through `intern_name` + the leaf pools to build a `KVMapRow`, then interns the row; `to_kvmap` reverses it (`DataValueRow::Syntax` clones the stored `Arc<Syntax>` — preserving the exact ptr-eq semantics `data_value_eq` uses today).

- [ ] **Step 4: Run tests, lint, commit.**

```bash
cargo test -p leanr_kernel bank:: 2>&1 | tail -3   # all pass
mise run lint
git add crates/leanr_kernel/src/bank crates/leanr_kernel/src/expr.rs
git commit -m "feat: kvmap and LetE-spill pools (bank Task 5)"
```

---

### Task 6: `TermBank` — expr rows, `Node` view, intern-constructors

**Files:**
- Create: `crates/leanr_kernel/src/bank/terms.rs`
- Modify: `crates/leanr_kernel/src/bank/mod.rs` (add `pub mod terms;`, `Store` field `terms: TermBank` + constructor methods), `crates/leanr_kernel/src/expr.rs` (make `pub(crate)`: `combine_app`, `combine_binder`, `combine_let`, `nat_lossy_u64`, `bvar_loose_range`, `depth_of`, `literal_hash`, the `TAG_*` consts, and `ExprData::pack`)
- Test: inline in `terms.rs`

**Interfaces:**
- Consumes: everything above; `ExprData` and the `pub(crate)` expr.rs helpers; `BinderInfo`.
- Produces:
  - `Tag` (`#[repr(u8)]`): `BVar, BVarBig, FVar, MVar, Sort, Const, App, Lam, Forall, LetE, LitNat, LitStr, MData, Proj, ProjBig` (15 ≤ 16). Packed tag byte: bits 0-3 tag, bits 4-5 `BinderInfo` (`Default=0, Implicit=1, StrictImplicit=2, InstImplicit=3`), bit 6 `non_dep`.
  - `TermBank { tags: Vec<u8>, a: Vec<u32>, b: Vec<u32>, c: Vec<u32>, data: Vec<u64>, table: IdTable, region: u32 }` — 21 B/row + table, exactly spec §1.
  - `Node` view enum (all fields ids/values, `Clone + Copy` except the two `Nat`-free forms — it is fully `Copy`):

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Node {
    BVar { idx: u32 },
    BVarBig { idx: NatId },
    FVar { id: Option<NameId> },
    MVar { id: Option<NameId> },
    Sort { level: LevelId },
    Const { name: Option<NameId>, levels: LevelsId },
    App { f: ExprId, arg: ExprId },
    Lam { binder_name: Option<NameId>, binder_type: ExprId, body: ExprId, binder_info: BinderInfo },
    Forall { binder_name: Option<NameId>, binder_type: ExprId, body: ExprId, binder_info: BinderInfo },
    LetE { decl_name: Option<NameId>, ty: ExprId, value: ExprId, body: ExprId, non_dep: bool },
    LitNat { v: NatId },
    LitStr { v: StrId },
    MData { data: KVMapId, expr: ExprId },
    Proj { type_name: Option<NameId>, idx: u32, structure: ExprId },
    ProjBig { type_name: Option<NameId>, idx: NatId, structure: ExprId },
}
```

  - `Store` intern-constructors, each computing its `ExprData` with the *same* recurrences as expr.rs's smart constructors (reusing the now-`pub(crate)` helpers; level-bearing nodes use the bank's cached level hash/flags instead of `Level::hash_val` — hash values differ from expr.rs's, which is fine: hashes never cross representations; flags/range/depth are identical by construction):
    - `expr_bvar(&mut self, base, idx: &Nat) -> Result<ExprId, _>` — inline when `idx` fits `u32` (tag `BVar`, `a = idx as u32`), else `BVarBig` with a pooled `NatId`; `data = pack(mix(TAG_BVAR, nat_lossy_u64(idx)), bvar_loose_range(idx), 1, false, false, false, false)` — byte-identical to `Expr::bvar`.
    - `expr_fvar/expr_mvar(&mut self, base, name: Option<NameId>)` — `mix(TAG_FVAR/TAG_MVAR, name_hash_of(name))`, flags as in expr.rs.
    - `expr_sort(&mut self, base, level: LevelId)` — `mix(TAG_SORT, level_hash)`, `has_level_mvar/param` from the cached flags byte. **O(1), no RecGuard** — the walk expr.rs needs is already amortized into the level rows.
    - `expr_const(&mut self, base, name: Option<NameId>, levels: LevelsId)` — folds the list's level hashes/flags (list is in the pool; O(len)).
    - `expr_app(f, arg)` → `combine_app(data_of(f), data_of(arg))`.
    - `expr_lam/expr_forall(binder_name, binder_type, body, binder_info)` → `combine_binder`.
    - `expr_let(decl_name, ty, value, body, non_dep)` → `combine_let`; row stores `a = ty, b = value, c = spill(decl_name, body)`.
    - `expr_lit_nat/expr_lit_str` → `mix(TAG_LIT, literal_hash(..))` (build the `Literal` transiently for the hash so values match expr.rs's convention).
    - `expr_mdata(kvmap, child)`, `expr_proj(type_name, idx, structure)` — per expr.rs `mdata`/`proj` recurrences (proj folds `name_hash_of` and `nat_lossy_u64`).
  - `Store::expr_node(&self, base, id: ExprId) -> Node` (decode the row), `Store::expr_data(&self, base, id: ExprId) -> ExprData`.
  - Row equality for the probe: two rows are equal iff same packed tag byte AND same `a, b, c` — complete because every field is an id into a deduplicated pool or an inline scalar (the spec §1 invariant; LetE relies on Task 5's deduplicated spill pool).
  - Table hash: the row's `data` hash word extended: `mix(packed_tag as u64, mix(a, mix(b, c)))` — do NOT use `data.hash()` alone (it is 32-bit and, for `Lam` vs `Forall`, identical since `combine_binder` ignores the tag; the row-content hash disambiguates).

- [ ] **Step 1: Failing tests** (representative; write all of these):

```rust
#[cfg(test)]
mod tests {
    use crate::bank::Store;
    use crate::{BinderInfo, Expr, Nat, RecGuard};
    use std::sync::Arc;

    #[test]
    fn app_dedups_and_children_route() {
        let mut s = Store::persistent();
        let n = s.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let a1 = s.expr_app(None, n, n).unwrap();
        let a2 = s.expr_app(None, n, n).unwrap();
        assert_eq!(a1, a2);
        match s.expr_node(None, a1) {
            crate::bank::terms::Node::App { f, arg } => {
                assert_eq!(f, n);
                assert_eq!(arg, n);
            }
            other => panic!("expected App, got {other:?}"),
        }
    }

    #[test]
    fn lam_and_forall_do_not_collide() {
        let mut s = Store::persistent();
        let t = s.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let b = s.expr_bvar(None, &Nat::from(1u64)).unwrap();
        let lam = s.expr_lam(None, None, t, b, BinderInfo::Default).unwrap();
        let pi = s.expr_forall(None, None, t, b, BinderInfo::Default).unwrap();
        assert_ne!(lam, pi);
    }

    #[test]
    fn binder_info_distinguishes_rows() {
        let mut s = Store::persistent();
        let t = s.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let b = s.expr_bvar(None, &Nat::from(1u64)).unwrap();
        let d = s.expr_lam(None, None, t, b, BinderInfo::Default).unwrap();
        let i = s.expr_lam(None, None, t, b, BinderInfo::Implicit).unwrap();
        assert_ne!(d, i);
    }

    #[test]
    fn data_word_matches_smart_constructor_for_level_free_terms() {
        // bvar/app/lam carry no levels, so even the hash halves must match
        // expr.rs exactly (same mix, same recurrences).
        let mut s = Store::persistent();
        let bank_bvar = s.expr_bvar(None, &Nat::from(3u64)).unwrap();
        let arc_bvar = Expr::bvar(Nat::from(3u64));
        assert_eq!(s.expr_data(None, bank_bvar), arc_bvar.data());
        let bank_app = s.expr_app(None, bank_bvar, bank_bvar).unwrap();
        let arc_app = Expr::app(Arc::clone(&arc_bvar), arc_bvar);
        assert_eq!(s.expr_data(None, bank_app), arc_app.data());
    }

    #[test]
    fn big_bvar_index_pools() {
        let mut s = Store::persistent();
        let big = Nat(num_bigint::BigUint::from(u64::MAX) * 4u32);
        let a = s.expr_bvar(None, &big).unwrap();
        let b = s.expr_bvar(None, &big).unwrap();
        assert_eq!(a, b);
        match s.expr_node(None, a) {
            crate::bank::terms::Node::BVarBig { idx } => {
                assert_eq!(s.nat_at(None, idx), &big);
            }
            other => panic!("expected BVarBig, got {other:?}"),
        }
    }

    #[test]
    fn lete_spill_roundtrips() {
        let mut s = Store::persistent();
        let t = s.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let l1 = s.expr_let(None, None, t, t, t, false).unwrap();
        let l2 = s.expr_let(None, None, t, t, t, false).unwrap();
        let l3 = s.expr_let(None, None, t, t, t, true).unwrap();
        assert_eq!(l1, l2);
        assert_ne!(l1, l3); // non_dep is part of identity
        match s.expr_node(None, l1) {
            crate::bank::terms::Node::LetE { ty, value, body, non_dep, .. } => {
                assert_eq!((ty, value, body, non_dep), (t, t, t, false));
            }
            other => panic!("expected LetE, got {other:?}"),
        }
    }

    #[test]
    fn sort_flags_come_from_level_bank() {
        let mut s = Store::persistent();
        let u = {
            let n = s.intern_str(None, "u").unwrap();
            let n = s.name_str(None, None, n).unwrap();
            s.level_param(None, Some(n)).unwrap()
        };
        let srt = s.expr_sort(None, u).unwrap();
        let d = s.expr_data(None, srt);
        assert!(d.has_level_param());
        assert!(!d.has_level_mvar());
        assert_eq!(d.loose_bvar_range(), 0);
    }
}
```

- [ ] **Step 2: Verify failure**, **Step 3: implement** `TermBank` + `Store` constructors per the Interfaces block (every constructor: compute `data`; pack tag byte; row = (tagbyte, a, b, c); `hash = mix(tagbyte as u64, mix(a as u64, mix(b as u64, c as u64)))` XOR'd with `data` low bits via `mix(row_hash, data_word)`; base lookup → own lookup → append+insert exactly like `NameBank`). `expr_node` decodes by tag. Add the `pub(crate)` visibility changes in expr.rs (mechanical: prepend `pub(crate)` to the listed items).

- [ ] **Step 4: Run tests, lint.** `cargo test -p leanr_kernel bank:: 2>&1 | tail -3`; `cargo test -p leanr_kernel 2>&1 | grep -c "test result: ok"` (existing suite still green); `mise run lint`.

- [ ] **Step 5: Commit.**

```bash
git add crates/leanr_kernel/src/bank crates/leanr_kernel/src/expr.rs
git commit -m "feat: TermBank expr rows with intern-constructors and Node view (bank Task 6)"
```

---

### Task 7: `Arc<Expr>` bridges (`intern_expr` / `to_expr`)

**Files:**
- Modify: `crates/leanr_kernel/src/bank/terms.rs` (bridge impls on `Store`), `crates/leanr_kernel/src/bank/mod.rs` if helper visibility needs it
- Test: inline in `terms.rs`

**Interfaces:**
- Consumes: Task 6 constructors; `ExprNode` (all 12 variants), `Expr::{node, data}`, `Literal`.
- Produces:
  - `Store::intern_expr(&mut self, base: Option<&Store>, e: &Arc<Expr>) -> Result<ExprId, KernelError>` — iterative two-phase stack (`Enter`/`Exit` exactly like Task 4's `intern_level`), memo keyed by `Arc::as_ptr as usize` (sound within the call: the borrowed root keeps every interior Arc alive — same argument as intern.rs's per-constant memo).
  - `Store::to_expr(&self, base: Option<&Store>, id: ExprId, g: &mut RecGuard) -> Result<Arc<Expr>, KernelError>` — iterative two-phase stack, memo keyed by `ExprId`; rebuilds via the existing smart constructors (`Expr::sort`/`Expr::const_` take `g`).

- [ ] **Step 1: Failing tests:**

```rust
    #[test]
    fn bridge_roundtrip_preserves_structure_and_data() {
        let mut s = Store::persistent();
        let mut g = RecGuard::new();
        // λ (x : Nat), f x x  — exercises lam/app/const/fvar-free path.
        let nat = Expr::const_(
            Arc::new(crate::Name::Str {
                parent: Arc::new(crate::Name::Anonymous),
                part: "Nat".to_string(),
            }),
            vec![],
            &mut g,
        )
        .unwrap();
        let f = Expr::const_(
            Arc::new(crate::Name::Str {
                parent: Arc::new(crate::Name::Anonymous),
                part: "f".to_string(),
            }),
            vec![],
            &mut g,
        )
        .unwrap();
        let body = Expr::app(Expr::app(f, Expr::bvar(Nat::from(0u64))), Expr::bvar(Nat::from(0u64)));
        let e = Expr::lam(
            Arc::new(crate::Name::Str {
                parent: Arc::new(crate::Name::Anonymous),
                part: "x".to_string(),
            }),
            nat,
            body,
            BinderInfo::Default,
        );
        let id = s.intern_expr(None, &e).unwrap();
        let back = s.to_expr(None, id, &mut g).unwrap();
        assert!(Expr::structural_eq(&e, &back, &mut g).unwrap());
        assert_eq!(back.data(), e.data());
    }

    #[test]
    fn bridge_intern_is_idempotent_and_dedups() {
        let mut s = Store::persistent();
        let e1 = Expr::app(Expr::bvar(Nat::from(0u64)), Expr::bvar(Nat::from(1u64)));
        let e2 = Expr::app(Expr::bvar(Nat::from(0u64)), Expr::bvar(Nat::from(1u64)));
        let a = s.intern_expr(None, &e1).unwrap();
        let b = s.intern_expr(None, &e2).unwrap();
        assert_eq!(a, b, "structurally equal Arc trees intern to one id");
    }

    #[test]
    fn bridge_survives_deep_chains() {
        let mut s = Store::persistent();
        let mut g = RecGuard::new();
        let mut e = Expr::bvar(Nat::from(0u64));
        for _ in 0..20_000 {
            e = Expr::app(e, Expr::bvar(Nat::from(0u64)));
        }
        let id = s.intern_expr(None, &e).unwrap();
        let back = s.to_expr(None, id, &mut g).unwrap();
        assert!(Expr::structural_eq(&e, &back, &mut g).unwrap());
    }
```

- [ ] **Step 2: Verify failure**, **Step 3: implement**. `intern_expr`'s `Exit` arm maps each `ExprNode` variant to its Task 6 constructor (Const: `intern_name` + `intern_level` each level + `intern_level_list`; MData: `intern_kvmap`; Lit: `expr_lit_nat`/`expr_lit_str`; Proj: inline vs `ProjBig` on `nat_to_u32` fit). `to_expr`'s `Exit` arm maps each `Node` back through `Expr::{bvar, fvar, mvar, sort, const_, app, lam, forall_e, let_e, lit, mdata, proj}` using `to_name`/`to_level`/`to_kvmap`/`nat_at`.

- [ ] **Step 4: Run tests, lint, commit.**

```bash
cargo test -p leanr_kernel bank:: 2>&1 | tail -3
mise run lint
git add crates/leanr_kernel/src/bank
git commit -m "feat: Arc<Expr> bridges into/out of the term bank (bank Task 7)"
```

---

### Task 8: Property/differential suite (the interning invariant, tested)

**Files:**
- Create: `crates/leanr_kernel/src/bank/tests.rs`
- Modify: `crates/leanr_kernel/src/bank/mod.rs` (add `#[cfg(test)] mod tests;`)

**Interfaces:**
- Consumes: bridges (Task 7), `Expr::structural_eq`.
- Produces: nothing (test-only). The deterministic generator is self-contained (SplitMix64; no new deps, no `Math.random`-style nondeterminism).

- [ ] **Step 1: Write the suite** (this task is test-only; "failing first" = write it against the finished Task 7 API and let any invariant violation fail loudly — if all pass immediately, mutate one constructor locally to confirm the suite catches it, then revert):

```rust
//! Differential property tests for the interning invariant (spec §1):
//! equal ids ⇔ `Expr::structural_eq`. The existing `Arc<Expr>`
//! representation is the oracle.

use super::Store;
use crate::{BinderInfo, Expr, Level, Literal, Name, Nat, RecGuard};
use std::sync::Arc;

/// SplitMix64 — deterministic, dependency-free.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn nm(s: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: s.to_string(),
    })
}

/// Random term over a tiny vocabulary; `depth` bounds recursion.
fn gen(r: &mut Rng, depth: u32, g: &mut RecGuard) -> Arc<Expr> {
    if depth == 0 {
        return match r.below(4) {
            0 => Expr::bvar(Nat::from(r.below(3))),
            1 => Expr::lit(Literal::NatVal(Nat::from(r.below(5)))),
            2 => Expr::const_(nm(["A", "B"][r.below(2) as usize]), vec![], g).unwrap(),
            _ => Expr::sort(
                Arc::new(Level::Succ(Arc::new(Level::Zero))),
                g,
            )
            .unwrap(),
        };
    }
    match r.below(5) {
        0 => Expr::app(gen(r, depth - 1, g), gen(r, depth - 1, g)),
        1 => Expr::lam(
            nm(["x", "y"][r.below(2) as usize]),
            gen(r, depth - 1, g),
            gen(r, depth - 1, g),
            [BinderInfo::Default, BinderInfo::Implicit][r.below(2) as usize],
        ),
        2 => Expr::forall_e(nm("x"), gen(r, depth - 1, g), gen(r, depth - 1, g), BinderInfo::Default),
        3 => Expr::let_e(
            nm("z"),
            gen(r, depth - 1, g),
            gen(r, depth - 1, g),
            gen(r, depth - 1, g),
            r.below(2) == 0,
        ),
        _ => Expr::proj(nm("S"), Nat::from(r.below(3)), gen(r, depth - 1, g)),
    }
}

#[test]
fn interning_invariant_id_eq_iff_structural_eq() {
    let mut g = RecGuard::new();
    let mut s = Store::persistent();
    // Two independent streams with overlapping seeds ⇒ plenty of
    // structurally-equal-but-pointer-distinct pairs.
    let mut terms: Vec<Arc<Expr>> = Vec::new();
    for seed in 0..60u64 {
        let mut r = Rng(seed % 30); // seeds repeat: duplicates guaranteed
        terms.push(gen(&mut r, 4, &mut g));
    }
    let ids: Vec<_> = terms
        .iter()
        .map(|e| s.intern_expr(None, e).unwrap())
        .collect();
    for i in 0..terms.len() {
        for j in i..terms.len() {
            let structural = Expr::structural_eq(&terms[i], &terms[j], &mut g).unwrap();
            assert_eq!(
                ids[i] == ids[j],
                structural,
                "invariant violated between term {i} and term {j}"
            );
        }
    }
}

#[test]
fn roundtrip_preserves_structure_and_data_word() {
    let mut g = RecGuard::new();
    let mut s = Store::persistent();
    for seed in 0..40u64 {
        let mut r = Rng(seed);
        let e = gen(&mut r, 4, &mut g);
        let id = s.intern_expr(None, &e).unwrap();
        let back = s.to_expr(None, id, &mut g).unwrap();
        assert!(Expr::structural_eq(&e, &back, &mut g).unwrap(), "seed {seed}");
        assert_eq!(back.data(), e.data(), "seed {seed}");
    }
}

#[test]
fn reinterning_a_roundtripped_term_is_id_stable() {
    let mut g = RecGuard::new();
    let mut s = Store::persistent();
    for seed in 0..20u64 {
        let mut r = Rng(seed);
        let e = gen(&mut r, 3, &mut g);
        let id = s.intern_expr(None, &e).unwrap();
        let back = s.to_expr(None, id, &mut g).unwrap();
        let id2 = s.intern_expr(None, &back).unwrap();
        assert_eq!(id, id2, "seed {seed}");
    }
}
```

(`gen` recurses natively but depth is a hard-coded ≤ 4 — test-only, not attacker input.)

- [ ] **Step 2: Run.** `cargo test -p leanr_kernel bank::tests 2>&1 | tail -3` → 3 passed. Then mutate-to-verify: temporarily make `expr_lam` reuse the `Forall` tag, re-run, confirm `interning_invariant...` FAILS, revert, re-run green. (This mutation check replaces watch-it-fail for a test-only task.)

- [ ] **Step 3: Lint + commit.**

```bash
mise run lint
git add crates/leanr_kernel/src/bank
git commit -m "test: differential property suite for the interning invariant (bank Task 8)"
```

---

### Task 9: Scratch region + `promote`

**Files:**
- Create: `crates/leanr_kernel/src/bank/scratch.rs`
- Modify: `crates/leanr_kernel/src/bank/mod.rs` (add `pub mod scratch;`)
- Test: inline in `scratch.rs`

**Interfaces:**
- Consumes: everything above (`Store::scratch()` and the `base: Option<&Store>` threading already exist — Tasks 2-7 built cross-region interning in).
- Produces: `pub fn promote(base: &mut Store, scratch: &Store, id: ExprId) -> Result<ExprId, KernelError>` — iterative post-order walk translating every scratch-region id (expr rows AND the names/levels/pools they reference) into `base`; persistent-region ids pass through unchanged; memo keyed by scratch `ExprId`. This is phase 2's `add_core` promotion primitive (spec §2).

- [ ] **Step 1: Failing tests:**

```rust
#[cfg(test)]
mod tests {
    use super::promote;
    use crate::bank::Store;
    use crate::{Expr, Nat, RecGuard};
    use std::sync::Arc;

    #[test]
    fn scratch_reuses_persistent_ids() {
        let mut g = RecGuard::new();
        let mut base = Store::persistent();
        let e = Expr::app(Expr::bvar(Nat::from(0u64)), Expr::bvar(Nat::from(1u64)));
        let pid = base.intern_expr(None, &e).unwrap();
        let mut scr = Store::scratch();
        let sid = scr.intern_expr(Some(&base), &e).unwrap();
        assert_eq!(sid, pid, "term already in base ⇒ base id, no scratch row");
        assert!(!sid.is_scratch());
        let _ = &mut g;
    }

    #[test]
    fn scratch_novel_terms_get_scratch_ids_and_read_back() {
        let mut g = RecGuard::new();
        let mut base = Store::persistent();
        // Base knows the leaf, scratch builds a new parent over it.
        let leaf = Expr::bvar(Nat::from(0u64));
        let leaf_id = base.intern_expr(None, &leaf).unwrap();
        let mut scr = Store::scratch();
        let parent = Expr::app(Arc::clone(&leaf), leaf);
        let sid = scr.intern_expr(Some(&base), &parent).unwrap();
        assert!(sid.is_scratch());
        match scr.expr_node(Some(&base), sid) {
            crate::bank::terms::Node::App { f, arg } => {
                assert_eq!(f, leaf_id, "child resolves to the base id");
                assert_eq!(arg, leaf_id);
            }
            other => panic!("expected App, got {other:?}"),
        }
        let back = scr.to_expr(Some(&base), sid, &mut g).unwrap();
        assert!(Expr::structural_eq(&back, &Expr::app(
            Expr::bvar(Nat::from(0u64)),
            Expr::bvar(Nat::from(0u64))
        ), &mut g).unwrap());
    }

    #[test]
    fn promote_translates_scratch_terms_into_base() {
        let mut g = RecGuard::new();
        let mut base = Store::persistent();
        let mut scr = Store::scratch();
        let e = Expr::lam(
            Arc::new(crate::Name::Str {
                parent: Arc::new(crate::Name::Anonymous),
                part: "x".to_string(),
            }),
            Expr::bvar(Nat::from(0u64)),
            Expr::app(Expr::bvar(Nat::from(0u64)), Expr::bvar(Nat::from(0u64))),
            crate::BinderInfo::Default,
        );
        let sid = scr.intern_expr(Some(&base), &e).unwrap();
        assert!(sid.is_scratch());
        let pid = promote(&mut base, &scr, sid).unwrap();
        assert!(!pid.is_scratch());
        // The promoted term reads back structurally identical from base alone.
        let back = base.to_expr(None, pid, &mut g).unwrap();
        assert!(Expr::structural_eq(&back, &e, &mut g).unwrap());
        // Promoting a persistent id is the identity.
        assert_eq!(promote(&mut base, &scr, pid).unwrap(), pid);
        // Promotion is stable (memo/dedup): same input ⇒ same output id.
        assert_eq!(promote(&mut base, &scr, sid).unwrap(), pid);
    }

    #[test]
    fn dropping_scratch_frees_without_touching_base() {
        let mut base = Store::persistent();
        let before = base.terms_len();
        {
            let mut scr = Store::scratch();
            let e = Expr::app(Expr::bvar(Nat::from(5u64)), Expr::bvar(Nat::from(6u64)));
            let _ = scr.intern_expr(Some(&base), &e).unwrap();
        } // scratch dropped wholesale
        assert_eq!(base.terms_len(), before, "scratch interning never mutates base");
    }
}
```

(`Store::terms_len(&self) -> usize` is a one-line accessor added alongside.)

- [ ] **Step 2: Verify failure** (the first two may already pass — Tasks 2-7 built the threading; `promote` is the new code and its test MUST fail with "function not found"). Run: `cargo test -p leanr_kernel bank::scratch 2>&1 | tail -5`.

- [ ] **Step 3: Implement `promote`** in `scratch.rs` — a two-phase (`Enter`/`Exit`) explicit stack over `Node`s: `Enter(sid)` short-circuits when `!sid.is_scratch()` or memoized; otherwise pushes `Exit(sid)` + `Enter` for each child id in the node; `Exit(sid)` reads `scr.expr_node(Some(base_snapshot)…)` — note `base` is `&mut` during promotion while reads of scratch need `&base` for routing: structure the loop to read the scratch node FIRST into an owned `Node` (it is `Copy`), then translate leaf ids (names via `to_name`+`intern_name`, levels via `to_level`+`intern_level`, kvmaps/nats/strs likewise) and call `base`'s intern-constructors with `base: None`. Scratch-region name/level/pool ids are translated on the fly inside `Exit`; persistent ones pass through.

- [ ] **Step 4: Run tests, lint, commit.**

```bash
cargo test -p leanr_kernel bank:: 2>&1 | tail -3
mise run lint
git add crates/leanr_kernel/src/bank
git commit -m "feat: scratch region reads/interns through base; promote() for add_core (bank Task 9)"
```

---

### Task 10: Docs + full gate

**Files:**
- Modify: `ARCHITECTURE.md` (one short paragraph in the `leanr_kernel` section: the `bank` module exists, is phase 1 of the term-bank migration, cites the spec path, and is not yet on any production path)
- Test: full CI gate

- [ ] **Step 1: Write the ARCHITECTURE.md paragraph** (match the file's existing tone; 3-4 sentences, citing `docs/superpowers/specs/2026-07-06-compact-expr-term-bank-design.md`).

- [ ] **Step 2: Full gate.**

Run: `cargo test --workspace 2>&1 | grep -E "test result|FAILED"` → all ok.
Run: `mise run ci` → clean.

- [ ] **Step 3: Commit.**

```bash
git add ARCHITECTURE.md
git commit -m "docs: note bank module (term-bank phase 1) in architecture map"
```

---

## Plan self-review (performed at write time)

1. **Spec coverage (phase-1 slice):** ids + region bit (§1/§2 — T1), probe table ~8 B/entry (§1 — T1), side pools all deduplicated incl. the LetE spill (§1 — T2/T5), NameId/LevelId with cached level flags making `sort`/`const` O(1) (§1/§3 — T3/T4), 21 B struct-of-arrays rows with all 15 tag variants incl. `BVarBig`/`ProjBig` (§1 — T6), interning invariant tested differentially (§5/§6 — T8), scratch region + cross-region canonical ids + `promote` for `add_core` (§2 — T9), no new deps / no unsafe / no panic / bounded allocation (§5 — global constraints + `BankExhausted`). Phases 2-3 (kernel cutover, decoder, acceptance sweeps) are explicitly separate plans per the approved phasing.
2. **Placeholder scan:** the one intentionally deferred body is `to_level`'s reverse walk (T4) and `intern_kvmap`'s field mapping (T5), both specified as "mirror the adjacent fully-written function" with the exact pattern (`intern_level`, `intern_str`) present in the same task — acceptable mirrors of code shown in full, not TBDs. Fixed the `names.rs` skeleton's stray import note inline.
3. **Type consistency:** `Store` methods all take `base: Option<&Store>` first; id types round-trip via `bits/from_bits`; `Node` field names match between T6 (definition), T7 (bridges), and T9 (promotion); `promote(base: &mut Store, scratch: &Store, id: ExprId)` matches its T9 test usage.
