# M1a — olean decoder + kernel data model Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Decode complete `.olean` files into owned kernel data types (`Name`, `Level`, `Expr`, `ConstantInfo`), demoed by `leanr olean decls`, validated against the oracle by golden fixtures and a sweep over all ~2,400 stdlib modules.

**Architecture:** New TCB crate `leanr_kernel` (data only, no workspace deps). `leanr_olean` gains a two-phase decoder: phase A walks the compacted object region into a generic, validated, offset-memoized `RawValue` DAG (the entire untrusted-bytes surface); phase B interprets that DAG into kernel types, preserving sharing via per-type memos. Spec: `docs/superpowers/specs/2026-07-04-m1a-olean-decoder-design.md`.

**Tech Stack:** Rust (mise-pinned), num-bigint, thiserror, proptest, cargo-fuzz (local only), the pinned oracle toolchain `leanprover/lean4:v4.32.0-rc1` for fixtures.

## Global Constraints

- Only these cargo deps may be added: `num-bigint` (leanr_kernel, leanr_olean) and `libfuzzer-sys` (in the workspace-excluded fuzz crate). Anything else needs a plan change.
- `leanr_kernel` depends on **no workspace crate** (TCB rule, AGENTS.md). Dependency direction: `leanr_olean → leanr_kernel`, never reverse.
- `.olean` bytes are untrusted: no panic, no unbounded recursion (decode **and** `Drop`), no unbounded allocation not tied to input length. Every claim about the format cites oracle source (file:line at tag `v4.32.0-rc1`) in a comment.
- The oracle pin (`lean-toolchain` = `leanprover/lean4:v4.32.0-rc1`, githash `b4812ae53eea93439ad5dce5a5c26591c31cb697`) does not change in this plan.
- Lint gate before every commit: `mise run lint` (fmt --check + clippy -D warnings). Full gate `mise run ci` where a task says so.
- Tools via mise only, exact-pinned (`mise use --pin`). Tasks run via `mise run <task>`.
- Conventional-commit prefixes (`feat:`, `test:`, `docs:`, `ci:`, `chore:`).
- Decoder supports 64-bit little-endian `.olean`s only (all oracle release platforms); document, don't detect.

## Layout reference (verified against oracle source at v4.32.0-rc1)

Facts below were read directly from the oracle sources at the pinned tag during planning. Cite these locations in code comments. If an implementation test contradicts one, re-read the cited source — do not guess.

**File layout (v2 olean)** — `src/library/module.cpp:107-144` (header struct), `:317-343` (v2 write path), `src/runtime/compact.cpp:479-517` (`operator()` allocates the root slot first):

```text
offset  0..88   header (M0's parser): marker "olean", version u8 @5 (must be 2),
                flags u8 @6 (bit 0: 1 = GMP bignum encoding), lean_version[33] @7,
                githash[40] @40, base_addr u64 LE @80
offset 88..96   root pointer word (an object_offset, see below)
offset 96..     objects, each 8-byte aligned (compact.cpp:163-166 pads all allocs)
```

`header.base_addr` is the address the *start of the file* would be mmapped at (module.cpp:131-132, `:334`). Pointer word → file offset: `off = ptr - base_addr`; valid object pointers satisfy `96 <= off`, `off % 8 == 0`, `off + 8 <= file_len`. A pointer word with bit 0 set is a boxed scalar with value `word >> 1` (lean.h:324-326). `0xFFFF_FFFF_FFFF_FFFE` is the compactor's internal null sentinel, never valid on disk (compact.cpp:156-161).

**Multi-part modules:** `saveModuleDataParts` (Environment.lean:1745-1750) writes `Foo.olean`, then `Foo.olean.server`/`Foo.olean.private` *sharing one compactor*, so later parts contain pointers below their own `base_addr` into earlier parts. The base `.olean` (first part) is always self-contained. This plan decodes base parts only; out-of-range pointers in `.server`/`.private` parts surface as `BadPointer` by construction.

**Object header** (8 bytes, lean.h:143-148): bytes 0-3 `m_rc` (0 in regions), 4-5 `m_cs_sz` u16 LE, 6 `m_other`, 7 `m_tag`. For ctor/thunk/task/ref/promise/mpz objects `m_cs_sz` = object byte size **as allocated on the heap, i.e. possibly rounded up past the logical field size** (copy_object, compact.cpp:233-243, stores `lean_object_byte_size(o)`, which for heap objects is the malloc bucket size) — so validate scalar areas with **minimum**-length checks, never exact-length. For array/sarray/string, `m_cs_sz` = 1 (`lean_set_non_heap_header_for_big`, lean.h) and real size comes from the object's own size fields.

**Tags** (lean.h:92-104): `0..=243` constructor (`m_other` = #pointer fields, scalars follow them); `244` Promise, `245` Closure, `246` Array, `247` StructArray, `248` ScalarArray (`m_other` = elem size), `249` String, `250` MPZ, `251` Thunk, `252` Task, `253` Ref, `254` External, `255` Reserved. The compactor can emit ctor/array/sarray/string/mpz plus thunk/task/promise/ref (value field at byte offset 8, matching `region_reader::fix_*`); closures throw in v2 (compact.cpp:355-375). Decode: 245 → `Unsupported`, 247/254/255 → `BadTag`.

**Payload layouts** (lean.h:182-209):
- Array (246): `m_size` u64 @8, `m_capacity` @16, `m_size` pointer words from @24.
- ScalarArray (248): `m_size` @8, `m_capacity` @16, `m_size * elem_size` bytes from @24.
- String (249): `m_size` (bytes incl. NUL) @8, `m_capacity` @16, `m_length` (UTF-8 chars) @24, bytes @32. Validate: `m_size >= 1`, last byte NUL, `bytes[..m_size-1]` valid UTF-8 (interior NUL is legal in Lean strings).
- MPZ (250), GMP encoding only (header flags bit 0 = 1; all official builds — module.cpp:114-122): after the 8-byte header, GMP `__mpz_struct`: `_mp_alloc` i32 @8 (= #limbs), `_mp_size` i32 @12 (sign × #limbs), `_mp_d` u64 pointer @16 which the writer always points at the limb data directly following at @24 (insert_mpz, compact.cpp:407-421) — enforce `_mp_d == base_addr + off + 24`. Limbs are u64 LE, least significant first (`BigUint::from_bytes_le` on the limb bytes works directly). Flags bit 0 = 0 → `Unsupported`.

**Constructor field order rule:** pointer-sized object fields first in declaration order, then scalar fields sorted by decreasing size (u64 before u8), declaration order within a size. `@[computed_field]`s (all u64 here) are scalars. Proof from the C++ kernel reading these exact objects: `letE`'s `nondep` bool is read at `4*sizeof(void*) + sizeof(uint64_t)` (src/kernel/expr.h:265) — 4 object fields, then the u64 `data`, then the u8. Fieldless ctors are boxed scalars `box(ctor_idx)` even when the inductive has computed fields (`Name.anonymous` = `box(0)`).

**Type layouts** (obj fields in order; scalar area offsets are relative to the end of the obj fields):

| Type (source) | Tag | Obj fields | Scalars |
|---|---|---|---|
| `Name.anonymous` (Init/Prelude.lean:4693-4717) | — | `box(0)` | |
| `Name.str` | 1 | pre, str (String) | hash u64 @0 (ignore; recomputable) |
| `Name.num` | 2 | pre, i (Nat) | hash u64 @0 |
| `Level` zero/succ/max/imax/param/mvar (Level.lean:90-103) | 0..5 | zero: `box(0)`; succ: 1; max/imax: 2; param/mvar: 1 (LMVarId ≅ Name) | data u64 @0 (ignore) |
| `Expr` (Expr.lean:321-471): bvar(Nat) fvar(Name) mvar(Name) sort(Level) const(Name, List Level) app(2×Expr) lam/forallE(Name, Expr, Expr) letE(Name, 3×Expr) lit(Literal) mdata(KVMap, Expr) proj(Name, Nat, Expr) | 0..11 | as listed (FVarId/MVarId ≅ Name — single-field structures are represented as the field itself) | data u64 @0 (ignore); lam/forallE: binderInfo u8 @8; letE: nondep u8 @8 |
| `Literal` natVal(Nat)/strVal(String) (Expr.lean:18-23) | 0/1 | 1 | |
| `BinderInfo` (Expr.lean:71-80) | — | scalar 0..3 | |
| `List` nil/cons | box(0)/1 | cons: head, tail | |
| `Prod.mk` | 0 | fst, snd | |
| `Bool`/enums in obj-field position | — | `box(0)`/`box(1)` | as struct field: u8 |
| `Nat`/`Int` in obj-field position | — | boxed scalar (Nat: `w>>1`; Int: 63-bit sign-extend) or MPZ pointer | |
| `KVMap` (Data/KVMap.lean:71-73) | — | ≅ `List (Name × DataValue)` (single-field struct) | |
| `DataValue` (Data/KVMap.lean:18-25) ofString/ofBool/ofName/ofNat/ofInt/ofSyntax | 0..5 | ofBool: 0; ofSyntax: unsupported; others: 1 | ofBool: v u8 @0 |
| `ModuleData` (Environment.lean:109-129) | 0 | imports, constNames, constants, extraConstNames, entries | isModule u8 @0 |
| `Import` (Setup.lean:25-32) | 0 | module | importAll, isExported, isMeta u8 @0,1,2 |
| `ConstantInfo` (Declaration.lean:429-437) Axiom/Defn/Thm/Opaque/Quot/Induct/Ctor/Rec | 0..7 | 1 (the Val) | |
| `ConstantVal` (Declaration.lean:95-99) | 0 | name, levelParams (List Name), type (Expr) | |
| `AxiomVal` (:101-103) | 0 | toConstantVal | isUnsafe u8 @0 |
| `DefinitionVal` (:120-133) | 0 | toConstantVal, value, hints, all | safety u8 @0 (0 unsafe, 1 safe, 2 partial — :116-118) |
| `ReducibilityHints` (:46-50) | — | opaque `box(0)`, abbrev `box(1)`, regular: tag 2, 0 obj | regular: height u32 @0 |
| `TheoremVal` (:142-146) | 0 | toConstantVal, value, all | |
| `OpaqueVal` (:156-160) | 0 | toConstantVal, value, all | isUnsafe u8 @0 |
| `QuotVal`/`QuotKind` (:410-421) | 0 | toConstantVal | kind u8 @0 (0 type, 1 ctor, 2 lift, 3 ind) |
| `InductiveVal` (:261-301) | 0 | toConstantVal, numParams, numIndices, all, ctors, numNested | isRec, isUnsafe, isReflexive u8 @0,1,2 |
| `ConstructorVal` (:328-334) | 0 | toConstantVal, induct, cidx, numParams, numFields | isUnsafe u8 @0 |
| `RecursorRule` (:348-356) | 0 | ctor, nfields, rhs | |
| `RecursorVal` (:357-379) | 0 | toConstantVal, all, numParams, numIndices, numMotives, numMinors, rules | k, isUnsafe u8 @0,1 |

`entries : Array (Name × Array EnvExtensionEntry)` payloads are arbitrary compacted objects — phase A validates them generically; phase B only counts them.

---

### Task 1: `leanr_kernel` crate — `Nat`, `Int`, `Name`

**Files:**
- Create: `crates/leanr_kernel/Cargo.toml`
- Create: `crates/leanr_kernel/src/lib.rs`
- Create: `crates/leanr_kernel/src/num.rs`
- Create: `crates/leanr_kernel/src/name.rs`
- Test: `crates/leanr_kernel/tests/name.rs`
- Modify: `Cargo.toml` (workspace member + `[workspace.dependencies]`)

**Interfaces:**
- Consumes: nothing.
- Produces: `leanr_kernel::{Nat, Int, Name}`. `Nat(pub num_bigint::BigUint)` with `From<u64>` and `Display`; `Int(pub num_bigint::BigInt)`; `Name` enum `{ Anonymous, Str { parent: Arc<Name>, part: String }, Num { parent: Arc<Name>, part: Nat } }` with iterative (non-recursive) `PartialEq`/`Hash`/`Display`/`Drop`. Every later task builds on these.

- [ ] **Step 1: Create the crate**

Add `"crates/leanr_kernel"` to `members` in the root `Cargo.toml`, and add to the root `Cargo.toml`:

```toml
[workspace.dependencies]
num-bigint = "0.4"
```

Create `crates/leanr_kernel/Cargo.toml`:

```toml
[package]
name = "leanr_kernel"
version.workspace = true
edition.workspace = true
license.workspace = true

[dependencies]
num-bigint = { workspace = true }
```

Create `crates/leanr_kernel/src/lib.rs`:

```rust
//! Kernel data model. This crate is the trusted computing base (see
//! AGENTS.md): it must depend on no other workspace crate, and it holds
//! only the data types in M1a — the checker arrives in M1b.
//!
//! Values of these types are built from UNTRUSTED `.olean` bytes by
//! `leanr_olean`, so they can be adversarially shaped (e.g. 100k-deep
//! `Name` parent chains). Nothing here may recurse proportionally to
//! value depth: traversals are loops or explicit stacks, and the `Arc`
//! tree types implement iterative `Drop`.

mod name;
mod num;

pub use name::Name;
pub use num::{Int, Nat};
```

Create `crates/leanr_kernel/src/num.rs`:

```rust
use std::fmt;

/// Lean `Nat`: arbitrary precision by language semantics (`.olean` files
/// really contain GMP-backed bignums for literals >= 2^63).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Nat(pub num_bigint::BigUint);

impl From<u64> for Nat {
    fn from(v: u64) -> Nat {
        Nat(num_bigint::BigUint::from(v))
    }
}

impl fmt::Display for Nat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// Lean `Int` (only reachable through `Expr` metadata in M1a).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Int(pub num_bigint::BigInt);

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
```

- [ ] **Step 2: Write the failing tests**

Create `crates/leanr_kernel/tests/name.rs`:

```rust
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use leanr_kernel::{Name, Nat};

fn str_name(parent: Arc<Name>, part: &str) -> Arc<Name> {
    Arc::new(Name::Str { parent, part: part.to_string() })
}

fn simple(parts: &[&str]) -> Arc<Name> {
    parts.iter().fold(Arc::new(Name::Anonymous), |p, s| str_name(p, s))
}

fn hash_of(n: &Name) -> u64 {
    let mut h = DefaultHasher::new();
    n.hash(&mut h);
    h.finish()
}

#[test]
fn display_matches_lean_unescaped_tostring() {
    assert_eq!(Name::Anonymous.to_string(), "[anonymous]");
    assert_eq!(simple(&["Init"]).to_string(), "Init");
    assert_eq!(simple(&["Init", "Nat", "add"]).to_string(), "Init.Nat.add");
    let hygienic = Arc::new(Name::Num {
        parent: simple(&["foo", "_hyg"]),
        part: Nat::from(23u64),
    });
    assert_eq!(hygienic.to_string(), "foo._hyg.23");
}

#[test]
fn equality_and_hashing_are_structural() {
    assert_eq!(*simple(&["a", "b"]), *simple(&["a", "b"]));
    assert_ne!(*simple(&["a", "b"]), *simple(&["a", "c"]));
    assert_ne!(*simple(&["a"]), Name::Anonymous);
    assert_eq!(hash_of(&simple(&["a", "b"])), hash_of(&simple(&["a", "b"])));
}

/// Untrusted input can produce arbitrarily deep parent chains; every
/// operation on `Name` (drop, eq, hash, display) must be iterative.
#[test]
fn deep_chains_do_not_overflow_the_stack() {
    const DEPTH: usize = 200_000;
    let build = || {
        let mut n = Arc::new(Name::Anonymous);
        for _ in 0..DEPTH {
            n = str_name(n, "x");
        }
        n
    };
    let a = build();
    let b = build();
    assert_eq!(*a, *b);
    assert_eq!(hash_of(&a), hash_of(&b));
    let rendered = a.to_string();
    assert_eq!(rendered.len(), DEPTH * 2 - 1); // "x.x.....x"
    drop(a);
    drop(b); // iterative Drop: must not overflow
}
```

- [ ] **Step 3: Run tests to verify they fail**

Run: `cargo test --package leanr_kernel`
Expected: compilation FAILS (`name.rs` module missing / `Name` not defined).

- [ ] **Step 4: Implement `Name`**

Create `crates/leanr_kernel/src/name.rs`:

```rust
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::sync::Arc;

use crate::Nat;

/// Lean hierarchical name (oracle: Init/Prelude.lean:4693-4717). The
/// oracle's runtime objects also carry a cached hash as a computed
/// field; we drop it on decode and recompute lazily when needed (M1b).
///
/// INVARIANT (crate docs): parent chains can be untrusted-deep, so
/// PartialEq/Hash/Display/Drop below are all loops, never recursion.
/// Deriving any of them would reintroduce a stack overflow on
/// adversarial input — do not "simplify" back to derives.
#[derive(Debug)]
pub enum Name {
    Anonymous,
    Str { parent: Arc<Name>, part: String },
    Num { parent: Arc<Name>, part: Nat },
}

impl Name {
    fn parent(&self) -> Option<&Arc<Name>> {
        match self {
            Name::Anonymous => None,
            Name::Str { parent, .. } | Name::Num { parent, .. } => Some(parent),
        }
    }
}

impl PartialEq for Name {
    fn eq(&self, other: &Name) -> bool {
        let (mut a, mut b) = (self, other);
        loop {
            match (a, b) {
                (Name::Anonymous, Name::Anonymous) => return true,
                (
                    Name::Str { parent: pa, part: sa },
                    Name::Str { parent: pb, part: sb },
                ) => {
                    if sa != sb {
                        return false;
                    }
                    (a, b) = (pa, pb);
                }
                (
                    Name::Num { parent: pa, part: na },
                    Name::Num { parent: pb, part: nb },
                ) => {
                    if na != nb {
                        return false;
                    }
                    (a, b) = (pa, pb);
                }
                _ => return false,
            }
        }
    }
}

impl Eq for Name {}

impl Hash for Name {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut cur = self;
        loop {
            match cur {
                Name::Anonymous => {
                    state.write_u8(0);
                    return;
                }
                Name::Str { parent, part } => {
                    state.write_u8(1);
                    part.hash(state);
                    cur = parent;
                }
                Name::Num { parent, part } => {
                    state.write_u8(2);
                    part.hash(state);
                    cur = parent;
                }
            }
        }
    }
}

/// Matches the oracle's `Name.toString (escape := false)`: components
/// joined with `.`, no identifier escaping. The golden-fixture dump
/// script (tests/fixtures/dump_decls.lean) prints names the same way,
/// so the two sides compare byte-for-byte.
impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if matches!(self, Name::Anonymous) {
            return f.write_str("[anonymous]");
        }
        let mut components: Vec<&Name> = Vec::new();
        let mut cur = self;
        while !matches!(cur, Name::Anonymous) {
            components.push(cur);
            cur = cur.parent().expect("non-anonymous names have parents");
        }
        for (i, component) in components.iter().rev().enumerate() {
            if i > 0 {
                f.write_str(".")?;
            }
            match component {
                Name::Anonymous => unreachable!("filtered above"),
                Name::Str { part, .. } => f.write_str(part)?,
                Name::Num { part, .. } => write!(f, "{part}")?,
            }
        }
        Ok(())
    }
}

impl Drop for Name {
    fn drop(&mut self) {
        // Detach the parent and unwind the chain with an explicit
        // stack. Each node we uniquely own gets its parent replaced by
        // Anonymous before it drops, so its own Drop recursion is O(1).
        let mut stack: Vec<Arc<Name>> = Vec::new();
        if let Some(parent) = self.parent_mut() {
            stack.push(mem::replace(parent, Arc::new(Name::Anonymous)));
        }
        while let Some(node) = stack.pop() {
            if let Ok(mut owned) = Arc::try_unwrap(node) {
                if let Some(parent) = owned.parent_mut() {
                    stack.push(mem::replace(parent, Arc::new(Name::Anonymous)));
                }
            }
        }
    }
}

impl Name {
    fn parent_mut(&mut self) -> Option<&mut Arc<Name>> {
        match self {
            Name::Anonymous => None,
            Name::Str { parent, .. } | Name::Num { parent, .. } => Some(parent),
        }
    }
}
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test --package leanr_kernel`
Expected: all 3 tests PASS. If `deep_chains_do_not_overflow_the_stack` crashes (SIGSEGV/abort rather than a failed assert), a derive or recursion crept in — fix the implementation, never shrink DEPTH.

- [ ] **Step 6: Lint and commit**

```bash
mise run lint
git add Cargo.toml Cargo.lock crates/leanr_kernel/
git commit -m "feat: leanr_kernel crate - Nat, Int, and adversarial-depth-safe Name"
```

---

### Task 2: `leanr_kernel` — `Level`, `Expr`, `Literal`, `BinderInfo`, `KVMap`

**Files:**
- Create: `crates/leanr_kernel/src/level.rs`
- Create: `crates/leanr_kernel/src/expr.rs`
- Test: `crates/leanr_kernel/tests/expr.rs`
- Modify: `crates/leanr_kernel/src/lib.rs`

**Interfaces:**
- Consumes: `Nat`, `Int`, `Name` from Task 1.
- Produces: `leanr_kernel::{Level, Expr, Literal, BinderInfo, KVMap, DataValue}` exactly as defined below; Task 3's `ConstantVal` holds `Arc<Expr>`, Task 6's interpreter constructs all of them.

- [ ] **Step 1: Write the failing tests**

Create `crates/leanr_kernel/tests/expr.rs`:

```rust
use std::sync::Arc;

use leanr_kernel::{BinderInfo, Expr, Level, Literal, Name, Nat};

fn bvar(idx: u64) -> Arc<Expr> {
    Arc::new(Expr::BVar { idx: Nat::from(idx) })
}

#[test]
fn constructing_a_small_term_works() {
    // fun (x : Sort 0) => x  (shape only; no checker yet)
    let lam = Expr::Lam {
        binder_name: Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: "x".to_string(),
        }),
        binder_type: Arc::new(Expr::Sort { level: Arc::new(Level::Zero) }),
        body: bvar(0),
        binder_info: BinderInfo::Default,
    };
    match lam {
        Expr::Lam { binder_info: BinderInfo::Default, .. } => {}
        _ => panic!("pattern"),
    }
    let _lit = Expr::Lit(Literal::StrVal("hello".to_string()));
}

/// Untrusted input can produce arbitrarily deep terms; Drop must be
/// iterative for every Arc-recursive kernel type.
#[test]
fn deep_expr_and_level_drops_do_not_overflow() {
    const DEPTH: usize = 200_000;
    let mut e = bvar(0);
    for _ in 0..DEPTH {
        e = Arc::new(Expr::App { f: e, arg: bvar(1) });
    }
    drop(e);

    let mut l = Arc::new(Level::Zero);
    for _ in 0..DEPTH {
        l = Arc::new(Level::Succ(l));
    }
    drop(l);
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test --package leanr_kernel --test expr`
Expected: compilation FAILS (`Level`, `Expr` not defined).

- [ ] **Step 3: Implement `Level`**

Create `crates/leanr_kernel/src/level.rs`:

```rust
use std::mem;
use std::sync::Arc;

use crate::Name;

/// Universe level (oracle: src/Lean/Level.lean:90-103). The oracle also
/// stores a computed `data` u64 (hash/depth/flags); we drop it on
/// decode and recompute in M1b. `MVar` is decoded faithfully; the
/// checker rejects metavariables, not the parser (spec).
///
/// No derived Eq/Ord/Hash: adversarial depth makes derived recursive
/// traversals a stack-overflow hazard; M1b adds hash-consed comparison.
#[derive(Debug)]
pub enum Level {
    Zero,
    Succ(Arc<Level>),
    Max(Arc<Level>, Arc<Level>),
    IMax(Arc<Level>, Arc<Level>),
    Param(Arc<Name>),
    MVar(Arc<Name>),
}

impl Drop for Level {
    fn drop(&mut self) {
        let mut stack: Vec<Arc<Level>> = Vec::new();
        take_level_children(self, &mut stack);
        while let Some(node) = stack.pop() {
            if let Ok(mut owned) = Arc::try_unwrap(node) {
                take_level_children(&mut owned, &mut stack);
            }
        }
    }
}

/// Detach `Arc<Level>` children into `stack`, leaving cheap leaves
/// behind so the node's own drop is O(1).
fn take_level_children(l: &mut Level, stack: &mut Vec<Arc<Level>>) {
    let zero = || Arc::new(Level::Zero);
    match l {
        Level::Zero | Level::Param(_) | Level::MVar(_) => {}
        Level::Succ(a) => stack.push(mem::replace(a, zero())),
        Level::Max(a, b) | Level::IMax(a, b) => {
            stack.push(mem::replace(a, zero()));
            stack.push(mem::replace(b, zero()));
        }
    }
}
```

- [ ] **Step 4: Implement `Expr` and friends**

Create `crates/leanr_kernel/src/expr.rs`:

```rust
use std::mem;
use std::sync::Arc;

use crate::{Int, Level, Name, Nat};

/// Binder annotation (oracle: src/Lean/Expr.lean:71-80).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

/// Literal (oracle: src/Lean/Expr.lean:18-23).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    NatVal(Nat),
    StrVal(String),
}

/// A value in expression metadata (oracle: src/Lean/Data/KVMap.lean:18-25).
/// `ofSyntax` is not represented: the decoder rejects it as unsupported
/// in M1a; the stdlib sweep (Task 8) is the arbiter of whether real
/// kernel-relevant terms ever carry Syntax metadata.
#[derive(Debug, Clone)]
pub enum DataValue {
    OfString(String),
    OfBool(bool),
    OfName(Arc<Name>),
    OfNat(Nat),
    OfInt(Int),
}

/// Expression metadata map (oracle: src/Lean/Data/KVMap.lean:71-73; a
/// single-field structure, so its runtime representation is the entry
/// list itself).
#[derive(Debug, Clone, Default)]
pub struct KVMap(pub Vec<(Arc<Name>, DataValue)>);

/// Kernel expression (oracle: src/Lean/Expr.lean:321-471). The oracle
/// stores a computed `data` u64 per node (hash, flags, loose-bvar
/// range); we drop it on decode — M1b reintroduces cached metadata
/// behind this same enum.
///
/// No derived Eq/Hash (see `Level`); `Drop` is iterative because term
/// depth is attacker-controlled.
#[derive(Debug)]
pub enum Expr {
    BVar { idx: Nat },
    FVar { id: Arc<Name> },
    MVar { id: Arc<Name> },
    Sort { level: Arc<Level> },
    Const { name: Arc<Name>, levels: Vec<Arc<Level>> },
    App { f: Arc<Expr>, arg: Arc<Expr> },
    Lam { binder_name: Arc<Name>, binder_type: Arc<Expr>, body: Arc<Expr>, binder_info: BinderInfo },
    ForallE { binder_name: Arc<Name>, binder_type: Arc<Expr>, body: Arc<Expr>, binder_info: BinderInfo },
    LetE { decl_name: Arc<Name>, ty: Arc<Expr>, value: Arc<Expr>, body: Arc<Expr>, non_dep: bool },
    Lit(Literal),
    MData { data: KVMap, expr: Arc<Expr> },
    Proj { type_name: Arc<Name>, idx: Nat, structure: Arc<Expr> },
}

impl Drop for Expr {
    fn drop(&mut self) {
        let mut stack: Vec<Arc<Expr>> = Vec::new();
        take_expr_children(self, &mut stack);
        while let Some(node) = stack.pop() {
            if let Ok(mut owned) = Arc::try_unwrap(node) {
                take_expr_children(&mut owned, &mut stack);
            }
        }
    }
}

fn take_expr_children(e: &mut Expr, stack: &mut Vec<Arc<Expr>>) {
    let leaf = || Arc::new(Expr::BVar { idx: Nat::from(0u64) });
    match e {
        Expr::BVar { .. }
        | Expr::FVar { .. }
        | Expr::MVar { .. }
        | Expr::Sort { .. }
        | Expr::Const { .. }
        | Expr::Lit(_) => {}
        Expr::App { f, arg } => {
            stack.push(mem::replace(f, leaf()));
            stack.push(mem::replace(arg, leaf()));
        }
        Expr::Lam { binder_type, body, .. } | Expr::ForallE { binder_type, body, .. } => {
            stack.push(mem::replace(binder_type, leaf()));
            stack.push(mem::replace(body, leaf()));
        }
        Expr::LetE { ty, value, body, .. } => {
            stack.push(mem::replace(ty, leaf()));
            stack.push(mem::replace(value, leaf()));
            stack.push(mem::replace(body, leaf()));
        }
        Expr::MData { expr, .. } | Expr::Proj { structure: expr, .. } => {
            stack.push(mem::replace(expr, leaf()));
        }
    }
}
```

Update `crates/leanr_kernel/src/lib.rs` module list and re-exports:

```rust
mod expr;
mod level;
mod name;
mod num;

pub use expr::{BinderInfo, DataValue, Expr, KVMap, Literal};
pub use level::Level;
pub use name::Name;
pub use num::{Int, Nat};
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test --package leanr_kernel`
Expected: all tests PASS, including Task 1's.

- [ ] **Step 6: Lint and commit**

```bash
mise run lint
git add crates/leanr_kernel/
git commit -m "feat: kernel Level and Expr data model with adversarial-depth-safe drops"
```

---

### Task 3: `leanr_kernel` — `ConstantInfo` and `Environment`

**Files:**
- Create: `crates/leanr_kernel/src/decl.rs`
- Create: `crates/leanr_kernel/src/env.rs`
- Test: `crates/leanr_kernel/tests/env.rs`
- Modify: `crates/leanr_kernel/src/lib.rs`

**Interfaces:**
- Consumes: `Name`, `Nat`, `Expr` from Tasks 1-2.
- Produces: `leanr_kernel::{ConstantVal, AxiomVal, DefinitionVal, TheoremVal, OpaqueVal, QuotVal, InductiveVal, ConstructorVal, RecursorRule, RecursorVal, ReducibilityHints, DefinitionSafety, QuotKind, ConstantInfo, Environment, EnvironmentError}`. `ConstantInfo::kind()` returns the exact strings Task 5's dump script prints (`axiom def thm opaque quot induct ctor rec`); `Environment::from_modules` is the spec's merge entry point.

- [ ] **Step 1: Write the failing tests**

Create `crates/leanr_kernel/tests/env.rs`:

```rust
use std::sync::Arc;

use leanr_kernel::{
    AxiomVal, ConstantInfo, ConstantVal, Environment, EnvironmentError, Expr, Level, Name,
};

fn name(s: &str) -> Arc<Name> {
    Arc::new(Name::Str { parent: Arc::new(Name::Anonymous), part: s.to_string() })
}

fn axiom_named(s: &str) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        val: ConstantVal {
            name: name(s),
            level_params: Vec::new(),
            ty: Arc::new(Expr::Sort { level: Arc::new(Level::Zero) }),
        },
        is_unsafe: false,
    })
}

#[test]
fn kind_strings_match_the_oracle_dump_script() {
    // Must stay in lockstep with kindStr in tests/fixtures/dump_decls.lean.
    assert_eq!(axiom_named("a").kind(), "axiom");
}

#[test]
fn from_modules_merges_and_indexes_by_name() {
    let env = Environment::from_modules([
        vec![axiom_named("a"), axiom_named("b")],
        vec![axiom_named("c")],
    ])
    .unwrap();
    assert_eq!(env.len(), 3);
    assert!(env.get(&name("b")).is_some());
    assert!(env.get(&name("zzz")).is_none());
}

#[test]
fn from_modules_rejects_duplicate_names() {
    let err = Environment::from_modules([vec![axiom_named("a")], vec![axiom_named("a")]])
        .unwrap_err();
    let EnvironmentError::DuplicateName(n) = err;
    assert_eq!(n.to_string(), "a");
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test --package leanr_kernel --test env`
Expected: compilation FAILS (`ConstantInfo` not defined).

- [ ] **Step 3: Implement declarations**

Create `crates/leanr_kernel/src/decl.rs`:

```rust
//! Constant declarations as the kernel sees them (oracle:
//! src/Lean/Declaration.lean; per-type line cites below). Field names
//! and order mirror the oracle so the decoder and future checker read
//! like the original.

use std::sync::Arc;

use crate::{Expr, Name, Nat};

/// oracle: Declaration.lean:95-99
#[derive(Debug, Clone)]
pub struct ConstantVal {
    pub name: Arc<Name>,
    pub level_params: Vec<Arc<Name>>,
    pub ty: Arc<Expr>,
}

/// oracle: Declaration.lean:46-50
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityHints {
    Opaque,
    Abbrev,
    Regular(u32),
}

/// oracle: Declaration.lean:116-118
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial,
}

/// oracle: Declaration.lean:410-415
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

/// oracle: Declaration.lean:101-103
#[derive(Debug, Clone)]
pub struct AxiomVal {
    pub val: ConstantVal,
    pub is_unsafe: bool,
}

/// oracle: Declaration.lean:120-133
#[derive(Debug, Clone)]
pub struct DefinitionVal {
    pub val: ConstantVal,
    pub value: Arc<Expr>,
    pub hints: ReducibilityHints,
    pub safety: DefinitionSafety,
    pub all: Vec<Arc<Name>>,
}

/// oracle: Declaration.lean:142-146
#[derive(Debug, Clone)]
pub struct TheoremVal {
    pub val: ConstantVal,
    pub value: Arc<Expr>,
    pub all: Vec<Arc<Name>>,
}

/// oracle: Declaration.lean:156-160
#[derive(Debug, Clone)]
pub struct OpaqueVal {
    pub val: ConstantVal,
    pub value: Arc<Expr>,
    pub is_unsafe: bool,
    pub all: Vec<Arc<Name>>,
}

/// oracle: Declaration.lean:417-421
#[derive(Debug, Clone)]
pub struct QuotVal {
    pub val: ConstantVal,
    pub kind: QuotKind,
}

/// oracle: Declaration.lean:261-301
#[derive(Debug, Clone)]
pub struct InductiveVal {
    pub val: ConstantVal,
    pub num_params: Nat,
    pub num_indices: Nat,
    pub all: Vec<Arc<Name>>,
    pub ctors: Vec<Arc<Name>>,
    pub num_nested: Nat,
    pub is_rec: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}

/// oracle: Declaration.lean:328-334
#[derive(Debug, Clone)]
pub struct ConstructorVal {
    pub val: ConstantVal,
    pub induct: Arc<Name>,
    pub cidx: Nat,
    pub num_params: Nat,
    pub num_fields: Nat,
    pub is_unsafe: bool,
}

/// oracle: Declaration.lean:348-356
#[derive(Debug, Clone)]
pub struct RecursorRule {
    pub ctor: Arc<Name>,
    pub nfields: Nat,
    pub rhs: Arc<Expr>,
}

/// oracle: Declaration.lean:357-379
#[derive(Debug, Clone)]
pub struct RecursorVal {
    pub val: ConstantVal,
    pub all: Vec<Arc<Name>>,
    pub num_params: Nat,
    pub num_indices: Nat,
    pub num_motives: Nat,
    pub num_minors: Nat,
    pub rules: Vec<RecursorRule>,
    pub k: bool,
    pub is_unsafe: bool,
}

/// oracle: Declaration.lean:429-437; variant order is the on-disk ctor
/// tag order, do not reorder.
#[derive(Debug, Clone)]
pub enum ConstantInfo {
    Axiom(AxiomVal),
    Defn(DefinitionVal),
    Thm(TheoremVal),
    Opaque(OpaqueVal),
    Quot(QuotVal),
    Induct(InductiveVal),
    Ctor(ConstructorVal),
    Rec(RecursorVal),
}

impl ConstantInfo {
    pub fn constant_val(&self) -> &ConstantVal {
        match self {
            ConstantInfo::Axiom(v) => &v.val,
            ConstantInfo::Defn(v) => &v.val,
            ConstantInfo::Thm(v) => &v.val,
            ConstantInfo::Opaque(v) => &v.val,
            ConstantInfo::Quot(v) => &v.val,
            ConstantInfo::Induct(v) => &v.val,
            ConstantInfo::Ctor(v) => &v.val,
            ConstantInfo::Rec(v) => &v.val,
        }
    }

    pub fn name(&self) -> &Arc<Name> {
        &self.constant_val().name
    }

    /// One-word kind label. Must stay byte-identical to `kindStr` in
    /// tests/fixtures/dump_decls.lean — the golden decls fixtures
    /// compare these strings against the oracle's output.
    pub fn kind(&self) -> &'static str {
        match self {
            ConstantInfo::Axiom(_) => "axiom",
            ConstantInfo::Defn(_) => "def",
            ConstantInfo::Thm(_) => "thm",
            ConstantInfo::Opaque(_) => "opaque",
            ConstantInfo::Quot(_) => "quot",
            ConstantInfo::Induct(_) => "induct",
            ConstantInfo::Ctor(_) => "ctor",
            ConstantInfo::Rec(_) => "rec",
        }
    }
}
```

Create `crates/leanr_kernel/src/env.rs`:

```rust
use std::collections::HashMap;
use std::sync::Arc;

use crate::{ConstantInfo, Name};

#[derive(Debug, PartialEq, Eq)]
pub enum EnvironmentError {
    DuplicateName(Arc<Name>),
}

/// The constant map the checker (M1b) will consult. M1a ships only
/// construction and lookup.
#[derive(Debug, Default)]
pub struct Environment {
    constants: HashMap<Arc<Name>, ConstantInfo>,
}

impl Environment {
    /// Merge decoded modules' constants; duplicate names are an error
    /// (spec: "errors on duplicates").
    pub fn from_modules<I>(modules: I) -> Result<Environment, EnvironmentError>
    where
        I: IntoIterator<Item = Vec<ConstantInfo>>,
    {
        let mut constants: HashMap<Arc<Name>, ConstantInfo> = HashMap::new();
        for module in modules {
            for info in module {
                let name = Arc::clone(info.name());
                if constants.contains_key(&name) {
                    return Err(EnvironmentError::DuplicateName(name));
                }
                constants.insert(name, info);
            }
        }
        Ok(Environment { constants })
    }

    pub fn get(&self, name: &Arc<Name>) -> Option<&ConstantInfo> {
        self.constants.get(name)
    }

    pub fn len(&self) -> usize {
        self.constants.len()
    }

    pub fn is_empty(&self) -> bool {
        self.constants.is_empty()
    }
}
```

Update `crates/leanr_kernel/src/lib.rs`:

```rust
mod decl;
mod env;
mod expr;
mod level;
mod name;
mod num;

pub use decl::{
    AxiomVal, ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety, DefinitionVal,
    InductiveVal, OpaqueVal, QuotKind, QuotVal, RecursorRule, RecursorVal, ReducibilityHints,
    TheoremVal,
};
pub use env::{Environment, EnvironmentError};
pub use expr::{BinderInfo, DataValue, Expr, KVMap, Literal};
pub use level::Level;
pub use name::Name;
pub use num::{Int, Nat};
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test --package leanr_kernel`
Expected: all tests PASS.

- [ ] **Step 5: Lint and commit**

```bash
mise run lint
git add crates/leanr_kernel/
git commit -m "feat: kernel ConstantInfo (all eight kinds) and Environment merge"
```

---

### Task 4: `leanr_olean` — phase A: raw compacted-region decoder

**Files:**
- Create: `crates/leanr_olean/src/raw.rs` (decoder + unit tests + proptests in `#[cfg(test)]`)
- Modify: `crates/leanr_olean/src/lib.rs` (header `version`/`flags` fields, new `OleanError` variants, `mod raw;`)
- Modify: `crates/leanr_olean/Cargo.toml` (`num-bigint`)

**Interfaces:**
- Consumes: `OleanHeader::parse` from M0.
- Produces: `pub(crate) mod raw` with `RawValue` (`Scalar(u64) | Ctor { tag: u8, fields: Vec<Arc<RawValue>>, scalars: Vec<u8> } | Array(Vec<Arc<RawValue>>) | ScalarArray { elem_size: u8, data: Vec<u8> } | Str(String) | BigInt(num_bigint::BigInt) | Indirect(Arc<RawValue>)`) and `pub(crate) fn parse_bytes(bytes: &[u8]) -> Result<Arc<RawValue>, OleanError>` — Task 6's `ModuleData::parse` calls this as phase A. Extends `OleanHeader` with `pub version: u8, pub flags: u8` and `OleanError` with `UnsupportedVersion(u8) | OutOfBounds { offset: u64 } | BadPointer { word: u64 } | BadTag { offset: u64, tag: u8 } | Cycle { offset: u64 } | Malformed { offset: u64, what: &'static str } | Unsupported { what: &'static str }`.

Tests live in a `#[cfg(test)] mod tests` inside `raw.rs` (the module is crate-private; integration tests can't see it — the public never-panic surface gets integration/fuzz coverage in Tasks 6-9).

- [ ] **Step 1: Extend the header parser and error enum**

In `crates/leanr_olean/src/lib.rs`:

1. Add to `OleanHeader` (with doc comments citing module.cpp:110-122): `pub version: u8` (byte 5) and `pub flags: u8` (byte 6), populated in `parse` (`let version = bytes[5]; let flags = bytes[6];` — both inside the already-bounds-checked header). Existing tests keep passing (no exhaustive struct construction outside `parse`).
2. Make the header length available to the decoder: `pub(crate) const HEADER_LEN: usize = ...` (change `const` to `pub(crate) const`).
3. Add `mod raw;` and extend `OleanError`:

```rust
    /// The version byte is not 2 (the plain module format). v3 regions
    /// (allowClosures) and unknown future versions are out of scope.
    #[error("unsupported olean format version {0} (leanr reads v2 module files)")]
    UnsupportedVersion(u8),
    /// A read past the end of the file (offset is the file offset).
    #[error("olean corrupt: read past end of file at offset {offset:#x}")]
    OutOfBounds { offset: u64 },
    /// A pointer word that is not a boxed scalar and does not resolve
    /// to an aligned in-bounds object (word is the raw pointer value).
    #[error("olean corrupt: bad object pointer {word:#x}")]
    BadPointer { word: u64 },
    /// An object tag that cannot appear in a module's object graph.
    #[error("olean corrupt: unexpected object tag {tag} at offset {offset:#x}")]
    BadTag { offset: u64, tag: u8 },
    /// The object graph contains a reference cycle (legitimate files
    /// are acyclic; a crafted cycle must error, not hang).
    #[error("olean corrupt: object cycle at offset {offset:#x}")]
    Cycle { offset: u64 },
    /// A structurally invalid object (bad sizes, bad UTF-8, bad enum
    /// byte, ...). `what` names the check that failed.
    #[error("olean corrupt: {what} at offset {offset:#x}")]
    Malformed { offset: u64, what: &'static str },
    /// A well-formed construct leanr does not read yet.
    #[error("unsupported olean content: {what}")]
    Unsupported { what: &'static str },
```

Add `num-bigint = { workspace = true }` under `[dependencies]` in `crates/leanr_olean/Cargo.toml`, and `leanr_olean` keeps `thiserror`; also add `[dev-dependencies] proptest = "1"` if not already present (it is, from M0).

- [ ] **Step 2: Write `raw.rs` skeleton + failing unit tests**

Create `crates/leanr_olean/src/raw.rs` with the types, an `unimplemented` body is NOT allowed — write the real implementation in Step 3; first commit the test module so you can watch it fail to compile. The test module (bottom of `raw.rs`):

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::OleanError;
    use proptest::prelude::*;

    /// Builds a syntactically valid v2 olean byte buffer around
    /// hand-placed objects (layout reference in the M1a plan).
    struct Builder {
        bytes: Vec<u8>,
    }

    const BASE: u64 = 0x7a0f_0000_0000;

    fn boxed(v: u64) -> u64 {
        (v << 1) | 1
    }

    impl Builder {
        fn new() -> Builder {
            let mut bytes = Vec::new();
            bytes.extend_from_slice(b"olean"); // marker
            bytes.push(2); // version
            bytes.push(1); // flags: GMP bignums
            bytes.extend_from_slice(&[0u8; 33]); // lean_version
            bytes.extend_from_slice(&[b'a'; 40]); // githash (hex)
            bytes.extend_from_slice(&BASE.to_le_bytes()); // base_addr
            bytes.extend_from_slice(&[0u8; 8]); // root slot (patched later)
            Builder { bytes }
        }

        fn set_root(&mut self, word: u64) {
            self.bytes[88..96].copy_from_slice(&word.to_le_bytes());
        }

        fn align(&mut self) {
            while self.bytes.len() % 8 != 0 {
                self.bytes.push(0);
            }
        }

        /// Emit an object header + body; returns the pointer word.
        fn object(&mut self, tag: u8, other: u8, cs_sz: u16, body: &[u8]) -> u64 {
            self.align();
            let off = self.bytes.len() as u64;
            self.bytes.extend_from_slice(&0u32.to_le_bytes()); // m_rc
            self.bytes.extend_from_slice(&cs_sz.to_le_bytes());
            self.bytes.push(other);
            self.bytes.push(tag);
            self.bytes.extend_from_slice(body);
            BASE + off
        }

        fn ctor(&mut self, tag: u8, fields: &[u64], scalars: &[u8]) -> u64 {
            let mut body = Vec::new();
            for f in fields {
                body.extend_from_slice(&f.to_le_bytes());
            }
            body.extend_from_slice(scalars);
            let cs_sz = (8 + body.len()) as u16;
            self.object(tag, fields.len() as u8, cs_sz, &body)
        }

        fn array(&mut self, elems: &[u64]) -> u64 {
            let mut body = Vec::new();
            body.extend_from_slice(&(elems.len() as u64).to_le_bytes()); // size
            body.extend_from_slice(&(elems.len() as u64).to_le_bytes()); // capacity
            for e in elems {
                body.extend_from_slice(&e.to_le_bytes());
            }
            self.object(246, 0, 1, &body)
        }

        fn string(&mut self, s: &str) -> u64 {
            let size = (s.len() + 1) as u64;
            let mut body = Vec::new();
            body.extend_from_slice(&size.to_le_bytes());
            body.extend_from_slice(&size.to_le_bytes()); // capacity
            body.extend_from_slice(&(s.chars().count() as u64).to_le_bytes());
            body.extend_from_slice(s.as_bytes());
            body.push(0);
            self.object(249, 0, 1, &body)
        }

        fn mpz(&mut self, limbs: &[u64], negative: bool) -> u64 {
            self.align();
            let off = self.bytes.len() as u64;
            let n = limbs.len() as i32;
            let mut body = Vec::new();
            body.extend_from_slice(&n.to_le_bytes()); // _mp_alloc
            body.extend_from_slice(&(if negative { -n } else { n }).to_le_bytes()); // _mp_size
            body.extend_from_slice(&(BASE + off + 24).to_le_bytes()); // _mp_d
            for l in limbs {
                body.extend_from_slice(&l.to_le_bytes());
            }
            self.object(250, 0, 24, &body)
        }

        /// Reserve a ctor whose field words get patched later (cycles).
        fn patch_field(&mut self, obj_word: u64, field_idx: usize, new_word: u64) {
            let off = (obj_word - BASE) as usize + 8 + field_idx * 8;
            self.bytes[off..off + 8].copy_from_slice(&new_word.to_le_bytes());
        }

        fn finish(self) -> Vec<u8> {
            self.bytes
        }
    }

    fn parse(b: Builder) -> Result<Arc<RawValue>, OleanError> {
        parse_bytes(&b.finish())
    }

    #[test]
    fn scalar_root() {
        let mut b = Builder::new();
        b.set_root(boxed(21));
        assert!(matches!(*parse(b).unwrap(), RawValue::Scalar(21)));
    }

    #[test]
    fn ctor_graph_preserves_sharing() {
        let mut b = Builder::new();
        let s = b.string("hi");
        let root = b.ctor(0, &[s, s], &[7]);
        b.set_root(root);
        let v = parse(b).unwrap();
        let RawValue::Ctor { tag: 0, fields, scalars } = &*v else {
            panic!("expected ctor, got {v:?}")
        };
        assert_eq!(scalars, &[7]);
        assert!(Arc::ptr_eq(&fields[0], &fields[1]), "memo must dedupe shared offsets");
        assert!(matches!(&*fields[0], RawValue::Str(s) if s == "hi"));
    }

    #[test]
    fn arrays_and_bignums_decode() {
        let mut b = Builder::new();
        let big = b.mpz(&[0, 1], false); // 2^64
        let arr = b.array(&[boxed(1), big]);
        b.set_root(arr);
        let v = parse(b).unwrap();
        let RawValue::Array(elems) = &*v else { panic!() };
        assert!(matches!(&*elems[0], RawValue::Scalar(1)));
        let RawValue::BigInt(i) = &*elems[1] else { panic!() };
        assert_eq!(*i, num_bigint::BigInt::from(2u128.pow(64)));
    }

    #[test]
    fn negative_mpz_keeps_its_sign() {
        let mut b = Builder::new();
        let big = b.mpz(&[0, 1], true);
        b.set_root(big);
        let RawValue::BigInt(i) = &*parse(b).unwrap() else { panic!() };
        assert_eq!(*i, -num_bigint::BigInt::from(2u128.pow(64)));
    }

    #[test]
    fn cycles_error_instead_of_hanging() {
        let mut b = Builder::new();
        let c = b.ctor(0, &[boxed(0)], &[]);
        b.patch_field(c, 0, c); // now points at itself
        b.set_root(c);
        assert!(matches!(parse(b), Err(OleanError::Cycle { .. })));
    }

    #[test]
    fn bad_pointers_and_tags_error() {
        let mut b = Builder::new();
        let unaligned = b.ctor(0, &[BASE + 100], &[]); // even but 100 % 8 != 0
        b.set_root(unaligned);
        assert!(matches!(parse(b), Err(OleanError::BadPointer { .. })));

        let mut b = Builder::new();
        let oob = b.ctor(0, &[BASE + (1 << 20)], &[]); // aligned but past EOF
        b.set_root(oob);
        assert!(matches!(parse(b), Err(OleanError::BadPointer { .. })));

        let mut b = Builder::new();
        let bad = b.object(247, 0, 1, &[0; 16]); // StructArray: never valid
        b.set_root(bad);
        assert!(matches!(parse(b), Err(OleanError::BadTag { tag: 247, .. })));

        let mut b = Builder::new();
        let closure = b.object(245, 0, 24, &[0; 24]);
        b.set_root(closure);
        assert!(matches!(parse(b), Err(OleanError::Unsupported { .. })));
    }

    #[test]
    fn version_3_is_rejected() {
        let mut b = Builder::new();
        b.bytes[5] = 3;
        b.set_root(boxed(0));
        assert!(matches!(parse(b), Err(OleanError::UnsupportedVersion(3))));
    }

    #[test]
    fn deep_graphs_decode_and_drop_iteratively() {
        let mut b = Builder::new();
        let mut prev = boxed(0);
        for _ in 0..200_000 {
            prev = b.ctor(1, &[prev], &[]);
        }
        b.set_root(prev);
        let v = parse(b).unwrap();
        drop(v); // must not overflow the stack
    }

    #[test]
    fn the_real_oracle_fixture_decodes() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/fixtures/Sample.olean"
        );
        let bytes = std::fs::read(path).unwrap();
        let v = parse_bytes(&bytes).unwrap();
        assert!(matches!(&*v, RawValue::Ctor { tag: 0, .. }), "root must be ModuleData");
    }

    proptest! {
        /// Untrusted input: never panic, never hang, whatever the bytes.
        #[test]
        fn arbitrary_bytes_never_panic(bytes in proptest::collection::vec(any::<u8>(), 0..512)) {
            let _ = parse_bytes(&bytes);
        }

        /// Mutations of a real file exercise deep decoder paths.
        #[test]
        fn mutated_fixture_never_panics(idx in 0usize..100_000, byte in any::<u8>()) {
            let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/fixtures/Sample.olean");
            let mut bytes = std::fs::read(path).unwrap();
            let i = idx % bytes.len();
            bytes[i] = byte;
            let _ = parse_bytes(&bytes);
        }
    }
}
```

- [ ] **Step 3: Implement the decoder (top of `raw.rs`)**

```rust
//! Phase A of `.olean` decoding: walk the compacted object region into
//! a validated, offset-memoized [`RawValue`] DAG.
//!
//! This module is the ENTIRE untrusted-bytes surface of leanr_olean
//! (docs/THREAT_MODEL.md): every pointer is bounds- and
//! alignment-checked, every tag matched against what the oracle's
//! compactor can emit, cycles are detected, and both the walk and
//! `RawValue`'s `Drop` are iterative so adversarial nesting cannot
//! overflow the stack. Phase B (`interp`) consumes the DAG and never
//! touches raw bytes.
//!
//! Region model (oracle at v4.32.0-rc1 — src/library/module.cpp:107-144
//! v2 write path :317-343; src/runtime/compact.cpp:479-517 root slot,
//! :163-166 8-byte alignment, :183-198 max-sharing):
//! file = [88-byte header][8-byte root pointer word][objects...].
//! Pointer words are `base_addr`-relative addresses of the file start;
//! odd words are boxed scalars (lean.h:324-326).

use std::collections::HashMap;
use std::mem;
use std::sync::Arc;

use num_bigint::{BigInt, BigUint, Sign};

use crate::{OleanError, OleanHeader, HEADER_LEN};

/// File offset of the root pointer word (compact.cpp:483-489: the
/// compactor allocates the root slot before any object).
const ROOT_PTR_OFFSET: u64 = HEADER_LEN as u64;
/// First possible object offset: right after the root slot.
const FIRST_OBJECT_OFFSET: u64 = ROOT_PTR_OFFSET + 8;
/// The compactor's internal null sentinel (compact.cpp:156-161);
/// never valid in a written file.
const NULL_SENTINEL: u64 = u64::MAX - 1;

// Non-constructor tags, lean.h:92-104.
const TAG_PROMISE: u8 = 244;
const TAG_CLOSURE: u8 = 245;
const TAG_ARRAY: u8 = 246;
const TAG_STRUCT_ARRAY: u8 = 247;
const TAG_SCALAR_ARRAY: u8 = 248;
const TAG_STRING: u8 = 249;
const TAG_MPZ: u8 = 250;
const TAG_THUNK: u8 = 251;
const TAG_TASK: u8 = 252;
const TAG_REF: u8 = 253;

/// A decoded object graph node. Owned, `Arc`-shared exactly where the
/// file shared offsets. `Indirect` wraps thunk/task/ref/promise value
/// cells (compact.cpp insert_thunk/insert_task/insert_promise/
/// insert_ref: single compacted value at byte offset 8).
#[derive(Debug)]
pub(crate) enum RawValue {
    Scalar(u64),
    Ctor { tag: u8, fields: Vec<Arc<RawValue>>, scalars: Vec<u8> },
    Array(Vec<Arc<RawValue>>),
    ScalarArray { elem_size: u8, data: Vec<u8> },
    Str(String),
    BigInt(BigInt),
    Indirect(Arc<RawValue>),
}

impl Drop for RawValue {
    fn drop(&mut self) {
        // Adversarial nesting depth: unwind with an explicit stack.
        let mut stack: Vec<Arc<RawValue>> = Vec::new();
        take_raw_children(self, &mut stack);
        while let Some(node) = stack.pop() {
            if let Ok(mut owned) = Arc::try_unwrap(node) {
                take_raw_children(&mut owned, &mut stack);
            }
        }
    }
}

fn take_raw_children(v: &mut RawValue, stack: &mut Vec<Arc<RawValue>>) {
    match v {
        RawValue::Scalar(_)
        | RawValue::ScalarArray { .. }
        | RawValue::Str(_)
        | RawValue::BigInt(_) => {}
        RawValue::Ctor { fields, .. } => stack.append(fields),
        RawValue::Array(elems) => stack.append(elems),
        RawValue::Indirect(inner) => {
            stack.push(mem::replace(inner, Arc::new(RawValue::Scalar(0))));
        }
    }
}

/// Parse a whole `.olean` file into its root value (phase A entry;
/// Task 6's `ModuleData::parse` is the public wrapper).
pub(crate) fn parse_bytes(bytes: &[u8]) -> Result<Arc<RawValue>, OleanError> {
    let header = OleanHeader::parse(bytes)?;
    // v3 moves the object data (module.cpp:133-140); everything this
    // decoder assumes below is the v2 layout.
    if header.version != 2 {
        return Err(OleanError::UnsupportedVersion(header.version));
    }
    let region = Region {
        bytes,
        base_addr: header.base_addr,
        // flags bit 0: GMP vs Lean-native bignum encoding (module.cpp:114-122).
        gmp: header.flags & 1 == 1,
    };
    match region.resolve(region.word(ROOT_PTR_OFFSET)?)? {
        Word::Scalar(v) => Ok(Arc::new(RawValue::Scalar(v))),
        Word::ObjectAt(off) => decode_graph(&region, off),
    }
}

struct Region<'a> {
    bytes: &'a [u8],
    base_addr: u64,
    gmp: bool,
}

enum Word {
    Scalar(u64),
    ObjectAt(u64),
}

impl Region<'_> {
    fn len(&self) -> u64 {
        self.bytes.len() as u64
    }

    fn slice(&self, off: u64, len: u64) -> Result<&[u8], OleanError> {
        let end = off.checked_add(len).ok_or(OleanError::OutOfBounds { offset: off })?;
        if end > self.len() {
            return Err(OleanError::OutOfBounds { offset: off });
        }
        Ok(&self.bytes[off as usize..end as usize])
    }

    fn word(&self, off: u64) -> Result<u64, OleanError> {
        Ok(u64::from_le_bytes(self.slice(off, 8)?.try_into().expect("8 bytes")))
    }

    fn u32(&self, off: u64) -> Result<u32, OleanError> {
        Ok(u32::from_le_bytes(self.slice(off, 4)?.try_into().expect("4 bytes")))
    }

    /// Classify a pointer word (lean.h:324-326; layout reference).
    fn resolve(&self, word: u64) -> Result<Word, OleanError> {
        if word & 1 == 1 {
            return Ok(Word::Scalar(word >> 1));
        }
        if word == NULL_SENTINEL {
            return Err(OleanError::BadPointer { word });
        }
        let off = word
            .checked_sub(self.base_addr)
            .ok_or(OleanError::BadPointer { word })?;
        if off < FIRST_OBJECT_OFFSET || off % 8 != 0 || off + 8 > self.len() {
            return Err(OleanError::BadPointer { word });
        }
        Ok(Word::ObjectAt(off))
    }
}

/// One object's parsed shape: everything needed to (a) enumerate its
/// children and (b) build its `RawValue` once the children exist.
enum Shape {
    Ctor { tag: u8, field_words: Vec<u64>, scalars: Vec<u8> },
    Array { elem_words: Vec<u64> },
    ScalarArray { elem_size: u8, data: Vec<u8> },
    Str(String),
    BigInt(BigInt),
    Indirect { value_word: u64 },
}

impl Shape {
    fn child_words(&self) -> &[u64] {
        match self {
            Shape::Ctor { field_words, .. } => field_words,
            Shape::Array { elem_words } => elem_words,
            Shape::Indirect { value_word } => std::slice::from_ref(value_word),
            _ => &[],
        }
    }
}

/// Read and validate the object at `off` (layout reference in the M1a
/// plan; object header lean.h:143-148, payloads lean.h:182-209).
fn read_object(region: &Region, off: u64) -> Result<Shape, OleanError> {
    let header = region.word(off)?;
    let rc = header as u32;
    let cs_sz = (header >> 32) as u16;
    let other = (header >> 48) as u8;
    let tag = (header >> 56) as u8;
    if rc != 0 {
        // lean_set_non_heap_header zeroes m_rc for every region object.
        return Err(OleanError::Malformed { offset: off, what: "nonzero refcount" });
    }
    match tag {
        TAG_ARRAY => {
            let size = region.word(off + 8)?;
            // Guard allocation: an honest size fits in the file.
            if size > (region.len() - off) / 8 {
                return Err(OleanError::Malformed { offset: off, what: "array size" });
            }
            let mut elem_words = Vec::with_capacity(size as usize);
            for i in 0..size {
                elem_words.push(region.word(off + 24 + 8 * i)?);
            }
            Ok(Shape::Array { elem_words })
        }
        TAG_SCALAR_ARRAY => {
            if !(1..=8).contains(&other) {
                return Err(OleanError::Malformed { offset: off, what: "sarray elem size" });
            }
            let size = region.word(off + 8)?;
            let byte_len = size
                .checked_mul(other as u64)
                .ok_or(OleanError::Malformed { offset: off, what: "sarray size" })?;
            Ok(Shape::ScalarArray { elem_size: other, data: region.slice(off + 24, byte_len)?.to_vec() })
        }
        TAG_STRING => {
            let size = region.word(off + 8)?;
            if size == 0 {
                return Err(OleanError::Malformed { offset: off, what: "empty string object" });
            }
            let data = region.slice(off + 32, size)?;
            if data[data.len() - 1] != 0 {
                return Err(OleanError::Malformed { offset: off, what: "string missing NUL" });
            }
            let s = std::str::from_utf8(&data[..data.len() - 1])
                .map_err(|_| OleanError::Malformed { offset: off, what: "string not UTF-8" })?;
            Ok(Shape::Str(s.to_string()))
        }
        TAG_MPZ => {
            if !region.gmp {
                // module.cpp:114-122: flag bit 0 = 0 means Lean-native
                // limb encoding; every official build uses GMP. Revisit
                // only if the stdlib sweep ever hits this.
                return Err(OleanError::Unsupported { what: "non-GMP bignum encoding" });
            }
            let alloc = region.u32(off + 8)? as i32;
            let mp_size = region.u32(off + 12)? as i32;
            let data_ptr = region.word(off + 16)?;
            let nlimbs = mp_size.unsigned_abs() as u64;
            if nlimbs == 0 || alloc != mp_size.abs() {
                return Err(OleanError::Malformed { offset: off, what: "mpz limb count" });
            }
            // insert_mpz (compact.cpp:407-421) always points _mp_d at
            // the limbs directly following the 24-byte mpz_object.
            if data_ptr != region.base_addr + off + 24 {
                return Err(OleanError::Malformed { offset: off, what: "mpz data pointer" });
            }
            let limb_bytes = region.slice(off + 24, 8 * nlimbs)?;
            let magnitude = BigUint::from_bytes_le(limb_bytes);
            let sign = if mp_size < 0 { Sign::Minus } else { Sign::Plus };
            Ok(Shape::BigInt(BigInt::from_biguint(sign, magnitude)))
        }
        TAG_PROMISE | TAG_THUNK | TAG_TASK | TAG_REF => {
            // Value cell at byte offset 8 (compact.cpp fix_thunk et al.).
            Ok(Shape::Indirect { value_word: region.word(off + 8)? })
        }
        TAG_CLOSURE => Err(OleanError::Unsupported { what: "closure (v3-only content)" }),
        TAG_STRUCT_ARRAY | 254 | 255 => Err(OleanError::BadTag { offset: off, tag }),
        _ => {
            // Constructor object: `other` = #pointer fields; cs_sz =
            // heap byte size (>= logical size; see layout reference —
            // minimum-length checks only).
            let num_fields = other as u64;
            let min_sz = 8 + 8 * num_fields;
            if (cs_sz as u64) < min_sz {
                return Err(OleanError::Malformed { offset: off, what: "ctor size" });
            }
            let mut field_words = Vec::with_capacity(num_fields as usize);
            for i in 0..num_fields {
                field_words.push(region.word(off + 8 + 8 * i)?);
            }
            let scalars = region.slice(off + min_sz, cs_sz as u64 - min_sz)?.to_vec();
            Ok(Shape::Ctor { tag, field_words, scalars })
        }
    }
}

enum Slot {
    InProgress,
    Done(Arc<RawValue>),
}

/// Iterative post-order DFS with offset memoization. `InProgress` on
/// re-visit means the offset is on the current DFS path → cycle.
fn decode_graph(region: &Region, root_off: u64) -> Result<Arc<RawValue>, OleanError> {
    enum Step {
        Visit(u64),
        Build(u64, Shape),
    }
    let mut memo: HashMap<u64, Slot> = HashMap::new();
    let mut stack = vec![Step::Visit(root_off)];
    while let Some(step) = stack.pop() {
        match step {
            Step::Visit(off) => match memo.get(&off) {
                Some(Slot::Done(_)) => {}
                Some(Slot::InProgress) => return Err(OleanError::Cycle { offset: off }),
                None => {
                    memo.insert(off, Slot::InProgress);
                    let shape = read_object(region, off)?;
                    let children: Vec<u64> = shape.child_words().to_vec();
                    stack.push(Step::Build(off, shape));
                    for word in children {
                        if let Word::ObjectAt(child) = region.resolve(word)? {
                            stack.push(Step::Visit(child));
                        }
                    }
                }
            },
            Step::Build(off, shape) => {
                let resolve_child = |word: u64| -> Result<Arc<RawValue>, OleanError> {
                    match region.resolve(word)? {
                        Word::Scalar(v) => Ok(Arc::new(RawValue::Scalar(v))),
                        Word::ObjectAt(o) => match memo.get(&o) {
                            Some(Slot::Done(v)) => Ok(Arc::clone(v)),
                            // Post-order guarantees children are built;
                            // reaching this is a decoder bug, and the
                            // spec says internal errors panic loudly.
                            _ => unreachable!("child at {o:#x} not built before parent"),
                        },
                    }
                };
                let value = match shape {
                    Shape::Ctor { tag, field_words, scalars } => RawValue::Ctor {
                        tag,
                        fields: field_words
                            .iter()
                            .map(|w| resolve_child(*w))
                            .collect::<Result<_, _>>()?,
                        scalars,
                    },
                    Shape::Array { elem_words } => RawValue::Array(
                        elem_words.iter().map(|w| resolve_child(*w)).collect::<Result<_, _>>()?,
                    ),
                    Shape::ScalarArray { elem_size, data } => {
                        RawValue::ScalarArray { elem_size, data }
                    }
                    Shape::Str(s) => RawValue::Str(s),
                    Shape::BigInt(i) => RawValue::BigInt(i),
                    Shape::Indirect { value_word } => RawValue::Indirect(resolve_child(value_word)?),
                };
                memo.insert(off, Slot::Done(Arc::new(value)));
            }
        }
    }
    match memo.remove(&root_off) {
        Some(Slot::Done(v)) => Ok(v),
        _ => unreachable!("root not built by the DFS"),
    }
}
```

Note on the header word decode: `m_rc` is bytes 0-3, `m_cs_sz` bytes 4-5, `m_other` byte 6, `m_tag` byte 7 (lean.h:143-148, little-endian) — the shifts above implement exactly that; keep the citation.

- [ ] **Step 4: Run the tests**

Run: `cargo test --package leanr_olean`
Expected: all `raw::tests` PASS, plus M0's header tests. `the_real_oracle_fixture_decodes` is the canary: if it fails with `BadTag`/`Malformed`, some layout assumption is off — re-read the cited oracle source, fix the constant, and note the correction in the code comment. Do not loosen validation to make it pass.

- [ ] **Step 5: Lint and commit**

```bash
mise run lint
git add crates/leanr_olean/ Cargo.toml Cargo.lock
git commit -m "feat: leanr_olean raw compacted-region decoder - validated, memoized, cycle-safe"
```

---

### Task 5: Oracle fixtures — rich sample module + golden decls dumps

**Files:**
- Create: `tests/fixtures/SampleRich.lean`
- Create: `tests/fixtures/dump_decls.lean`
- Create (generated, committed): `tests/fixtures/SampleRich.olean`, `tests/fixtures/Sample.decls.txt`, `tests/fixtures/SampleRich.decls.txt`
- Modify: `mise.toml` (`fixtures:regen`)

**Interfaces:**
- Consumes: the pinned oracle toolchain (via `elan:bootstrap`), existing `Sample.lean`.
- Produces: committed golden fixtures consumed by Task 6's decoder tests and Task 7's CLI tests. The decls format is one constant per line, **in `ModuleData.constants` order**: `<kind> <name>` where `<kind>` ∈ `axiom def thm opaque quot induct ctor rec` (must equal `ConstantInfo::kind()` from Task 3) and `<name>` is the unescaped dot-joined name (must equal Task 1's `Display for Name`).

- [ ] **Step 1: Write the rich sample module**

Create `tests/fixtures/SampleRich.lean` — exercises every constant kind reachable in a user module (quotInfo only exists in core's `Init.Prelude`; the stdlib sweep covers it), plus a GMP bignum literal and a unicode string:

```lean
axiom richAxiom : Nat → Prop

opaque richOpaque : Nat := 7

inductive RichTree where
  | leaf : RichTree
  | node : RichTree → RichTree → RichTree

structure RichPoint where
  x : Nat
  y : Nat

def richBig : Nat := 340282366920938463463374607431768211455

def richString : String := "héllo⟨w⟩orld"

theorem richTheorem : richOpaque = richOpaque := rfl

partial def richPartial (n : Nat) : Nat :=
  if n == 0 then 0 else richPartial (n - 1)

mutual
  def richEven : Nat → Bool
    | 0 => true
    | n + 1 => richOdd n
  def richOdd : Nat → Bool
    | 0 => false
    | n + 1 => richEven n
end
```

- [ ] **Step 2: Write the oracle dump script**

Create `tests/fixtures/dump_decls.lean`:

```lean
/-
Golden-fixture generator: prints one `<kind> <name>` line per constant
in a module's `.olean`, in `ModuleData.constants` order. leanr's
`ConstantInfo::kind()` and `Display for Name` (unescaped, dot-joined)
must match this output byte-for-byte — that is the golden contract.
Run via `mise run fixtures:regen`.
-/
import Lean

open Lean

def kindStr : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"

def main (args : List String) : IO Unit := do
  let (mod, region) ← readModuleData ⟨args.head!⟩
  for c in mod.constants do
    IO.println s!"{kindStr c} {c.name.toString (escape := false)}"
  -- Keep the region alive until after printing: `mod`'s objects live
  -- inside it.
  discard <| pure region
```

If the pinned toolchain rejects `toString (escape := false)` (signature drift), check `Name.toString`'s actual signature in the oracle source at the tag and adapt the call — but keep output unescaped and dot-joined, and keep Task 1's `Display` in lockstep.

- [ ] **Step 3: Extend the regen task**

Replace the `fixtures:regen` task in `mise.toml` with:

```toml
[tasks."fixtures:regen"]
description = "Regenerate oracle golden fixtures (requires the pinned Lean toolchain)"
depends = ["elan:bootstrap"]
run = [
  "lean tests/fixtures/Sample.lean -o tests/fixtures/Sample.olean",
  "lean tests/fixtures/SampleRich.lean -o tests/fixtures/SampleRich.olean",
  "sh -c 'lean --run tests/fixtures/dump_decls.lean tests/fixtures/Sample.olean > tests/fixtures/Sample.decls.txt'",
  "sh -c 'lean --run tests/fixtures/dump_decls.lean tests/fixtures/SampleRich.olean > tests/fixtures/SampleRich.decls.txt'",
  "sh -c 'lean --githash > tests/fixtures/oracle-githash.txt'",
]
```

- [ ] **Step 4: Generate and sanity-check**

```bash
mise run fixtures:regen
wc -l tests/fixtures/*.decls.txt
grep -c "^induct RichTree$" tests/fixtures/SampleRich.decls.txt
grep -c "^ctor RichTree.node$" tests/fixtures/SampleRich.decls.txt
grep -c "^rec RichTree.rec$" tests/fixtures/SampleRich.decls.txt
grep -c "^axiom richAxiom$" tests/fixtures/SampleRich.decls.txt
grep -c "^opaque richOpaque$" tests/fixtures/SampleRich.decls.txt
grep -c "^thm richTheorem$" tests/fixtures/SampleRich.decls.txt
git status --short tests/fixtures/
```

Expected: each grep prints `1`; `Sample.decls.txt` has a handful of lines (`def leanrFixture`, `thm leanrFixtureIsAnswer`, plus compiler-generated auxiliaries — whatever the oracle says is correct by definition); new files show as untracked. If `lean --run` fails, read its error — fix the script, not the format contract. `Sample.olean` should regenerate byte-identically; if it diffs, commit the regenerated bytes (the oracle is deterministic per toolchain).

- [ ] **Step 5: Commit**

```bash
git add mise.toml tests/fixtures/
git commit -m "feat: rich oracle fixture module and golden decls dumps"
```

---

### Task 6: `leanr_olean` — phase B: interpret the raw DAG into kernel types

**Files:**
- Create: `crates/leanr_olean/src/interp.rs`
- Create: `crates/leanr_olean/src/module_data.rs`
- Test: `crates/leanr_olean/tests/module_data.rs`
- Modify: `crates/leanr_olean/src/lib.rs`, `crates/leanr_olean/Cargo.toml`

**Interfaces:**
- Consumes: `raw::{RawValue, parse_bytes}` (Task 4), all `leanr_kernel` types (Tasks 1-3), fixtures (Task 5).
- Produces: `leanr_olean::{ModuleData, Import}` and `ModuleData::parse(bytes: &[u8]) -> Result<ModuleData, OleanError>` — the spec's public entry point, consumed by Task 7's CLI, Task 8's sweep, Task 9's fuzz target, and M1b. Adds `OleanError::BadShape { expected: &'static str }`.

`ModuleData` is:

```rust
pub struct Import {
    pub module: Arc<Name>,
    pub import_all: bool,
    pub is_exported: bool,
    pub is_meta: bool,
}

pub struct ModuleData {
    pub is_module: bool,
    pub imports: Vec<Import>,
    pub const_names: Vec<Arc<Name>>,
    pub constants: Vec<ConstantInfo>,
    pub extra_const_names: Vec<Arc<Name>>,
    /// entries are validated by phase A but not interpreted (spec:
    /// elaborator territory, M4).
    pub num_entries: usize,
}
```

- [ ] **Step 1: Write the failing golden tests**

Create `crates/leanr_olean/tests/module_data.rs`:

```rust
use std::path::PathBuf;
use std::sync::Arc;

use leanr_olean::{ModuleData, OleanError};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

fn parse_fixture(name: &str) -> ModuleData {
    ModuleData::parse(&std::fs::read(fixture(name)).unwrap()).unwrap()
}

fn decls_lines(md: &ModuleData) -> Vec<String> {
    md.constants
        .iter()
        .map(|c| format!("{} {}", c.kind(), c.name()))
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
    let md = parse_fixture("Sample.olean");
    assert_eq!(decls_lines(&md), golden_lines("Sample.decls.txt"));
}

#[test]
fn sample_rich_constants_match_the_oracle_dump() {
    let md = parse_fixture("SampleRich.olean");
    assert_eq!(decls_lines(&md), golden_lines("SampleRich.decls.txt"));
}

#[test]
fn imports_and_metadata_decode() {
    let md = parse_fixture("Sample.olean");
    assert!(
        md.imports.iter().any(|i| i.module.to_string() == "Init"),
        "non-prelude modules implicitly import Init, got {:?}",
        md.imports.iter().map(|i| i.module.to_string()).collect::<Vec<_>>()
    );
    assert_eq!(md.const_names.len(), md.constants.len());
}

/// The spec's sharing guarantee: `constNames` is built by the oracle as
/// `constants.map (·.name)`, so the file shares those Name objects and
/// the decoder must map one file offset to one Arc.
#[test]
fn decoding_preserves_object_sharing() {
    let md = parse_fixture("SampleRich.olean");
    for (n, c) in md.const_names.iter().zip(md.constants.iter()) {
        assert!(Arc::ptr_eq(n, c.name()), "constNames entry not shared with ConstantVal.name");
    }
}

#[test]
fn garbage_still_fails_cleanly() {
    assert!(matches!(
        ModuleData::parse(b"definitely not an olean"),
        Err(OleanError::Truncated(_))
    ));
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test --package leanr_olean --test module_data`
Expected: compilation FAILS (`ModuleData` not defined).

- [ ] **Step 3: Implement the interpreter**

Add to `crates/leanr_olean/Cargo.toml`:

```toml
leanr_kernel = { path = "../leanr_kernel" }
```

Add to `OleanError` in `lib.rs`:

```rust
    /// Phase B found a raw value whose shape does not match the kernel
    /// type expected at that position (bad ctor tag, wrong field
    /// count, scalar where an object belongs, ...).
    #[error("olean module data malformed: expected {expected}")]
    BadShape { expected: &'static str },
```

and register the modules + re-exports:

```rust
mod interp;
mod module_data;
mod raw;

pub use module_data::{Import, ModuleData};
```

Create `crates/leanr_olean/src/interp.rs`:

```rust
//! Phase B: interpret the validated [`RawValue`] DAG into
//! `leanr_kernel` types, following the layout table in the M1a plan
//! (each conversion cites its oracle definition). Phase A already
//! bounds-checked every byte, so this module only checks *shape*.
//!
//! Sharing: per-type memos keyed by raw node address map one file
//! offset to one `Arc`, preserving the file's DAG structure (the
//! oracle max-shares aggressively; naive tree conversion would explode
//! memory). Expr/Level conversion is an explicit-stack post-order walk
//! because term depth is attacker-controlled.

use std::collections::HashMap;
use std::sync::Arc;

use leanr_kernel::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, DataValue,
    DefinitionSafety, DefinitionVal, Expr, InductiveVal, Int, KVMap, Level, Literal, Name, Nat,
    OpaqueVal, QuotKind, QuotVal, RecursorRule, RecursorVal, ReducibilityHints, TheoremVal,
};
use num_bigint::{BigInt, BigUint};

use crate::raw::RawValue;
use crate::OleanError;

type Raw = Arc<RawValue>;

fn key(r: &Raw) -> *const RawValue {
    Arc::as_ptr(r)
}

fn bad(expected: &'static str) -> OleanError {
    OleanError::BadShape { expected }
}

/// Exact-count ctor accessor: `m_other` is the writer's exact pointer
/// field count, so field counts are exact; scalar areas may be padded
/// (layout reference), so those are minimum checks at use sites.
fn ctor<'r>(r: &'r Raw, tag: u8, fields: usize, expected: &'static str)
    -> Result<(&'r [Raw], &'r [u8]), OleanError> {
    match &**r {
        RawValue::Ctor { tag: t, fields: f, scalars } if *t == tag && f.len() == fields => {
            Ok((f, scalars))
        }
        _ => Err(bad(expected)),
    }
}

fn boolean(byte: Option<&u8>, expected: &'static str) -> Result<bool, OleanError> {
    match byte.copied() {
        Some(0) => Ok(false),
        Some(1) => Ok(true),
        _ => Err(bad(expected)),
    }
}

fn nat(r: &Raw) -> Result<Nat, OleanError> {
    match &**r {
        RawValue::Scalar(v) => Ok(Nat::from(*v)),
        RawValue::BigInt(i) => {
            let mag: BigUint = i.clone().try_into().map_err(|_| bad("non-negative Nat"))?;
            Ok(Nat(mag))
        }
        _ => Err(bad("Nat")),
    }
}

fn int(r: &Raw) -> Result<Int, OleanError> {
    match &**r {
        // Boxed Int scalars are 63-bit two's complement (lean.h
        // lean_scalar_to_int): sign-extend from bit 62.
        RawValue::Scalar(v) => Ok(Int(BigInt::from(((v << 1) as i64) >> 1))),
        RawValue::BigInt(i) => Ok(Int(i.clone())),
        _ => Err(bad("Int")),
    }
}

fn string(r: &Raw) -> Result<String, OleanError> {
    match &**r {
        RawValue::Str(s) => Ok(s.clone()),
        _ => Err(bad("String")),
    }
}

/// `List α` → element raw nodes (nil = box(0), cons = tag 1).
fn list(r: &Raw) -> Result<Vec<&Raw>, OleanError> {
    let mut items = Vec::new();
    let mut cur = r;
    loop {
        match &**cur {
            RawValue::Scalar(0) => return Ok(items),
            RawValue::Ctor { tag: 1, fields, .. } if fields.len() == 2 => {
                items.push(&fields[0]);
                cur = &fields[1];
            }
            _ => return Err(bad("List")),
        }
    }
}

fn array(r: &Raw) -> Result<&[Raw], OleanError> {
    match &**r {
        RawValue::Array(elems) => Ok(elems),
        _ => Err(bad("Array")),
    }
}

pub(crate) struct Interp {
    names: HashMap<*const RawValue, Arc<Name>>,
    levels: HashMap<*const RawValue, Arc<Level>>,
    exprs: HashMap<*const RawValue, Arc<Expr>>,
    anonymous: Arc<Name>,
    zero: Arc<Level>,
}

impl Interp {
    pub(crate) fn new() -> Interp {
        Interp {
            names: HashMap::new(),
            levels: HashMap::new(),
            exprs: HashMap::new(),
            anonymous: Arc::new(Name::Anonymous),
            zero: Arc::new(Level::Zero),
        }
    }

    /// Name (Init/Prelude.lean:4693-4717): walk the parent chain down
    /// iteratively, then build back up, memoizing each node.
    fn name(&mut self, r: &Raw) -> Result<Arc<Name>, OleanError> {
        let mut chain: Vec<&Raw> = Vec::new();
        let mut cur = r;
        let mut built = loop {
            if let RawValue::Scalar(0) = &**cur {
                break Arc::clone(&self.anonymous);
            }
            if let Some(n) = self.names.get(&key(cur)) {
                break Arc::clone(n);
            }
            match &**cur {
                RawValue::Ctor { tag: 1 | 2, fields, .. } if fields.len() == 2 => {
                    chain.push(cur);
                    cur = &fields[0];
                }
                _ => return Err(bad("Name")),
            }
        };
        for node in chain.into_iter().rev() {
            let RawValue::Ctor { tag, fields, .. } = &**node else { unreachable!() };
            let name = match tag {
                1 => Name::Str { parent: built, part: string(&fields[1])? },
                2 => Name::Num { parent: built, part: nat(&fields[1])? },
                _ => unreachable!(),
            };
            built = Arc::new(name);
            self.names.insert(key(node), Arc::clone(&built));
        }
        Ok(built)
    }

    fn sub_level(&self, r: &Raw) -> Result<Arc<Level>, OleanError> {
        if let RawValue::Scalar(0) = &**r {
            return Ok(Arc::clone(&self.zero));
        }
        self.levels.get(&key(r)).cloned().ok_or_else(|| bad("Level subterm"))
    }

    /// Level (Level.lean:90-103): explicit-stack post-order.
    fn level(&mut self, root: &Raw) -> Result<Arc<Level>, OleanError> {
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
                        1 => 1,           // succ
                        2 | 3 => 2,       // max, imax
                        4 | 5 => 0,       // param, mvar (Name field)
                        _ => return Err(bad("Level tag")),
                    };
                    let expected_fields = if *tag == 1 { 1 } else if *tag <= 3 { 2 } else { 1 };
                    if fields.len() != expected_fields {
                        return Err(bad("Level fields"));
                    }
                    stack.push(Step::Build(r));
                    for f in &fields[..n_level_children] {
                        stack.push(Step::Visit(f));
                    }
                }
                Step::Build(r) => {
                    let RawValue::Ctor { tag, fields, .. } = &**r else { unreachable!() };
                    let level = match tag {
                        1 => Level::Succ(self.sub_level(&fields[0])?),
                        2 => Level::Max(self.sub_level(&fields[0])?, self.sub_level(&fields[1])?),
                        3 => Level::IMax(self.sub_level(&fields[0])?, self.sub_level(&fields[1])?),
                        4 => Level::Param(self.name(&fields[0])?),
                        5 => Level::MVar(self.name(&fields[0])?),
                        _ => unreachable!(),
                    };
                    self.levels.insert(key(r), Arc::new(level));
                }
            }
        }
        self.sub_level(root)
    }

    fn sub_expr(&self, r: &Raw) -> Result<Arc<Expr>, OleanError> {
        self.exprs.get(&key(r)).cloned().ok_or_else(|| bad("Expr subterm"))
    }

    /// Expr (Expr.lean:321-471): explicit-stack post-order over the
    /// Expr-typed fields; Name/Level/Literal fields convert inline.
    fn expr(&mut self, root: &Raw) -> Result<Arc<Expr>, OleanError> {
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

    fn build_expr(&mut self, r: &Raw) -> Result<Arc<Expr>, OleanError> {
        let RawValue::Ctor { tag, fields, scalars } = &**r else { unreachable!() };
        // Scalar area: computed `data` u64 first (ignored; recomputed
        // in M1b), then u8 flags (kernel/expr.h:265 proves the order).
        let expr = match tag {
            0 => Expr::BVar { idx: nat(&fields[0])? },
            1 => Expr::FVar { id: self.name(&fields[0])? },
            2 => Expr::MVar { id: self.name(&fields[0])? },
            3 => Expr::Sort { level: self.level(&fields[0])? },
            4 => Expr::Const {
                name: self.name(&fields[0])?,
                levels: list(&fields[1])?
                    .into_iter()
                    .map(|l| self.level(l))
                    .collect::<Result<_, _>>()?,
            },
            5 => Expr::App { f: self.sub_expr(&fields[0])?, arg: self.sub_expr(&fields[1])? },
            6 | 7 => {
                let binder_info = match scalars.get(8).copied() {
                    Some(0) => BinderInfo::Default,
                    Some(1) => BinderInfo::Implicit,
                    Some(2) => BinderInfo::StrictImplicit,
                    Some(3) => BinderInfo::InstImplicit,
                    _ => return Err(bad("BinderInfo")),
                };
                let (binder_name, binder_type, body) = (
                    self.name(&fields[0])?,
                    self.sub_expr(&fields[1])?,
                    self.sub_expr(&fields[2])?,
                );
                if *tag == 6 {
                    Expr::Lam { binder_name, binder_type, body, binder_info }
                } else {
                    Expr::ForallE { binder_name, binder_type, body, binder_info }
                }
            }
            8 => Expr::LetE {
                decl_name: self.name(&fields[0])?,
                ty: self.sub_expr(&fields[1])?,
                value: self.sub_expr(&fields[2])?,
                body: self.sub_expr(&fields[3])?,
                non_dep: boolean(scalars.get(8), "letE nondep")?,
            },
            9 => Expr::Lit(self.literal(&fields[0])?),
            10 => Expr::MData { data: self.kvmap(&fields[0])?, expr: self.sub_expr(&fields[1])? },
            11 => Expr::Proj {
                type_name: self.name(&fields[0])?,
                idx: nat(&fields[1])?,
                structure: self.sub_expr(&fields[2])?,
            },
            _ => unreachable!("tag checked in Visit"),
        };
        Ok(Arc::new(expr))
    }

    fn literal(&mut self, r: &Raw) -> Result<Literal, OleanError> {
        match &**r {
            RawValue::Ctor { tag: 0, fields, .. } if fields.len() == 1 => {
                Ok(Literal::NatVal(nat(&fields[0])?))
            }
            RawValue::Ctor { tag: 1, fields, .. } if fields.len() == 1 => {
                Ok(Literal::StrVal(string(&fields[0])?))
            }
            _ => Err(bad("Literal")),
        }
    }

    /// KVMap ≅ List (Name × DataValue) (Data/KVMap.lean:71-73).
    fn kvmap(&mut self, r: &Raw) -> Result<KVMap, OleanError> {
        let mut entries = Vec::new();
        for pair in list(r)? {
            let (fields, _) = ctor(pair, 0, 2, "Prod")?;
            entries.push((self.name(&fields[0])?, self.data_value(&fields[1])?));
        }
        Ok(KVMap(entries))
    }

    /// DataValue (Data/KVMap.lean:18-25).
    fn data_value(&mut self, r: &Raw) -> Result<DataValue, OleanError> {
        match &**r {
            RawValue::Ctor { tag: 0, fields, .. } if fields.len() == 1 => {
                Ok(DataValue::OfString(string(&fields[0])?))
            }
            RawValue::Ctor { tag: 1, fields, scalars } if fields.is_empty() => {
                Ok(DataValue::OfBool(boolean(scalars.first(), "DataValue bool")?))
            }
            RawValue::Ctor { tag: 2, fields, .. } if fields.len() == 1 => {
                Ok(DataValue::OfName(self.name(&fields[0])?))
            }
            RawValue::Ctor { tag: 3, fields, .. } if fields.len() == 1 => {
                Ok(DataValue::OfNat(nat(&fields[0])?))
            }
            RawValue::Ctor { tag: 4, fields, .. } if fields.len() == 1 => {
                Ok(DataValue::OfInt(int(&fields[0])?))
            }
            RawValue::Ctor { tag: 5, .. } => {
                // Syntax values drag in the whole Syntax type family;
                // the stdlib sweep decides if real kernel terms ever
                // carry them (spec: deferred).
                Err(OleanError::Unsupported { what: "Syntax in expression metadata" })
            }
            _ => Err(bad("DataValue")),
        }
    }

    fn names(&mut self, items: Vec<&Raw>) -> Result<Vec<Arc<Name>>, OleanError> {
        items.into_iter().map(|n| self.name(n)).collect()
    }

    /// ConstantVal (Declaration.lean:95-99).
    fn constant_val(&mut self, r: &Raw) -> Result<ConstantVal, OleanError> {
        let (fields, _) = ctor(r, 0, 3, "ConstantVal")?;
        Ok(ConstantVal {
            name: self.name(&fields[0])?,
            level_params: self.names(list(&fields[1])?)?,
            ty: self.expr(&fields[2])?,
        })
    }

    /// ReducibilityHints (Declaration.lean:46-50).
    fn reducibility(&mut self, r: &Raw) -> Result<ReducibilityHints, OleanError> {
        match &**r {
            RawValue::Scalar(0) => Ok(ReducibilityHints::Opaque),
            RawValue::Scalar(1) => Ok(ReducibilityHints::Abbrev),
            RawValue::Ctor { tag: 2, fields, scalars } if fields.is_empty() => {
                let bytes = scalars.get(..4).ok_or_else(|| bad("regular height"))?;
                Ok(ReducibilityHints::Regular(u32::from_le_bytes(
                    bytes.try_into().expect("4 bytes"),
                )))
            }
            _ => Err(bad("ReducibilityHints")),
        }
    }

    /// ConstantInfo (Declaration.lean:429-437) and its Val payloads.
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
                    hints: self.reducibility(&f[2])?,
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
                    induct: self.name(&f[1])?,
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
                        ctor: self.name(&rf[0])?,
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

    /// Import (Setup.lean:25-32).
    fn import(&mut self, r: &Raw) -> Result<crate::Import, OleanError> {
        let (f, s) = ctor(r, 0, 1, "Import")?;
        Ok(crate::Import {
            module: self.name(&f[0])?,
            import_all: boolean(s.first(), "Import.importAll")?,
            is_exported: boolean(s.get(1), "Import.isExported")?,
            is_meta: boolean(s.get(2), "Import.isMeta")?,
        })
    }

    /// ModuleData (Environment.lean:109-129).
    pub(crate) fn module_data(&mut self, root: &Raw) -> Result<crate::ModuleData, OleanError> {
        let (f, s) = ctor(root, 0, 5, "ModuleData")?;
        Ok(crate::ModuleData {
            is_module: boolean(s.first(), "ModuleData.isModule")?,
            imports: array(&f[0])?
                .iter()
                .map(|i| self.import(i))
                .collect::<Result<_, _>>()?,
            const_names: array(&f[1])?
                .iter()
                .map(|n| self.name(n))
                .collect::<Result<_, _>>()?,
            constants: array(&f[2])?
                .iter()
                .map(|c| self.constant_info(c))
                .collect::<Result<_, _>>()?,
            extra_const_names: array(&f[3])?
                .iter()
                .map(|n| self.name(n))
                .collect::<Result<_, _>>()?,
            num_entries: array(&f[4])?.len(),
        })
    }
}
```

Create `crates/leanr_olean/src/module_data.rs`:

```rust
//! The decoded contents of one `.olean` module (oracle:
//! src/Lean/Environment.lean:109-129).

use std::sync::Arc;

use leanr_kernel::{ConstantInfo, Name};

use crate::{interp::Interp, raw, OleanError};

/// oracle: src/Lean/Setup.lean:25-32
#[derive(Debug, Clone)]
pub struct Import {
    pub module: Arc<Name>,
    pub import_all: bool,
    pub is_exported: bool,
    pub is_meta: bool,
}

#[derive(Debug)]
pub struct ModuleData {
    pub is_module: bool,
    pub imports: Vec<Import>,
    pub const_names: Vec<Arc<Name>>,
    pub constants: Vec<ConstantInfo>,
    pub extra_const_names: Vec<Arc<Name>>,
    /// Environment-extension entries are validated by phase A but kept
    /// opaque (spec: interpreted by the elaborator in M4).
    pub num_entries: usize,
}

impl ModuleData {
    /// Decode a whole `.olean` file. `bytes` is untrusted input; every
    /// failure mode is an `OleanError`, never a panic (see
    /// docs/THREAT_MODEL.md and the raw-module docs).
    pub fn parse(bytes: &[u8]) -> Result<ModuleData, OleanError> {
        let root = raw::parse_bytes(bytes)?;
        Interp::new().module_data(&root)
    }
}
```

- [ ] **Step 4: Run the golden tests**

Run: `cargo test --package leanr_olean`
Expected: all tests PASS. The two `*_match_the_oracle_dump` tests are the milestone gate: a mismatch means a layout constant or kind string is wrong — diff the two line lists, find the first divergence, re-read the cited oracle definition, fix the decoder or `kind()`/`Display`. Never edit the fixture.

- [ ] **Step 5: Lint, full gate, commit**

```bash
mise run ci
git add crates/leanr_olean/ Cargo.toml Cargo.lock
git commit -m "feat: decode full ModuleData into kernel types, golden-tested against the oracle"
```

---

### Task 7: `leanr olean decls` CLI subcommand

**Files:**
- Modify: `crates/leanr_cli/src/main.rs`
- Test: `crates/leanr_cli/tests/cli.rs` (extend)

**Interfaces:**
- Consumes: `leanr_olean::ModuleData::parse` (Task 6), fixtures (Task 5).
- Produces: `leanr olean decls <path>` — the M1a demo deliverable. Output format is exactly the golden decls format (one `<kind> <name>` line per constant, module order).

- [ ] **Step 1: Write the failing tests**

Append to `crates/leanr_cli/tests/cli.rs`:

```rust
#[test]
fn olean_decls_matches_the_oracle_dump() {
    let expected = std::fs::read_to_string(fixture("SampleRich.decls.txt")).unwrap();
    Command::cargo_bin("leanr")
        .unwrap()
        .args(["olean", "decls"])
        .arg(fixture("SampleRich.olean"))
        .assert()
        .success()
        .stdout(expected);
}

#[test]
fn olean_decls_on_garbage_fails_without_panicking() {
    let dir = std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR"));
    let garbage = dir.join("garbage-decls.olean");
    std::fs::write(&garbage, b"definitely not an olean").unwrap();

    Command::cargo_bin("leanr")
        .unwrap()
        .args(["olean", "decls"])
        .arg(&garbage)
        .assert()
        .failure()
        .stderr(predicates::str::contains("not an olean file"));
}

#[test]
fn olean_decls_on_missing_file_names_the_file() {
    Command::cargo_bin("leanr")
        .unwrap()
        .args(["olean", "decls", "does-not-exist.olean"])
        .assert()
        .failure()
        .stderr(predicates::str::contains("does-not-exist.olean"));
}
```

(Reuse the existing `fixture` helper and imports already present in `cli.rs` from M0.)

- [ ] **Step 2: Run tests to verify the new ones fail**

Run: `cargo test --package leanr_cli`
Expected: the three new tests FAIL (unknown subcommand `decls`); M0's tests still pass.

- [ ] **Step 3: Implement the subcommand**

In `crates/leanr_cli/src/main.rs`, extend `OleanCommand` and dispatch (CLI stays logic-free — read, call the library, print):

```rust
#[derive(Subcommand)]
enum OleanCommand {
    /// Print the header of an .olean file.
    Info { path: PathBuf },
    /// List the declarations stored in an .olean file.
    Decls { path: PathBuf },
}
```

```rust
        Command::Olean {
            command: OleanCommand::Decls { path },
        } => olean_decls(&path),
```

```rust
fn olean_decls(path: &std::path::Path) -> ExitCode {
    let bytes = match std::fs::read(path) {
        Ok(bytes) => bytes,
        Err(err) => {
            eprintln!("error: cannot read {}: {err}", path.display());
            return ExitCode::FAILURE;
        }
    };
    match leanr_olean::ModuleData::parse(&bytes) {
        Ok(module) => {
            // Same line format as the oracle-side dump script
            // (tests/fixtures/dump_decls.lean) — golden-compared in CI.
            let mut out = String::new();
            for c in &module.constants {
                out.push_str(&format!("{} {}\n", c.kind(), c.name()));
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

- [ ] **Step 4: Run the full gate**

```bash
mise run ci
```

Expected: everything green. Also eyeball the demo:

```bash
cargo run -p leanr_cli -- olean decls tests/fixtures/SampleRich.olean | head
```

Expected: `axiom richAxiom`, `induct RichTree`, ... — the module's contents.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_cli/
git commit -m "feat: leanr olean decls subcommand - M1a demo deliverable"
```

---

### Task 8: Stdlib sweep — decode every toolchain `.olean`

**Files:**
- Test: `crates/leanr_olean/tests/stdlib_sweep.rs`
- Modify: `mise.toml` (`sweep:stdlib` task)

**Interfaces:**
- Consumes: `ModuleData::parse` (Task 6), the elan-installed pinned toolchain.
- Produces: `mise run sweep:stdlib` — the contributor-side completeness gate (CI stays hermetic; it has no Lean toolchain by design). M1b reuses this harness for kernel-checking sweeps.

- [ ] **Step 1: Write the sweep test**

Create `crates/leanr_olean/tests/stdlib_sweep.rs`:

```rust
//! Decodes every base `.olean` shipped with the pinned toolchain
//! (~2,400 modules — all of Init/Std/Lean). Ignored by default: it
//! needs the oracle toolchain on disk, which CI does not have. Run via
//! `mise run sweep:stdlib`.

use std::path::{Path, PathBuf};

use leanr_olean::ModuleData;

fn collect_oleans(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_oleans(&path, out);
        } else if path.extension().is_some_and(|e| e == "olean") {
            // `Foo.olean.server`/`.olean.private` have extension
            // "server"/"private", so this filter keeps base parts only
            // (multi-part modules share a compactor; only the base
            // part is self-contained — see the plan's layout notes).
            out.push(path);
        }
    }
}

#[test]
#[ignore = "needs the pinned Lean toolchain; run via `mise run sweep:stdlib`"]
fn every_stdlib_olean_decodes() {
    let dir = std::env::var("LEANR_SWEEP_DIR")
        .expect("LEANR_SWEEP_DIR must point at the toolchain lib/lean dir");
    let mut files = Vec::new();
    collect_oleans(Path::new(&dir), &mut files);
    files.sort();
    assert!(
        files.len() > 1000,
        "suspiciously few .olean files ({}) under {dir} — wrong directory?",
        files.len()
    );

    let mut failures = Vec::new();
    let mut constants = 0usize;
    for path in &files {
        let bytes = std::fs::read(path).unwrap();
        match ModuleData::parse(&bytes) {
            Ok(md) => constants += md.constants.len(),
            Err(err) => failures.push(format!("{}: {err}", path.display())),
        }
    }
    println!(
        "swept {} modules, {} constants, {} failures",
        files.len(),
        constants,
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "decoder incomplete for {} of {} modules:\n{}",
        failures.len(),
        files.len(),
        failures.join("\n")
    );
}
```

- [ ] **Step 2: Add the mise task**

Append to `mise.toml`:

```toml
[tasks."sweep:stdlib"]
description = "Decode every .olean shipped with the pinned toolchain (local; CI has no Lean)"
depends = ["elan:bootstrap"]
run = "sh -c 'LEANR_SWEEP_DIR=\"$(lean --print-libdir)\" cargo test --release --package leanr_olean --test stdlib_sweep -- --ignored --nocapture'"
```

(`lean --print-libdir` prints `<prefix>/lib/lean`, where the stdlib `.olean`s live — verified against the pinned toolchain. `--release` because debug-mode decoding of ~hundreds of MB is needlessly slow.)

- [ ] **Step 3: Run the sweep**

```bash
mise run sweep:stdlib
```

Expected: `swept ~2400 modules, <millions> constants, 0 failures` and a green test. This is the decoder's first contact with the full breadth of real data; failures here are the *point* of the task. Triage protocol for any failure:

1. The error names the check (`BadTag`, `BadShape { expected }`, `Unsupported { what }`) and the file.
2. Re-read the cited oracle definition **at the pinned tag** for the type involved; a failure usually means a layout detail this plan missed (e.g. a `DataValue.ofSyntax` in real metadata, or a thunk where none was expected).
3. Extend the decoder to handle what the oracle actually writes (new `RawValue` handling or interp case, with the oracle citation), add a regression unit test if the shape is constructible with the `Builder`, and re-run the sweep. If the fix requires representing `Syntax` in `leanr_kernel`, STOP and flag it — that is a scope decision for the human.
4. Never "fix" a failure by skipping files or downgrading an error to a default value.

Then run the spec's demo deliverable on a real core module and eyeball it:

```bash
export PATH="$HOME/.elan/bin:$PATH"
cargo run --release -p leanr_cli -- olean decls "$(lean --print-libdir)/Init/Prelude.olean" | head -20
cargo run --release -p leanr_cli -- olean decls "$(lean --print-libdir)/Init/Prelude.olean" | wc -l
```

Expected: real core declarations (`induct Bool`, `ctor Bool.true`, `quot Quot`, ...) and a count in the thousands — `Init.Prelude` is where `quotInfo` constants live, so all eight kinds have now decoded from oracle-produced bytes.

- [ ] **Step 4: Commit**

```bash
mise run lint
git add crates/leanr_olean/tests/stdlib_sweep.rs mise.toml
git commit -m "test: stdlib sweep - decode all ~2400 toolchain oleans with zero errors"
```

---

### Task 9: Fuzz target, docs, and the M1a gate

**Files:**
- Create: `crates/leanr_olean/fuzz/Cargo.toml`, `crates/leanr_olean/fuzz/fuzz_targets/module_data.rs` (via `cargo fuzz init`)
- Modify: `Cargo.toml` (workspace `exclude`), `mise.toml` (nightly rust + cargo-fuzz + `fuzz` task), `.gitignore` (fuzz artifacts), `ARCHITECTURE.md`

**Interfaces:**
- Consumes: `ModuleData::parse` (Task 6), fixtures as seed corpus.
- Produces: `mise run fuzz` (local, best-effort continuous validation of the never-panic guarantee — fuzzing was deferred from M0 to exactly this parser); updated codebase map.

- [ ] **Step 1: Pin the fuzz toolchain**

cargo-fuzz needs a nightly rustc (sanitizer flags). Pin both via mise:

```bash
mise use --pin "cargo:cargo-fuzz"
mise use --pin rust@nightly-2026-07-01
mise install
mise exec rust@nightly-2026-07-01 -- cargo --version
cargo fuzz --version
```

Expected: exact-pinned entries in `mise.toml` and both versions print. If mise's rust backend rejects a second channel-pinned version, fall back to `rustup toolchain install nightly-2026-07-01` and invoke `cargo +nightly-2026-07-01` in the task below instead — record whichever form worked in the task's `description`.

- [ ] **Step 2: Create the fuzz target**

```bash
cd crates/leanr_olean && cargo fuzz init && cargo fuzz add module_data && cd ../..
rm crates/leanr_olean/fuzz/fuzz_targets/fuzz_target_1.rs
```

Remove the generated `fuzz_target_1` entry from `crates/leanr_olean/fuzz/Cargo.toml` (keep only the `module_data` `[[bin]]` section).

Replace `crates/leanr_olean/fuzz/fuzz_targets/module_data.rs` with:

```rust
#![no_main]

use libfuzzer_sys::fuzz_target;

// The never-panic guarantee (docs/THREAT_MODEL.md): any byte input
// must produce Ok or a structured OleanError — no panic, no abort, no
// hang, no unbounded allocation.
fuzz_target!(|data: &[u8]| {
    let _ = leanr_olean::ModuleData::parse(data);
});
```

Exclude the fuzz crate from the workspace (it is nightly-only and must not break `mise run test`): in the root `Cargo.toml` add

```toml
[workspace]
resolver = "2"
members = ["crates/leanr_cli", "crates/leanr_query", "crates/leanr_olean", "crates/leanr_kernel"]
exclude = ["crates/leanr_olean/fuzz"]
```

(keep the existing members list; just add `exclude`). Seed the corpus with real files:

```bash
mkdir -p crates/leanr_olean/fuzz/corpus/module_data
cp tests/fixtures/Sample.olean tests/fixtures/SampleRich.olean crates/leanr_olean/fuzz/corpus/module_data/
```

Append to `.gitignore`:

```
crates/leanr_olean/fuzz/artifacts/
crates/leanr_olean/fuzz/target/
crates/leanr_olean/fuzz/Cargo.lock
```

Add the task to `mise.toml`:

```toml
[tasks.fuzz]
description = "Fuzz the olean decoder (local; needs the pinned nightly)"
dir = "crates/leanr_olean"
run = "mise exec rust@nightly-2026-07-01 -- cargo fuzz run module_data -- -max_total_time=60"
```

- [ ] **Step 3: Run the fuzzer**

```bash
mise run fuzz
```

Expected: 60 seconds of fuzzing, `Done`, no crashes. A crash artifact means the never-panic guarantee is broken: minimize (`cargo fuzz tmin module_data <artifact>`), turn the input into a `Builder`-based regression unit test in `raw.rs`, fix, re-run. Do not commit crash artifacts.

- [ ] **Step 4: Update the codebase map**

In `ARCHITECTURE.md`, update the crate list: add `leanr_kernel` before `leanr_query`:

```markdown
- `crates/leanr_kernel` — the trusted computing base: kernel data
  types (`Name`, `Level`, `Expr`, `ConstantInfo`, `Environment`).
  Depends on nothing in the workspace; nothing reaches into it. Data
  only until M1b adds the checker. Values can originate from untrusted
  bytes, so all traversals (including `Drop`) are iterative.
```

and extend the `leanr_olean` bullet:

```markdown
- `crates/leanr_olean` — reader for official Lean `.olean` artifacts.
  Trust boundary: input bytes are untrusted (`docs/THREAT_MODEL.md`).
  Two phases: `raw` walks the compacted region into a validated,
  offset-memoized DAG (the entire untrusted-bytes surface, fuzzed via
  `mise run fuzz`); `interp` shapes it into `leanr_kernel` types.
  Golden-tested against the oracle (`mise run fixtures:regen`) and
  swept over the full toolchain stdlib (`mise run sweep:stdlib`).
```

- [ ] **Step 5: Full gate, push, verify CI**

```bash
mise run ci
git add Cargo.toml mise.toml .gitignore ARCHITECTURE.md crates/leanr_olean/fuzz/
git commit -m "feat: cargo-fuzz target for the olean decoder + codebase map update"
git push origin main
gh run watch --exit-status
```

Expected: CI green on main. **M1a exit criteria met:** kernel data model in a TCB crate, full olean decode with golden parity against the oracle, sharing preserved, never-panic surface fuzzed, all ~2,400 stdlib modules decoding cleanly, and `leanr olean decls tests/fixtures/SampleRich.olean` demoing it.

---

## What this plan deliberately defers

- **M1b (next plan):** the type checker (defeq, whnf, inductive checking), import-closure resolution and search paths, `Expr` metadata caches (hash, flags) and hash-consing, `Environment` used in anger.
- **M1 final slice:** parallel checking over all of Mathlib; Mathlib-scale sweep (needs `lake exe cache` download infra that M2 builds properly).
- `Syntax` values in expression metadata — only if the stdlib sweep proves real modules need it (Task 8 triage protocol).
- Env-extension interpretation (M4, elaborator), `.olean.server`/`.olean.private` multi-part decoding (needs cross-region pointer support — not needed for kernel checking).
- Zero-copy loading — only if profiling ever shows load time matters (spec records the API seam).
