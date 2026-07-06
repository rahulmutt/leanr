# Compact `Expr`: index-based term bank — design spec

**Date:** 2026-07-06
**Status:** approved (brainstorming), pending implementation plan
**Milestone:** M1b follow-up (memory, phase 2). Supersedes the residual goals of
the 2026-07-06 hash-consing spec; builds on its measurements and on the two
bug fixes below.

## Problem

`leanr check --all` (2433 stdlib modules) cannot complete inside the 32 GiB
pod limit. The 2026-07-06 investigation decomposed the blowup into three
mechanisms:

1. **Uncached substitution walkers** (`instantiate_go`, `abstract_go`,
   `lift_go`, `lparams_go`) did tree-sized work on DAG-shared terms — the
   oracle memoizes these traversals by (pointer, offset) in `replace_fn.cpp`
   (`replace_rec_fn`, :27-30). **Fixed** in `6fce3c6` (verdict-preserving,
   full suite green).
2. **Missing `m_unfold` memo** — repeated unfolds of one universe-polymorphic
   `Const` each built a fresh copy of the definition's value, defeating every
   downstream pointer-keyed cache. **Fixed** in `937c5fc` (oracle:
   type_checker.cpp:505-511).
3. **No structural identity for kernel-built terms.** Kernel-reducing a
   `grind` reflection certificate (measured on
   `_private.Init.Data.Char.Ordinal.0.Char.ofOrdinal._proof_3`; the killed
   full-sweep run died on the sibling `ofOrdinal_ordinal._proof_1_5`) executes
   ~10⁶+ recursor steps (`Int.rec`/`List.rec`/`Nat.rec`/`Option.rec` over
   `Int.negOfNat/add/mul/…` unfolds), allocating hundreds of millions of
   fresh nodes. Structurally-equal terms built at different moments are
   distinct pointers, so the per-declaration caches neither deduplicate nor
   hit: measured live-node counter showed **54M live `Expr` nodes (~5 GiB)
   at only 40M whnf_core calls and still climbing linearly** — pinned by
   `whnf_cache` (~812k entries) and the equiv-manager UnionFind (**3.25M
   `ExprPtr` entries**), each entry keeping whole fresh trees alive until the
   declaration finishes. One declaration transiently exceeds 25 GiB.
   **Open — this spec.**

Post-fix baseline: environment steady state ~10.8 GiB (structurally interned
`Arc<Expr>` graph at ~72-80 B/node plus ~60 B/node of interner tables);
single pathological declarations add 15-20+ GiB transient. Target
(user-set): **≤ 6 GiB peak for the full sweep — oracle-class** — with
Mathlib-scale headroom in mind.

## Goal

Replace the `Arc<Expr>` representation with a compact, index-based,
intern-at-construction term bank so that:

- structural equality is integer equality (`ExprId ==`), making every
  type-checker cache structural;
- a distinct term costs ~21 bytes + ~8 bytes of dedup table (vs ~140 today);
- per-declaration transients are deduplicated as they are built and freed
  wholesale when the declaration completes;
- `check --all` completes with peak ≤ 6 GiB, **without changing any
  accept/reject verdict**.

## Non-goals

- Oracle-identical memory layout, hash values, or `Expr` object identity.
- Garbage collection inside a region (regions grow monotonically and drop
  wholesale; bounded by input size).
- Changing kernel *algorithms* (`is_def_eq`, whnf, inductive admission
  logic) — only the term representation and the operations on it.
- New external dependencies (`leanr_kernel` stays dependency-free; the probe
  table is hand-rolled safe code).
- Parallelism, persistence of banks across runs, or olean format changes.

## §1 Core representation

**Identity.** `ExprId(NonZeroU32)`; `Option<ExprId>` is free. Top bit =
region (persistent/scratch), leaving 2³¹ ids per region (stdlib ≈ 10⁸
distinct nodes). Id exhaustion is a `KernelError` (never a panic); ids are
only minted per distinct interned node, so allocation is bounded by input
size.

**Storage: `TermBank`, struct-of-arrays** (no padding, no Arc headers):

| array | type | content |
|---|---|---|
| `tag` | `Vec<u8>` | variant (4 bits) + `BinderInfo` (2 bits) + `non_dep` |
| `a, b, c` | `Vec<u32>` | variant-dependent fields (below) |
| `data` | `Vec<u64>` | the existing packed `ExprData` word, semantics unchanged |

21 bytes/node. Field assignment per variant:

- `App { a = f, b = arg }`
- `Lam`/`ForallE` `{ a = binder_type, b = body, c = binder NameId }`
  (binder info in tag)
- `LetE { a = ty, b = value, c = spill id }` → spill pool of
  `(decl NameId, body ExprId)` pairs, itself deduplicated (required so the
  row remains a complete structural key); `non_dep` in tag
- `Const { a = NameId, b = LevelsListId }`
- `BVar { a = index }` for indices < 2³²; a separate `BVarBig` tag whose
  `a` indexes the bignum pool (larger indices are attacker-constructible)
- `Sort { a = LevelId }`, `FVar`/`MVar { a = NameId }`
- `Lit`: `LitNat { a = NatPoolId }` / `LitStr { a = StrPoolId }`
- `MData { a = KVMapPoolId, b = child }`
- `Proj { a = type NameId, b = idx, c = structure }` for idx < 2³²; a
  `ProjBig` tag variant pools the index, mirroring `BVar`/`BVarBig`

**Side pools**, each interned/deduplicated the same way: `NameId` bank
(parent NameId + string-pool part; replaces `Arc<Name>`), `LevelId` bank
(5 variants), a level-*list* pool for `Const` (deduped vectors), a `Nat`
bignum pool (deduped by value), a string pool, a `KVMap` pool.

**Dedup at construction.** Every constructor interns: children are already
canonical ids, so the packed row (tag + a/b/c + any pool ids) is a complete
shallow structural key. Hash it (the `data` hash word) and probe a
hand-rolled open-addressing table of `u32` ids that rehashes candidate rows
directly from the bank (~8 B/node; no key duplication; safe code; unit- and
property-tested). Equal row ⇒ same id, hence:

> **Interning invariant:** `id_1 == id_2` ⇔ the terms are structurally
> equal (including binder names, `BinderInfo`, `non_dep`, `KVMap` — exactly
> today's `structural_eq` relation).

## §2 Regions and lifecycle

- **Persistent bank** — owned by `Environment`, alongside its pools and the
  constants map. The olean decoder writes into it directly (§4). Grows
  monotonically; never freed mid-run; bounded by input size. Replaces both
  today's decoded-`Arc` graph and the `Interner` (intern.rs), whose tables
  it obsoletes.
- **Scratch bank** — owned by each per-declaration `TypeChecker`. All
  whnf/instantiate/infer transients intern here. Scratch interning consults
  the persistent table first, so a term structurally equal to an env term
  receives the persistent id; scratch nodes may reference persistent ids,
  never the reverse. On declaration completion the scratch bank, its table,
  and all id-keyed caches drop wholesale — transient cost is bounded by
  *distinct* transient terms and then mass-freed.
- **Promotion.** Kernel-generated data that outlives the declaration
  (inductive types', constructors', recursors' `ConstantInfo`s incl.
  `RecursorRule.rhs`) is re-interned scratch→persistent by an id-translating
  walk at `Environment::add_core` — the single choke point every admission
  already passes through (established in hash-consing Task 5).

## §3 Kernel API migration

- `Expr` becomes `ExprId`. Reads go through a `Terms` view holding
  `&TermBank` (persistent) plus the checker's scratch; the region bit routes.
  `terms.node(id)` returns a `Copy` view enum mirroring today's `ExprNode`
  with id fields, so pattern-matching code ports mechanically.
- Construction: fallible intern-constructors on the writable region
  (checker → scratch; decoder/admission → persistent). Smart-constructor
  `ExprData` computation is unchanged.
- `Drop for Expr`, the iterative drop stack, and `ExprPtr` disappear.
  `RecGuard` stays for all recursion over untrusted-depth terms.
- Caches: `infer_cache`, `whnf_cache`, `whnf_core_cache`, `failure_cache`,
  `unfold_memo` become id-keyed maps; the equiv-manager UnionFind holds
  `u32`s. All become structural for free (by the interning invariant).
- `Name`/`Level` migrate to `NameId`/`LevelId` throughout (`LocalContext`,
  FVar ids, `ConstantInfo` level params, quotient/inductive machinery).
- `ConstantInfo` holds `ExprId`s; `Environment` owns bank + pools; public
  kernel API changes accordingly (`leanr_olean` and the CLI adapt).

## §4 Decoder and replay boundary

- `leanr_olean` decodes straight into the persistent bank via the
  intern-constructors; its per-module memo maps olean offsets → `ExprId`.
  Decoding *is* interning: the decode → batch-canonicalize → pre-intern
  pipeline (hash-consing Tasks 3-5, B/Fix1) collapses into one pass and its
  transient double-representation disappears.
- Replay operates on id-based `ConstantInfo`s; the replay pre-intern pass is
  deleted. The postponed constructor/recursor structural checks
  (`constant_info_eq`) reduce to id comparisons — same relation as today's
  `structural_eq` by the interning invariant.

## §5 Soundness and TCB discipline

- **Verdict preservation.** Kernel algorithm logic is untouched; only
  representation operations swap. The one load-bearing lemma is the
  interning invariant (§1), enforced by construction: rows are compared
  exactly (tag + scalar fields + child ids) and children are interned
  bottom-up. `structural_eq` ⇒ id equality replaces today's fast path;
  caches remain sound because id identity now *implies* structural identity
  (strictly stronger than the pointer-identity assumption they made before).
- **Untrusted input.** Ids are minted only by interning, so stored ids are
  valid by construction; accessors bounds-check and return errors, never
  panic. Bignum `Nat` handling (`BVarBig`, pool) keeps the exact-arithmetic
  discipline. Recursion over attacker-shaped terms stays `RecGuard`-guarded.
  No `unsafe` code anywhere, including the probe table.
- The bank lives in `leanr_kernel` (replacing `expr.rs` internals and
  `intern.rs`); the crate remains free of workspace/external deps.

## §6 Testing

- **Unit:** probe table (collision clusters, growth, u32-exhaustion error);
  pool dedup; region-bit routing; promotion walk preserves structure;
  idempotence (interning a canonical row returns the same id).
- **Property (in-crate, deterministic generators):** for randomly generated
  terms, (a) bank round-trip is structurally identical to a shadow reference
  tree; (b) `id equality ⇔ reference structural_eq` — the interning
  invariant, tested not assumed.
- **Ports:** the entire existing kernel test suite migrates with the API;
  `tests/check_fixtures.rs` (real replay + hermetic mutation-differential
  verdicts) is the hard verdict gate and must stay green unmodified in
  spirit.
- **Acceptance (controller-run, watchdog):**
  1. `leanr check Init.Data.Char.Ordinal` — the standing canary; must exit 0
     quickly in bounded memory (was: >25 GiB kill on one declaration).
  2. Full `check --all` sweep — exit 0, `checked 2433 modules, …`, peak
     **≤ 6 GiB** (record peak + wall-clock + declaration count).

## §7 Sequencing (for writing-plans)

Bottom-up, tests ported with each stage: (1) bank + pools + probe table,
standalone with property tests; (2) `Name`/`Level` banks; (3) `Expr` bank +
`expr.rs` API + `subst.rs`; (4) `tc.rs`; (5) `inductive`/`quot`/`env`/
`replay`; (6) decoder; (7) CLI + acceptance. Wall-clock is expected to
improve (structural cache hits, no refcounts, dense layout); any regression
is acceptable only if the sweep completes within the pod limit — memory is
the blocker.

## Constraints (inherited)

- `leanr_kernel` depends on no workspace crate; no new external deps.
- `.olean`-derived values untrusted: no panic, no unguarded recursion,
  allocation bounded by input size; checked/exact arithmetic.
- Oracle discipline: representation changes cite the invariants they
  preserve (`ExprData`, `structural_eq` in expr.rs); algorithmic behavior
  continues to cite oracle source lines.
- Lint gate (`mise run lint`) per commit; full gate (`mise run ci`) where a
  task says so; conventional-commit prefixes.
