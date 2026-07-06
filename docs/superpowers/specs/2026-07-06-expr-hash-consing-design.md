# Expr hash-consing (structural interning) — design spec

**Date:** 2026-07-06
**Status:** approved (brainstorming), pending implementation plan
**Milestone:** M1b follow-up (memory). Prerequisite finding from M1b Task 16 Step 4.

## Problem

`leanr check --all` kernel-checks the entire pinned toolchain (~2433 `.olean`
modules) into a single `Environment`. Measured peak resident memory is **≥31
GiB** — a ~26 GiB steady-state plateau (the whole-stdlib env) plus a terminal
+4–5 GiB spike as the last, largest compiler modules and their recursors are
admitted. This exceeds the 32 GiB pod limit; exceeding it OOM-kills the whole
pod (k8s `OOMKilled`), taking the session with it.

Diagnosis (M1b Task 16, instrumented sweep): the spike is genuine `env` growth
in the main replay loop, **not** the end-of-run postponed constructor/recursor
structural checks (the phase marker never printed — the process died mid-main-
loop). So the footprint is the environment itself, in the current `Expr`
representation.

Root cause: **no structural sharing.** Each decoded expression is a fresh
`Arc<Expr>` tree. Every occurrence of common subterms — `Nat`, `Prop`,
`Type`, `Eq`, ubiquitous instance arguments, shared signatures — is a separate
allocation, duplicated across 2433 modules. The oracle's C++ kernel checks the
same stdlib in a few GB because Lean's `Expr` is maximally shared (hash-consed);
we are ~5–10× heavier for lack of that sharing.

## Goal

Cut the whole-stdlib check footprint enough to complete `check --all` with
comfortable margin under 32 GiB (target: well under, ideally ~8–14 GiB peak),
**without changing any accept/reject verdict** and without introducing global
mutable state into the trusted computing base (TCB).

## Non-goals

- Oracle-identical memory layout or `Expr` identity semantics.
- Persistent/interned-forever expression identity, or an `Expr` newtype that
  guarantees global uniqueness. We want *sharing*, not a uniqueness invariant.
- Interning the kernel's transient working-set exprs (whnf/instantiate/defeq).
  Those are short-lived and freed already; interning them would add hot-path
  cost for no retained benefit.
- Changing the decoder's per-module memoization or the olean format.
- Reducing wall-clock. A modest one-time canonicalization cost is acceptable;
  memory is the blocker, not speed.

## Approach: one-shot batch canonicalization before replay

Interning is realized as a **single batch pass**, not a persistent structure.

1. In the CLI `check` path, after the decoded constants map is built and
   **before** `replay`, run a canonicalization pass over every decoded
   `ConstantInfo`'s expressions (types and values).
2. The pass uses a **transient** `HashMap<NodeKey, Arc<Expr>>` of canonical
   nodes (plain **strong** refs — the map is local and dropped at the end of
   the pass). Bottom-up, each subterm is replaced by the map's canonical `Arc`
   (inserted on first sight). Structurally-identical subterms across all
   modules collapse to one shared `Arc`.
3. When the pass returns, the map is **dropped**. The dedup is now baked into
   the `Arc` graph itself: shared children *are* shared pointers. The `env`,
   built during replay from these canonicalized constants, inherits all the
   sharing. Duplicate allocations are freed as canonicalization replaces them.

Because the interner is transient, there is **no global state, no `Weak`
bookkeeping, and no hot-path cost** — the three things that make general
hash-consing painful are all avoided.

### The canonical-node key (shallow, exact)

Canonicalization is bottom-up, so a node's children are *already* canonical
`Arc`s. A node's identity is therefore a **shallow** key — no deep recursion:

- the `ExprNode` discriminant, plus
- all scalar fields: `binder_name`, `binder_info`, `decl_name`, `non_dep`,
  `type_name`, `idx` (`Nat`), literal value, level list (`Vec<Arc<Level>>`),
  `mdata` (`KVMap`), fvar/mvar `Name`, sort `Level`, and
- the child `Arc<Expr>` **pointers** (by address).

Two nodes are the same iff same discriminant + equal scalar fields +
pointer-equal children. This is exact: identical canonical children ⇒ pointer
identity ⇒ the subtrees are structurally identical. Levels inside `Const`/`Sort`
should likewise be canonicalized (a parallel, cheaper level-interning step) so
level-bearing exprs share; this is a secondary refinement (see Scope).

Keyed/bucketed by the node's already-computed `ExprData.hash()` (a structural
hash: `structural_eq ⇒ equal hashes` already holds, per expr.rs). This makes the
map lookup O(1) amortized with the existing hash.

### Where it lives

A guarded canonicalizer in `leanr_kernel` (it needs `Expr`/`ExprNode`
structural knowledge and the smart constructors), invoked from the CLI
`check` driver. It operates **outside** the trusted admission path
(`add_decl`/inductive/quot are untouched), so the TCB surface of this change
is limited to a pure, side-effect-free tree-rewrite utility.

### Guarded recursion (the one care-point)

The pass recurses over untrusted, possibly-deep decoded expr trees. It MUST use
the sanctioned pattern — `RecGuard::enter` (stacker + depth cap → error) or an
explicit worklist/stack — never unguarded recursion. On depth-cap it returns a
`KernelError` (incompleteness, never a panic), consistent with the rest of the
crate. Bottom-up canonicalization maps naturally to an explicit post-order
stack, which also sidesteps deep native recursion entirely; prefer that.

## Soundness argument

Canonicalization replaces an `Arc<Expr>` with a **structurally identical**
one (same node, same scalar fields, structurally identical children). The
kernel decides types by `structural_eq`/`is_def_eq`, which compare by value;
`Arc::ptr_eq` appears only as a *fast path* that short-circuits when pointers
match and otherwise falls through to structural comparison. Therefore:

- No verdict can change: any `is_def_eq`/`structural_eq`/`infer` result is a
  function of expr *structure*, which canonicalization preserves exactly.
- The type checker's pointer-keyed caches (`ExprPtr` = `Arc::ptr_eq` /
  address hash, tc.rs) become *more* effective (structurally-equal exprs now
  share a pointer → more cache hits) and remain sound (a pointer hit still
  implies structural identity; the reverse was never assumed).
- `ExprData` is a pure function of children + scalar fields, so canonical
  nodes carry identical `ExprData` to what they replaced — hashes, flags,
  `loose_bvar_range`, and `approx_depth` are unchanged.
- The postponed structural checks (`constant_info_eq`, decoded vs kernel-
  regenerated) still compare by value and are unaffected.

## Testing

- **Unit (canonicalizer):** (a) idempotence — canonicalizing an already-
  canonical tree is a no-op returning pointer-equal results; (b) merging — two
  independently-built, structurally-equal, pointer-distinct exprs canonicalize
  to one shared `Arc` (`Arc::ptr_eq`); (c) preservation — for many generated
  exprs, `structural_eq(e, canon(e))` holds and `ExprData` is identical;
  (d) deep-tree safety — a pathologically deep tree returns `DeepRecursion`
  (or is handled by the explicit stack) without panicking or overflowing.
- **Regression (verdict-preserving):** the full `cargo test --workspace` stays
  green — crucially `check_fixtures.rs` (real replay + hermetic mutation-
  differential verdicts) and the kernel unit suite. Any verdict drift shows
  here.
- **Acceptance:** the controller re-runs the full `check --all` stdlib sweep
  under the memory watchdog. Pass = exit 0 with the expected
  `checked N modules, M declarations` line, peak comfortably under 32 GiB
  (record peak + wall-clock + declaration count in the commit message).

## Scope / sequencing

- **Step 1 (this spec's core):** canonicalize decoded constants before replay
  (boundary #1). Expected to capture the dominant win; measure.
- **Level interning:** intern `Level`s during the pass so level-bearing exprs
  (`Const`, `Sort`) share their level lists. Cheap; include in Step 1.
- **Step 2 (only if Step 1's measured peak is not comfortably under 32 GiB):**
  intern kernel-generated recursors as they are stored into `env` (boundary
  #2) — a small, localized addition inside inductive admission. Gated on
  measurement; not built up front (YAGNI).

## Constraints (inherited from the M1b plan / AGENTS.md)

- `leanr_kernel` depends on no workspace crate; no new external deps.
- `.olean`-derived values are untrusted: no panic, no unguarded recursion, no
  unbounded allocation not tied to input length. Canonicalization is bounded by
  the decoded input size; the transient map is bounded by the number of
  distinct nodes (≤ total nodes) and freed after the pass.
- Checked arithmetic on olean-derived values (the `Nat` idx in the key).
- Lint gate before commit (`mise run lint`); full gate (`mise run ci`) where a
  task says so. Conventional-commit prefixes.
- Every claim about kernel semantics cites oracle source where relevant; this
  change is a representation optimization, so it cites the existing
  `structural_eq`/`ExprData` invariants in `expr.rs` rather than new oracle
  lines.
