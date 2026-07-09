# Term-bank kernel migration — design spec (compact Expr, phase 2)

**Date:** 2026-07-06
**Status:** approved (brainstorming), pending implementation plan
**Milestone:** compact-Expr phase 2 of 3. Parent spec:
`2026-07-06-compact-expr-term-bank-design.md` (§3–§5, §7 stages 3–5).
Phase 1 (standalone bank, bridges, `promote`) merged in PR #1.

## Problem

The phase-1 term bank exists but nothing uses it: the kernel still runs
on `Arc<Expr>` with pointer-keyed caches, so the mechanism-3 blowup
(structurally equal terms at distinct pointers defeating every cache)
still kills `check --all` inside the 32 GiB pod limit, and the
environment still pays ~140 B/node plus interner tables.

## Goal

Migrate the kernel — `subst`, `local_ctx`, `tc`, `quot`, `inductive`,
`env`, `replay` — from `Arc<Expr>`/`Arc<Name>`/`Level` to
`ExprId`/`NameId`/`LevelId`, with:

- every type-checker cache structural by the interning invariant;
- per-declaration transients interned in a scratch `Store` and freed
  wholesale;
- decoded modules bridge-interned into the persistent bank one at a
  time, each module's Arc graph dropped before the next is touched;
- **no accept/reject verdict change**, demonstrated by a dual-checker
  differential gate before the flip.

**Acceptance (user-set):** the full differential fixture suite green;
the `Init.Data.Char.Ordinal` canary exits 0 in bounded memory; and
**full `check --all` completes inside the 32 GiB pod limit** (peak RSS,
wall-clock, and declaration count recorded). The ≤ 6 GiB peak target
remains phase 3's bar (direct decode removes the per-module Arc
transient and the bridge walk).

## Non-goals

- Rewriting the `.olean` decoder (phase 3): `leanr_olean` keeps
  producing `Arc`-based `ConstantInfo`s; the kernel boundary bridges.
- Deleting the `Arc<Expr>`/`Arc<Name>`/`Level` tree types: they remain
  the decoder-boundary input and bridge source until phase 3.
- Changing kernel algorithms, the ≤ 6 GiB sweep target, parallelism, or
  anything else the parent spec's non-goals exclude.

## Approach (decided)

Three sequencing options were considered:

- **A. Parallel id-native kernel, then flip** — build id-based modules
  as `bank/` siblings, each task green, old kernel untouched; a
  dual-checker differential gate tests verdict preservation before a
  final flip task swaps them in. **Chosen:** it is the only option
  where every commit is green *and* the flip is protected by a tested
  (not argued) verdict-preservation gate, matching the repo's oracle
  discipline and the phase-1 pattern. Cost: ~8k lines temporarily
  duplicated; tests ported rather than moved.
- B. In-place bottom-up swap — least code, but the crate doesn't fully
  compile mid-branch and the verdict gate is dark for most of the
  migration. Rejected.
- C. Checker-internals only with lazy env interning — smallest step,
  but throwaway machinery, leaves `inductive` admission unprotected,
  and does the migration twice. Rejected.

## §1 Module layout

New id-native modules grow inside `bank/` as siblings of the phase-1
representation, each landing green and unit-tested with the old kernel
untouched:

| new module | replaces (at flip) |
|---|---|
| `bank/decl.rs` | id-twins of `ConstantInfo`/`DefinitionVal`/`RecursorRule`/… + `ConstantInfo` ↔ id-twin bridges |
| `bank/local_ctx.rs` | `local_ctx.rs` (`LocalContext`, `FVarIdGen`) |
| `bank/subst.rs` | `subst.rs` |
| `bank/tc.rs` | `tc.rs` |
| `bank/quot.rs` | `quot.rs`, `quot_red.rs` |
| `bank/inductive.rs` | `inductive.rs` |
| `bank/env.rs` | `env.rs` internals (persistent `Store` + `HashMap<NameId, ConstantInfo>` id-variant + `add_core` with `promote`) |
| `bank/replay.rs` | `replay.rs` (pre-intern pass deleted) |

The final flip task `git mv`s each over the module it replaces — the
end-state layout matches today's; no permanent `bank::` indirection in
the public API. Deleted at the flip: the Arc-based checker modules
above, `intern.rs`, the replay pre-intern pass, and `ExprPtr`-keyed
caching. `expr.rs`/`name.rs`/`level.rs`/`syntax.rs` survive as
decoder-boundary types until phase 3.

The bridge seam is `ConstantInfo` ↔ id-twin: the unit the environment
stores, the checker consumes, the dual-checker gate compares, and the
decoder boundary crosses. Phase-1 expr/name/level bridges extend one
level up to cover it.

## §2 Data flow and lifecycle

**Load.** `Environment::from_modules(modules)` iterates decoded modules
one at a time: bridge-intern every `ConstantInfo` into the persistent
`Store` (names, levels, exprs, kvmaps dedup on the way in), insert the
id-twin into the constants map, then drop that module's Arc graph
before touching the next. Peak decode-side memory is one module's Arc
graph plus the growing bank — this per-module drop is what gets the
full sweep under the pod limit in phase 2.

**Check.** `TypeChecker::new(&env)` creates a per-declaration scratch
`Store` whose interns consult the persistent table first (phase-1
semantics). All transients intern into scratch. Caches migrate:
`infer_cache`, `whnf_cache`, `whnf_core_cache`, `unfold_memo` become
`HashMap<ExprId, ExprId>`; `failure_cache` a
`HashSet<(ExprId, ExprId)>`; the equiv-manager UnionFind holds raw
`u32` id bits. By the interning invariant every cache is structural —
the mechanism-3 blowup is gone by construction.

**Admission.** `add_decl` checks with the scratch store; `add_core`
calls phase-1 `promote()` on exactly the kernel-generated values that
outlive the declaration (inductive/constructor/recursor
`ConstantInfo`s including `RecursorRule.rhs`). On `TypeChecker` drop,
the scratch store, its probe table, and every id-keyed cache free
wholesale. The nested-inductive scratch env becomes a delta over the
real one: it borrows the persistent bank read-only, clones only the
constants map, and interns its transient declarations' terms into the
checker's scratch region (they drop with the declaration; the real
admission still promotes at `add_core`). The empty-interner clone hack
disappears.

**Names, levels, FVars.** `ConstantVal` level params become `LevelId`;
`LocalContext` and FVar identities become `NameId`; `FVarIdGen` mints
fresh names by interning into scratch. FVar ids are therefore
scratch-region ids — sound because local contexts never outlive the
declaration, and promoted values are closed terms by existing kernel
invariants (a loose FVar in a promoted value is a bug today too).

## §3 Verification

- **Per-task:** each `bank/` module ports its predecessor's unit tests
  (run against id terms via the bridges) and adds a differential
  property test — random terms through the phase-1 generators, the
  operation applied both ways, results bridge-compared. The old kernel
  and the standing fixture gate stay green throughout the branch.
- **Pre-flip gate (the heart of approach A):** a dual-checker
  integration test decodes every fixture module, builds both
  environments (Arc and id), replays every declaration through both
  `TypeChecker`s, and requires identical verdicts — including the
  hermetic mutation fixtures, rejected by both with the same
  `KernelError` variant. Must pass before the flip task may start.
- **Flip:** `tests/check_fixtures.rs` ports to the id kernel — same
  fixtures, same verdicts ("green unmodified in spirit").
  `leanr_olean`/CLI call sites rewire; `lib.rs` exports go id-based.
- **Acceptance (controller-run, watchdog):** (1) `leanr check
  Init.Data.Char.Ordinal` exits 0 in bounded memory; (2) full
  `check --all` exits 0 with `checked 2433 modules, …` inside the
  32 GiB pod limit; record peak RSS, wall-clock, declaration count.

## §4 Error handling

`KernelError` payloads that today carry `Arc<Expr>`/`Arc<Name>` render
to owned strings at construction, via the scratch+persistent view alive
at the error site (errors are cold; scratch ids must not outlive the
scratch store). Bank/id exhaustion stays `KernelError::BankExhausted`,
never a panic. Accessor bounds-checks and `RecGuard` discipline carry
over unchanged.

## §5 Sequencing (for writing-plans)

1. `bank/decl.rs` id-twins + `ConstantInfo` bridges
2. `bank/local_ctx.rs` + `bank/subst.rs`
3. `bank/tc.rs`
4. `bank/quot.rs` + `bank/inductive.rs`
5. `bank/env.rs` + `bank/replay.rs`
6. dual-checker differential gate
7. flip (`git mv`, rewire, delete Arc checker + `intern.rs`)
8. acceptance runs

## Constraints (inherited)

- `leanr_kernel` depends on no workspace crate; no new external deps;
  no `unsafe`.
- `.olean`-derived values untrusted: no panics reachable from attacker
  data, explicit stacks or `RecGuard` for attacker-depth recursion,
  checked/exact arithmetic.
- Oracle discipline: representation changes cite the invariants they
  preserve; algorithmic behavior continues to cite oracle source lines
  (the ported `tc`/`inductive` keep their oracle citations).
- Lint gate (`mise run lint`) per commit; full gate (`mise run ci`)
  where a task says so; conventional-commit prefixes.
- Wall-clock: regression acceptable only if the sweep completes within
  the pod limit; improvement expected (structural hits, no refcounts).

---

## Phase-2 Acceptance Findings (Task 9, 2026-07-08/09)

Task 9 ran the canary (`leanr check Init.Data.Char.Ordinal`) under a
memory watchdog (the prior session's canary OOM-killed the *container*
because it ran without one). Two independent results came out of it.

### Result A — the migration's representational goal is MET (env memory)

The id-native kernel's **persistent environment is tiny**. Checking the
226-module import closure of `Init.Data.Char.Ordinal` (15,642 declarations),
the id kernel's process RSS stays **flat at ~0.55 GiB** across the whole
env; the pre-flip Arc kernel holds **~15–23 GiB** for the same env. That is
the ~30–40× env-storage reduction this phase set out to buy, and it is what
phase-1 hash-consing could not achieve (phase-1 plateau was ~21–24 GiB).
Every declaration checks with correct verdicts; no verdict drift.

### Result B — a PRE-EXISTING kernel reduction divergence blocks the sweep

One declaration, `_private.Init.Data.Char.Ordinal.0.Char.ofOrdinal._proof_3`
(a `by grind` proof), blows the **checking transient** from 0.55 GiB to
~25 GiB and never finishes. This is **not** caused by the migration:

- The pre-flip **Arc** kernel (commit `9b1c773`) hits the same ~23–25 GiB
  on the same declaration. Both Rust kernels share the same reduction
  engine, so both diverge from real Lean the same way. The plan's own
  Task-9 note ("old behavior was a >25 GiB kill on one declaration")
  already recorded this.
- Real Lean kernel-checks this proof in **<1 s** (the module compiles in
  ~1–2 s). Our kernel performs **100M+ interned reduction steps** and
  OOMs. Kernel whnf runs at ~1–10M steps/s, so real Lean physically
  cannot be doing the same walk — **it truncates a reduction chain our
  kernel walks in full. This is a divergence, not an inherent cost.**

**Mechanism (diagnosed):** `grind`/`omega` discharge the bound via the
linear-arithmetic normalizer `Nat.Linear.Poly.cancel`, which calls
`cancelAux` with `hugeFuel = 1_000_000` (`def hugeFuel := 1000000 -- any
big number should work`). `cancelAux` recurses structurally on `fuel`,
compiled via `Nat.brecOn`/`Nat.rec` + `Nat.below`. Our kernel walks that
recursion chain (a linearly-growing set of distinct `Nat.rec` reductions),
materializing `Nat.below` course-of-values structure real Lean never
forces.

**What it is NOT** (ruled out by measurement):

- **Not smart unfolding.** `smartUnfolding`/`_sunfold` live in
  `Lean/Meta/WHNF.lean` (elaborator, not kernel); real Lean stays fast
  with `set_option smartUnfolding false`.
- **Not a sharing/recomputation (memoization) bug.** A per-major-value
  tally on the real blowup showed `max_repeats = 5` (no level reduced
  more than 5×) with *distinct* majors growing linearly — a linear walk,
  not exponential recomputation.
- **Not transient-retention alone.** The timing argument above shows real
  Lean does far fewer reductions; it truncates rather than "walks + frees".

`reduce_recursor`, `reduce_proj`, and `is_def_eq` each look lazy in
isolation, so the missing short-circuit is a subtle interaction not yet
pinned to a line. A simple single-recursion analogue (`loop fuel xs`
with an empty-list base case) checks in ~0.4 ms in our kernel — the
blowup needs `cancelAux`'s specific shape (body accesses `below` for its
recursive calls). Minimal `grind`/`omega` bound proofs re-derived by hand
did **not** reproduce it (the elaborated proof term is context-sensitive),
so the only confirmed reproducer is the real `_proof_3` (via the CLI's
per-declaration isolation).

### Disposition

- The migration lands as the **representational win it is** (Result A);
  its correctness is unchanged (Task 1–8 reviews clean, dual-checker gate
  green at Task 7).
- The **full-stdlib acceptance sweep (peak RSS < 32 GiB) remains gated**
  on fixing Result B, which is a **pre-existing kernel-reduction
  divergence** (present in the Arc kernel too), tracked as its own
  focused, TCB-sensitive effort: find and add the reduction short-circuit
  real Lean uses so `Nat.brecOn`/`Nat.below` over large `fuel` does not
  walk in full. It is verdict-preserving by construction (a reduction
  optimization, not a semantics change).
