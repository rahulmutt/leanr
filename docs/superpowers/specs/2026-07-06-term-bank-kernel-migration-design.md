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
