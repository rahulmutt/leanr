# M1-final — parallel checking + Mathlib-scale sweep — design spec

Date: 2026-07-10. Milestone: M1 ("`leanr check` re-checks all of
Mathlib from `.olean`s") — final slice. Parent:
`2026-07-04-leanr-architecture-design.md` (§Milestones, M1).
Predecessors: `2026-07-05-m1b-type-checker-design.md` (shipped the
sequential checker; deferred "parallel checking + Mathlib-scale sweep"
to exactly this slice) and `2026-07-10-direct-to-id-decode-design.md`
(term-bank phase 3, whose frozen-after-decode persistent bank is what
makes lock-free parallel replay possible).

## Problem

`leanr check` is correct and fast per-declaration but single-threaded:
the full stdlib sweep runs `replay()` sequentially over ~2,433 modules
/ ~203k declarations. M1's shipping claim — "the fastest Mathlib proof
checker; an independent Rust audit of Lean's kernel" — requires two
things this slice delivers:

1. **Parallel replay**, so the checker uses all cores.
2. **Mathlib scale**, so the claim is measured against Mathlib (not
   just the toolchain stdlib) and benchmarked against the checker
   Mathlib CI actually uses (`lean4checker`).

## Goal

Ship the fastest Mathlib proof checker: `leanr check --all` checks all
of pinned Mathlib green, in parallel, faster than `lean4checker`'s
best-configured run on the same machine, within the 32 GiB pod
envelope. Verdict semantics are unchanged from sequential `replay()` —
still LeanChecker `--fresh` (every declaration re-checked once from an
empty environment) — and that equivalence is proved by a differential
gate before the parallel path becomes the default.

Explicitly **out of scope** (and where it lands): parallel *decode*
(sequential decode is the Amdahl floor; measured during stdlib runs,
spec'd as a follow-up only if it dominates at Mathlib scale); stable
error codes / `leanr explain` (M2+ diagnostics); env-extension
interpretation (M4).

## Key enabling observation

On a green run the persistent bank is **effectively frozen after
decode**. Three facts, all already true in the codebase, combine:

- Decoded constants are fully interned into the persistent `Store`
  (direct-to-id decode, phase 3) — no further interning happens during
  checking.
- `add_decl` checks a declaration against a read-only `EnvView` plus a
  fresh **per-declaration scratch `Store`** (`bank/scratch.rs` region
  discipline); the only persistent-store mutation is the final
  `add_core` commit.
- For defs/axioms/theorems/opaques, `add_core` promotes the very
  `ConstantInfo` it was handed — already present, verbatim, in the
  decoded union. For constructors/recursors, replay never admits the
  decoded copy at all; it admits the kernel's *regenerated* infos and
  then asserts each decoded twin is structurally identical
  (`replay.rs::check_postponed_{constructors,recursors}` →
  `constant_info_eq`). By the interning invariant, structural equality
  **is** id equality.

Therefore a parallel checker need not mutate the persistent store to
represent "the environment so far". It can pre-populate a read-only
declaration table with the decoded union and gate visibility with a
per-entry atomic flag — checking a declaration observes exactly its
transitively-checked dependencies, which is a valid sequential prefix,
so every verdict is one a sequential replay could have produced. The
only genuinely new kernel check this requires: extend the
decoded-vs-regenerated structural check to the **inductive infos**
themselves (sequential replay admits the regenerated inductive infos
and discards the decoded ones; the pre-populated table keeps the
decoded ones, so they must be proven identical). This is a strict
strengthening — see Soundness.

**Lock-free for the majority; one serialized point.** Defs, axioms,
theorems, and opaques never promote and need no post-check comparison —
their decoded `ConstantInfo` is already the survivor, already in the
table, so a worker simply checks and flips the flag, fully lock-free.
Constructors, recursors, and inductive blocks are different: the
kernel *regenerates* them in the worker's scratch region, and
comparing a regenerated info against its decoded twin by
`constant_info_eq` is id equality, which is only meaningful when both
sides live in the **same** store. So an inductive/quotient block's
regenerated survivors must be promoted (interned) into the shared
persistent store to canonicalize their ids before comparison — a write
to the otherwise-frozen store. That promotion-and-compare step is
serialized behind a single mutex (design decision, 2026-07-10):
inductive/quot tasks are a minority, promotion of an identical info is
idempotent and fast, and this reuses the existing, proven
`constant_info_eq` verbatim rather than adding a new cross-region
comparison primitive to the TCB. The def/axiom/theorem/opaque hot path
takes no lock.

The kernel's only interior mutability is a `#[cfg(test)]`/debug trace
tally (`tc/trace.rs`); `&Store` and `&EnvView` are otherwise plain
`Sync` data.

## Architecture

Two workstreams sharing one acceptance gate.

### Workstream 1 — parallel replay

1. **Decode (sequential, unchanged).** `load_closure` decodes the
   import closure into the persistent bank; the CLI folds per-module
   constants into the name-deduped union and an owner map (module that
   first supplies each constant, for error attribution) — exactly as
   `leanr_cli::check` does today.
2. **Freeze.** The `Store` moves behind an `Arc` and is never mutably
   borrowed again.
3. **Table build.** The union becomes a `CheckedConstants` table: a
   `NameId`-keyed map of decoded `ConstantInfo`s, each paired with an
   `AtomicBool` admitted flag (initially unset). `get(n)` returns the
   entry only if its flag is set.
4. **Dependency pass (parallel, read-only).** Workers run
   `used_constants` over every entry to build the task graph. Tasks:
   one per def/axiom/theorem/opaque; one per mutual inductive *block*
   (the `all` members plus their constructors and recursors — admitted
   as a unit sequentially, so scheduled as a unit); one for quotient
   init with an explicit edge to `Eq`. Output: per-task dependency
   counts + reverse-adjacency lists. The walk stays `RecGuard`-guarded
   like every term recursion.
5. **Parallel replay.** A ready queue seeds with zero-dependency tasks.
   Worker loop: pop task → fresh scratch `Store` reading through the
   frozen base → run the *check half* of admission against the gated
   table → on success set the admitted flag(s) (`Release`), decrement
   dependents' atomic counters, push newly-ready tasks → drop scratch.
   Def/axiom/theorem/opaque tasks take no lock. Inductive-block and
   quotient tasks, after checking, take a single shared promotion mutex
   to intern their regenerated survivors into the persistent store and
   run the postponed ctor/recursor comparisons **and** the new
   inductive-info comparison via `constant_info_eq`, before flag-setting.
6. **Verdict.** All tasks green → the same final stats line as today
   (`checked`/`skipped` counts are order-independent → deterministic
   output). Any failure → cancel and report (see Error handling).

### Workstream 2 — Mathlib scale + benchmark

- A pinned Mathlib commit whose `lean-toolchain` matches ours,
  recorded as a project constant (`mathlib-pin`, next to
  `lean-toolchain`).
- `mise run mathlib:fetch`: clone Mathlib at the pin and
  `lake exe cache get` the prebuilt `.olean`s onto the pod. One-time,
  network; acceptance runs are offline thereafter.
- `mise run check:mathlib`: `leanr check --all` over the fetched tree.
- `mise run bench:mathlib`: build `lean4checker` at the pinned
  toolchain, run it (best thread configuration) and
  `leanr check --all --jobs N` over the same tree on the same pod,
  record wall-clock + peak RSS for both.

## Components

### `leanr_kernel` (TCB) — check-only API, no threads, no new deps

- **`CheckedConstants`** (new, `env/`): the gated declaration table.
  `NameId`-keyed decoded `ConstantInfo`s, each with an `AtomicBool`
  admitted flag; `get` returns an entry only when its flag is set.
  Gating is soundness-relevant (it is what makes "env = my checked
  prefix" true), so it lives inside the kernel. `Sync` by construction
  — std atomics only, preserving the zero-dependency rule.
- **`check_declaration(view, scratch, decl) -> Result<Admitted,
  KernelError>`** (new): today's `add_decl` body split at the commit
  point — check against a view, return the survivor `ConstantInfo`(s)
  instead of inserting them. `add_decl` is refactored to `check +
  commit` so its signature and every existing kernel test are
  unchanged; the parallel driver calls only the check half and then
  flips flags (commits are redundant per Key enabling observation).
- **`replay()`** stays as-is: the semantic reference and the
  differential twin for the new driver.

### `leanr_check` (new crate) — the parallel driver

Owns everything with threads in it: the parallel dependency pass, block
grouping, the ready-queue DAG scheduler (std `thread` + channels — no
rayon; ~150 lines, keeps `deny.toml` quiet and the dep count honest),
cancellation, stats. Depends on `leanr_kernel` (check API) and
`leanr_olean` (loaded modules); sits between `leanr_olean` and
`leanr_cli` in the crate order. Added to ARCHITECTURE.md.

### `leanr_cli`

`check` gains `--jobs N` (default `std::thread::available_parallelism`),
routing through `leanr_check`. Progress reporting shifts from per-module
lines to a periodic declarations-checked counter plus the final stats
line — the **same final format**, so `dump_decls`/goldens survive.
Error attribution keeps the owner map.

### Repo / tasks

`mathlib-pin` recorded next to `lean-toolchain`; mise tasks
`mathlib:fetch`, `check:mathlib`, `bench:mathlib` (above). ARCHITECTURE.md
gains the crate; THREAT_MODEL.md gains the cycle/starvation DoS note.

## Data flow and concurrency invariants

Stated once, relied on throughout:

- The frozen store is shared immutably (`&Store` is plain `Sync` data;
  no interior mutability on the check path).
- All new term construction happens in worker-local scratch regions
  that die with the check — a hostile module cannot accumulate scratch
  across tasks.
- The *only* cross-thread communication is the admitted flags, the
  per-task dependency counters, the ready queue, and the promotion
  mutex. Writers store `Release`, readers load `Acquire`.
- The promotion mutex guards the sole writer of the persistent store
  after freeze: inductive/quotient survivors are interned + compared
  under it, so no two workers mutate the store concurrently. The
  def/axiom/theorem/opaque hot path never takes it.
- A declaration's check observes an environment of exactly its
  transitively-checked dependencies — a valid sequential prefix.
- Theorem duplicate-tolerance (`replay.rs`'s Thm arm) needs no code:
  the union map is name-deduped before the table is built, as today.

Memory budget (32 GiB pod): one Mathlib-scale frozen bank (~4–8 GiB,
extrapolated from stdlib's 1 GiB) + task graph (hundreds of MB at
Mathlib's edge count) + bounded per-worker scratch.

## Soundness and TCB discipline

- **Verdict preservation.** Kernel checking logic is untouched; the
  parallel driver only reorders *independent* checks and defers the
  persistent-store commit into a gated-flag flip. Each verdict is one a
  sequential replay could produce (valid-prefix argument above). Proved,
  not asserted, by the differential gate below.
- **The one new check.** Decoded-vs-regenerated *inductive-info*
  comparison via the existing `constant_info_eq`. Strictly stronger
  than sequential replay (which never compared them), so it can only
  ever *reject* — and the stdlib differential gate proves it never
  rejects a real declaration (a divergence would surface as the
  parallel path erroring where sequential passed). No new comparison
  code enters the TCB: the regenerated survivors are promoted into the
  persistent store (under the promotion mutex) exactly as sequential
  replay promotes them, then compared with the same `constant_info_eq`
  the sequential path uses.
- **Untrusted input.** Constants, cross-references, and therefore the
  task graph are attacker-shaped. No panics; no `unwrap`/index on
  untrusted-derived values; the dependency walk stays `RecGuard`-bounded.
  Task-graph memory is O(total term size) — same order as the decode it
  follows. No `unsafe` anywhere in the driver.
- **TCB shape.** `CheckedConstants` and `check_declaration` live in
  `leanr_kernel`, which keeps zero workspace deps and no new external
  deps (std atomics only). All threading lives in `leanr_check`, outside
  the TCB.

## Error handling

- **Failure flow.** The first check failure sets a shared cancellation
  flag and records the error; workers observe it between tasks and
  drain (in-flight checks are bounded by existing per-declaration
  guards). Report and exit 1. Blame keeps today's shape — `while
  replaying declaration '<name>': <error>`, attributed to the owning
  module. Concurrent failures: the exit-determining error is the race
  winner; all recorded errors go to stderr. The sequential path's
  "first" error was already `HashMap`-iteration nondeterministic, so
  this is no regression.
- **Missing dependency.** A dep absent from the table is caught in the
  dependency pass → `MissingConstant` (same error as sequential, just
  earlier).
- **Cycles / starvation.** A cycle (impossible from a well-formed
  `.olean`, constructible by an attacker) leaves tasks permanently
  un-ready. After the queue drains, unfinished tasks with no recorded
  error ⇒ a cycle → reported as a replay error naming a member, never a
  hang or deadlock. This is the parallel twin of `RecGuard` bounding the
  sequential recursive descent.
- **Watchdog.** Acceptance sweeps run under the external memory
  watchdog (as with Result-B), so a scheduler livelock dies visibly at
  the resource bound rather than silently wedging CI.

## Testing

- **Unit (`leanr_check`).** Scheduler on synthetic DAGs, no kernel:
  linear chains, wide fan-out, diamonds (shared dep runs once, both
  dependents wait), a deliberate cycle (→ reported error, not hang), a
  missing-dependency edge (→ `MissingConstant`). Run under a
  thread-sanitizer CI config so flag/counter ordering is machine-checked.
- **Kernel unit tests** — untouched (`add_decl` keeps `check + commit`).
  `CheckedConstants` gating tested directly (flag unset ⇒ `get` `None`;
  set ⇒ entry).
- **Differential gate (load-bearing).** `leanr check --all --jobs 1`
  (parallel driver, one worker) vs. `replay()` (sequential reference)
  over the full stdlib: identical verdicts and identical
  `checked`/`skipped` counts — proves verdict-equivalence before any
  multi-thread nondeterminism. Then `--jobs N` for several N matches
  `--jobs 1` (verdict determinism under scheduling). Twin of the
  phase-3 differential gate; deleted once the flip is accepted.

## Acceptance (controller-run, under the 32 GiB watchdog)

1. **Canary.** `leanr check Init.Data.Char.Ordinal --jobs N` — exit 0,
   bounded.
2. **Full stdlib sweep** at `--jobs N` — exit 0, matches recorded
   declaration counts; record wall + peak RSS vs. the sequential
   baseline (peak RSS must not meaningfully regress; wall-clock should
   improve).
3. **Mathlib sweep + benchmark** (the milestone bar) —
   `leanr check --all --jobs N` over pinned Mathlib: exit 0, expected
   declaration count, peak RSS ≤ 32 GiB, wall-clock beating
   `lean4checker`'s best-configured run on the same pod. Both figures
   recorded in this spec's Acceptance section on completion.

## Sequencing (for writing-plans)

Bottom-up, tests with each stage:

1. `check_declaration` split + `add_decl = check + commit` refactor;
   kernel tests stay green unmodified.
2. `CheckedConstants` gated table + unit tests.
3. `leanr_check`: dependency pass + block grouping over the frozen
   store (single-threaded first), reproducing `replay()`'s task set.
4. `leanr_check`: DAG scheduler + worker pool + cancellation; scheduler
   unit tests (synthetic DAGs, TSan).
5. Extended inductive-info structural check.
6. CLI `--jobs`; differential gate (`--jobs 1` vs `replay()`, then
   `--jobs N`) green over full stdlib.
7. Flip default; delete the differential gate.
8. Mathlib pin + `mathlib:fetch` + `bench:mathlib`; acceptance sweep.

## Constraints (inherited)

- `leanr_kernel` depends on no workspace crate; no new external deps
  (std atomics only).
- `.olean`-derived values untrusted: no panic, no unguarded recursion,
  no deadlock/livelock on hostile graphs; allocation bounded by input
  size.
- Oracle discipline: verdict semantics cite sequential `replay()` /
  `Replay.lean` as the reference; the Mathlib pin is a project constant
  revisited only at a milestone boundary.
- Lint gate (`mise run lint`) per commit; full gate (`mise run ci`)
  where a task says so; conventional-commit prefixes.
