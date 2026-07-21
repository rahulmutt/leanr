# M4a plan 3 — `is_def_eq`: assignment, lazy delta, approximations, and the defeq cache — design spec

Status: approved (brainstormed 2026-07-21)
Parent: [2026-07-20-m4a-meta-core-design.md](2026-07-20-m4a-meta-core-design.md)
Predecessor plan: [../plans/2026-07-20-m4a-reduction-inference-harness.md](../plans/2026-07-20-m4a-reduction-inference-harness.md) (plan 2 of 4, merged)

## Problem

Plans 1 and 2 of M4a are merged: `leanr_meta` has the transparency
model, defeq `Config` with its cache key, the metavariable context,
`whnf`, `infer_type`, and the tier-1 `meta:fast` differential gate over
purpose-built fixtures. Nothing unifies: there is no `is_def_eq`, no
occurs check beyond `MetavarContext::assign`'s local guard, no level
unification, and the seams plan 2 left named (`synth_pending`,
`whnf_delayed_assigned`, the unification-hints failure path) have
nothing behind or around them.

This slice (plan 3 of 4) delivers `is_def_eq`. Plan 4 adds the
instance-extension decode, tabled synthesis, and the `meta:nightly`
discovery sweep.

## Goal

`is_def_eq` in `leanr_meta` — mvar assignment with occurs check, level
unification with postponement, lazy delta, the five approximation
flags, and the transient/permanent defeq cache — agreeing with the
oracle on committed `defeq` and `defeq_mvar` fixture queries under two
named config profiles, gated by the existing `meta:fast` task.
`leanr_kernel` and `leanr_olean` are unmodified.

## Scope decisions (agreed in brainstorming)

- **One plan, staged tasks, `meta:fast` green throughout** — plan 2's
  precedent. Considered and rejected: splitting into 3a (core defeq)
  / 3b (approximations + cache), which would merge an `is_def_eq`
  behaviorally wrong on any query Lean's approximations accept and
  force the corpus to dodge them; and deferring the approximations to
  plan 4, which would push the parent spec's highest-risk unspecified
  behavior past the point where the nightly sweep would exercise it.

- **Mvar-dependent behavior is differentially verified in tier 1, not
  deferred to plan 4's nightly.** The parent spec placed synthesized
  mvar queries in tier 2, but plan 3's core new behavior — assignment,
  the occurs check, the approximations — only manifests on terms with
  mvars, and merging it verified solely by transcribed unit tests
  would leave the slice's highest-risk code never having faced the
  oracle. So `dump_defeq.lean` itself creates mvars over the small
  fixture corpus (see § Acceptance harness). Plan 4's nightly then
  scales the same query shape to Mathlib; the parent spec's honest
  limitation (synthesized queries are a plausible guess at what the
  elaborator asks, not a record of it) applies at both scales and
  stands unchanged.

- **Full level defeq, including postponement.** `is_def_eq` bottoms
  out in level unification whenever it compares `Sort`s or constant
  instances, and mvar queries over universe-polymorphic fixtures
  create level mvars immediately. A simplified version (assignment
  without postponement, or ground-only comparison) would diverge from
  the oracle in ways indistinguishable from expr-side bugs. The
  postponed-constraint queue is the oracle's actual shape and lands
  whole.

- **Backtracking is clone-on-checkpoint.** Lean's `checkpointDefEq`
  saves and restores its metavariable context around trial
  unifications — free for Lean's persistent structures, not for
  `MetavarContext`'s mutable maps. Chosen: snapshot = clone the expr-
  and level-assignment maps plus the postponed queue; restore = swap
  back. Semantically identical to the oracle's save/restore and
  trivially correct; tier-1 mctxs are tiny. Rejected: an undo trail
  (every mutation site must participate, and a missed site is a
  silent cross-trial state leak that differential testing only
  catches if the corpus hits it) and persistent maps (a new
  dependency needing justification, slower on the no-backtrack path).
  Recorded as a performance simplification; plan 4's nightly is the
  measurement point for revisiting.

- **Channels whose engines don't exist keep plan 2's seam
  treatment**, documented at the seam with the oracle citation:
  `isDefEqNative` needs compiled evaluation (`reduceNative?`) and
  returns undef; `isDefEqOffset` needs the `offset_cnstrs` machinery
  plan 1 flagged as unconsulted (Nat `?x + k =?= n` constraints) and
  returns undef; `synth_pending` keeps returning `false` until
  plan 4; unification hints stay an unpopulated seam on the
  `isDefEqOnFailure` path per the parent spec. `isDefEqProofIrrel`,
  `isDefEqNat`, and `isDefEqStringLit` are **implemented**, not seamed
  — they are `infer_type`/`isProp`/literal reduction over machinery
  plan 2 already built.

- **No new olean decode.** Reducibility (plan 1) and matchers
  (plan 2) are already typed; instances are plan 4's. `leanr_olean`
  is untouched, so this slice adds no new untrusted-input surface.

## Architecture

### Module map

One concern per file, each an `impl MetaCtx` block, direct calls, no
dynamic dispatch. **Lean's implementation is the specification**: the
plan transcribes rule-by-rule with a citation per rule against the
pinned toolchain's `ExprDefEq.lean`, `LevelDefEq.lean`, and the
`isLevelDefEqAux` machinery in `Basic.lean` — never reconstructed
from memory. Where this spec and Lean's source disagree, Lean's
source wins and the plan records the correction.

| module | oracle source region | concern |
|---|---|---|
| `defeq.rs` | `isExprDefEqAuxImpl`, the `isDefEqQuick` family, `isExprDefEqExpensive` (eta, eta-struct, unit-like, proj, app args, Nat/String/native/offset channels, delta dispatch, `isDefEqProjInst`, `isDefEqOnFailure`) | the entry ladder and its escalation order |
| `assign.rs` | `processAssignment'`/`processAssignment`, `CheckAssignmentQuick.check`, the full `CheckAssignmentM` check, `typeOccursCheck`, `checkTypesAndAssign`, `mkLambdaFVarsWithLetDeps`, `simpAssignmentArg`, `processAssignmentFOApprox`, `processConstApprox` | mvar assignment, the occurs check, the assignment-side approximations |
| `level.rs` | `LevelDefEq.lean` + `isLevelDefEqAux` (Basic.lean) | level unification, `univ_approx`, the postponed-constraint queue |
| `lazy_delta.rs` | `isDefEqDelta`, `isDefEqDeltaStep`, the `unfold*DefEq` family, `isNonTrivialRegular`, `tryHeuristic` | lazy delta with `ReducibilityHints`-guided stepping |
| `cache.rs` | `getDefEqCacheKind`, `mkCacheKey`, `getCachedResult`/`cacheResult` | the transient/permanent split |

The entry ladder, from the oracle: quick structural/mvar paths →
proof irrelevance → a `whnf_core` loop (`whnfCoreAtDefEq`, projection
mode `yesWithDeltaI`) → mvar instantiation → cache lookup → the
expensive ladder. The five approximation flags stay at their oracle
call sites — fo/ctx/quasi-pattern/const in `assign.rs`, univ in
`level.rs` — as explicit `Config` fields consulted at named sites,
never implicit fallback. No separate `approx.rs`: the call sites are
assignment-shaped, and pulling them out would separate the flags from
the only code that gives them meaning.

### Backtracking (`MetaCtx`)

A `checkpoint()` / `rollback(snapshot)` pair on `MetaCtx`
transcribing `checkpointDefEq`: the snapshot clones the expr
assignment map, the level assignment map, delayed assignments, and
the postponed level-constraint queue. The highest-frequency
checkpoint site is `tryHeuristic` (trial `isDefEqArgs` on same-head
applications before unfolding); `isDefEqArgs`'s first/second-pass
structure and the binder walker are the others.

### Level defeq and postponement (`level.rs`)

Structural equality, level-mvar assignment guarded by
`strictOccursMax`, the two `univ_approx`-gated approximations
(`tryApproxSelfMax`, `tryApproxMaxMax`), and postponement: constraints
neither decidable nor refutable yet (`max`/`imax` shapes with
unassigned mvars) are pushed onto a `MetaCtx`-owned queue
(`postponeIsLevelDefEq`) and re-processed as level mvars get assigned,
resolved at checkpoint boundaries. The queue participates in
clone-on-checkpoint.

### Lazy delta (`lazy_delta.rs`)

The `isDefEqDelta` state machine: when both sides carry delta
candidates, compare `ReducibilityHints` heights and unfold the taller
side; `unfoldReducibleDefEq` handles the asymmetric reducible-vs-not
case; `sameHeadSymbol` applications get `tryHeuristic` first. Note
`ReducibilityHints` (already decoded, inline in `DefinitionVal`) is
**not** plan 1's `ReducibilityStatus`; the modules consulting each are
disjoint (`lazy_delta.rs` reads hints, `transparency.rs` reads
statuses), which keeps the parent spec's conflation warning
structural rather than a convention.

### The defeq cache (`cache.rs`)

`getDefEqCacheKind`: permanent for mvar/fvar-free pairs under a
standard config, transient otherwise — the split the parent spec
assigned to defeq and plan 2's correction deferred here, landing in
its oracle shape. Key = `(Config::cache_key(), lhs, rhs)`, so plan
1's `size_of::<Config>()` guard covers these caches with no new
mechanism. One transcribed subtlety: a result is not cached when the
query postponed level constraints (the oracle's `numPostponed`
comparison in `isExprDefEqAuxImpl`) — such a verdict is not yet
grounded.

## Error handling & edge cases

- `isDefEqStuckEx` is a typed `MetaError::IsDefEqStuck(ExprId)`
  variant — "not yet decidable, may become solvable once more mvars
  are assigned" — distinct from a `false` verdict and from budget
  exhaustion, per the parent spec.
- Every failure remains incompleteness, never unsoundness: the kernel
  independently re-checks anything elaboration produces.
- Every new recursive path routes through the plan-2 `guarded`
  wrapper (depth limit + `stacker`), and deterministic step budgets
  report as `StepBudgetExhausted`.
- `leanr_kernel` and `leanr_olean` are not modified.

## Acceptance harness

`tests/fixtures/meta/dump_defeq.lean` gains two query kinds beside
plan 2's `whnf`/`infer` records — same JSONL, same stable-id rule
(constant name + query kind + index, never a global counter), same
`fixtures:regen` wiring, CI still never installs Lean.

### Query kinds

- **`defeq`** — mvar-free pairs mined from purpose-built fixture
  modules, each written to exercise one ladder rung: eta, eta-struct,
  unit-like structures, projection defeq, proof irrelevance, the
  literal channels, and delta at each transparency × reducibility-
  status combination. Record: both terms (structural serialization,
  the existing shape), transparency, config profile, verdict.
- **`defeq_mvar`** — the oracle metaprogram creates the mvars itself:
  abstract an argument of a fixture application into
  `mkFreshExprMVar`, run `isDefEq` against the original, and record
  the verdict **plus the resulting assignments**, mvars renumbered
  canonically in creation order per query (the parent spec's rule —
  never verdict-only, because two implementations can agree on every
  boolean while assigning differently). Includes deliberate
  occurs-failure queries and universe-polymorphic fixtures that force
  level-mvar assignment and postponement.

### Config profiles

Every query runs under two named profiles: `default` (approximation
flags off, as `Meta.isDefEq` defaults them) and `approx` (the five
flags on, as elaboration's `approxDefEq` contexts set them). The
approximations only fire when enabled; a corpus that never enables
them verifies nothing about the parent spec's highest-risk item. The
profile is part of the query record and the stable id.

### Determinism

Queries that come near any step budget on either side are recorded
and excluded from the gate, per the parent spec's deliberate
divergence from `maxHeartbeats`.

### The gate

`mise run meta:fast`, extended in place: the acceptance test replays
`defeq` and `defeq_mvar` queries through `MetaCtx` and diffs verdicts
and canonical assignments. Seconds, no corpus walk, no Lean.

### Existing gates that stay green

Workspace tests, lint, `cargo deny`, parse-acceptance, both fuzz
targets, the never-hang storms, `fmt:mathlib`, `parse:mathlib:fast`,
and plan 2's `whnf`/`infer` fixtures.

## Staging

Task order keeps `meta:fast` green throughout:

1. `MetaCtx` additions — checkpoint/rollback, the postponed queue,
   the defeq cache maps.
2. `level.rs` — level unification and postponement.
3. Quick paths + `assign.rs` with approximations off; first
   `defeq_mvar` fixtures.
4. The expensive ladder + `lazy_delta.rs`; `defeq` fixtures per rung.
5. The five approximations; `approx`-profile fixtures.
6. `cache.rs` — the split and the postponed-count guard.

## Risks

1. **The approximation flags have no specification** — the parent
   spec's risk 1, concentrated in this slice. The two-profile corpus
   is the only mitigation, and it only catches divergence it
   contains.
2. **Clone-on-checkpoint cost is unmeasured** until plan 4's nightly
   runs real Mathlib-scale queries. If it dominates, the revisit path
   is an undo trail behind the same `checkpoint`/`rollback` API.
3. **`ctx_approx` coverage will be the thinnest of the five.** It
   needs binder/local-instance-heavy fixtures that are awkward to
   write; recorded rather than papered over, and plan 4's synthesized
   Mathlib queries are the follow-up coverage.
4. **The assignments comparison surface grows.** `defeq_mvar` records
   compare assignment maps, not just terms; a canonicalization bug on
   either side shows up as false divergence. Mitigated by reusing
   plan 2's structural serialization and the creation-order
   renumbering rule unchanged.

## Out of scope (and where it lands)

- Instance/default-instance extension decode, discrimination trees,
  tabled synthesis, a live `synth_pending`, `meta:nightly` → plan 4.
- Unification-hints population, coercions, the term elaborator and
  the postponement/synthetic-mvar ladder → M4b, per the parent spec.
- Native reduction (`reduceNative?`) → the VM slice.
