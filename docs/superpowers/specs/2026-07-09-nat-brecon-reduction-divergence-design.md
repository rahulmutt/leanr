# Nat.brecOn / Nat.below reduction-divergence fix (Result B)

**Status:** design
**Date:** 2026-07-09
**Predecessor:** `2026-07-06-term-bank-kernel-migration-design.md` (Phase-2
Acceptance Findings, Result B)

## Problem

The term-bank kernel migration landed its representational win (Result A:
persistent env flat at ~0.55 GiB vs. ~15–23 GiB pre-flip). It left one
explicit open thread — **Result B**, a *pre-existing* kernel-reduction
divergence present in the Arc kernel too:

One `by grind` proof,
`_private.Init.Data.Char.Ordinal.0.Char.ofOrdinal._proof_3`, blows the
checking transient from 0.55 GiB to ~25 GiB and never finishes. Real Lean
kernel-checks it in <1 s. Our kernel performs 100M+ interned reduction
steps and OOMs.

**Mechanism (diagnosed at the class level, not yet pinned to a line):**
`grind`/`omega` discharge the bound via `Nat.Linear.Poly.cancel`, which
calls `cancelAux` with `hugeFuel = 1_000_000`. `cancelAux` recurses
structurally on `fuel`, compiled via `Nat.brecOn` / `Nat.rec` +
`Nat.below`. Our kernel walks that recursion chain (a linearly-growing set
of distinct `Nat.rec` reductions), materializing `Nat.below`
course-of-values structure real Lean never forces. `cancelAux` returns
early when its polynomial lists are empty, so real Lean forces `below`
only a few levels deep; our kernel forces it to full `fuel` depth at some
site not yet identified.

**Ruled out by measurement** (from the migration findings, carried
forward): smart unfolding (elaborator, not kernel); a memoization bug
(`max_repeats = 5` — a linear walk, not exponential recomputation);
transient-retention alone (real Lean does far fewer reductions — it
truncates, it doesn't "walk + free").

## Goal

Remove the divergence so `mise run check:stdlib` completes under a 32 GiB
peak-RSS watchdog, **verdict-identical** to the pinned Lean. This is a
reduction optimization (force-order / laziness), not a semantics change:
verdict-preserving by construction.

## Scope

**In scope**
- A bounded diagnosis spike that pins the eager-force site to a
  `tc.rs` file:line and selects the fix branch.
- A spike-selected, verdict-preserving reduction fix in `leanr_kernel`.
- The sweep acceptance harness (`check:stdlib` under a memory watchdog)
  and a residual-divergence policy.

**Out of scope**
- Any semantics change or new verdict.
- The term-bank representation (settled in the migration).
- Elaborator-side machinery (`smartUnfolding` / `_sunfold`) — already
  ruled out; not in the kernel.

**Hard constraints (inherited)**
- `leanr_kernel` depends on no workspace crate; no new external deps; no
  `unsafe`.
- Oracle discipline: the fix cites the exact Lean source lines it mirrors
  and states the invariant it preserves.
- No verdict drift: dual-checker differential path + existing
  fixture/property suites stay green.
- `.olean`-derived values remain untrusted (no panics on attacker data,
  bounded recursion via the existing guard).

## Design

The fix is spike-gated: we cannot design the exact short-circuit without
pinning the divergence to a line. The design therefore front-loads a
bounded diagnosis spike, enumerates the candidate fix branches, and gives
the criterion that routes the spike's finding to a branch.

### Component 1 — Diagnosis spike (plan step 1)

**Deliverable:** the eager-force site pinned to a `tc.rs` file:line, with
a trace, plus a written selection verdict (F1 vs F2), committed as a
findings note.

- **(a) Instrument the real reproducer.** Add a compile-gated
  (feature/env) step-counter/trace in `whnf_core` / `reduce_recursor`,
  keyed by `(callee symbol, major head node-kind)`. Run the real
  `_proof_3` (isolated via the CLI's per-declaration path) under the
  watchdog until the ~1M-distinct-major site is identified. Cross-check
  node-kinds: `Nat.rec` vs `Nat.below` vs `brecOn` unfolding. This is the
  only confirmed reproducer, so we instrument *it*, not a guess.
- **(b) `cancelAux`-shaped synthetic fixture.** Hand-reconstruct the shape
  that matters — recursion whose body reads `below` for its recursive
  call, base case returns early on empty-list data — **not** the naive
  `loop fuel xs`, which the migration findings showed does not reproduce.
  If it reproduces, it becomes the millisecond-scale iteration harness for
  the fix. If it does not, record the delta (context-sensitivity in the
  elaborated term) and rely on the real reproducer.

**Exit criterion:** a one-paragraph written mechanism + the file:line that
deterministically routes to F1 or F2. Time-boxed; if (a) pins the site but
(b) will not reduce, that is an acceptable exit.

### Component 2 — Fix branch (spike selects exactly one)

Leading hypothesis: real Lean is simply **lazier** than us — no exotic
short-circuit — so F1 is the default.

- **F1 — restore laziness at the force site (default).** Stop forcing the
  recursive `Nat.rec` / `below` argument where Lean keeps it a thunk.
  Candidate sites: how the `below` minor-premise argument is built in
  recursor reduction; an `infer_type` / `is_def_eq` that over-normalizes.
  Oracle-anchored to Lean's `whnf_core`; smallest TCB delta.
- **F2 — targeted `Nat.below` / `brecOn` short-circuit (fallback).** If
  materializing the below tower is intrinsic, reduce it to yield
  projections on demand without building full depth. Larger TCB surface;
  taken only if the spike rules out F1.
- **F3 — documented dead branch.** Extra memoization; ruled out up front
  by `max_repeats = 5` (linear walk, not recomputation). Recorded so the
  plan does not rediscover it.

**Selection criterion:** a general over-force in shared whnf/`is_def_eq`
machinery → F1; an intrinsic below-tower materialization → F2. Whichever
wins cites the exact oracle lines it mirrors and states the preserved
invariant (reduction *result* unchanged; only force-order / laziness
changes).

### Component 3 — Guardrails

- **Verdict preservation.** Dual-checker differential path + existing
  fixture/property suites green. A new fixture asserts `_proof_3` (and the
  synthetic case, if it reproduces) now checks with the correct verdict.
- **Sweep acceptance.** `mise run check:stdlib` under a 32 GiB RSS
  watchdog wrapper. **Residual-divergence policy:** a *same-class* blowup
  elsewhere must be covered by the fix; a *new-class* blowup is logged as
  a scoped follow-up (surfaced, never silently absorbed), so the sweep's
  completion is honest.

## Testing

Tiers, fastest first:

1. Synthetic unit fixture (milliseconds — if the spike's (b) reproduces).
2. `_proof_3` regression fixture.
3. Canary: `leanr check Init.Data.Char.Ordinal` (226-module closure) under
   the watchdog.
4. Full `mise run check:stdlib` under the 32 GiB watchdog — the
   acceptance gate.

## Risks

- **Spike (b) may not reproduce.** Mitigated: rely on the instrumented
  real reproducer; (b) is an accelerator, not a prerequisite.
- **Full stdlib may surface a different divergence class.** Mitigated by
  the residual-divergence policy — scope it, do not absorb it.
- **TCB change.** Mitigated by oracle anchoring + the verdict gate before
  merge; F1 preferred precisely because it is the smallest TCB delta.

## Acceptance

- The eager-force site is pinned and documented.
- `_proof_3` checks under a sane memory/time budget with the correct
  verdict.
- Dual-checker + fixture/property suites green (no verdict drift).
- `mise run check:stdlib` completes under a 32 GiB peak-RSS watchdog;
  any residual divergence is a logged, scoped follow-up.
