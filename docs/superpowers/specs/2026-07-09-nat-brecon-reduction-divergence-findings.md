# Nat.brecOn / Nat.below reduction-divergence — diagnosis findings (Result B)

**Status:** findings (diagnosis spike complete)
**Date:** 2026-07-09
**Design:** `2026-07-09-nat-brecon-reduction-divergence-design.md`
**Branch:** `nat-brecon-reduction-divergence`
**Reproducer:** `leanr check Init.Data.Char.Ordinal` (isolates
`_private.Init.Data.Char.Ordinal.0.Char.ofOrdinal._proof_3`), run under
`scripts/mem-watchdog.sh` with `--features leanr_kernel/trace-reductions`.

## TL;DR

- **Pinned eager-force site:** the `lazy_delta_reduction` loop at
  **`tc.rs:2713`** (fn at `tc.rs:2708`), whose per-iteration force is
  **`unfold_and_whnf` at `tc.rs:2700`** (its
  `whnf_core(u, false, /*cheap_proj=*/true)` at `tc.rs:2702`). Recursors
  fire beneath it at `whnf_core`'s recursor dispatch **`tc.rs:1506`** →
  `reduce_recursor` (`tc.rs:1748`) → `inductive_reduce_rec`
  (`tc.rs:1752`).
- **Offending `(callee, major_kind, count)`:** `(Nat.rec, "app-ctor",
  ≥ 6_164_429 and climbing linearly)`. It splits ~2:1 into two
  co-descending walks: a `Nat.beq` Bool-valued recursion (~2/3) and its
  `brecOn` `PProd` course-of-values tower (~1/3). Every other recursor is
  flat (List.rec ~47k, Int.rec ~39k, …).
- **Verdict: F1** — restore the native/lazy short-circuit in the shared
  whnf / `is_def_eq` machinery. The `Nat.below` tower is *not* intrinsic
  here; it is only walked because the native `Nat.beq`/`Nat.ble`
  reduction is bypassed on this path.

## What the trace showed (real `_proof_3`)

Under a 5 GiB RSS watchdog with the feature-gated tally, the periodic
stderr dump (survives the SIGKILL) reported one clearly dominant site,
growing monotonically while all others stayed flat:

```
total recursor fires = 6291456
     6164429  Nat.rec  (app-ctor)      <-- dominant, climbing linearly
       47021  List.rec (app-ctor)      <-- flat
       39013  Int.rec  (app-ctor)      <-- flat
       11863  Option.rec (app-ctor)    <-- flat
        ...
```

This is a **linear** walk (a monotonically growing single site, other
recursors frozen), consistent with the migration finding's
`max_repeats = 5` — not exponential recomputation (rules out F3).

Finer gated instrumentation (motive classification, deep-sample shape
rendering, a `guard_depth` probe, a per-`unfold_and_whnf` fire counter,
and one `std::backtrace` capture — all since reverted) established:

1. **Two Nat.rec walks, descending in lockstep.** Classifying the
   recursor motive split the `Nat.rec (app-ctor)` fires into
   `motive=PProd` (~1/3, the `brecOn` value tower `Nat.rec (motive := λt.
   PProd (C t) (Nat.below C t))`) and `motive=app-lam` (~2/3, a
   Bool-valued recursion `Nat.rec (motive := λn. … Bool …) … (Nat.succ
   <lit>)`).

2. **It is a LOOP, not deep Rust recursion.** At two samples 300 000
   fires apart the `guarded()` recursion depth was **constant at 16**.
   A deep whnf/recursor Rust recursion would have shown depth growing
   into the hundreds of thousands (the `MAX_REC_DEPTH` cap is 1e6). The
   captured backtrace confirmed the driver frame is a single
   `lazy_delta_reduction` `loop {}` at `tc.rs:2713`:

   ```
   inductive_reduce_rec (record site)
   reduce_recursor           tc.rs:1748
   whnf_core (recursor fire)  tc.rs:1506
   whnf_core (beta)           tc.rs:1504
   unfold_and_whnf            tc.rs:2702
   lazy_delta_reduction_step  tc.rs:2642
   lazy_delta_reduction  (LOOP) tc.rs:2713
   is_def_eq_core             tc.rs:2768
   … is_def_eq / infer_app / infer_type_core (deep proof term) …
   ```

3. **Each iteration fires only ~4 recursors.** No single
   `unfold_and_whnf` call fired > 1000 recursors. So a *single* whnf does
   **not** materialize the tower in one shot; the `lazy_delta_reduction`
   loop iterates ~1e6 times, each unfolding one `Nat.below` level.

4. **The walked term is `Nat.beq` in `brecOn` form.** Rendering the
   loop's in/out heads at the deep samples showed each iteration turning
   a `Nat.casesOn … <lit> …` into

   ```
   Nat.beq._f (Nat.succ <lit>) (Nat.rec λ.… … lit) <lit>
              ^operand           ^Nat.below tower    ^operand
   ```

   Both operands are **fvar-free** (`has_fvar = false`), and yet
   `reduce_nat` reports **not applicable** to this term — because the
   head is `Nat.beq._f` (the `brecOn`-compiled functional), not the
   `Nat.beq` const that `reduce_nat` keys on.

## Mechanism (one paragraph)

The `_proof_3` certificate (discharged by `grind`/`omega`, ultimately via
`Nat.Linear.Poly.cancel`) requires the kernel to decide equality of two
large `Nat` values via `Nat.beq`. `Nat.beq` is compiled with structural
recursion through `Nat.brecOn` / `Nat.rec` + `Nat.below`. Real Lean's
kernel evaluates `Nat.beq a b` on literal-reducible operands **natively**
(GMP, O(1)) and never forces the `Nat.below` course-of-values tower. Our
kernel's native short-circuit (`reduce_nat`, `tc.rs:2005`, which handles
`"beq"`/`"ble"` at `tc.rs:2094-2095`) is only reachable from the
top-level `whnf` (`tc.rs:1420`) and from `lazy_delta_reduction`'s
`!has_fvar` branch (`tc.rs:2718`, calls at `tc.rs:2719`/`tc.rs:2722`) —
**both key on the `Nat.beq` const**.
On the `is_def_eq` path the term is reduced with `whnf_core` (which never
consults `reduce_nat`) and, once one `lazy_delta_reduction_step` delta-
unfolds `Nat.beq` into its `Nat.beq._f`/`brecOn` body, the native
fast-path can no longer match it. From there `lazy_delta_reduction`
(`tc.rs:2713`) walks the `Nat.below` tower one level per iteration —
~1e6 iterations, ~4 `Nat.rec` fires each — blowing the transient from
~0.55 GiB to ~25 GiB and never finishing. Nothing forces the tower
except this bypass; the walk is a lockstep descent of the value recursion
(`motive=app-lam`) and its below tower (`motive=PProd`).

## Synthetic reproducer

**Not achieved (time-boxed, as anticipated).** Reproducing the pathology
in a fast unit test requires building `Nat.beq`'s `brecOn` /`Nat.below` /
`PProd` compiled form (and driving it through `is_def_eq` /
`lazy_delta_reduction`) in the kernel's `mini::env()`, which has none of
those constants. The naive `loop fuel xs` shape does not reproduce (per
the migration findings), and hand-encoding the course-of-values term was
out of the time-box. The real `_proof_3` (isolated by
`leanr check Init.Data.Char.Ordinal`) is the iteration harness for
Task 4; the gated tally + periodic dump make it observable.

## Verdict: F1 (restore laziness / native short-circuit in shared machinery)

**Justification (per the design's selection criterion):** the over-force
lives in **shared whnf / `is_def_eq` machinery** —
`lazy_delta_reduction` (`tc.rs:2713`) + `unfold_and_whnf` (`tc.rs:2700`)
walking a `Nat`-native operation's `brecOn` body — not in a dedicated
`Nat.below` reducer. The below tower is materialized *only because* the
native `Nat.beq`/`Nat.ble` reduction is not applied on this path; once it
is, the tower is never forced. That is F1 by definition ("a general
over-force in shared whnf/`is_def_eq` machinery → F1"; "an `is_def_eq`
that over-normalizes"), and it is the smallest-TCB-delta fix. F2 (a
bespoke `Nat.below`/`brecOn` short-circuit) is **not** indicated: the
below-tower materialization is not intrinsic. F3 (extra memoization) is
ruled out by the linear (`max_repeats = 5`) walk.

**Oracle anchor for Task 4.** The reduction that must reach this path is
Lean's native `Nat` reduction (`src/kernel/type_checker.cpp` `reduce_nat`,
mirrored here at `tc.rs:2005`), applied to `Nat.beq`/`Nat.ble` before the
`brecOn` body is walked. Invariant preserved: the *reduction result* is
unchanged (`Nat.beq a b` and its `brecOn` unfolding are definitionally
the bool); only force-order / laziness changes — verdict-preserving by
construction.

**Actionable direction (Task 4 designs the exact insertion).** Ensure the
native `Nat.beq`/`Nat.ble` reduction fires on the `is_def_eq` reduction
path so a `Nat.beq`/`Nat.ble` application whose operands reduce to
literals is never delta-unfolded into its walkable `._f`/`brecOn` form.
Candidate sites, oracle-cross-checked: (i) have `whnf_core`'s
non-lambda app branch consult `reduce_nat` (as Lean's whnf does) so the
`Nat.beq`-const form is collapsed before `unfold_definition` ever sees
it; and/or (ii) guard `lazy_delta_reduction_step` / `unfold_definition`
so a `Nat.beq`/`Nat.ble` const with literal-reducible, fvar-free operands
is natively reduced rather than delta-unfolded. **Residual to resolve in
Task 4:** the precise reason the *first* unfold escaped the existing
`reduce_nat` guards (`tc.rs:1420` / `tc.rs:2718`) — i.e., whether an
operand was not yet literal-reducible at that instant — which decides
between (i) and (ii). The site and branch (F1) are firm; only the exact
insertion point remains a fix-design choice.

## Instrumentation kept vs reverted

- **Kept (committed, gated `#[cfg(feature = "trace-reductions")]`, off by
  default → TCB byte-for-byte unchanged):** a periodic stderr dump in
  `crates/leanr_kernel/src/tc/trace.rs` (`record` dumps the running
  `total()` + top `snapshot()` entries every `1<<20` fires, plus a
  reusable `dump_stderr()`). This is what makes the OOM-then-SIGKILL run
  observable and is the iteration harness Task 4 will reuse.
- **Reverted (spike-only):** the motive classifier + second `record`
  call, the deep-sample shape renderer (`dbg_shape`), the `guard_depth`
  probe, the per-`unfold_and_whnf` fire counter, and the one-shot
  backtrace capture. `tc.rs` and `guard.rs` are back to their pre-spike
  state (`git diff` on both is empty).
