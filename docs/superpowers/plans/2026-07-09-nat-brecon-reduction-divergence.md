# Nat.brecOn / Nat.below reduction-divergence fix (Result B) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove the pre-existing kernel-reduction divergence (Result B) so `mise run check:stdlib` completes under a 32 GiB peak-RSS watchdog, verdict-identical to the pinned Lean.

**Architecture:** Front-load a bounded diagnosis spike (feature-gated reduction trace + best-effort synthetic reproducer) to pin the eager-force site in `crates/leanr_kernel/src/tc.rs` to a line, then apply a spike-selected, verdict-preserving reduction fix. A memory-watchdog harness both makes the spike safe to run and defines the acceptance gate.

**Tech Stack:** Rust (`leanr_kernel`, no workspace deps, no `unsafe`); the pinned Lean toolchain via `mise run elan:bootstrap`; POSIX shell for the watchdog; `cargo test` / `cargo run` driven by mise tasks.

## Global Constraints

- `leanr_kernel` depends on no workspace crate; no new external deps; no `unsafe`. (Trace instrumentation is `#[cfg(feature = "trace-reductions")]` — off by default, so the shipped TCB is unchanged.)
- Oracle discipline: any algorithmic change cites the exact Lean source line(s) it mirrors and states the invariant it preserves.
- No verdict drift: the dual-checker differential path and existing kernel fixture/property suites stay green.
- `.olean`-derived values remain untrusted: no panics on attacker data; attacker-depth recursion stays behind the existing `RecGuard`.
- Lint gate (`mise run lint`) per commit; conventional-commit prefixes.
- Toolchain-dependent tasks run locally (`mise run elan:bootstrap` first); CI has no Lean.

---

### Task 1: Feature-gated reduction trace

**Files:**
- Modify: `crates/leanr_kernel/Cargo.toml` (add `[features]` with `trace-reductions`)
- Create: `crates/leanr_kernel/src/tc/trace.rs`
- Modify: `crates/leanr_kernel/src/tc.rs` (declare `mod trace`; record at `whnf_core` recursor-fire site ~`tc.rs:1504` and in `inductive_reduce_rec` ~`tc.rs:1799`)
- Test: `crates/leanr_kernel/src/tc/tests.rs`

**Interfaces:**
- Produces: `trace::record(callee: &str, major_kind: &'static str)`, `trace::snapshot() -> Vec<((String, &'static str), u64)>` (sorted desc by count), `trace::reset()`, and `trace::total() -> u64`. All are no-ops compiled to empty bodies when the feature is off. Under the feature they read/write a `thread_local!` `RefCell<HashMap<(String, &'static str), u64>>`.

- [ ] **Step 1: Add the feature flag**

In `crates/leanr_kernel/Cargo.toml`, after `[dependencies]`:

```toml
[features]
# Off by default: gates reduction-step instrumentation used only by the
# Result-B diagnosis spike. The shipped TCB compiles with this off.
trace-reductions = []
```

- [ ] **Step 2: Write the trace module**

Create `crates/leanr_kernel/src/tc/trace.rs`:

```rust
//! Feature-gated reduction-step tally for the Result-B diagnosis spike.
//! Off by default (`trace-reductions`), so the shipped kernel is unchanged.

#[cfg(feature = "trace-reductions")]
mod imp {
    use std::cell::RefCell;
    use std::collections::HashMap;

    thread_local! {
        static TALLY: RefCell<HashMap<(String, &'static str), u64>> =
            RefCell::new(HashMap::new());
    }

    pub fn record(callee: &str, major_kind: &'static str) {
        TALLY.with(|t| {
            *t.borrow_mut()
                .entry((callee.to_string(), major_kind))
                .or_insert(0) += 1;
        });
    }

    pub fn reset() {
        TALLY.with(|t| t.borrow_mut().clear());
    }

    pub fn total() -> u64 {
        TALLY.with(|t| t.borrow().values().sum())
    }

    pub fn snapshot() -> Vec<((String, &'static str), u64)> {
        TALLY.with(|t| {
            let mut v: Vec<_> = t.borrow().iter().map(|(k, &c)| (k.clone(), c)).collect();
            v.sort_by(|a, b| b.1.cmp(&a.1));
            v
        })
    }
}

#[cfg(not(feature = "trace-reductions"))]
mod imp {
    #[inline(always)]
    pub fn record(_callee: &str, _major_kind: &'static str) {}
    #[inline(always)]
    pub fn reset() {}
    #[inline(always)]
    pub fn total() -> u64 {
        0
    }
    #[inline(always)]
    pub fn snapshot() -> Vec<((String, &'static str), u64)> {
        Vec::new()
    }
}

pub use imp::{record, reset, snapshot, total};
```

- [ ] **Step 3: Wire the trace into the reduction sites**

In `crates/leanr_kernel/src/tc.rs`, add near the other `mod` declarations at the top of the file:

```rust
pub(crate) mod trace;
```

In `inductive_reduce_rec` (`tc.rs`), immediately after the major is fully reduced to constructor form and the rule is selected — right after the `let major_args = self.get_app_args(major);` line (~`tc.rs:1813`) — insert:

```rust
{
    let callee = self.name_to_string(rec_name);
    let kind = match self.node(major) {
        Node::App { .. } => "app-ctor",
        Node::Const { .. } => "const-ctor",
        Node::LitNat { .. } => "lit-nat",
        _ => "other",
    };
    trace::record(&callee, kind);
}
```

Use whatever the crate's existing "NameId → String" helper is (search for how errors render names, e.g. `self.view` name rendering or a `name_to_string`/`display_name` helper); if none exists, format the `NameId` numerically as `format!("name#{:?}", rec_name)` — the site identity, not the pretty name, is what the spike needs.

- [ ] **Step 4: Write the failing test**

In `crates/leanr_kernel/src/tc/tests.rs`, add (gated so it only runs under the feature):

```rust
#[cfg(feature = "trace-reductions")]
#[test]
fn trace_counts_nat_rec_reductions() {
    use crate::tc::trace;
    trace::reset();
    let env = mini::env();
    let mut scratch = Store::scratch();
    let (cc, z, s) = (
        mini::cst("C", vec![]),
        mini::cst("z", vec![]),
        mini::cst("s", vec![]),
    );
    let natrec = mini::cstn(nm2("Nat", "rec"), vec![zero_lvl()]);
    // whnf drives Nat.rec on the literal 3 down to zero: 3 firings.
    let e = mini::appn(natrec, vec![cc, z, s, lit_nat(3)]);
    let _ = whnf(&env, &mut scratch, &e).unwrap();
    assert!(trace::total() >= 3, "snapshot: {:?}", trace::snapshot());
}
```

- [ ] **Step 5: Run the test — expect FAIL first, then PASS**

Run:

```bash
cargo test -p leanr_kernel --features trace-reductions trace_counts_nat_rec_reductions -- --nocapture
```

Expected: PASS after Steps 2–3 are in place. If it fails with a count of 0, the `trace::record` call site was placed on a branch the literal-major path doesn't reach — move it to just before rule selection so it fires once per constructor-layer reduction.

- [ ] **Step 6: Confirm the default build is untouched**

Run:

```bash
cargo build -p leanr_kernel && cargo test -p leanr_kernel
```

Expected: builds and the existing suite passes with the feature OFF (the trace calls compile to empty inlined bodies).

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_kernel/Cargo.toml crates/leanr_kernel/src/tc/trace.rs crates/leanr_kernel/src/tc.rs crates/leanr_kernel/src/tc/tests.rs
git commit -m "feat(kernel): feature-gated reduction-step trace for Result-B spike"
```

---

### Task 2: Memory-watchdog harness + watched sweep task

**Files:**
- Create: `scripts/mem-watchdog.sh`
- Modify: `mise.toml` (add `check:stdlib:watched`)

**Interfaces:**
- Produces: `scripts/mem-watchdog.sh <max_gib> <cmd> [args...]` — runs `<cmd>` in the background, polls its (and descendants') RSS every second via `/proc`, and SIGKILLs the tree if RSS exceeds `<max_gib>` GiB. Exit code: the child's on normal exit, or `137` when the watchdog kills it. Prints peak observed RSS to stderr on exit.
- Produces: mise task `check:stdlib:watched` — `check:stdlib` wrapped in the 32 GiB watchdog.

- [ ] **Step 1: Write the watchdog script**

Create `scripts/mem-watchdog.sh`:

```sh
#!/bin/sh
# Run a command under an RSS ceiling. Polls /proc once a second and
# SIGKILLs the whole process group if summed RSS exceeds <max_gib> GiB.
# Rust reserves large *virtual* memory, so `ulimit -v` is unusable here;
# we watch resident set instead. Exit 137 == killed for exceeding the cap.
set -eu

max_gib="$1"; shift
max_kib=$((max_gib * 1024 * 1024))

setsid "$@" &
child=$!
pgid=$child

peak_kib=0
status=0
while kill -0 "$child" 2>/dev/null; do
    # Sum VmRSS (kB) across the process group.
    rss_kib=$(ps -o rss= -g "$pgid" 2>/dev/null | awk '{s+=$1} END {print s+0}')
    [ "$rss_kib" -gt "$peak_kib" ] && peak_kib=$rss_kib
    if [ "$rss_kib" -gt "$max_kib" ]; then
        echo "mem-watchdog: RSS ${rss_kib} kB > cap ${max_kib} kB — killing" >&2
        kill -KILL -"$pgid" 2>/dev/null || true
        wait "$child" 2>/dev/null || true
        echo "mem-watchdog: peak RSS $((peak_kib / 1024 / 1024)) GiB (${peak_kib} kB)" >&2
        exit 137
    fi
    sleep 1
done
wait "$child" || status=$?
echo "mem-watchdog: peak RSS $((peak_kib / 1024 / 1024)) GiB (${peak_kib} kB)" >&2
exit "$status"
```

- [ ] **Step 2: Make it executable**

```bash
chmod +x scripts/mem-watchdog.sh
```

- [ ] **Step 3: Test the watchdog kills a hog and reports peak**

Run (a deliberate 2 GiB allocation under a 1 GiB cap must be killed):

```bash
scripts/mem-watchdog.sh 1 sh -c 'head -c 2000000000 /dev/zero | tail -c 1 >/dev/null; sleep 5'; echo "exit=$?"
```

Expected: stderr shows `killing` and a `peak RSS` line; `exit=137`.

- [ ] **Step 4: Test the watchdog passes a well-behaved command through**

Run:

```bash
scripts/mem-watchdog.sh 1 sh -c 'echo hello; exit 3'; echo "exit=$?"
```

Expected: prints `hello`, a `peak RSS` line on stderr, and `exit=3` (child's own status is preserved).

- [ ] **Step 5: Add the watched mise task**

In `mise.toml`, after the `check:stdlib` task:

```toml
[tasks."check:stdlib:watched"]
description = "check:stdlib under a 32 GiB RSS watchdog (Result-B acceptance gate; local, needs toolchain)"
depends = ["elan:bootstrap"]
run = "scripts/mem-watchdog.sh 32 sh -c 'cargo run --release -p leanr_cli -- check --all --path \"$(lean --print-libdir)\"'"
```

- [ ] **Step 6: Commit**

```bash
git add scripts/mem-watchdog.sh mise.toml
git commit -m "feat: RSS memory-watchdog harness and watched stdlib sweep task"
```

---

### Task 3: Diagnosis spike — pin the eager-force site and select the fix branch

**Files:**
- Create: `docs/superpowers/specs/2026-07-09-nat-brecon-reduction-divergence-findings.md`
- Test (best-effort): `crates/leanr_kernel/src/tc/tests.rs`

**Interfaces:**
- Consumes: `trace::snapshot`/`trace::total` (Task 1); `scripts/mem-watchdog.sh` (Task 2).
- Produces: a committed findings note stating (1) the reduction site pinned to `tc.rs:LINE`, (2) the offending `(callee, major_kind)` and its count, (3) a one-paragraph mechanism, (4) the branch verdict: **F1** (restore laziness in shared whnf/`is_def_eq`) or **F2** (targeted `Nat.below`/`brecOn` short-circuit).

This is a diagnosis task: its deliverable is a document + a verdict, not production code. Time-box the synthetic-reproducer sub-step; the real reproducer is the source of truth.

- [ ] **Step 1: Bootstrap the toolchain**

```bash
mise run elan:bootstrap
```

Expected: `lean --print-libdir` resolves (used by the sweep tasks).

- [ ] **Step 2 (a — the confirmed reproducer): trace the real `_proof_3`**

The CLI checks whole modules and isolates each declaration internally, so checking the module hits `_proof_3`. Run it under the watchdog with the trace on, capping RSS low enough to abort before OOM (5 GiB — far above the ~0.55 GiB healthy transient, far below the ~25 GiB blowup):

```bash
LEANR_TRACE_DUMP=1 scripts/mem-watchdog.sh 5 \
  cargo run --release --features leanr_kernel/trace-reductions -p leanr_cli -- \
  check Init.Data.Char.Ordinal 2>&1 | tee /tmp/proof3-trace.log
```

If the trace tally is only surfaced from library code (not the CLI), instead run it as a `#[cfg(feature = "trace-reductions")] #[ignore]` integration test that calls `trace::reset()`, checks the module, and on catch/timeout prints `trace::snapshot()` — add that test here if the CLI path cannot emit the snapshot. Either way, capture the `(callee, major_kind)` with the dominant count (expected: a `Nat.rec` / `Nat.below` / `brecOn`-family callee with a count in the millions).

- [ ] **Step 3: Read the dominant site off the tally and locate it in `tc.rs`**

From the snapshot, identify the callee driving the linear walk and map it to the exact `tc.rs` line where that reduction is forced (the recursor-fire path `tc.rs:1504` / `inductive_reduce_rec` `tc.rs:1799`, or a `reduce_proj` / `is_def_eq` / `infer_type` call that WHNFs the `below` argument). Confirm the walk is linear (distinct majors growing, low repeat count) — consistent with the migration finding's `max_repeats = 5`.

- [ ] **Step 4 (b — best-effort accelerator): attempt a synthetic reproducer**

Try to reproduce the blowup as a fast unit test. The shape that matters (per the migration finding) is recursion whose body reads its `below` course-of-values value for the recursive call, with a base case that returns *early on empty-list data* — **not** the naive `loop fuel xs`, which does not reproduce. In `crates/leanr_kernel/src/tc/tests.rs`:

```rust
#[cfg(feature = "trace-reductions")]
#[test]
#[ignore] // spike accelerator; promoted to a gated regression only if it reproduces
fn synthetic_cancel_aux_shape_blows_up() {
    use crate::tc::trace;
    trace::reset();
    // Build (in an env extended with Nat.below / Nat.brecOn / PProd) a
    // `cancelAux`-shaped term over a large literal fuel whose body reads
    // `below` for its recursive call and returns early on an empty list.
    // Assert the pathology via step count, not wall-clock:
    let env = /* mini env extended with brecOn/below/PProd */ mini::env();
    let mut scratch = Store::scratch();
    let e = /* cancelAux-shaped application over fuel = 100_000 */ unimplemented!();
    let _ = whnf(&env, &mut scratch, &e);
    // BEFORE the fix, the linear walk makes this explode:
    assert!(trace::total() > 10_000, "did not reproduce: {}", trace::total());
}
```

If constructing the term in the mini env proves infeasible within the time-box (it lacks `brecOn`/`below`/`PProd`), delete this test, note "synthetic reproducer not achieved; real `_proof_3` is the iteration harness" in the findings, and proceed. Do **not** let this block the task.

- [ ] **Step 5: Write and commit the findings note**

Create `docs/superpowers/specs/2026-07-09-nat-brecon-reduction-divergence-findings.md` with: the pinned `tc.rs:LINE`, the `(callee, major_kind, count)`, the one-paragraph mechanism, whether the synthetic reproducer was achieved, and the **F1/F2 verdict** with its one-line justification (general over-force in shared machinery → F1; intrinsic below-tower materialization → F2).

```bash
git add docs/superpowers/specs/2026-07-09-nat-brecon-reduction-divergence-findings.md crates/leanr_kernel/src/tc/tests.rs
git commit -m "docs(kernel): Result-B spike findings — pinned force site and fix-branch verdict"
```

---

### Task 4: Apply the spike-selected fix and hold the verdict-preservation gate

**Files:**
- Modify: `crates/leanr_kernel/src/tc.rs` (the site pinned in Task 3)
- Test: `crates/leanr_kernel/src/tc/tests.rs` (regression); the toolchain canary for `_proof_3`

**Interfaces:**
- Consumes: the Task-3 findings note (pinned line + F1/F2 verdict), the Task-1 trace, the Task-2 watchdog.
- Produces: a verdict-preserving reduction change; `_proof_3` and the module `Init.Data.Char.Ordinal` check under the watchdog with the correct verdict.

The exact diff is authored from Task 3's pinned site. Two shapes, one selected by the findings verdict:
- **F1 — restore laziness:** stop forcing the recursive `Nat.rec` / `below` argument at the pinned site where Lean keeps it a thunk; leave the projection to force only what it reads. Cite the Lean `whnf_core` / `inductive` line(s) mirrored.
- **F2 — targeted short-circuit:** special-case `Nat.below` / `Nat.brecOn` reduction to yield projections on demand without materializing the full-depth tower. Cite the mirrored Lean line(s).
Either way, the invariant stated in the code comment is: *reduction result is unchanged; only force-order / laziness changes.*

- [ ] **Step 1: Write the failing regression test (step-budget, feature-gated)**

If Task 3 achieved a synthetic reproducer, un-`#[ignore]` it and flip its assertion to the post-fix budget:

```rust
#[cfg(feature = "trace-reductions")]
#[test]
fn synthetic_cancel_aux_shape_is_bounded() {
    use crate::tc::trace;
    trace::reset();
    let env = mini::env(); // extended env from Task 3
    let mut scratch = Store::scratch();
    let e = /* same cancelAux-shaped term over fuel = 100_000 as Task 3 */ unimplemented!();
    let _ = whnf(&env, &mut scratch, &e).unwrap();
    // After the fix, force-order tracks the (empty) data, not the fuel:
    assert!(trace::total() < 1_000, "still walking: {}", trace::total());
}
```

If no synthetic reproducer exists, the failing test is the toolchain canary in Step 4 — record here that the regression gate is the canary, and skip to Step 2.

- [ ] **Step 2: Run it to confirm RED**

```bash
cargo test -p leanr_kernel --features trace-reductions synthetic_cancel_aux_shape_is_bounded -- --nocapture
```

Expected: FAIL (pre-fix count far exceeds the budget). Skip if the gate is the canary.

- [ ] **Step 3: Apply the fix at the pinned site**

Edit `crates/leanr_kernel/src/tc.rs` at the Task-3 line per the selected branch (F1 or F2). Add the oracle citation comment and the invariant line. Keep the change minimal and local to the pinned site.

- [ ] **Step 4: Confirm the fix — synthetic budget + real canary under the watchdog**

Synthetic (if present):

```bash
cargo test -p leanr_kernel --features trace-reductions synthetic_cancel_aux_shape_is_bounded -- --nocapture
```

Expected: PASS.

Real canary (the 226-module closure that contains `_proof_3`), release build, under the watchdog:

```bash
scripts/mem-watchdog.sh 32 sh -c 'cargo run --release -p leanr_cli -- check Init.Data.Char.Ordinal'
```

Expected: exits 0 (all declarations check, correct verdicts); watchdog reports peak RSS well under 32 GiB (target: order ~1 GiB, not ~25 GiB).

- [ ] **Step 5: Hold the verdict-preservation gate — no drift**

Run the full kernel suite and the differential/dual-checker fixtures (feature OFF, so the shipped path is exercised):

```bash
cargo test -p leanr_kernel && mise run test && mise run lint
```

Expected: all green — the fix changed force-order, not any verdict. If any fixture flips verdict, the change is not verdict-preserving: revert and re-derive the branch.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_kernel/src/tc.rs crates/leanr_kernel/src/tc/tests.rs
git commit -m "fix(kernel): bound Nat.brecOn/Nat.below reduction to forced course-of-values prefix (Result B)"
```

---

### Task 5: Full-stdlib acceptance sweep and residual triage

**Files:**
- Modify: `docs/superpowers/specs/2026-07-06-term-bank-kernel-migration-design.md` (record the sweep result, closing the Result-B disposition) and/or the Task-3 findings note.

**Interfaces:**
- Consumes: `check:stdlib:watched` (Task 2), the fix (Task 4).
- Produces: a recorded acceptance result — sweep completes under 32 GiB, or a scoped, logged follow-up for any residual divergence.

- [ ] **Step 1: Run the full sweep under the watchdog**

```bash
mise run check:stdlib:watched 2>&1 | tee /tmp/stdlib-sweep.log
```

Expected: exits 0; the watchdog's `peak RSS` line is under 32 GiB.

- [ ] **Step 2: Triage per the residual-divergence policy**

If the sweep completes under budget: done. If the watchdog kills on a *different* declaration:
- **Same class** (another `Nat.brecOn` / `below`-over-large-fuel walk — confirm by re-running that module under the trace feature as in Task 3 Step 2): the fix should cover it; if it does not, return to Task 4 and generalize the pinned-site change.
- **New class** (a different reduction pattern): log it as a scoped follow-up with the declaration name and its trace snapshot — surfaced, never silently absorbed. The sweep's honest status is "completes except for <logged item>."

- [ ] **Step 3: Record the acceptance result**

Append the outcome (peak RSS, pass/logged-residual) to the migration design's Result-B disposition so the phase-2 acceptance is closed or explicitly carries a named follow-up.

```bash
git add docs/superpowers/specs/2026-07-06-term-bank-kernel-migration-design.md docs/superpowers/specs/2026-07-09-nat-brecon-reduction-divergence-findings.md
git commit -m "docs: Result-B acceptance — full-stdlib sweep under 32 GiB watchdog"
```

---

## Self-Review

**Spec coverage** (design → task):
- Diagnosis spike (a instrument + b synthetic) → Task 1 (trace), Task 3 (run + synthetic + findings). ✓
- F1/F2/F3 branch selection → Task 3 verdict, Task 4 applies F1 or F2 (F3 documented-dead is carried in the design; no task needed by design). ✓
- Verdict-preservation guardrail → Task 4 Step 5. ✓
- Sweep acceptance + residual policy → Task 2 (harness), Task 5 (run + triage). ✓
- Testing tiers (synthetic → canary → full sweep) → Task 4 Steps 4, Task 5 Step 1. ✓

**Placeholder scan:** The two `unimplemented!()` terms in Tasks 3/4 are the synthetic reproducer's core, which is genuinely spike-discovered (the `mini` env lacks `brecOn`/`below`/`PProd`); each is guarded by an explicit "if infeasible, delete and rely on the canary" instruction, so no task is blocked on it. The fix diff in Task 4 is intentionally branch-shaped because it is spike-selected — the exact test gates it must satisfy are concrete. These are diagnosis-driven, not lazy placeholders.

**Type consistency:** `trace::record/reset/total/snapshot` signatures are identical across Tasks 1, 3, 4. `scripts/mem-watchdog.sh <max_gib> <cmd...>` and its exit-137 contract are used consistently in Tasks 2–5. `check:stdlib:watched` defined in Task 2, invoked in Task 5.
