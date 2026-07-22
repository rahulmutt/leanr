# M4a plan 4 — typeclass synthesis: instance decode, discrimination tree, tabled resolution, and the nightly discovery sweep — design spec

Status: approved (brainstormed 2026-07-22)
Parent: [2026-07-20-m4a-meta-core-design.md](2026-07-20-m4a-meta-core-design.md)
Predecessor plan: [../plans/2026-07-21-m4a-defeq.md](../plans/2026-07-21-m4a-defeq.md) (plan 3 of 4, merged)

## Problem

Plans 1–3 of M4a are merged: `leanr_meta` has the transparency model,
the defeq `Config` and its cache key, the metavariable context, `whnf`,
`infer_type`, `is_def_eq` (assignment, lazy delta, the five
approximations, the transient/permanent cache), and the tier-1
`meta:fast` differential gate over purpose-built fixtures.

Nothing synthesizes. `synth_pending` is a stub that returns `false`
(`whnf.rs:1097`), the `Lean.Meta.instanceExtension` and
`defaultInstanceExtension` environment extensions are still opaque in
`leanr_olean`, and no discrimination tree exists. The consequences:

- Typeclass search answers "no instance" for every goal, so the
  instance table is effectively empty.
- `is_def_eq`'s stuck-on-instance path — the `IsDefEqStuck` channel and
  the `get_stuck_mvar` / `unfold_proj_inst_when_instances` seams — is
  exercised only in the degenerate direction (synthesis never makes
  progress, so `synth_pending` always reports no change).
- The tier-2 nightly discovery sweep cannot run: its synthesized
  `synthInstance` and mvar `is_def_eq` queries over real Mathlib terms
  have no engine to answer them.

This is plan 4 of 4, the final slice of M4a. It delivers `instances.rs`,
`synth.rs`, a from-scratch discrimination tree, the two olean-extension
decodes, `synth_pending`, and the `meta:nightly` sweep — completing the
`MetaM` core.

## Goal

`instances.rs` and `synth.rs` in `leanr_meta` delivering a
discrimination-tree-indexed instance table and tabled (Prolog-style)
resolution, with `synth_pending` wired into the whnf/defeq stuck paths,
agreeing with the oracle. Verified in two tiers mirroring the existing
split: a `meta:fast` regression gate over a committed synthesis fixture
corpus for the dev loop, and a `meta:nightly` discovery sweep over
Mathlib. `leanr_kernel` unmodified.

## Scope decisions (agreed in brainstorming)

- **Delivered as three PRs, not one.** Plan 4 spans four fairly
  independent layers — olean decode, a general discrimination tree, the
  instance table plus tabled engine plus `synth_pending`, and the
  nightly workflow. Landing them as one PR (as plan 3 did) would present
  the largest review surface in M4a with no internal seams. The split:

  - **PR-A — olean decode.** Typed decode of `instanceExtension` and
    `defaultInstanceExtension` in `leanr_olean`. No `leanr_meta`
    changes; independently testable against a committed fixture olean;
    follows the decode-lands-separately precedent (reducibility in plan
    1, matcher in plan 2).
  - **PR-B — engine + tier-1 gate.** `discr_tree.rs`, `instances.rs`,
    `synth.rs`, and `synth_pending`, gated by `meta:fast` extended with
    a committed synthesis fixture corpus.
  - **PR-C — `meta:nightly`.** The tier-2 discovery workflow, separate
    from `nightly-sweep.yml`.

  Each PR keeps every existing gate green.

- **The discrimination tree is general, transcribed from Lean's
  `DiscrTree`, not an instance-only minimal index.** Lean's `DiscrTree`
  is reused by typeclass instances, `simp`, `rw`, and `exact?`; the
  later M4 tactic slices will want exactly this structure. An
  instance-minimal version now would risk a rebuild and a second
  oracle-transcription pass when simp arrives. Building it general once,
  under the same oracle discipline that governs the rest of the crate,
  is the cheaper total path. It follows Lean's own layering: the trie
  and `Key` model are a standalone, reusable, MetaM-free data structure;
  only the *path computation* (which whnf's at reducible transparency)
  is MetaM-coupled.

- **Tabled resolution, not memoized backtracking** — settled by the
  parent spec and restated here because it is load-bearing. Generator
  nodes, consumer nodes, waiters, and an answer table; cyclic instance
  graphs terminate under tabling and diverge without it. This is a
  correctness difference, not a performance one.

- **A deterministic step counter, not `maxHeartbeats`** — the parent
  spec's deliberate divergence. Queries that come near any step or depth
  budget on either side are recorded and excluded from the gate rather
  than allowed to disagree.

- **`leanr_kernel` is not modified.** The instance and reducibility
  tables live in `leanr_meta` (fed by `leanr_olean` decode), never in
  the kernel's `Environment`, which never reads them.

## Architecture

All new code lands in `leanr_meta` except the two extension decodes,
which land in `leanr_olean` alongside the parser/reducibility/matcher
precedent. The module map from the parent spec is unchanged; this slice
fills in `instances.rs` and `synth.rs` and adds `discr_tree.rs`.

### PR-A — olean decode of two extensions (`leanr_olean`)

`ModuleData` already decodes `parserExtension`, the two reducibility
extensions, and `matcherExtension` typed, keeping the rest opaque
(`num_entries`). This PR adds two more:

- **`Lean.Meta.instanceExtension`** — the registered instances. Each
  entry carries the instance constant's name, its priority, and the
  attribute-kind/keys Lean stores; the instance *type* is recovered from
  the constant's declaration, not from the extension. Global and scoped
  (`ScopedEnvExtension.Entry`) entries both decode, as reducibility
  already handles.
- **`Lean.Meta.defaultInstanceExtension`** — the default instances and
  their priorities, kept in a distinct decoded field so the instance
  table can hold them in a separate table (below).

Both are **untrusted input**: the decode must never panic on arbitrary
bytes (`docs/THREAT_MODEL.md`), the existing `leanr_olean` fuzz target
is extended to cover them, and unit tests decode a committed fixture
`.olean` built from a small source module with a handful of instances
and one default instance. A constant absent from the extension simply
has no instance entry — the fallback is "not an instance", never a
panic.

### PR-B, layer 1 — the discrimination tree (`discr_tree.rs`)

Two pieces, split as Lean splits core `DiscrTree` from `Meta.DiscrTree`:

- **The data structure — standalone, reusable, MetaM-free.** A `Key`
  enum transcribed from Lean: `const` (name + arity), `star` (the
  wildcard for metavariables and opaque subterms), `fvar`, `lit`,
  `sort`, `arrow`, and `proj`. A trie mapping key *paths* to value sets,
  with `insert` and `get_match` over **precomputed** paths. `get_match`
  returns candidates **specific-before-wildcard**, exactly as Lean's
  `getMatch` orders them. This module has no dependency on `MetaCtx` and
  owns its own unit tests; it is what `simp`/`rw`/`exact?` reuse later.

- **The path computation — MetaM-coupled, `impl MetaCtx`.** `mk_path`
  (for insertion) and the expression-driven side of `get_match` compute
  key paths from an `ExprId`, normalizing by whnf-ing at **reducible**
  transparency (Lean's `reduceDT`/`whnfR`) and skipping
  instance-implicit and type-family arguments per Lean's rules. Because
  it needs `whnf`, it lives adjacent to `instances.rs`, not inside the
  standalone module.

Key-computation fidelity is a named risk: the reducible-whnf during path
construction must match `reduceDT` exactly, or an instance is filed
under the wrong path and silently never matches.

### PR-B, layer 2 — the instance table (`instances.rs`)

Built from PR-A's decoded entries. Per instance: the constant name, its
type (from the declaration), its priority, and its **`synth_order`** —
the order in which its own instance-implicit subgoals are attempted,
**computed once at registration** by transcribing Lean's
`computeSynthOrder`, never recomputed per query.

The table is discrimination-tree indexed on the class head of the
instance's target. `get_match` on a goal returns candidates
specific-before-wildcard, then ordered by priority with a
registration-order tie-break, as Lean does. **Default instances live in
a separate table**, populated from `defaultInstanceExtension` and
consulted only in the default-instance phase of search. Table keys are
normalized so goals that are α-equivalent up to metavariables share an
entry.

### PR-B, layer 3 — tabled resolution (`synth.rs`)

Prolog-style tabling, held in one `MetaCtx`-owned `SynthState`:

- **Answer table** — keyed by normalized goal, holding the answers
  (synthesized instance terms) found so far plus a completion flag.
- **Generator node** — per goal, produces candidate instances from the
  instance table (via `get_match`); each candidate spawns subgoals for
  its instance-implicit arguments in `synth_order`.
- **Consumer node** — a goal with pending subgoals, resumed when a
  subgoal produces a new answer.
- **Waiters** — consumers blocked on a table entry, resumed when that
  entry gains an answer.

**The engine is an explicit work-list state machine over these nodes,
not native Rust recursion.** Tabling requires suspending a consumer
until a subgoal's table entry gains an answer and resuming it later;
native recursion cannot suspend and resume a stack frame that way. This
is the one genuine implementation-structure choice in the slice, and the
state machine is the shape that makes tabling expressible at all.

Search is bounded by the deterministic step counter
(`StepBudgetExhausted`) and the synthesis-reentrancy depth
(`maxSynthPendingDepth` → `DepthBudgetExhausted`); both error variants
already exist. On success the goal mvar is assigned the synthesized
term. A subgoal that is `IsDefEqStuck` propagates **stuck, never
`false`** — collapsing the two changes search results.

### PR-B, layer 4 — `synth_pending` (`whnf.rs`)

Replace the `whnf.rs:1097` stub. `synth_pending(mvar)`: if the mvar is a
pending instance goal whose type is now sufficiently instantiated to
have a concrete class head, run synthesis and return whether it
assigned. The call site at `whnf.rs:1404` already invokes it; this PR
gives it a real engine. It honors the `maxSynthPendingDepth` budget so
the mutual recursion between `is_def_eq` and synthesis (each can trigger
the other) terminates deterministically.

### The mutual recursion

`is_def_eq` and synthesis are mutually recursive across module
boundaries, as the parent spec anticipated: `is_def_eq` calls synthesis
on a pending instance problem, synthesis calls `is_def_eq` to match
candidates and discharge subgoals. All state is in the one `MetaCtx`;
each module contributes an `impl MetaCtx` block; the recursion stays
direct calls with no dynamic dispatch on the hot path.

## Differential harness

### Tier 1 — the fast gate (`meta:fast`, PR-B)

Purpose-built local fixtures, **not** mined from Mathlib, following the
plan-2 precedent (`Meta0.lean`) so `fixtures:regen` stays free of any
`.mathlib` dependency and CI never installs Lean. A new `dump_synth.lean`
metaprogram (following `dump_defeq.lean`) asks the oracle via
`Lean.Meta.synthInstance` and records the canonical result. The
committed corpus deliberately exercises:

- simple resolution (a class with a direct instance),
- subgoal chaining (an instance whose premises are themselves classes),
- a **diamond** (a goal reachable two ways — resolved to one answer,
  deterministically),
- a **cyclic** instance graph (must terminate under tabling),
- default instances (e.g. the `OfNat` default path),
- priority ordering (two applicable instances, higher priority wins),
- a deliberate **negative** (no instance — a real "no", not stuck),
- a **stuck** case (an output mvar blocks resolution — must report
  stuck, not `false`).

A query record holds a stable id (constant + query kind + index within
the constant), the transparency level, the config profile, and the
verdict — for success, the canonicalized synthesized term; for a
negative, the "no instance" verdict; for stuck, the stuck verdict. Mvars
are compared up to canonical renaming (creation order within a query),
as the harness already does for `defeq_mvar`. `meta:fast` is extended in
place; it stays seconds, no corpus walk, no Lean.

### Tier 2 — nightly discovery (`meta:nightly`, PR-C)

A full sweep over Mathlib constants plus **synthesized queries**, and a
**separate workflow from `nightly-sweep.yml`** (the parent spec's call:
the parse sweep's ~35h is dominated by olean-closure decode per import
set, while the defeq/synth sweep needs decoded constants but no corpus
walk, so their cost profiles and shard axes differ; folding them couples
two unrelated runtimes under one 6h-per-job budget).

- **What it queries.** For each Mathlib constant, mine its
  instance-argument positions and form `synthInstance` goals from the
  (closed) instance types, run leanr synthesis, and diff the synthesized
  term against the oracle. Plus the synthesized-mvar `is_def_eq` queries
  that plan 3 deferred to here: abstract an implicit argument of a real
  application into a fresh mvar and diff verdict-plus-assignments at each
  transparency level.
- **Shard axis: by constant index (`index % N`)**, *not* the parse
  sweep's import-set axis. Each shard loads the full pinned environment —
  a complete instance table requires the whole import closure — and
  processes the constants with `index % N == shard`. This is the
  "different axis" the parent spec requires; sharding on import sets
  would give each shard an incomplete instance table and therefore wrong
  "no instance" answers.
- **Import order is pinned explicitly** in the corpus definition:
  `synth_order` and instance registration order determine search, so an
  unpinned order makes nightly results irreproducible in a way that
  looks like a regression (parent risk 3).
- **Pass-list discipline mirrors `mathlib_sweep.rs`.** Check for
  regressions *before* rewriting the pass-list, log every dropped entry
  rather than silently absorbing it, fail the workflow on a true
  regression, and otherwise propose the changed pass-list as a PR on a
  stable nightly branch — never push to main.
- **Determinism.** Queries near any step or depth budget on either side
  are recorded and excluded from the gate.

### Existing gates that stay green

Workspace tests, lint, `cargo deny`, parse-acceptance, both fuzz
targets, the never-hang storms, `fmt:mathlib`, `parse:mathlib:fast`, and
plans 2–3's `meta:fast` `whnf`/`infer`/`defeq`/`defeq_mvar` fixtures.

## Error handling & edge cases

Every failure in this slice is **incompleteness, never unsoundness** —
the kernel independently re-checks whatever elaboration produces, so the
worst case is that a synthesis that should have succeeded does not. The
step and depth budgets are distinct error variants, never a negative
verdict; `IsDefEqStuck` is never collapsed to `false`. Deep terms use
`stacker`, as the rest of `leanr_meta` does, so the minimum-stack
contract holds on any thread. Arbitrary `.olean` bytes never panic the
decode.

## Staging

Task order keeps every gate green throughout:

1. **PR-A:** decode `instanceExtension` and `defaultInstanceExtension`;
   extend the fuzz target; unit tests against a committed fixture olean.
2. **PR-B:**
   1. `discr_tree.rs` — the standalone trie + `Key` model, with unit
      tests over precomputed paths.
   2. `mk_path` / `get_match` path computation (`impl MetaCtx`), reusing
      `whnf` at reducible transparency.
   3. `instances.rs` — build the table from PR-A data; `synth_order` at
      registration; the separate default-instance table.
   4. `synth.rs` — the tabled work-list engine; first tier-1 fixtures per
      shape.
   5. `synth_pending` — replace the stub; wire the stuck-path seams; the
      remaining tier-1 fixtures (diamond, cyclic, stuck, negative).
3. **PR-C:** `meta:nightly` workflow — synthesized queries, by-constant
   sharding, pinned import order, gate-before-rewrite reconcile.

## Risks

Parent risks 1–5, concentrated in this slice, plus two specific to it:

1. **The approximation flags have no specification** (parent risk 1).
   Synthesis reaches them through the subgoal `is_def_eq` calls; the
   two-profile corpus is the only mitigation and only for queries it
   contains.
2. **Corpus bias — the honest limitation** (parent risk 2). Mathlib
   constants are fully elaborated and mvar-free; tier-2's mvar queries
   are *synthesized by us*, a plausible guess at what the elaborator
   asks, not a record of it. Real validation arrives in M4b when the
   term elaborator generates queries naturally. A green plan 4 is strong
   evidence of instance-table and reduction fidelity, weaker evidence of
   unification-under-search fidelity.
3. **TC results depend on instance registration order, i.e. import
   order** (parent risk 3). `synth_order` is computed once at
   registration; the corpus pins import order or nightly diverges
   irreproducibly.
4. **Table-key normalization granularity** (parent risk 4). Too coarse
   and distinct goals collide on one entry (wrong answers); too fine and
   search blows up. No test isolates this — it surfaces as a wrong
   instance or a timeout.
5. **Cache-key completeness** (parent risk 5). Guarded by the
   `size_of::<Config>()` assertion; restated because Lean shipped this
   bug twice.
6. **DiscrTree key-computation fidelity** (plan-4-specific). The
   reducible-whnf during path construction must match `reduceDT`
   exactly, or an instance files under the wrong path and never matches —
   a silent "no instance" that looks like a missing instance rather than
   a bug.
7. **Tabling termination on cyclic graphs** (plan-4-specific). The
   generator/consumer/waiter structure is what makes cyclic instance
   graphs terminate; a bug there is non-termination, not a wrong answer.
   Covered by a dedicated cyclic fixture in tier 1.

## What plan 4 ships — and the stated M4a exception

Plan 4 completes M4a. Per the parent spec's recorded exception, M4a *as
a whole* is the "independently useful" unit — a `leanr_meta` core
(`whnf`, `infer_type`, `is_def_eq`, synthesis) verified against the
oracle, plus the query harness and two-tier gate every later M4 slice
reuses. Plan 4 inherits that exception: it ships no standalone
user-visible feature, and a diagnostic-only `leanr synth` subcommand
would be a contrivance rather than a deliverable.

## Out of scope (and where it lands)

- **Unification hints** — consulted from the `is_def_eq` failure path;
  the seam stays in place, unpopulated, until M4b.
- **The term elaborator, `TermElabM`, and the postponement /
  synthetic-mvar ladder** → M4b. This is where synthesis queries become
  elaborator-real rather than synthesized, closing risk 2.
- **The app elaborator, `elabAsElim`, dot notation, coercions,
  `binop%`** → M4b/M4c.
- **The match/equation compiler, the `do` elaborator, tactics, the VM**
  → later M4 slices.
- **`simp`/`rw`/`exact?`** — they reuse `discr_tree.rs`'s standalone
  data structure, but their own path-computation and rule tables are
  later slices.
- **salsa wiring** → M5.
