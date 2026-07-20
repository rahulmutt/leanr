# M4a plan 2 — reduction, type inference, and the oracle harness — design spec

Status: approved (brainstormed 2026-07-20)
Parent: [2026-07-20-m4a-meta-core-design.md](2026-07-20-m4a-meta-core-design.md)
Predecessor plan: [../plans/2026-07-20-m4a-meta-core-foundation.md](../plans/2026-07-20-m4a-meta-core-foundation.md) (plan 1 of 4, merged)

## Problem

The M4a foundation is merged: `leanr_meta` exists with its transparency
model, defeq `Config` and cache key, and metavariable context, plus the
reducibility-extension decode in `leanr_olean`. Nothing reduces and
nothing infers: there is no `whnf`, no `infer_type`, no `MetaCtx`, and
no differential gate — `leanr_meta` is currently verified only by unit
tests against transcribed rules, not against the oracle.

This slice (plan 2 of 4) delivers reduction, inference, and the tier-1
oracle harness. Plan 3 adds `is_def_eq` and the occurs check; plan 4
adds the instance-extension decode, tabled synthesis, and the
`meta:nightly` discovery sweep.

## Goal

`whnf` and `infer_type` in `leanr_meta`, agreeing with the oracle on a
committed fixture corpus, gated by a `meta:fast` mise task that runs in
seconds with no Lean and no Mathlib checkout. Plus the
`Lean.Meta.matcherExtension` decode in `leanr_olean` that matcher
unfolding requires.

## Scope decisions (agreed in brainstorming)

- **Traversal is `ExprId`-native — plan 1's deferred question, now
  answered.** Plan 1 explicitly deferred whether `leanr_meta` traverses
  bank rows by `ExprId` or materializes `Arc<Expr>` via
  `Store::to_expr`, so that `whnf` and the plan-3 occurs check would
  get one answer. The answer is bank rows, for three reasons:

  1. It is the only working precedent. `leanr_kernel/src/tc.rs` is
     entirely id-native — every cache is `ExprId`-keyed, every helper
     (`get_app_fn`, `mk_app_spine`, …) stays on ids, and nodes are
     decoded one level at a time via `Store::expr_node`. Its module doc
     records why. `Store::to_expr` exists as a boundary bridge for
     materialization at API edges, not hot-path machinery.
  2. `Arc<Expr>` traversal allocates a tree per query and the cost is
     permanent, while its simplicity benefit is front-loaded only.
  3. `Arc<Expr>` traversal forces a `Name`→`MVarId` reverse lookup that
     `MetavarContext` has no index for (an `Expr::MVar` node carries an
     `Arc<Name>`, not an id). Id-native traversal never leaves id
     space, so the lookup never needs to exist.

  The plan-3 occurs check inherits this decision.

- **The matcherExtension decode is in scope, and it is typed and
  complete.** `whnf`'s matcher unfolding must identify matcher
  definitions, and `Lean.Meta.matcherExtension` is still opaque in
  `leanr_olean` (only `parserExtension` and the two reducibility
  extensions are decoded). A name-pattern heuristic (`.match_<n>`) was
  considered and rejected — wrong in a way that mostly works, exactly
  the class of plausible approximation this project's oracle discipline
  exists to exclude. Deferring matcher unfolding was also rejected: it
  would make whnf normal forms over any equation-compiler output
  diverge from the oracle and hollow out the tier-1 corpus. The decode
  carries the full `MatcherInfo` payload, not an "is a matcher" bit,
  because `reduce_matcher` needs the arities (see § Architecture).

- **`infer_type` is in this slice, not deferred.** `whnf` needs pieces
  of it regardless (projection reduction needs the discriminant's
  type; smart unfolding involves type-directed checks), so splitting it
  out would rebuild half of it under another name.

- **The tier-1 corpus is purpose-built local fixtures, not mined from
  Mathlib.** New fixture `.lean` modules exercise each reduction rule
  deliberately; `fixtures:regen` stays free of any `.mathlib`
  dependency. Mathlib-scale discovery is tier 2's job (`meta:nightly`,
  plan 4, once `is_def_eq` and synthesis exist to make the synthesized
  mvar queries meaningful).

- **The transient/permanent cache split lands now**, not with defeq, so
  plan 3's defeq cache drops into an existing shape instead of
  retrofitting one.

## Architecture

### `MetaCtx` — the shared-state struct

The struct the parent spec's mutual-recursion section calls for,
introduced by the first modules that need shared state. Fields:
environment view, scratch `Store` overlaying the persistent bank (the
`tc.rs` view/scratch pattern), `MetavarContext`, `Config`, the caches
(§ Caching), and deterministic step/depth budgets surfacing as
`MetaError::StepBudgetExhausted` / `DepthBudgetExhausted`.

Each module contributes an `impl MetaCtx` block — inherent impls split
across files, direct calls, no dynamic dispatch. Recursive paths route
through a `guarded` wrapper combining a depth limit with
`stacker::maybe_grow`, transcribed from the `tc.rs` idiom
(`RED_ZONE`/`STACK_CHUNK`), so the minimum-stack contract holds on any
thread.

Plan 1's free functions and plain structs (`can_unfold`,
`MetavarContext`, `Config`) are consumed as-is; no rework.

### The matcherExtension decode (`leanr_olean`)

Follows the plan-1 reducibility playbook step for step: create a
fixture module containing `match` definitions, verify it against the
oracle, wire it into `fixtures:regen`, empirically pin the raw entry
shape with a temporary probe, remove the probe, then TDD the decoder.

Decoded payload: Lean's `MatcherInfo` per matcher constant — parameter
and discriminant counts, per-alternative argument arities, and the
universe-elimination position. Entries land as a new typed field on
`ModuleData` beside the reducibility entries; all other extensions stay
opaque. The decoder returns `OleanError` on arbitrary bytes, never
panics, and inherits the existing olean fuzz target automatically.

The exact raw shape is pinned empirically during implementation, not
assumed in this spec — the probe step exists precisely because
serialized extension layouts are not documented.

### Reduction (`whnf.rs`)

Two entry points, per the parent spec:

- **`whnf_core`** — no delta. Instantiates assigned mvars at the head,
  then applies beta, zeta (let), projection-of-constructor, literal
  reduction, iota (recursor) and quotient rules, and matcher reduction.
  (This corrects the parent spec's shorthand "beta/eta/proj/literal/
  matcher": eta is a defeq-side concern, not a `whnf_core` step, and
  iota/quotient were omitted there. Verified against the pinned
  toolchain's source during planning, per the transcription rule
  below.)
- **`whnf`** — loops `whnf_core` with delta unfolding, gated on
  `can_unfold` against the decoded `ReducibilityStatus` for the current
  `TransparencyMode`.

The two override channels are explicit, named code paths, because they
are orthogonal to transparency and to each other:

- **Smart unfolding**: the `_sunfold` auxiliary is found by Lean's name
  convention — an environment lookup, no extension decode needed.
- **Matcher unfolding**: a named `can_unfold_at_matcher` predicate
  backed by the decoded matcher table. `reduce_matcher` uses the
  decoded arities to check saturation and select alternatives.

**Lean's implementation is the specification.** The plan transcribes
the rule set and its ordering from the pinned toolchain's source,
rule-by-rule with a citation per rule — never reconstructed from
memory. Where this spec's rule list and Lean's source disagree, Lean's
source wins and the plan records the correction.

### Type inference (`infer.rs`)

Meta-level `infer_type`: mvar heads resolve through `MetavarContext`
declarations, fvars through the `LocalContext`, everything else by the
standard rules. Inference without checking — the kernel remains the
independent checker, so `infer.rs` never re-validates what it infers.
`ExprId`-keyed cache.

### Caching (`cache.rs`)

The transient/permanent split from the parent spec: permanent for
mvar-free terms under a standard config, transient otherwise. `whnf`
and `infer` caches key on `(Config::cache_key(), ExprId)`, so the
`size_of::<Config>()` guard from plan 1 protects these caches from the
missing-key-field failure mode from day one. The transient cache is
invalidated when mvar assignments change; the permanent cache never
holds an mvar-dependent answer.

## Error handling & edge cases

- Every `leanr_meta` failure is incompleteness, never unsoundness — the
  kernel independently re-checks anything elaboration produces.
- Deep terms: the `guarded` wrapper (depth limit + `stacker`) on every
  recursive path.
- Resource limits are deterministic step budgets, reported as
  `StepBudgetExhausted`, distinct from any genuine negative answer.
- `.olean` bytes are untrusted: the matcher decode returns errors,
  never panics, on arbitrary input, and is fuzzed.
- `leanr_kernel` is not modified.

## Acceptance harness

`tests/fixtures/meta/dump_defeq.lean`, following the
`dump_decls.lean` / `dump_syntax.lean` precedent: a Lean program run by
`fixtures:regen` under the pinned toolchain, enumerating queries over
purpose-built fixture modules and emitting canonical JSONL that is
committed. CI never installs Lean (`docs/ORACLE.md`).

### Corpus

New fixture `.lean` modules under `tests/fixtures/meta/`, each written
to exercise a specific rule: beta, zeta, projection, literal
reduction, iota/quotient, matcher reduction, smart unfolding, and
delta at each transparency level against each reducibility status. The
fixture set is the tier-1 pass-list analogue: bounded, committed, and
grown deliberately.

### Query records

For each query: a stable id (constant name + query kind + index within
that constant — never a global counter), the query kind (`whnf` or
`infer`), the transparency level, and the resulting term. Terms are
serialized structurally (the `stx.jsonl` shape precedent: nested
objects, not pretty-printed strings), with mvars renumbered canonically
in creation order per query so gensym'd oracle names never appear.

### The gate — `mise run meta:fast`

An acceptance test in `crates/leanr_meta/tests/` decodes the fixture
oleans, runs each committed query through `MetaCtx`, and compares
against the committed JSONL. Seconds, no corpus walk, no Lean — a pure
regression gate for the dev loop: "nothing that used to agree now
disagrees." Wired as a mise task beside `parse:mathlib:fast`.

### Existing gates that stay green

Workspace tests, lint, `cargo deny`, parse-acceptance, both fuzz
targets, the never-hang storms, `fmt:mathlib`, and
`parse:mathlib:fast`.

## Risks

1. **The reduction rule ordering is behavior.** `whnf_core`'s rule
   order and where matcher/smart unfolding interpose determine which
   normal form comes out. Transcription with per-rule citations plus
   the differential gate is the mitigation; the corpus only catches
   divergence it contains — same shape as the parent spec's risk 1.
2. **The matcher raw shape is unpinned until the probe runs.** If the
   serialized `MatcherInfo` layout is materially more complex than the
   reducibility entries (it nests arrays), the decode task grows. The
   probe step bounds the surprise to one task rather than the slice.
3. **Term serialization is a new comparison surface.** A bug in the
   JSONL encoder (either side) shows up as false divergence. Mitigated
   by keeping the encoding structural and minimal, and by the mvar
   canonical-renumbering rule from the parent spec.

## Out of scope (and where it lands)

- `is_def_eq` beyond plan 1's stubs, the occurs check, lazy delta, the
  approximation flags in action → plan 3.
- Instance/default-instance extension decode, discrimination trees,
  tabled synthesis, `meta:nightly` → plan 4.
- Unification hints seam population, coercions, the term elaborator →
  M4b and later, per the parent spec.
