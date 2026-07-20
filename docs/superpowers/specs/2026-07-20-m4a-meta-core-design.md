# M4a — the `MetaM` core: reduction, definitional equality, and typeclass synthesis — design spec

Status: approved (brainstormed 2026-07-20)
Predecessor: [2026-07-04-leanr-architecture-design.md](2026-07-04-leanr-architecture-design.md) (§ Milestones, M4)

## Problem

M3 is done: `leanr_syntax` produces lossless trees validated against
the oracle, and `leanr fmt` ships. M4 — "Elaborator + VM" in the
architecture spec — has no implementation and no design.

M4 as stated is not one milestone. It contains several independent
subsystems: reduction and definitional equality, typeclass synthesis,
the term elaborator and its postponement machinery, the application
elaborator, the match/equation compiler, and a bytecode VM. Designing
them in one pass would produce something too vague to implement, so M4
is decomposed and this spec covers only its bottom layer.

**M4a is that bottom layer**: an elaborator-level `MetaM` core —
`whnf`, `is_def_eq`, `infer_type`, and tabled typeclass synthesis —
over terms that may contain metavariables.

### Why this is not the kernel's defeq

`leanr_kernel/src/tc.rs` already implements `whnf`, `is_def_eq`, and
`infer_type` (2,928 lines), and re-checks all of Mathlib. That is the
*kernel's* definitional equality: no metavariables, no transparency
levels, no configuration, unfolds whatever it needs, and answers a
total question about closed terms.

The elaborator's `isDefEq` is a different problem. It works over open
terms containing metavariables, it assigns those metavariables as a
side effect, it is gated by six transparency levels, and it is
deliberately incomplete — a family of approximations makes
higher-order unification tractable at the cost of being
order-dependent. Lean maintains these as two independent
implementations, and so does leanr.

## Goal

A `leanr_meta` crate whose `whnf` / `is_def_eq` / `infer_type` /
instance synthesis agree with the oracle on a differential corpus
mined from Mathlib, gated in two tiers (a fast regression gate for the
dev loop, a nightly discovery sweep), with `leanr_kernel` unmodified.

## Scope decisions (agreed in brainstorming)

- **A separate implementation, not a generalization of the kernel.**
  Considered and rejected: parameterizing `leanr_kernel/src/tc.rs`
  over a `Reduction` trait supplying mvar lookup and an unfolding
  predicate, so both consume one implementation. Rejected for three
  reasons, in order of weight:

  1. **It destroys the kernel's independence.** The kernel is an
     independent check on what the elaborator produces. If both call
     the same reduction code, a bug there makes the elaborator emit a
     wrong term *and* makes the kernel accept it. The failure is
     correlated, and correlated failure is invisible to differential
     testing — both sides of leanr's own stack agree with each other
     for the same wrong reason. This is the same hazard the nightly
     merge job already guards against by refusing to use a filesystem
     existence test (AGENTS.md), raised to a soundness question.
  2. **The two-hook abstraction does not survive contact.** The
     differences are not a policy parameter: smart unfolding
     (`_sunfold` auxiliaries), `canUnfoldAtMatcher` and its override
     channel, the five approximation flags, `isDefEqStuckEx` as a
     control-flow channel, mvar assignment and the occurs check,
     delayed assignment, postponed universe constraints, and the
     transient/permanent cache split. None are expressible as
     `can_unfold`. The trait realistically grows past a dozen methods
     with the kernel stubbing most of them — TCB entanglement bought
     for very little sharing.
  3. **They evolve on different clocks.** Kernel defeq is pinned by
     the kernel specification and effectively frozen. `Meta.isDefEq`
     changes every Lean release: v4.29 changed transparency handling
     (PR #12179), v4.31 fixed two genuine cache-key correctness bugs
     (#13768, #13772). Coupling means every elaborator-tracking change
     edits the TCB.

  The duplication cost is smaller than `tc.rs`'s size suggests — most
  of it is `infer_type` plus inductive/quotient specifics that the
  Meta level needs differently anyway.

- **Typeclass synthesis is in M4a, not a follow-on.** `is_def_eq`
  calls into synthesis when it meets a pending instance problem, and
  synthesis calls back into `is_def_eq`; `maxSynthPendingDepth` makes
  the recursion depth semantically visible. They are not cleanly
  separable layers, and deferring synthesis would restrict the
  differential corpus to toy terms — real Mathlib terms are saturated
  with instance arguments.

- **`leanr_kernel` is not modified.** Its `ExprNode` already carries
  `MVar` and `FVar` variants and the `hasExprMVar` / `hasLevelMVar`
  cached bits; the kernel simply never meets an mvar in a checked
  term. `leanr_meta` reuses the hash-consed term bank and `ExprId`
  as-is and owns the metavariable *context*.

- **Two tiers of differential gate**, mirroring the existing
  `parse:mathlib:fast` / nightly split rather than inventing a new
  shape.

## Architecture

### Crate & module structure — `crates/leanr_meta`

Depends on `leanr_kernel` for `Expr` / `ExprId` / the term bank /
`Environment`, and on `leanr_olean` for the decoded environment-
extension data described under § Prerequisite (reducibility statuses,
the instance table). No reduction logic is shared with the kernel in
either direction, even where the rules coincide.

The `leanr_olean` dependency follows the existing `leanr_grammar`
pattern — a consumer of decoded `.olean` content — and is what keeps
the reducibility and instance tables out of the kernel's
`Environment`, which would otherwise mean TCB growth for data the
kernel never reads.

Ownership: the kernel owns terms (bank, interning, ids). `leanr_meta`
owns everything metavariable-shaped — mvar declarations, the
assignment map, delayed assignments, the local-context snapshot each
mvar was created in, level mvars, and postponed universe constraints.

| module | concern |
|---|---|
| `mvar_ctx` | mvar decls, assignment, occurs check, delayed assignment |
| `transparency` | the six levels + `ReducibilityStatus`, `can_unfold` |
| `config` | reduction/defeq config **and** its cache key |
| `whnf` | weak-head normalization, smart unfolding, matcher unfolding |
| `defeq` | `is_def_eq`, unification, the approximation flags |
| `infer` | `infer_type` at the Meta level |
| `instances` | instance table (discrimination-tree indexed) + `synth_order` |
| `synth` | tabled resolution: generator/consumer nodes, answers, waiters |
| `cache` | the transient/permanent split |

One concern each, so no file grows into the 2,900-line shape `tc.rs`
has.

### The mutual recursion

`is_def_eq` and synthesis are mutually recursive across module
boundaries. All state lives in one `MetaCtx` struct (environment,
bank, mvar context, caches, config, depth budgets) and each module
contributes an `impl MetaCtx` block — Rust permits inherent impls
split across files within a crate. The recursion stays direct calls,
files stay single-concern, and there is no dynamic dispatch on the hot
path.

### Prerequisite: typed decode of two environment extensions

Discovered while planning, and a genuine dependency of this slice
rather than an implementation detail.

`leanr_olean`'s `ModuleData` validates environment-extension entries
but keeps them **opaque** (`num_entries`), with only
`Lean.Parser.parserExtension` decoded typed (M3b2a). The in-source
comment anticipates this: "interpreted by the elaborator in M4."

Two of those opaque extensions are load-bearing for M4a:

- **The reducibility attributes** (`@[reducible]`, `@[irreducible]`,
  `@[instance_reducible]`, `@[implicit_reducible]`) carry
  `ReducibilityStatus`. Without them `can_unfold` cannot be
  implemented — every constant would look `semireducible`.
- **The instance extension and the default-instance extension** hold
  the synthesis candidates. Without them the instance table is empty
  and TC synthesis answers "no instance" for everything.

Note that `ReducibilityStatus` is **not** `ReducibilityHints`
(`Regular` / `Opaque` / `Abbrev`), which is an unfolding-cost
heuristic stored inline in `DefinitionVal` and already decoded. They
are unrelated despite the similar names, and conflating them yields a
`can_unfold` that is wrong in a way that typechecks.

Both decodes land in `leanr_olean` alongside the parser-entry
precedent, not in `leanr_meta`: they are olean-format concerns, and
`.olean` bytes are untrusted input, so they inherit the existing
never-panic obligation and its fuzz target.

The reducibility decode is a prerequisite of `transparency.rs`; the
instance decode is a prerequisite of `instances.rs` and may land with
it.

### Transparency (`transparency.rs`)

Six levels, ordered `none < reducible < instances < implicit <
default < all`, against five reducibility statuses (`reducible`,
`semireducible`, `irreducible`, `implicitReducible`,
`instanceReducible`).

**The ordering is written by hand and never derived.** In Lean the
constructor order of both `TransparencyMode` and `ReducibilityStatus`
deliberately does *not* match the unfolding order — a bootstrapping
constraint, documented in-source. A `#[derive(PartialOrd)]` here
would silently produce a wrong hierarchy that typechecks. `can_unfold`
is transcribed from Lean's `canUnfoldDefault` as the specification,
with a test per level/status pair.

`implicit` is distinct from `instances`: it unfolds for
implicit-argument defeq and instance-diamond resolution but stays
opaque to typeclass search. Collapsing the two reintroduces the class
of bugs Lean's v4.29 change set out to fix.

### Config and the cache key (`config.rs`, `cache.rs`)

The defeq cache key is derived from the **whole** config struct, plus
a `const` assertion on `size_of::<Config>()` that breaks the build
when a field is added, forcing the author to decide whether it belongs
in the key.

This is not speculative hardening. Lean shipped two wrong-answer bugs
of exactly this shape in a mature codebase: `TransparencyMode` packed
into two bits collided with an approximation bit in the cache key
(#13768), and `Config.zetaUnused` was missing from the key (#13772).
Both are one failure mode — a semantically relevant field absent from
the key — and both produce wrong answers only under cache pressure,
which is the hardest possible thing to attribute.

Caching is split transient/permanent as Lean's is: permanent for
mvar-free terms under a standard config, transient otherwise. Getting
the predicate wrong either poisons the permanent cache (wrong answers)
or destroys performance.

### Reduction (`whnf.rs`)

`whnf_core` (beta/eta/proj/literal/matcher, no delta) and `whnf`
(adds delta, gated on `can_unfold`).

Two override channels are modelled explicitly rather than emerging
from ad-hoc conditionals, because they are orthogonal to transparency
and to each other:

- **smart unfolding** — the `_sunfold` auxiliary definitions that
  equation-compiler definitions carry. Omitting it changes what
  unfolds, silently.
- **matcher unfolding** — `can_unfold_at_matcher` plus its override
  hook.

### Definitional equality (`defeq.rs`)

An explicit escalation, not one recursive predicate:

1. structural / pointer-equality fast paths
2. assignment, when one side is an unassigned mvar (with occurs check)
3. lazy delta, gated by transparency
4. the approximation flags

The five approximations (`fo`, `ctx`, `quasi_pattern`, `const`,
`univ`) are **explicit config fields consulted at named call sites**,
never implicit fallback behavior. They deliberately make higher-order
unification incomplete and order-dependent, which means they define
the accepted language and must be auditable against the oracle.

`isDefEqStuckEx` is a **typed error variant, not a `bool`**. It is the
channel by which synthesis learns "this may become solvable once more
mvars are assigned." Collapsing it into `false` loses the distinction
between *not equal* and *not yet decidable*, changing search results.

### Typeclass synthesis (`instances.rs`, `synth.rs`)

Tabled resolution (Prolog-style tabling), **not** memoized
backtracking: generator nodes producing candidate instances, consumer
nodes awaiting subgoal answers, waiters, and an answer table. Plain
backtracking gives different results, not merely worse performance —
cyclic instance graphs terminate under tabling and diverge without it.

The instance table is discrimination-tree indexed. `synth_order` — the
order an instance's own subgoals are attempted — is computed once at
registration, as Lean does. Default instances live in a separate table
from regular instances.

Table keys are normalized so goals that are α-equivalent up to
metavariables share an entry.

### Determinism: a deliberate divergence from the oracle

Lean bounds search with `maxHeartbeats`, which is time-derived and
therefore machine-dependent. `leanr_meta` uses a **deterministic step
counter** instead.

This is a knowing behavioral divergence. On a query near the limit,
Lean's verdict depends on the machine it ran on and leanr's does not.
Reproducing time-based limits would make the differential oracle
itself nondeterministic and every fixture flaky, which is a worse
trade. The harness records which queries came near any limit so they
can be excluded from the gate rather than silently disagreeing (see
§ Acceptance harness).

## Error handling & edge cases

**Every failure in `leanr_meta` is incompleteness, never
unsoundness.** The worst case is that elaboration which should have
succeeded does not, because the kernel independently re-checks the
result. This is the same framing `leanr_olean` already uses for
`KernelError::BankExhausted`, and it is what makes the approximations
tunable at all.

**Stack depth**: deep terms recurse deeply, the same hazard
`leanr_kernel` and `leanr_syntax` already hit. `leanr_meta` uses
`stacker`, so the minimum-stack contract holds on any thread rather
than becoming a precondition on callers.

**Resource limits** are deterministic step budgets (above), reported
as a distinct error from a genuine negative verdict.

## Acceptance harness

The harness is a Lean metaprogram,
`tests/fixtures/meta/dump_defeq.lean`, following the existing
`dump_decls.lean` / `dump_syntax.lean` precedent: it enumerates
queries, asks the oracle via `Lean.Meta.isDefEq` / `whnf` /
`inferType`, and emits canonical JSONL. Output is committed and
regenerated by `fixtures:regen`, so CI stays hermetic and never
installs Lean (`docs/ORACLE.md`).

### What a query record holds

A stable id, the query kind, the transparency level, the verdict, and
where applicable the resulting normal form and the mvar assignments.

**Not verdict-only.** Two implementations can agree on every boolean
while assigning metavariables differently; that divergence surfaces
much later in elaboration, where it is near-impossible to attribute.

### Two normalization problems the format must solve

Otherwise every fixture diff is noise:

1. **Mvar identity.** Lean's mvar names are gensym'd and will never
   match leanr's. Assignments are compared up to a canonical
   renaming — mvars numbered in creation order within a query, then
   compared structurally.
2. **Query identity.** Ids must be stable across regen, so they are
   derived from the constant name plus query kind plus an index within
   that constant, never from a global counter.

### Tier 1 — fast gate (`mise run meta:fast`)

A committed pass-list of constants, with mvar-free queries mined from
them: `infer_type(value)` against the stored type, and `whnf` normal
forms. Bounded and committed like the 23-entry
`mathlib-passlist.txt`, so it runs in seconds, with no corpus walk and
no Lean. This is a **regression** gate: "nothing that used to agree
now disagrees." Run it in the dev loop.

### Tier 2 — nightly discovery (`mise run meta:nightly`)

Full sweep over Mathlib constants, plus **synthesized mvar queries**:
take a real application, abstract an implicit argument into a fresh
metavariable, and ask `is_def_eq` against the original at each
transparency level. This is what exercises assignment, the occurs
check, and the approximation flags on real terms rather than toys.

Same discipline as the parse sweep: check for regressions *before*
rewriting the pass-list, so a regression fails before the baseline is
touched, and log every dropped entry rather than silently absorbing
it.

**A separate workflow from `nightly-sweep.yml`, not another job in
it.** The parse sweep's ~35h is dominated by olean closure decode per
distinct import set; the defeq sweep needs decoded constants but no
corpus walk, so its cost profile differs and it shards on a different
axis. Folding them together would couple two unrelated runtimes and
make the 6h-per-job budget harder to reason about.

**Import order is pinned explicitly** in the corpus definition, for
the reason in § Risks.

### Existing gates that stay green

Workspace tests, lint, `cargo deny`, parse-acceptance, both fuzz
targets, the never-hang storms, and `fmt:mathlib`.

## What M4a ships — and a stated exception

The architecture spec says every milestone after M0 ships something
independently useful. **M4a does not**, and this is recorded rather
than dressed up: it produces no user-visible feature, and a
diagnostic-only `leanr defeq` subcommand would be a contrivance, not a
deliverable.

What M4a delivers is a `leanr_meta` core independently verified
against the oracle, plus the query harness and two-tier gate that
every later M4 slice reuses. The "independently useful" rule holds at
the M4 level, not per sub-slice — an unavoidable consequence of
decomposing M4 at all.

## Risks

1. **The approximation flags have no specification.** They define
   which terms unify, and the only description of them is Lean's
   implementation. Differential testing is the sole way to find
   divergence, and only for queries the corpus happens to contain.
   Highest-risk item in the slice.

2. **The corpus is biased — M4a's honest limitation.** Mathlib
   constants are fully elaborated, hence mvar-free. Tier 2's mvar
   queries are *synthesized by us*, abstracting implicit arguments
   back out: a plausible guess at what the elaborator asks, not a
   record of it. Real validation arrives in M4b, when the term
   elaborator generates queries naturally. A green M4a is therefore
   strong evidence of reduction fidelity and weak evidence of
   unification fidelity. Better to build M4a knowing this than to
   discover it later.

3. **TC results depend on instance registration order, i.e. import
   order.** `synth_order` is computed once at registration, so two
   runs registering instances in different orders can search
   differently. The corpus pins import order explicitly, or nightly
   results become irreproducible in a way that looks like a real
   regression.

4. **Table-key normalization granularity.** Too coarse and distinct
   goals share a table entry, giving wrong answers; too fine and
   search blows up exponentially. No test isolates this — it appears
   as either a wrong instance or a timeout.

5. **Cache-key completeness.** Mitigated by the `size_of::<Config>()`
   guard, but worth restating: Lean shipped this bug twice.

## Out of scope (and where it lands)

- **The term elaborator, `TermElabM`, and the postponement /
  synthetic-mvar ladder** → M4b. The scheduling ladder is the highest
  fidelity risk in all of M4 (the accepted language is a fixpoint of
  an undocumented schedule), and it needs a working `MetaM` beneath it
  to be testable at all.
- **The app elaborator, `elabAsElim`, dot notation** → M4b/M4c.
- **Coercions, unification hints, `binop%`** → with the term
  elaborator; unification hints are consulted from the `is_def_eq`
  failure path, so the seam is left in place in M4a but unpopulated.
- **The match/equation compiler** → later M4 slice.
- **The `do` elaborator** → later M4 slice. Note that the new
  extensible `do` elaborator became the default in Lean v4.32.0
  (legacy behind `set_option backward.do.legacy true`), so the target
  is the new one: a direct CPS elaborator over `Expr` where the
  continuation is a deferred elaboration action, not the legacy
  code-tree IR that round-trips through `Syntax`.
- **Tactics** → later M4 slice.
- **The VM** → later M4 slice.
- **salsa wiring** → M5.
