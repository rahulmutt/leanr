# leanr — Architecture & Roadmap Design

**Date:** 2026-07-04
**Status:** Approved design, pre-implementation

## What leanr is

leanr is a pure-Rust implementation of the Lean 4 toolchain. The end goal is a
**full drop-in replacement** for the official `lean`/`lake` toolchain: leanr
elaborates `.lean` source directly, executes Lean-defined tactics and macros,
and builds Mathlib unmodified.

Its defining bets:

1. **Incremental latency first.** Edit any declaration in Mathlib — even in a
   low-level file — and get re-checked feedback in sub-second time, with
   downstream validation in seconds. Declaration-level invalidation, not
   file-level.
2. **Aggressive and correct caching.** Cache validity is structural (content
   hashes of inputs), never heuristic. Local and remote caches share one
   abstraction.
3. **Rust-quality ergonomics.** One `leanr` binary with cargo-quality
   diagnostics, an LSP server backed by the same engine, a formatter, and a
   doc generator.

## Decisions locked in

| Decision | Choice |
|---|---|
| End goal | Full drop-in toolchain (elaborator + evaluator included) |
| Compatibility target | Pinned to one Lean toolchain version — the version Mathlib pins at project start, recorded in-repo as the **oracle toolchain**. Newer versions are tracked only after Mathlib builds. |
| Correctness method | Differential testing against the official toolchain (the oracle) at every layer |
| Performance bar | Declaration-level incremental latency is the headline; clean-build throughput secondary |
| v1 tooling scope | Cargo-style CLI with lake compatibility, LSP server, distributed cache, formatter, doc generator |
| Sequencing | Useful milestones — every phase after M0 ships something independently adoptable |
| Architecture | Approach A: a single salsa-style incremental query engine is the spine; CLI/LSP/cache are frontends or query implementations |

## Non-goals

- Reproducing Lean's compiled-code *memory* semantics (refcount observability,
  pointer identity). leanr matches observable evaluation results only.
- Native code generation for user programs in v1 (the VM interprets; a JIT is
  a later internal optimization).
- Tracking Lean master or multiple Lean versions before M6 completes.
- A new surface language or any deviation from pinned-Lean semantics.

## Architecture

A cargo workspace. Dependency discipline: one query engine at the center;
everything else is either a query implementation or a thin frontend.

```
leanr_kernel    Trusted core: expressions, environments, definitional
                equality, inductive types, reduction. Depends on nothing
                else in the workspace. The only code whose bugs can make
                leanr accept a false theorem — kept small and auditable.
leanr_syntax    Lexer + Lean's extensible parser. Lossless rowan-style
                green/red syntax trees; one tree serves the elaborator,
                the formatter, and the LSP.
leanr_elab      Elaborator: metavariables, unification, typeclass
                resolution, macro expansion, tactic host.
leanr_vm        Bytecode VM executing Lean code (tactics, macros,
                lakefile.lean) + Rust implementations of core @[extern]
                primitives.
leanr_olean     .olean reader/writer — interop with official artifacts.
leanr_query     The salsa-style incremental engine (initially the salsa
                crate; replaceable behind our own trait boundary).
leanr_build     Lake-compatible package model + build orchestration.
leanr_cache     Content-addressed store: memory / disk / remote tiers.
leanr_lsp       LSP frontend.
leanr_fmt       Formatter.
leanr_doc       Doc generator.
leanr_cli       The `leanr` binary — thin frontend, no logic of its own.
```

Two boundaries are load-bearing:

- **The kernel is the trusted computing base.** Nothing reaches into it; it
  reaches into nothing. Soundness bugs can only live there or in what the
  elaborator feeds it.
- **CLI and LSP are the same program.** Both issue queries against the same
  engine, so editor performance and CI performance cannot diverge.

## The incrementality model

Everything is a memoized query: `parse(file)`, `elaborate(decl)`,
`kernel_check(decl)`, `resolve_package(dep)`. The engine tracks dependencies
automatically; an edit invalidates exactly the queries whose inputs changed.

The hard problem: Lean's grammar and environment are **sequentially
extensible**. A `notation` or `macro` command changes how later commands
parse; elaboration extends the environment later declarations see. Naively
every declaration depends on everything above it, collapsing incrementality
back to file granularity.

The answer is **firewall queries**. A file is a sequence of commands. Command
*N* depends not on command *N−1*'s full result but on two narrow fingerprints:

- the **parser-state fingerprint**: active notations, macros, precedences;
- the **environment fingerprint restricted to names actually referenced**,
  recorded during elaboration of *N* itself.

Editing a proof body changes neither fingerprint, so only that declaration
re-elaborates and nothing downstream wakes up. Editing a `notation` command
genuinely invalidates what follows — which is correct behavior.

Consequences:

- **Proof bodies are opaque to dependents.** Downstream declarations depend on
  a theorem's statement, never its proof term. Re-proving a lemma re-checks
  one declaration, not its ten thousand users.
- **Correct caching is structural.** A query result is reusable iff its input
  fingerprints match. Disk and remote caches are persisted query results keyed
  the same way — there is no separate invalidation logic to get wrong.

## Executing Lean code (the VM)

Tactics, macros, and `lakefile.lean` are Lean programs, so leanr includes an
evaluator: Lean core IR compiled to a compact bytecode, run on a
register-based VM in `leanr_vm`.

- **Interpreter first** — correctness and debuggability over speed. A
  Cranelift JIT over the same bytecode is a later, purely internal
  optimization gated on differential-test confidence.
- **Externs:** Rust implementations of Lean's `@[extern]` runtime primitives
  (Nat/Int bignum, String, Array, IO, ST). The surface is finite and
  enumerated from the oracle toolchain; every extern gets a differential test.
- We match observable evaluation results, not memory layout (see Non-goals).

## Diagnostics & error handling

- Every user-facing error has a **stable error code** (`leanr explain E0421`),
  a source span with labels, and a `help:` suggestion where one exists.
  Rendered by one miette/ariadne-style renderer shared by CLI and LSP.
- Internal errors are never swallowed into "elaboration failed" — they panic
  with a report-this-bug message including the query trace.
- Cache trust is always answerable: `leanr build --no-cache` bypasses all
  tiers; `leanr cache verify` re-derives a sample of cached results and diffs.

## Caching tiers

One abstraction, three tiers:

1. in-memory query memoization (the engine itself);
2. on-disk content-addressed store in `.leanr/`;
3. optional remote HTTP content-addressed cache (sccache-style).

Keys are `hash(query kind, input fingerprints, toolchain fingerprint, leanr
version)`. The remote tier replaces `lake exe cache`, but per-declaration
rather than per-file: a CI cache hit survives edits to unrelated declarations
in the same file.

## Security posture

Trust boundaries (per devkit security-practices):

- **Remote cache entries and third-party `.olean` files are untrusted input.**
  Default: everything imported is kernel-checked. Signed entries from a
  trusted org cache may skip the re-check — deliberately, never accidentally.
- The `.olean` reader and the VM are fuzzed continuously (they parse/execute
  attacker-controllable bytes).
- `lakefile.lean` execution is arbitrary code execution by design (as with
  lake); leanr does not pretend otherwise, but the VM gives us a natural
  place for a future sandbox/permissions story.
- Supply chain: dependency scanning (cargo-audit/cargo-deny) and secret
  scanning in CI from M0.

## Testing strategy

Four layers, cheapest first (devkit testing-practices: speed-tiered, each
layer catches what the previous can't):

1. **Unit + property tests per crate.** proptest on the kernel (generated
   well-typed terms survive reduction/defeq round-trips); parser round-trips
   `parse → print → parse` on arbitrary syntax.
2. **Golden/differential tests against the oracle.** The pinned toolchain's
   own test suite plus our corpus; diagnostics, elaborated terms, and `.olean`
   output compared against official lean. The oracle is used mercilessly —
   we have a reference implementation and that is leanr's greatest testing
   asset.
3. **Incrementality tests.** A harness applies a targeted edit and asserts
   *which queries re-ran*. Over-invalidation is a performance bug;
   under-invalidation is a correctness bug; both are tested identically.
4. **The Mathlib gauntlet.** CI elaborates a growing slice of Mathlib and
   requires identical results to the oracle. Fuzzing runs on the `.olean`
   reader and VM.

Benchmarks (criterion + a Mathlib-scale macro-benchmark suite) are tracked in
CI from M1 so performance regressions are caught like correctness ones.

## Developer environment & repo navigability

Per devkit developer-environment and navigable-codebases:

- **mise-pinned toolchain**: Rust version, the oracle Lean toolchain, and all
  dev tools pinned in `mise.toml`; devenv.nix only if mise can't provide a
  tool.
- **Named tasks** (mise tasks): `build`, `test`, `test:golden`, `gauntlet`,
  `bench`, `fuzz`, `lint` — CI runs the same tasks contributors run.
- **Front door from M0**: README (what/why/quickstart), AGENTS.md (how agents
  should work here), and a codebase map documenting the crate boundaries and
  the query-engine architecture. Single-sourced; onboarding verified by
  running it.

## Milestones

Every milestone after M0 ships something independently useful.

- **M0 — Foundations.** Repo skeleton, mise environment, CI, the query engine
  walking end-to-end on a toy query, `.olean` reader. The only non-shipping
  milestone; kept short.
- **M1 — `leanr check`.** The kernel re-checks all of Mathlib from `.olean`s,
  in parallel. *Ships:* the fastest Mathlib proof checker; an independent
  Rust audit of Lean's kernel.
- **M2 — `leanr build`.** Lake-compatible orchestrator driving the *official*
  lean binary, with content-addressed local + remote caching. *Ships:* a
  drop-in build accelerator and `lake exe cache` replacement for any Lean
  project — leanr's first real users; forces the package model right early.
- **M3 — Parser + formatter.** Full extensible-grammar parser, lossless
  trees, `leanr fmt`. *Ships:* the first Lean formatter; parser validated by
  round-tripping all of Mathlib.
- **M4 — Elaborator + VM.** Elaborate core/std, then growing Mathlib slices,
  differential-tested throughout. M2's orchestrator swaps official lean for
  leanr per-module, so adoption is incremental, not a cliff.
- **M5 — LSP.** The incrementality payoff: sub-second feedback editing
  Mathlib in VS Code.
- **M6 — Full gauntlet.** All of Mathlib elaborates identically; `leanr doc`;
  the drop-in claim is made publicly and defended by CI.

## Risks & mitigations

- **Elaborator fidelity is the long pole.** Mathlib exercises dark corners of
  unification and typeclass resolution; "almost identical" elaboration is
  not identical. Mitigation: differential testing from the first declaration;
  M4 progress measured in Mathlib slices, not features.
- **Firewall fingerprints must be sound.** An under-inclusive environment
  fingerprint silently caches wrong results. Mitigation: incrementality test
  harness treats under-invalidation as a release-blocking correctness bug;
  `leanr cache verify` exists from M2.
- **Oracle drift.** Mathlib eventually moves past the pinned toolchain.
  Mitigation: the pin is a project-level constant, revisited only at
  milestone boundaries; the compat layer (olean version, extern list) is
  isolated in `leanr_olean`/`leanr_vm`.
- **salsa fit.** If the salsa crate's model fights Lean's sequential
  environments, `leanr_query`'s trait boundary lets us replace the engine
  without rewriting query implementations.

## Next step

Invoke the writing-plans skill to produce the M0+M1 implementation plan,
applying all devkit skills (developer-environment, testing-practices,
writing-clean-code, security-practices, navigable-codebases) in full.
