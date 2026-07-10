# Architecture

One incremental query engine is the spine; everything else is a query
implementation or a thin frontend. Full design:
`docs/superpowers/specs/2026-07-04-leanr-architecture-design.md`.

## Crates (current)

- `crates/leanr_kernel` — the trusted computing base: kernel data
  types (`Name`, `Level`, `Expr`, `ConstantInfo`, `Environment`).
  Depends on nothing in the workspace; nothing reaches into it. Data
  only until M1b adds the checker. Values can originate from untrusted
  bytes, so all traversals (including `Drop`) are iterative.
  `crates/leanr_kernel/src/bank/` holds the compact index-based term
  bank (id types, probe table, value/name/level banks, kvmap/spill
  pools, and a scratch region with promotion) built to close the
  ~30 GiB whole-stdlib memory wall of the old `Arc`-per-node
  representation; see
  `docs/superpowers/specs/2026-07-06-compact-expr-term-bank-design.md`
  for the full 3-phase design. As of the kernel-migration flip
  (`docs/superpowers/specs/2026-07-06-term-bank-kernel-migration-design.md`,
  phase 2), the bank IS the kernel's representation: `subst`,
  `local_ctx`, `tc`, `quot`, `inductive`, `env`, and `replay` all run
  on `bank::{ExprId, NameId, LevelId}`, and `Environment`/`ConstantInfo`
  are id-native. As of the direct-to-id decode flip
  (`docs/superpowers/specs/2026-07-10-direct-to-id-decode-design.md`,
  phase 3), `leanr_olean` decodes `.olean` bytes straight into the
  caller's term-bank store — `interp`'s only remaining Arc-emitting
  decode is the `Syntax` metadata family (`Syntax`, `SourceInfo`,
  `Substring`, `Preresolved`), an opaque payload the kernel never
  inspects. The Arc declaration family (`ArcConstantInfo`,
  `ArcDeclaration`, the `Arc*Val` structs, and the `intern_module`/
  `intern_declaration` bridges) has no production caller left; it
  survives solely as `#[cfg(test)]` kernel test support (hand-rolled
  fixture `Environment`s in `testenv.rs`, `quot`/`inductive` unit
  tests, and the replay differential harness).
- `crates/leanr_query` — the salsa-based incremental engine. Everything
  computable is a memoized query; **early cutoff** (a recomputed query
  whose value is unchanged does not wake its dependents) is the
  mechanism the whole incrementality story rests on.
- `crates/leanr_olean` — reader for official Lean `.olean` artifacts.
  Trust boundary: input bytes are untrusted (`docs/THREAT_MODEL.md`).
  Two phases: `raw` walks the compacted region into a validated,
  offset-memoized DAG (the entire untrusted-bytes surface, fuzzed via
  `mise run fuzz`); `interp` decodes it directly into the caller's
  term-bank `Store` via the bank's typed intern-constructors
  (explicit-stack walk, olean-offset → id memo), yielding id-native
  `ConstantInfo`s — only the Syntax metadata family is still built as
  Arc trees, as an opaque payload. Golden-tested against the oracle
  (`mise run fixtures:regen`) and swept over the full toolchain
  stdlib (`mise run sweep:stdlib`).
- `crates/leanr_cli` — the `leanr` binary. Thin: argument parsing and
  printing only, so CLI and (future) LSP can never diverge in behavior.

## Why the boundaries fall here

- The `leanr_kernel` is the trusted computing base — it depends on
  nothing in the workspace and nothing reaches into it.
- CLI and LSP are frontends over the same query engine by design;
  logic in `leanr_cli` is a bug.

## Oracle

`lean-toolchain` pins the official Lean version Mathlib uses — our
differential-testing oracle. Golden fixtures live in `tests/fixtures/`
(regenerate: `mise run fixtures:regen`).
