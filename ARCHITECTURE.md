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
- `crates/leanr_check` — the parallel kernel-check driver (default as of
  M1-final; `leanr check`'s `--sequential` flag opts back into the
  single-threaded `replay` reference path). Builds a dependency DAG over
  a frozen `Arc<CheckedConstants>` (decoded declarations gated by
  per-entry admitted flags) and drives it with a std-thread worker pool
  (a ready-queue `Mutex`+`Condvar`, per-task atomic dependency counters,
  a cancellation flag, a first-failure slot — no rayon). Def/axiom/
  theorem/opaque tasks are fully lock-free: a worker checks against the
  gated table and flips the entry's flag. Inductive/quotient blocks are
  *also* lock-free — the kernel regenerates their constructors/
  recursors/inductive-infos in per-worker scratch, then each survivor is
  translated by `resolve_constant_info`, a **read-only** lookup against
  the frozen store (a miss means the survivor differs from its decoded
  twin and the check is rejected; on all-hits the resolved ids are
  compared to the twin with `constant_info_eq`). The persistent `Store`
  is `Arc`-frozen after decode and never mutated again — no promotion,
  no interior mutability, no `unsafe`. Verdict-equivalent to sequential
  `replay`, proved by the full-stdlib differential gate
  (`mise run check:stdlib:differential`, kept as a permanent regression
  gate). Spec:
  `docs/superpowers/specs/2026-07-10-m1-final-parallel-mathlib-design.md`.
- `crates/leanr_build` — Lake-compatible package model + module graph
  (M2a: lakefile.toml schema, translate-config bridge, manifest-driven
  git materialization, import DAG) and the build orchestrator (M2b:
  `setup` plans per-module official-`lean` invocations into leanr's own
  layout under `.leanr/build/`; `pool` is a fail-fast dependency-counter
  scheduler; `compile` drives one `lean` process per module). M2c adds
  two more modules on the same `pool`/`setup` seam: `fingerprint`, a
  recursive content-Merkle over each module's source, semantic setup
  inputs, toolchain/leanr-version, package provenance, and the
  fingerprints of its direct imports (so one fixed-size hash captures
  the whole transitive input closure — no mtimes); and `cache`, the XDG
  content-addressed artifact store (`$XDG_CACHE_HOME/leanr/cache/`,
  sharded blob tree + fingerprint-keyed manifests, atomic flock-guarded
  writes, hardlink materialization into the project's `.leanr/build/`
  layout with a copy fallback across filesystem mounts) plus `verify`
  (store-integrity check) and `gc` (LRU eviction to a size cap).
  `leanr build` is cache-aware by default (a fingerprint hit
  materializes from the store and skips `lean` entirely); `--no-cache`
  reverts to M2b's unconditional path (neither reads nor writes the
  cache) and `--force` always runs `lean` then refreshes the cache with
  the result. Dependency sources live in the per-user XDG cache
  (`$XDG_CACHE_HOME/leanr/src/<name>/<rev>/`, immutable, flock-guarded),
  as does the bridge cache; Lake-layout interop is retired as of the
  M2b spec (`docs/superpowers/specs/2026-07-12-m2b-build-orchestrator-design.md`).
  `leanr build` / `leanr build --dry-run` / `leanr cache verify [--deep]`
  / `leanr cache gc --max-size`. No kernel dependency. M2d adds
  `remote`, the network tier over the same CAS: `leanr build` reads
  through a dumb-HTTP remote on local miss (blobs verified against
  their content keys before insertion — see docs/THREAT_MODEL.md
  §Remote cache ingestion), `leanr cache push` uploads via presigned
  S3 PUTs, `leanr cache get` prefetches the closure. The remote
  mirrors the CAS layout under `v1/` with zstd-compressed blobs;
  remote availability affects speed, never correctness (`--no-remote`
  / `LEANR_REMOTE_CACHE`).
- `crates/leanr_syntax` — lossless Lean source trees + the extensible
  parser (M3a). Trust boundary: source text is untrusted input
  (`docs/THREAT_MODEL.md`) — the lexer/parser never panic and always
  terminate, fuzzed via `mise run fuzz:syntax`, and `text(parse(src))
  == src` holds for every input including parse errors (error nodes +
  command-resync recovery). The parser interprets a ParserDescr-shaped
  combinator tree (`grammar::Prim`) over an explicit, fingerprintable
  `GrammarSnapshot` (token table + Pratt categories) — the
  parser-state firewall seam the architecture's incrementality story
  needs, kept batch-mode until M5. M3a ships the builtin grammar
  (ports of the pinned toolchain's compiled `@[builtin_*_parser]`
  set, enumerated in
  `docs/superpowers/specs/2026-07-13-m3a-builtin-surface.md`);
  imported/declared grammar (ParserDescr interpretation from
  `.olean`s) is M3b. Correctness bar: byte round-trip + node-exact
  equality against official parse trees
  (`tests/fixtures/syntax/`, dumped by `dump_syntax.lean`, regen via
  `mise run fixtures:regen`). No workspace-crate dependencies.
  `leanr parse [--dump]` in the CLI.
- `crates/leanr_cli` — the `leanr` binary. Thin: argument parsing and
  printing only, so CLI and (future) LSP can never diverge in behavior.

## Why the boundaries fall here

- The `leanr_kernel` is the trusted computing base — it depends on
  nothing in the workspace and nothing reaches into it.
- `leanr_check` depends on `leanr_kernel` (its check-only API:
  `CheckedConstants`, `check_declaration`, `resolve_constant_info`,
  `constant_info_eq`) and `leanr_olean` (loaded modules), and sits
  between them and `leanr_cli` in the crate order. It is outside the
  TCB: every kernel-check verdict it produces is one a sequential
  `replay()` over the kernel alone could have produced, so all `std`
  threading, scheduling, and cancellation logic lives here rather than
  in `leanr_kernel`.
- CLI and LSP are frontends over the same query engine by design;
  logic in `leanr_cli` is a bug.

## Oracle

`lean-toolchain` pins the official Lean version Mathlib uses — our
differential-testing oracle. Golden fixtures live in `tests/fixtures/`
(regenerate: `mise run fixtures:regen`).
