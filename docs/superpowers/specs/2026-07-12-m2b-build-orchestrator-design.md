# M2b — build orchestrator — design spec

Date: 2026-07-12. Milestone: M2 ("`leanr build` — Lake-compatible
orchestrator with content-addressed caching") — second slice. Parent:
`2026-07-04-leanr-architecture-design.md` (§Milestones, M2);
predecessor: `2026-07-11-m2a-package-model-design.md`.

## Problem

M2a resolves a workspace and plans a build; nothing executes it. Bare
`leanr build` still errors "coming in M2b". Until M4, official `lean`
is the only program that can turn a `.lean` file into a `.olean`, so
M2b's job is everything *around* the compiler: scheduling, per-module
invocation, artifact layout — one `lean` process per module (Lake's
own model, and forced: no batch or persistent worker mode exists).

## Goal

Bare `leanr build` works on a fresh clone: resolve the workspace
(M2a), then compile every planned module by driving pinned official
`lean` processes in parallel over the module DAG, **unconditionally**
(no up-to-date skipping), writing artifacts to leanr's own layout.

Acceptance target: the full pinned-Mathlib closure (~8,564 modules)
built from a fresh clone, every artifact byte-diffed against
lake-built artifacts.

*Ships:* the first `lake`-free source build of Mathlib, and the
scheduler/process layer that M2c wraps with caching and M4 swaps
per-module for leanr's own elaborator (the incremental-adoption seam
named in the architecture spec).

## Scope decisions (agreed in brainstorming)

- **Libraries only.** `.olean`-family + `.ilean` for `lean_lib`
  targets. No `-c`, no `leanc`, no linking; `lean_exe` stays
  modeled-but-unplanned and errors clearly if requested. Motivation:
  covers the acceptance target with zero C surface, serving the
  project's long-term goal of avoiding the C toolchain. The recorded
  post-M6 candidate for native code is a pure-Rust backend
  (Cranelift + Rust object emission/linking), *not* LLVM — LLVM would
  link a giant C++ codebase into leanr, defeating that motivation.
- **Unconditional rebuilds.** No skip logic of any kind in M2b.
  Fingerprint design is where staleness-correctness risk lives (an
  under-inclusive fingerprint is a release-blocking bug per the
  architecture spec) and gets its own M2c design, not a rushed
  version here. Consequence, stated honestly: an interrupted build
  redoes everything next run — acceptable precisely because M2c is
  the immediate next slice.
- **Lake interop is retired.** This spec consciously supersedes
  M2a's "lake and leanr interoperate on the same checkout in both
  directions": leanr does not write Lake's layout or `.trace` files.
  leanr is its own build system that reads Lake *configuration*
  (lakefile + manifest), not one that populates `.lake/build`. This
  frees M2c to design leanr's cache on its own terms.
- **Layout freedom, cargo's model:** immutable inputs shared
  per-user (XDG), build outputs per-project (§Layout). Revises M2a's
  shipped `.lake/packages/` materialization.
- **Full-Mathlib acceptance.** One expensive recorded run, matching
  M1/M2a precedent.

Explicitly **out of scope** (and where it lands): up-to-date
skipping, incremental rebuilds, `cache verify` (M2c); remote cache
(M2d); `lean_exe`, native code, a Lean backend of our own (post-M6;
Cranelift candidate recorded above); `precompileModules`, plugins,
dynlibs — error naming the package if a config requires them (the
Mathlib closure does not: aesop pins `precompileModules = false`);
test drivers; custom targets (M2a's discard-with-warning stands —
proven safe for ProofWidgets, see below); `--keep-going` (deferred
until someone wants it).

## Key empirical facts (verified 2026-07-12 on the pinned toolchain, 4.32.0-rc1)

- `lake build --verbose` shows the per-module invocation:
  `LEAN_PATH=<lib dirs> lean <src>.lean -o <mod>.olean -i <mod>.ilean
  -c <mod>.c --setup <mod>.setup.json --json`. One process per
  module; `-c` is a separate request we simply don't make.
- `--setup` ("supersedes the file's header") is a JSON file naming:
  `importArts` — the **exact artifact paths** of each direct import
  (`.olean`, plus `.ir`/`.olean.server`/`.olean.private` for
  module-system imports); `options` — the owning lib's `leanOptions`
  (Mathlib sets nine per lib); `package`, `name`, `isModule`,
  `plugins`, `dynlibs`. Because the setup file controls import
  resolution explicitly, leanr's layout freedom costs nothing in
  `lean` interop. `LEAN_PATH` is still required for transitive
  `.olean` loads; lake sets both, and so do we.
- Module-system modules (`module` keyword; all of Mathlib on this
  toolchain) each produce an artifact family: `.olean`,
  `.olean.private`, `.olean.server`, `.ir`, `.ilean`. Sibling paths
  are derived by `lean` from `-o`.
- `.ilean` is module-relative JSON (declaration positions, module
  names) — no absolute paths; the whole artifact family is
  byte-diffable against oracle artifacts.
- Pinned ProofWidgets **commits its built widget JS to git** (21
  files under `widget/js/`), so its `include_str` elaboration works
  from a bare checkout — no npm, no cloud release. Discarding its
  custom `needs`/`widgetJsAll` targets (M2a's existing warning) does
  not block building it from source.
- The `.mathlib` checkout already holds lake-built artifacts for the
  full closure (used by M2a's module-set oracle), so acceptance
  never needs to run lake itself. Some may have arrived via
  Mathlib's CI cache rather than a local lake run — still built by
  lake on the same pinned toolchain; cross-machine determinism is
  exactly what the byte-diff then tests, and any divergence it
  surfaces is documented, not skipped.

## Layout

**Sources — XDG-shared, immutable (revises M2a):** dependency
checkouts live at `$XDG_CACHE_HOME/leanr/src/<name>/<rev>/`
(fallback `~/.cache/leanr`; XDG resolution hand-rolled, no new
crate) and are shared across projects. Keying by rev makes a
checkout immutable-once-created: fetch clones, checks out the
manifest rev, `rev-parse`-verifies (M2a's logic, reused), and never
touches it again — a new rev is a new directory, never a mutation.
Concurrent materialization of the same rev takes an advisory `flock`
on a lockfile beside the checkout (`libc`, already a dependency;
unix-only, matching the bridge's existing cfg split). A pre-existing
directory that fails rev verification is an error naming the path —
never a silent re-clone.

**Artifacts — project-local:** everything under
`.leanr/build/<package>/` — dependencies' artifacts included, since
shared immutable checkouts cannot hold outputs. Per module:
`.leanr/build/<pkg>/lib/<Module/Path>.{olean,olean.private,olean.server,ir,ilean}`;
leanr-generated setup files under `.leanr/build/<pkg>/setup/`. One
directory to delete; a future `leanr clean` is trivial.

**Bridge cache — moves to XDG** (`…/leanr/config-cache/`): already
content-keyed by blake3 of the lakefile, so cross-project sharing is
staleness-free and a second project's fresh clone skips
`lake translate-config` entirely. In-project `.leanr/` then holds
build outputs only.

**Owned consequences:** the dry-run plan's "no absolute paths in
JSON output" rule is revised — module sources now live outside the
project root, so the JSON plan carries package-relative file paths
plus a per-package source-dir field. Path deps and the root package
are unaffected (they build in place). Nothing consumes
`.lake/packages` anymore; M2a's tests are updated with the move.

## Architecture

Three components inside `leanr_build` (which stays off the kernel's
dependency graph and gains no workspace-crate dependencies),
consuming M2a's `Workspace` unchanged:

1. **`setup`** — pure functions computing each module's invocation
   from the graph: artifact output paths (our layout), the setup
   JSON (importArts from direct deps' artifact paths — workspace
   modules from our layout, toolchain modules from
   `lean --print-libdir`; `options` from the owning lib's
   `leanOptions`; `isModule` from the scanner), and the environment
   (`LEAN_PATH` = every package's `.leanr/build/<pkg>/lib`).
   Deterministic; testable without running anything.
2. **`pool`** — the `leanr_check` scheduler shape, reimplemented for
   subprocess jobs (~150 lines; deliberately *not* extracted into a
   shared crate — flagged as an optional later refactor): per-module
   atomic dependency counters over `graph.deps`, a ready-queue
   `Mutex`+`Condvar`, `--jobs N` workers (default: available cores),
   a cancellation flag, a first-failure slot. Greedy on the critical path — no
   wave barriers (M2a's `waves` remain display-only in the dry-run
   plan). **Fail-fast:** on first failure, queued work is abandoned,
   in-flight processes run to completion, the failure is reported
   with that module's diagnostics. The pool is generic over its job
   ("module ready → run job → outcome") — the seam where M2c inserts
   cache lookup and M4 swaps in leanr's elaborator.
3. **`job`** — spawn `lean` with an explicit argv (no shell): source
   path, `-o`/`-i` (siblings derived by lean), `--setup`, `--json`;
   captured output. No timeout — a Mathlib module legitimately
   elaborates for minutes; Ctrl-C kills the process group (same
   `libc` mechanism as the bridge). `--json` diagnostics are parsed
   and rendered: warnings surfaced inline, errors attributed to
   file/line. On failure the module's declared outputs are deleted,
   so a failed build never leaves partial artifacts a later run
   could trust.

**Toolchain discovery** reuses M2a's pattern: the elan shim resolves
`lean-toolchain` from the workspace root (as `LakeInvoker` does for
lake); `lean --print-libdir` is resolved once at startup
(`ResolveOptions.toolchain_olean_dir` already carries it).

**CLI:** `leanr build [targets] [--jobs N]`; `--dry-run` unchanged.
Progress: streaming `[built/total] Module.Name (elapsed)` lines,
warnings inline, end summary — mirroring dry-run's human-output
conventions.

**New cargo dependencies: none.** `serde_json` (setup files),
`blake3`, and `libc` (flock, process groups) are already justified
in-tree.

## Error handling & trust

- Every error names its module/package and the fixing action: a
  failing module → file, lean's diagnostics verbatim, exit status; a
  wrong-rev shared checkout → the XDG path and what diverged; a
  package requiring `precompileModules`/plugins → which package and
  that M2b doesn't support it.
- Threat surface (`docs/THREAT_MODEL.md` gains an M2b section):
  running `lean` on package sources is arbitrary code execution by
  design (elaboration runs metaprograms) — same posture as the M2a
  bridge and lake itself. The XDG shared cache is a new
  cross-project surface: entries are keyed by `<name>/<rev>` and
  rev-verified on every use, so a tampered checkout fails
  verification and errors rather than being trusted; the bridge
  cache stays content-keyed, so sharing cannot serve stale or
  foreign config. Setup files are leanr-written, never parsed;
  leanr never decodes `lean`'s outputs in M2b (decoding stays in
  `leanr_olean`, used only by test oracles).
- Subprocess hygiene as established: explicit argv, no shell,
  captured stderr, process-group kill on Ctrl-C.

## Testing

Oracle discipline: correctness is defined against pinned official
lake/lean.

**Unit tier (CI, every commit):**

- `setup`: golden tests over a synthetic multi-package workspace —
  importArts paths, per-lib `leanOptions` propagation, `isModule`,
  `LEAN_PATH` assembly, artifact-path derivation.
- `pool`: synthetic DAGs with instant fake jobs — dependency order
  respected, parallelism bounded by `--jobs`, first failure cancels
  queued-but-not-in-flight work, failure attribution, no deadlock on
  chains/diamonds/wide fan-out.
- XDG resolution (env override); shared-cache `flock` contention
  (two threads materialize the same rev: one clones, one waits, both
  verify); failed-job artifact deletion.

**Differential tier (local, needs elan + network — like
`check:mathlib`):**

- **Probe-project oracle** — small fixture projects covering the
  feature matrix (plain modules, `module`-keyword modules, per-lib
  `leanOptions`, a git dependency, `prelude`): each built by pinned
  lake *and* by leanr; every artifact in the family byte-diffed.
  Cheap; catches invocation drift feature by feature.

**Acceptance (the M2b bar; results recorded here on completion):**
in a temp directory with a redirected `XDG_CACHE_HOME` (full
isolation), fresh `git clone` of pinned Mathlib → `leanr build` →
exit 0; all ~8,564 planned modules' artifact families byte-diffed
against the lake-built artifacts in `.mathlib`; zero mismatches (any
legitimate divergence documented and fixed, not skipped); wall time,
`--jobs`, and module count recorded. One expensive run, hours,
accepted knowingly.

New/changed mise tasks: the probe oracle joins `build:differential`;
`build:acceptance` is redefined as the M2b full-build acceptance run
(fresh clone → build → diff), replacing its M2a dry-run meaning. CI
runs the unit tier only, matching the existing split.

## Constraints (inherited)

- `leanr_kernel` untouched; `leanr_build` stays off the kernel's
  dependency graph and gains no workspace-crate dependencies.
- Oracle discipline: the Mathlib pin and `lean-toolchain` are
  project constants, revisited only at milestone boundaries.
- Environment: tools mise-pinned; no new cargo dependencies needed.
- Lint gate (`mise run lint`) per commit; full gate (`mise run ci`)
  where a task says so; conventional-commit prefixes.

## Next step

Invoke the writing-plans skill to produce the M2b implementation
plan.
