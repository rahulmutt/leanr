# M2a — package model + module graph — design spec

Date: 2026-07-11. Milestone: M2 ("`leanr build` — Lake-compatible
orchestrator with content-addressed caching") — first slice. Parent:
`2026-07-04-leanr-architecture-design.md` (§Milestones, M2).

## M2 decomposition (agreed before this spec)

M2 as roadmapped bundles four subsystems; each is its own
spec → plan → implementation cycle, built in order:

- **M2a (this spec)** — package model + module graph: parse Lake
  configuration, materialize dependencies from the committed manifest,
  build the module DAG, ship `leanr build --dry-run`.
- **M2b** — build orchestrator: drive official `lean` workers in
  parallel over M2a's DAG, producing artifacts in Lake's layout.
- **M2c** — local content-addressed cache: fingerprints, `.leanr/`
  store, incremental rebuilds, `cache verify`.
- **M2d** — remote cache: HTTP content-addressed tier; the
  `lake exe cache` replacement (untrusted input per the threat model).

The load-bearing boundary: M2a's output (a resolved `Workspace` +
module DAG) is the interface M2b consumes; M2c/M2d share one cache
abstraction differing only in tier.

## Problem

Everything after M1 needs a package model. The kernel can check
Mathlib's `.olean`s, but leanr cannot yet answer "what is this
project, what does it depend on, and what modules exist in what
order" — and today that answer requires the user to have run official
`lake` first (`check:mathlib` steals Lake's resolved `LEAN_PATH`).

## Goal

`leanr build --dry-run` works on a **fresh clone** of any Lean project
with a committed `lake-manifest.json`: it resolves the workspace,
fetches dependencies natively (no lake invocation by the user, ever),
and prints the module-level build plan without compiling anything.

Acceptance target: the pinned Mathlib closure (Mathlib + its 8
dependencies), differential-tested against pinned official lake.
Arbitrary projects work insofar as they use the same feature surface.

Explicitly **out of scope** (and where it lands): compilation (M2b);
`lake update` semantics — resolving `require`s to revs and *writing*
manifests (later M2 slice, if demand warrants); Reservoir registry
lookups (ditto); toolchain management (elan owns it); building
`lean_exe` targets (modeled, not planned; M2b); non-declarative
lakefile.lean config — custom targets, build hooks (discarded by the
bridge with a warning; the M4 VM is the real fix).

## Key empirical facts (verified on the pinned toolchain, 4.32.0-rc1)

- Pinned Mathlib itself uses `lakefile.lean` (178 lines of real Lake
  DSL — `abbrev`s, array maps, computed options; not declaratively
  parseable). 7 of its 8 deps use `lakefile.toml`; proofwidgets uses
  `lakefile.lean`.
- `lake-manifest.json` (schema 1.2.0) records the **full transitive**
  closure: name, git URL, exact rev, `subDir`, `configFile`,
  `inherited`, git-vs-path type.
- `lake translate-config toml` **fully evaluates** a `lakefile.lean`
  and emits complete declarative TOML — including computed
  `leanOptions` arrays, per-target globs, and require options.
  Documented caveat: "non-declarative configuration will be
  discarded."

## Config acquisition: decision

For packages configured by `lakefile.lean`, evaluated config is
unrecoverable without running Lean code. Approaches considered:

- **A — native TOML parser + `lake translate-config` bridge
  (chosen).** One native config schema (the `lakefile.toml` format).
  TOML packages parse natively; `.lean`-config packages are bridged
  through pinned official lake once, cached by lakefile content hash.
  Full fidelity for evaluated config (verified on Mathlib); one parser
  to test; the bridge is exactly the component the M4 VM later
  replaces. Cost: needs the official toolchain installed for
  `.lean`-config packages — already an M2 requirement (M2b drives the
  official `lean` binary), and elan bootstraps it from
  `lean-toolchain` on a fresh clone.
- **B — declarative-subset parser for `lakefile.lean` (rejected).**
  Provably insufficient: Mathlib's `leanOptions` are computed by real
  Lean code. Silent wrong config is worse than a subprocess; also
  front-runs M3's parser with a throwaway one.
- **C — read Lake's elaborated config olean (rejected).**
  Undocumented internal format containing closures; only exists after
  lake has run, contradicting the fresh-clone requirement.

Companion decisions, same "no new machinery" logic:

- **Git fetching** shells out to the `git` CLI (official lake does the
  same; zero new linked dependencies).
- **Module headers** are scanned by a small native lexer (no
  evaluation problem exists there).
- **No salsa queries yet**: resolution is pure functions with
  fingerprint-friendly inputs; M2c wraps them in queries when
  memoization pays. Wrapping pure functions later is mechanical; the
  reverse is not.

## Interface

- CLI: `leanr build --dry-run [targets...]`, plus `--json` for
  machine-diffable output (used by the differential tests). Targets
  default to the root package's `defaultTargets`.
- `--dry-run` is **mandatory** in M2a: bare `leanr build` errors "not
  yet implemented — coming in M2b", so no misleading half-build
  exists.
- Even dry-run materializes dependencies — imports of code not on
  disk cannot be scanned. (Cargo-like: resolution touches the
  network; compilation doesn't happen.)
- Human output: resolved packages at their revs, then modules in
  topological order grouped into parallelism waves.

**Layout compatibility:** leanr materializes into Lake's own layout —
`.lake/packages/<name>/` at manifest revs — not a parallel tree, so
lake and leanr interoperate on the same checkout in both directions.
The bridge cache is the only leanr-private state, under `.leanr/`.

## Architecture

New crate `leanr_build` (named in the architecture spec). Depends on
no workspace crate except (dev-dependency only) `leanr_olean` for the
import-graph oracle test. `leanr_cli` wires it to `build`. M2b
consumes its output type: `Workspace { packages, module_graph }`.

Five components, each independently testable:

1. **`config`** — Rust types mirroring the `lakefile.toml` schema:
   `PackageConfig` (name, `defaultTargets`, `srcDir`, dirs),
   `LeanLibConfig` (name, `srcDir`, `roots`, `globs`, `leanOptions`),
   `LeanExeConfig` (modeled, never planned), `Require` (name, scope,
   rev, options). Coverage = what the Mathlib closure exercises plus
   obvious basics. Unknown keys → warning naming the key (forward
   compatibility), never a silent drop or hard error. `leanOptions`
   values are the sum type TOML admits (bool/int/string).
2. **`bridge`** — for `.lean`-config packages: run pinned
   `lake translate-config toml <out>` in the package directory, parse
   the result with `config`. Cached at
   `.leanr/config-cache/<blake3(lakefile)>.toml`; lake runs once per
   lakefile change and never for TOML packages. Running the bridge
   executes the lakefile — arbitrary code execution by design,
   identical to running lake (architecture §Security posture).
   Verified empirically: translation works in a bare checkout with no
   materialized dependencies and produces byte-identical output, so
   bridging the root config before fetching (pipeline step 2 before
   step 4) is sound. Operational notes: lake errors if the out-file
   exists (the bridge writes to a fresh temp path, then moves into the
   cache) and drops a `.lake/config` cache as a side effect (Lake's
   own directory; harmless).
3. **`manifest`** — parses `lake-manifest.json`. Version-checked:
   unknown major → clear error. Yields the flat transitive package
   list.
4. **`fetch`** — ensures `.lake/packages/<name>` is a git checkout at
   exactly the manifest rev via the `git` CLI (clone if absent;
   fetch + checkout if present at the wrong rev; `rev-parse HEAD`
   verified). A dirty or diverged checkout is an **error**, never a
   silent overwrite. Path dependencies are validated to exist.
   Independent entries fetch concurrently (plain threads suffice at
   n≈8).
5. **`modules`** — expands each `lean_lib`'s roots/globs to `.lean`
   files (glob semantics copied from Lake, verified against the
   oracle), scans each header (`prelude`, `import Foo.Bar`, stop at
   the first non-header token; parallel per file), builds the module
   DAG. Imports resolving to no workspace module are classified
   toolchain-provided (`Init`/`Std`/`Lean` …, external leaves, no
   build node) — error if not found there either. Cycles are a hard
   error naming the cycle.

New dependencies (justified per AGENTS.md): `toml` (the config
format), `serde`/`serde_json` (manifest), `blake3` (bridge cache key,
and the hash M2c standardizes on), `thiserror` (error type derives),
unix-only `libc` (`std::process` has no API to SIGKILL a process
group; needed so a timed-out `lake translate-config` and any
grandchildren holding the stderr pipe are reliably killed;
`cfg(not(unix))` falls back to `Child::kill`). Git and lake are
subprocesses, not linked deps.

## Data flow

Straight-line pure-function pipeline:

1. **Locate root** — walk up from CWD for `lakefile.toml` /
   `lakefile.lean` (TOML wins if both exist, matching Lake).
2. **Load root config** — native parse or bridge.
3. **Read manifest** — no manifest → error: "no lake-manifest.json;
   run `lake update` once and commit it" (the deferred-resolution
   boundary).
4. **Materialize packages** — fetch/verify each entry, concurrently.
5. **Load dependency configs** — per-package `configFile` decides
   native vs bridge.
6. **Build module graph** — globs → headers → DAG → cycle check.
7. **Emit plan** — topological waves; text or `--json`.

Cross-check: every root-config `require` must have a manifest entry;
a missing one means the manifest is stale → error suggesting
`lake update`, never a guess.

## Error handling & trust

- Every error names the file/package it came from and the action that
  fixes it (stale manifest → `lake update`; dirty checkout → the path
  and what diverged; bridge failure → lake's stderr verbatim).
- **No panics on untrusted bytes.** The header scanner runs over
  arbitrary file contents and must never panic — same discipline and
  fuzz treatment as the `.olean` parser (`docs/THREAT_MODEL.md`).
  Manifest/TOML parse errors are typed errors with positions.
- Subprocess hygiene: `git`/`lake` get explicit argument vectors (no
  shell), captured stderr, and timeouts — a hung
  `lake translate-config` cannot hang leanr forever.
- Threat surface, stated honestly: executing a lakefile (bridge) and
  cloning manifest-supplied git URLs are arbitrary-code-execution /
  network operations by design — exactly as with lake. New vs M1:
  manifest URLs are validated (https/ssh/path forms; no `-` prefix, so
  no git argument injection). `docs/THREAT_MODEL.md` gains a section
  for this surface.

## Testing

Oracle discipline: correctness is defined against pinned official
lake.

**Unit tier (CI, every commit):**

- `config`: the 7 real dependency `lakefile.toml`s vendored as
  fixtures + edge cases (unknown keys, every option value type,
  `«guillemet»` names).
- `manifest`: Mathlib's real manifest as fixture + malformed and
  wrong-version cases.
- Header scanner: table-driven cases (comments before imports,
  `prelude`, doc comments, unicode) + a no-panic property test over
  arbitrary bytes.
- Glob expansion + DAG assembly on synthetic tempdir package trees,
  including cycle detection.

**Differential tier (local, needs the `.mathlib` checkout — like
`check:mathlib`):**

1. **Bridge golden** — `lake translate-config` output for Mathlib's
   lakefile committed as a golden fixture; regenerated via a mise
   task; pin-bump drift is a visible diff, not a surprise.
2. **Import-graph oracle (the strong one)** — every Mathlib-closure
   module's `.olean` records its actual imports, and `leanr_olean`
   already reads them. Diff header-scanned imports against
   olean-recorded imports for all ~8,000 modules. Zero mismatches;
   any legitimate divergence is documented and fixed, not skipped.
3. **Module-set oracle** — the set of modules leanr plans for the
   `Mathlib` target equals the set of `.olean`s lake's build produced
   for it.

**Acceptance (the M2a bar; results recorded here on completion):**
in a temp directory, fresh `git clone` of pinned Mathlib (no `.lake/`,
lake never run) → `leanr build --dry-run --json` → exit 0; all 8
dependencies materialized at exactly the manifest revs (`rev-parse`
verified); plan module count matches the recorded constant; output
byte-identical to the plan computed on the pre-materialized
`.mathlib` checkout.

New mise tasks: `build:dryrun-mathlib` (differential tier); fixture
regeneration folded into `fixtures:regen`. CI runs the unit tier
only, matching the existing split.

## Constraints (inherited)

- `leanr_kernel` untouched; `leanr_build` stays off the kernel's
  dependency graph.
- Oracle discipline: the Mathlib pin and `lean-toolchain` are project
  constants, revisited only at milestone boundaries.
- Environment: tools mise-pinned; each new cargo dependency justified
  (done above).
- Lint gate (`mise run lint`) per commit; full gate (`mise run ci`)
  where a task says so; conventional-commit prefixes.

## Next step

Invoke the writing-plans skill to produce the M2a implementation
plan.
