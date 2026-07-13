# M2c — content-addressed cache & incremental builds — design spec

Date: 2026-07-12. Milestone: M2 ("`leanr build` — Lake-compatible
orchestrator with content-addressed caching") — third slice. Parent:
`2026-07-04-leanr-architecture-design.md` (§Milestones, M2);
predecessor: `2026-07-12-m2b-build-orchestrator-design.md`.

## Problem

M2b builds the full pinned-Mathlib closure from source but rebuilds
**unconditionally** — no skip logic of any kind. An interrupted build
redoes everything next run; a one-line edit rebuilds all ~8,564
modules; switching git branches or worktrees shares nothing. M2b
deferred this on purpose: staleness-correctness is where the risk
lives, and an under-inclusive fingerprint is a *release-blocking*
correctness bug per the architecture spec — it silently serves stale
artifacts. M2c is that fingerprint-and-cache slice, designed on its
own terms now that Lake-layout interop is retired.

The seam is already in place: M2b's `pool` is generic over its job
("module ready → run job → outcome"). M2c replaces the job body with
*fingerprint → cache lookup → hit: materialize (no `lean`); miss: run
`lean`, insert, materialize.* The scheduler is untouched.

## Goal

Make `leanr build` cache-aware: a module whose complete input surface
is unchanged is served from a shared, content-addressed store instead
of re-running `lean`. Reuse survives `leanr clean`, git branch
switches, worktrees, and separate project checkouts — because the
cache is keyed by content, not by filesystem location or mtime. Ship
`leanr cache verify` as the correctness safety net.

Acceptance target (recorded run, matching M1/M2a/M2b precedent): a
warm rebuild of the full Mathlib closure runs **~zero `lean`
invocations** with byte-identical artifacts; a single-leaf edit runs
`lean` for **exactly** the affected downstream cone.

## Scope decisions (agreed in brainstorming)

- **Shared content-addressed store (CAS), not in-project skip logic.**
  Reusable artifacts live in a per-user store under XDG, keyed by each
  module's fingerprint; the project's `.leanr/build/<pkg>/lib` is
  *materialized* from it (hardlink, copy fallback). This buys
  cross-project / cross-branch / cross-worktree reuse and is exactly
  the population layer M2d's remote cache will wrap. An in-project-only
  fingerprint sidecar was rejected: it cannot key a cross-machine store
  and would have to be redone for M2d.
- **Recursive content-Merkle fingerprint.** A module's key folds in
  the *content* of its source, setup inputs, toolchain, and the
  *fingerprints of its direct imports* (§Fingerprint). Pure content —
  no mtimes — so it reproduces across machines and worktrees.
  Rejected: Lake-style mtime/`.trace` sidecars (fragile across clone/
  touch/worktree; not content-addressable, so it cannot key the CAS).
- **Fingerprint includes leanr's own version.** A leanr upgrade
  invalidates the whole cache. Coarse but sound: no change in how
  leanr constructs `--setup`/argv can silently reuse artifacts built
  by old logic. Cost, stated honestly: upgrading leanr costs one full
  rebuild. (A finer manually-bumped "invocation schema version" was
  considered and rejected — it relies on humans remembering to bump.) `leanr_version_id` must be a
  *stable* identifier (release version or git commit), never a
  per-compilation nonce — otherwise warm hits would never occur between
  dev rebuilds. Dev builds derive it from `git describe`; a dirty tree
  is treated as its own (uncachable-across-edits) id.
- **`cache verify` is layered.** Default `verify` is a cheap integrity
  check (blob bytes == content key; manifests reference live blobs;
  the project's materialized files match the store). `verify --deep`
  is the oracle: rebuild a module set with `lean` and byte-diff
  against the cached artifacts, directly testing fingerprint
  completeness.
- **Manual GC only.** Ship `leanr cache gc --max-size` (LRU by access
  time over blobs); no automatic/background GC in M2c. The store is
  unbounded-by-default, like cargo's `target/`.
- **No mtime fast-path.** The fingerprint hashes source content
  directly. Whether hashing ~8,564 sources per invocation is a
  bottleneck is an empirical question; measure before adding a second
  code path. Recorded as an optional later optimization, not built.
- **Recorded full-Mathlib acceptance.** One expensive run, matching
  M1/M2a/M2b precedent.

Explicitly **out of scope** (and where it lands): remote / shared-team
cache upload & download, and ingesting *untrusted* remote blobs (M2d —
this spec's CAS and `verify` integrity check are the seam it wraps);
mtime fast-path (deferred, measure first); automatic/background GC
(deferred); `lean_exe`, native code, plugins/dynlibs-requiring configs
(unchanged from M2b — error naming the package; the Mathlib closure
needs none); `--keep-going` (still deferred until wanted).

## Key facts carried from M2b (the fingerprint's input surface)

M2b established that the `--setup` JSON is the **complete** declaration
of what a per-module `lean` invocation depends on. That enumeration is
what makes a sound fingerprint tractable:

- Per-module invocation:
  `LEAN_PATH=<lib dirs> lean <src>.lean -o <mod>.olean -i <mod>.ilean
  --setup <mod>.setup.json --json` (we omit `-c`). Sibling artifacts
  (`.olean.private`, `.olean.server`, `.ir`) are derived by `lean`
  from `-o`.
- `--setup` names: `importArts` (exact artifact paths of each direct
  import), `options` (the owning lib's `leanOptions` — Mathlib sets
  nine per lib), `package`, `name`, `isModule`, `plugins`, `dynlibs`.
- Module-system modules (all of Mathlib on this toolchain) each
  produce the family `.olean`, `.olean.private`, `.olean.server`,
  `.ir`, `.ilean` — all byte-diffable against oracle artifacts (no
  absolute paths; `.ilean` is module-relative JSON).
- ProofWidgets declares extra build inputs via `input_file`/
  `input_dir`/`needs` (M2a parses these) and commits built widget JS
  to git. These are real inputs `lean`/the build reads — the
  fingerprint must include their content (see §Fingerprint,
  correctness note).

## Fingerprint

Each module gets a blake3 digest computed by pure functions over
M2a's `Workspace`/graph and M2b's setup inputs — deterministic and
testable without running anything.

```
fp(m) = blake3(
  DOMAIN_TAG,               # domain-separation constant for this hash
  FP_SCHEMA_VERSION,        # bumped if the fingerprint's own layout changes
  leanr_version_id,         # STABLE leanr release/commit id (not a per-build nonce) — upgrade ⇒ full rebuild
  toolchain_id,             # lean-toolchain pin
  platform_triple,          # target triple
  owner_provenance(m),          # git dep: the package's PINNED REV (captures the whole
                                #   immutable rev-keyed checkout — incl. committed non-.lean
                                #   compile inputs like ProofWidgets' JS — by reference,
                                #   sound because fetch.rs verifies rev == checkout bytes).
                                # root / path dep (no rev): hash of any declared
                                #   input_file/input_dir file contents, path-sorted.
  source_bytes(m),
  canonical(setup_inputs(m)),   # options (k/v sorted), isModule, plugins, dynlibs
  sorted[ (import_name, fp(import)) for import in direct_imports(m) ],
)
```

Computed bottom-up over the import DAG (topological order, memoized).
A root module (no imports) is fingerprinted from its inputs alone.

**Merkle property.** Each direct import's `fp` already encodes that
import's entire transitive closure, so folding in only *direct*
imports captures the full input surface in one small, fixed-size hash.
Change a leaf → its `fp` changes → every module transitively importing
it re-fingerprints and misses; every unrelated module keeps its `fp`
and stays a hit. This is cargo/nix/bazel's model and matches leanr's
existing blake3 content-keying (the bridge/config cache).

**Correctness notes (this is where staleness bugs hide):**

- We hash the *semantic* setup inputs (`options`, `isModule`,
  `plugins`, `dynlibs`), **not** the generated `--setup` JSON file:
  its `importArts` are machine-specific absolute paths. The imported
  artifacts' *identity/content* enters the key via the recursive
  import fps instead — so relocating the store or building on another
  machine does not change any fingerprint.
- `owner_provenance(m)` closes the non-`.lean` compile-input hole
  (ProofWidgets commits built JS to git; if a module reads it at
  compile time, hashing only the `.lean` source would miss it — an
  under-inclusive, release-blocking fingerprint). For **git deps** the
  package's pinned rev captures the whole immutable checkout by
  reference — sound because `fetch.rs` already verifies rev-parse ==
  checkout (a tampered checkout is a hard error, never trusted). For
  the **root and path deps** (mutable, no rev) we hash the contents of
  any declared `input_file`/`input_dir` files instead. This supersedes
  an earlier `extra_input_contents` sketch that lacked clean per-module
  attribution and never folded the rev in.
- Completeness is asserted, not assumed: the §Staleness-correctness
  harness perturbs each input axis and fails on under-invalidation,
  and `verify --deep` re-derives artifacts against the oracle.

## Layout — CAS in XDG (extends M2b's layout)

M2b already placed immutable inputs (`src/`) and the bridge
(`config-cache/`) under `$XDG_CACHE_HOME/leanr/`. M2c adds the
artifact store there:

```
$XDG_CACHE_HOME/leanr/            # fallback ~/.cache/leanr (M2b's hand-rolled XDG)
  src/<name>/<rev>/               # M2b: immutable dependency checkouts
  config-cache/                   # M2b: blake3-keyed translate-config bridge
  cache/
    blobs/<aa>/<blake3-of-bytes>  # every artifact file, content-addressed, sharded, read-only
    modules/<aa>/<fp>.json        # fingerprint → { olean, olean.private, olean.server, ir, ilean } → blob hash
```

Two levels: a module manifest keyed by **fingerprint** names the
artifact family; each family member points at a **content blob** keyed
by the blake3 of its own bytes. Identical artifacts dedup across
fingerprints (common for stable leaf modules across branches).

**Project artifacts (unchanged path, new provenance):** modules still
land at `.leanr/build/<pkg>/lib/<Module/Path>.{olean,…}` — but M2c
*materializes* them from the store rather than writing them directly.
Materialize = **hardlink** from the blob (same filesystem: free, and
dedups the working tree against the store); **copy fallback** when the
project and XDG store are on different mounts. Materialized files
inherit the blobs' read-only bit.

**Writes are atomic and flock-guarded** (reusing M2b's advisory-`flock`
pattern, `libc`, unix-only cfg): write a temp file in `cache/`, fsync,
atomic-rename into place. Two builders inserting the same blob or the
same `<fp>.json` race safely — the rename is atomic and the content is
identical. Blobs and manifests are immutable once written; only GC
removes them.

## Architecture

Two new modules in `leanr_build` (still off the kernel graph, no new
workspace-crate deps), plus a thin CLI surface. M2a's `Workspace` and
M2b's `pool`/`job` are consumed unchanged.

1. **`fingerprint`** — pure `fp(m)` over the graph + setup inputs
   (§Fingerprint). Bottom-up, memoized. No I/O beyond reading the
   declared input files. Fully unit-testable.
2. **`cache`** — the CAS: `lookup(fp) -> Option<Manifest>`,
   `insert(fp, artifacts)`, `materialize(manifest, dest)`, plus the
   `verify` and `gc` operations. Owns the XDG `cache/` tree, atomic
   writes, flock, and hardlink/copy materialization.
3. **`pool` job body (the M2b seam)** — for each ready module `m`:
   1. compute `fp(m)` (imports are already resolved, so their fps are
      known);
   2. `cache.lookup(fp)` → **hit:** `materialize` into the project
      layout; record as *cached* in the `BuildReport`; **no `lean`**;
   3. **miss:** run M2b's `job` (spawn `lean`, capture `--json`
      diagnostics) into a staging dir → on success `cache.insert`
      (hash each artifact, store blobs, write the `<fp>.json`
      manifest) then `materialize`; on failure keep M2b's hygiene
      (delete declared outputs, fail-fast) and insert nothing.

   The scheduler (dependency counters, ready-queue `Mutex`+`Condvar`,
   `--jobs`, cancellation, first-failure slot) is byte-for-byte M2b.
   `BuildReport` gains a `cached` count alongside `built`.

## Commands & flags

- `leanr build` — cache-aware by default.
- `leanr build --no-cache` — neither reads nor writes the CAS (M2b's
  pure unconditional path; for debugging and oracle work).
- `leanr build --force` — always runs `lean`, then refreshes the cache
  with the result (rebuild but repopulate).
- `leanr cache verify` — **integrity:** re-hash every blob and assert
  its filename equals its content hash; assert every module manifest
  references live blobs; assert the current project's materialized
  files match their store blobs. I/O- and hash-bound; no `lean`.
- `leanr cache verify --deep` — **oracle:** rebuild a module set
  (a subtree by default; the full closure in CI) with `lean` into
  scratch and byte-diff against the cached artifacts for their
  fingerprints. A mismatch means an under-inclusive fingerprint
  (release-blocking) or `lean` nondeterminism — either way it fails
  loudly. This is the direct test of fingerprint completeness.
- `leanr cache gc --max-size <bytes>` — LRU eviction by blob access
  time down to the cap; unreferenced-manifest cleanup. Manual only;
  no automatic/background GC in M2c.

All new CLI logic stays in `leanr_cli` as argument parsing + printing
over `leanr_build` APIs — `leanr_cli` holds no build logic (M2b rule).

## Staleness-correctness test harness (release-blocking guard)

A dedicated test tier — `mise run cache:incremental` — over a small
synthetic multi-module fixture project (fast, hermetic):

1. Build the fixture; assert a full cold build, then a full warm hit
   (0 `lean` invocations, identical artifacts).
2. Perturb **one** input along each axis, one at a time:
   - edit a leaf module's source;
   - toggle one `leanOption` on the owning lib;
   - change `toolchain_id` / `leanr_version_id`;
   - change a git dep's pinned rev (must invalidate every module of
     that dep and their downstream cone), and change a path-dep's
     declared `input_file` contents.
3. Assert **exactly** the downstream cone rebuilds — **no
   under-invalidation** (a changed input that fails to invalidate a
   dependent is a release-blocking failure) and **no
   over-invalidation** (an unrelated module that rebuilds is a
   correctness-adjacent regression: it means the fingerprint is
   folding in something it shouldn't, which erodes the early-cutoff
   the whole cache rests on).

A scaled version runs over a Mathlib subtree in the differential tier,
alongside `verify --deep`. This mirrors `leanr_check`'s standing
differential gate: under-invalidation is treated exactly as an
unsound kernel verdict would be.

## Acceptance (recorded run)

1. **Cold:** the full pinned-Mathlib closure builds from a fresh
   clone, populating the CAS; every artifact still byte-diffs against
   lake-built artifacts (M2b's gate, now run *through* the cache).
2. **Warm:** a second build from a fresh worktree (or after `leanr
   clean`) is a full cache hit — **~zero `lean` invocations**,
   artifacts byte-identical, wall-clock dominated by materialization.
3. **Incremental:** edit one leaf module → `lean` runs for **exactly**
   the downstream cone (invocation count == cone size), and the result
   still byte-diffs against a full lake rebuild of that edited state.
4. **Integrity:** `leanr cache verify` clean; `verify --deep` over a
   subtree byte-clean.

The run is recorded (script + results committed) as with M1/M2a/M2b.

## Threat model touch

In M2c every CAS blob is produced locally by our own `lean` runs, so
the store's contents are as trusted as the build that made them. The
`verify` integrity check (blob bytes == content key) is nonetheless
built now because it is precisely the seam that will make **M2d's
untrusted remote blobs** safe to ingest: a downloaded blob is only
materialized if its bytes hash to the key it was fetched under. The
existing rule stands unchanged — `.olean` bytes are untrusted and the
`leanr_olean` parser must never panic on them (`docs/THREAT_MODEL.md`);
M2c adds cache-store integrity as a new, documented invariant.

## Next step

Invoke the writing-plans skill to produce the M2c implementation plan.
