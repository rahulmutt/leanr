# M2d — remote cache — design spec

Date: 2026-07-13. Milestone: M2 ("`leanr build` — Lake-compatible
orchestrator with content-addressed caching") — fourth and final
slice. Parent: `2026-07-04-leanr-architecture-design.md` (§Milestones,
M2); predecessor: `2026-07-12-m2c-cache-incremental-design.md`.

## Problem

M2c's CAS is per-user, per-machine. A team (or CI) building the same
pinned Mathlib closure repeats identical `lean` runs on every machine;
a fresh checkout on a new laptop pays the full multi-hour cold build
even though the exact artifacts — keyed by the exact same
content-Merkle fingerprints — already exist somewhere else. M2c built
the population layer and the integrity seam on purpose ("precisely the
seam that will make M2d's untrusted remote blobs safe to ingest");
M2d is the network tier that wraps it.

## Goal

Make the M2c CAS shareable over the network: `leanr build`
transparently pulls artifacts a teammate or CI already built, and
`leanr cache push` publishes local entries. A remote is any dumb HTTP
host serving content-addressed paths (CDN, public bucket, static
server); writes go through the S3-compatible API.

Acceptance target (recorded run, matching M1/M2a/M2b/M2c precedent): a
fresh machine with an **empty local CAS** builds the full
pinned-Mathlib closure with **~zero `lean` invocations**, artifacts
byte-identical to lake's.

## Scope decisions (agreed in brainstorming)

- **leanr-native remote CAS, not Mathlib-cache interop.** The remote
  speaks leanr's own fingerprint/blob scheme. Downloading from
  leanprover-community's existing cache (`.ltar` archives keyed by
  Lake's trace hashes) was rejected: it means reimplementing Lake's
  hash scheme and archive format — a compat layer against a moving
  upstream target, keyed by someone else's keys. The cost, stated
  honestly: a warm Mathlib cache only exists once someone (e.g. this
  project's CI) hosts one populated by leanr builds.
- **Dumb HTTP reads + S3-compatible writes; no server component.**
  Reads are plain `GET`s of content-addressed paths — any static
  host, CDN, or public bucket works with zero server logic. Writes go
  via sigv4-presigned S3 `PUT`s (AWS S3, Cloudflare R2, GCS interop,
  MinIO). Rejected: a leanr-defined GET/PUT bearer-token protocol
  (stock object stores don't accept raw PUTs, so hosting is fiddlier)
  and a leanr cache server binary (a whole deployable to build,
  secure, and operate — heavy for this slice).
- **Explicit push only.** `leanr cache push` uploads; CI runs
  build-then-push. Developer machines never upload implicitly — no
  surprise egress, credentials only where push runs. Rejected:
  `build --upload` (tangles network failure modes into the build
  path); out-of-band bucket sync (makes the on-disk layout a public
  interface by accident).
- **Trust the configured endpoint.** Content-addressing verifies each
  blob's bytes against its key before insertion, and manifests are
  parsed defensively — but the manifest *mapping* (fp → blob hashes)
  is only as trustworthy as the endpoint: a compromised server can
  serve self-consistent malicious artifacts for a fingerprint.
  Configuring a remote = trusting its operator, the same posture as
  sccache/bazel/cargo remote caches and `lake exe cache` itself, and
  documented as such in the threat model. Signed manifests are the
  recorded future upgrade; kernel-checking ingested `.olean`s (unique
  M1 leverage) was considered and set aside — it cannot cover the
  `.ir`/`.ilean` siblings and adds real latency to warm builds.
- **Per-blob mirror of the CAS, zstd-compressed.** Remote layout =
  M2c's tree (manifests by fp, blobs by content hash). Keeps blob
  dedup on the wire: when a fingerprint changes but outputs are
  byte-identical (the early-cutoff cone), only manifests are
  re-fetched, never artifact bytes. Cost: ~43k small objects for the
  full closure (~8.5k modules × ~5 artifacts) plus ~8.5k manifests;
  the acceptance run records request counts and throughput, and a
  per-module bundle tier (lake's `.ltar` shape: ~6× fewer requests,
  better compression, but an archive format to define and defensively
  parse, and no wire-level dedup) is the recorded fallback
  optimization if measured slow.
- **Inline fetch in the build, plus `leanr cache get`.** The M2c job
  body grows one tier (local miss → remote fetch → re-lookup);
  builds are transparently accelerated with no extra step. `cache
  get` prefetches the whole closure explicitly (CI warm-up, offline
  prep) through the same code path. Rejected: get-only (forgetting
  the step silently costs a full rebuild); inline-only (CI has no
  warm-up handle).
- **Sync `ureq` on threads, not tokio.** The workspace is uniformly
  sync + thread-pool (M2b's `pool`); a bounded connection pool
  saturates a CDN for this workload without introducing an async
  runtime.

Explicitly **out of scope** (and where it lands): signed manifests
(future; the seam is the manifest fetch path); Mathlib `.ltar`/lake
cache interop (rejected above); per-module bundles (deferred —
measure first); implicit upload from developer machines (never);
a cache server binary (rejected); a committed project-config surface
for the remote URL (deferred until leanr grows a config file for
other reasons); remote GC/retention (operator concern — bucket
lifecycle rules; `leanr cache gc` stays local-only).

## Wire layout & protocol

The remote mirrors the local CAS tree under a version prefix:

```
<base-url>/v1/
  blobs/<aa>/<blake3-of-uncompressed-bytes>   # zstd-compressed artifact bytes
  modules/<aa>/<fp>.json                      # manifest JSON, stored plain
```

- **Blob objects are zstd-compressed on the wire and at rest
  remotely, but named by the blake3 of the *uncompressed* bytes** —
  the same key as the local CAS, so identity is preserved across
  tiers and verification is decompress-then-hash. Manifests are small
  JSON, stored uncompressed for simplicity.
- **Reads** are plain `GET`s — no auth, no query strings, no server
  logic. A manifest 404 is a remote miss.
- **Writes** (push only) are sigv4-presigned S3 `PUT`s constructed
  via `rusty-s3`; the target is `s3://bucket/prefix`, credentials and
  endpoint from standard `AWS_*` env vars. Read URL and write target
  are configured independently — a CDN in front of a bucket is the
  expected shape.
- **Upload ordering: blobs before their manifest**, so a concurrent
  reader never sees a manifest whose blobs are missing (M2c's
  self-healing lookup covers the race regardless). Objects are
  immutable once written; same-content re-`PUT`s are harmless.
- The `v1/` prefix is the layout-evolution escape hatch; a future
  bundle tier would live beside it, not replace it.

**Configuration:** `--remote <url>` on `build`/`cache get`, or the
`LEANR_REMOTE_CACHE` env var; the flag wins. `--no-remote` forces
local-only without disturbing the environment. `cache push` takes
`--to s3://bucket/prefix`. Plain `http://` is permitted (localhost
testing, hermetic CI); the recorded posture is that production
remotes are `https://`.

## Architecture

One new module, `remote.rs`, in `leanr_build` (still off the kernel
graph; no new *workspace-crate* deps — the three new *external*
crates are justified below). It never touches the project
layout — it only populates the local CAS, which remains the sole
materialization source. M2c's `Cache` (`lookup`/`insert`/
`store_blob`/`materialize`/`verify`/`gc`) is consumed unchanged.

- `RemoteCache::fetch(fp) -> FetchOutcome` — GET the manifest;
  defensively parse; for each referenced blob missing locally: GET,
  zstd-decompress (capped), **blake3-verify against the key before
  insertion**; then write the manifest locally — blobs first,
  manifest last (crash-safe with M2c's self-healing lookup). Returns
  hit / miss / degraded — *degraded* means the remote had the
  manifest but a blob failed to download or verify: treated as a
  miss by the build, reported distinctly so operators can tell "not
  cached" from "cached but unhealthy".
- `RemoteCache::push(fps) -> PushReport` — for each fp with a local
  manifest: skip if the remote manifest already exists; else upload
  missing blobs (compressed), then the manifest. Parallel,
  idempotent.

**Build integration (the M2c seam, one new tier).** The job body
becomes: local `lookup(fp)` → **hit:** materialize (unchanged) →
**miss:** if a remote is configured, `remote.fetch(fp)`, then
re-`lookup` locally → **hit:** materialize; **still miss:** run
`lean`, `insert`, materialize (unchanged from M2c). Because the
local CAS is the only thing that ever materializes into a project,
every M2c integrity invariant — and `leanr cache verify` —
automatically covers remote-sourced entries: there is a single
ingestion choke point where untrusted bytes become trusted store
contents. The scheduler (dependency counters, ready queue, `--jobs`,
cancellation, first-failure slot) is byte-for-byte M2b/M2c; inline
fetches ride the existing pool threads.

**CLI surface (parsing + printing only, per the M2b rule):**

- `leanr build` — remote-aware when configured; `--no-remote` opts
  out; `--no-cache` continues to bypass everything (and therefore
  also the remote).
- `leanr cache get` — computes the full graph's fingerprints (pure,
  no `lean` — M2c's `fingerprint` module) and batch-fetches with its
  own bounded connection pool.
- `leanr cache push --to s3://bucket/prefix` — as above.
- `BuildReport` gains a `downloaded` count alongside `built`/`cached`.

**New dependencies** (each justified per AGENTS.md's minimal-deps
rule): `ureq` (sync HTTP client, rustls — no async runtime enters
the workspace), `zstd` (blob compression), `rusty-s3` (lightweight
sigv4 presigning — avoids the AWS SDK; pairs with ureq).

## Error handling

The governing rule: **remote availability affects speed, never
correctness or build success.**

- Network errors and timeouts → warn once, count as a miss, build
  proceeds via `lean`. A **circuit breaker** (sticky atomic flag)
  disables the remote for the rest of the run after the first
  connect-level failure — an offline laptop gets one warning, not
  8,564 timeouts.
- Verification failure (hash mismatch, malformed manifest,
  decompression-cap breach) → warn naming the fp/blob, treat as a
  miss, **insert nothing** — unverified bytes never enter the local
  CAS.
- `cache push` failures are **hard errors** (CI must notice).
  `cache get` reports fetched/missed/failed counts and exits nonzero
  on hard failures — fetching is its whole job.

## Threat model touch

`docs/THREAT_MODEL.md`'s "Remote cache entries" row becomes concrete:

- **Single ingestion choke point:** every remote blob is
  decompressed and blake3-verified against its content key *before*
  `store_blob`; a mismatch is rejected and logged, never stored.
- **Defensive parsing:** manifest JSON from the wire is untrusted —
  size-capped, parse errors are misses (never panics), hashes are
  strictly validated hex (reusing M2c's total `shard()`); no
  wire-derived string forms a filesystem path except through
  validated hex. Decompression enforces the declared-size check plus
  a streaming cap (bomb defense).
- **Trust boundary, stated:** configuring a remote = trusting its
  operator with the fp→artifact mapping. Signed manifests are the
  recorded future upgrade; the manifest-fetch path is the seam.

## Testing

- **Unit:** defensive manifest parsing (arbitrary bytes → error,
  never panic, per the untrusted-input rule), strict hex validation,
  decompression caps, verify-before-insert rejecting wrong bytes with
  the local CAS left untouched.
- **Hermetic integration tier (`mise run cache:remote`):** a
  ~100-line test-only static file server on `std::net::TcpListener`
  (GET + PUT over a temp dir; zero new deps). Scenario: build the
  synthetic fixture with CAS dir A → `push` → fresh empty CAS dir B →
  build with the remote → **0 `lean` invocations**, byte-identical
  artifacts, `cache verify` clean. Tamper tests: flip a byte in a
  served blob / corrupt a manifest / serve an oversized decompression
  → build still succeeds via `lean`, warning emitted, local CAS
  clean. Offline test: unreachable remote → one warning (circuit
  breaker), normal build. Push idempotence: second `push` uploads
  nothing.
- **Recorded acceptance run:** full Mathlib closure — `push` from a
  populated local CAS to a local static server, then build against a
  fresh XDG cache dir: ~zero `lean` invocations, artifacts byte-diff
  clean against lake, request counts and wall-clock recorded. This
  validates the mechanism hermetically; real-CDN latency is
  environment-dependent and noted as such in the record. Script +
  results committed, as with M1–M2c.

## Next step

Invoke the writing-plans skill to produce the M2d implementation plan.

## Acceptance results (recorded 2026-07-13)

`scripts/remote-cache-acceptance.sh` against the pinned Mathlib (8564 modules, 8 jobs, single host simulating machines A/B/C with isolated XDG cache homes):

- Machine A cold build: `built 8564 modules (0 cached, 0 downloaded)` in 7256.4s.
- `cache push` to the local S3 stand-in: 8564 manifests pushed (0 already remote), 42820 blobs, 1,848,036,065 bytes uploaded (~1.72 GiB compressed), 14s wall.
- Machine B `build --remote` (empty local CAS): `built 0 modules (0 cached, 8564 downloaded)` in 11.6s (18s wall including resolve) — zero lean invocations, every module tagged `(downloaded)`.
- Strict A↔B byte-diff: all 42820 artifacts byte-identical (zero tolerance; A↔lake fidelity remains `scripts/build-fresh-acceptance.sh`'s standing gate — same builder's bytes through the wire).
- Machine B `cache verify`: store integrity clean.
- Machine C `cache get` (explicit prefetch, empty CAS): 8564 fetched, 0 already local, 0 not on remote, 0 failed; subsequent `build --no-remote`: `built 0 modules (8564 cached, 0 downloaded)` in 2.3s.

Recorded finding: the first acceptance run FAILED its strict byte-diff (25/42820 artifacts across 5 module families) and exposed a latent M2c bug — the fingerprint omitted module identity, so Mathlib's six byte-identical `Subpresheaf` deprecation stubs (plus one Batteries twin pair) shared fingerprints and the CAS served one twin's artifacts for the others. Fixed by folding the fully-qualified module name into the fingerprint (schema bumped to `leanr-m2d-fingerprint-v2`) with a pinned regression test (`identical_content_modules_get_distinct_fingerprints`); the re-run passed with zero mismatches. This is precisely the failure class the strict-byte-identity gate exists to catch.
