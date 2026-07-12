# leanr threat model (M0)

## Assets

1. **Soundness** — leanr must never accept a proof the Lean kernel
   would reject. A soundness bug is the worst possible defect.
2. **User machines** — leanr parses and (later) executes bytes it did
   not produce.

## Trust boundaries and controls

| Boundary | Who controls the bytes | Control |
|---|---|---|
| `.olean` files | Any package author / cache | Parse defensively: no panics on arbitrary bytes (fuzz/property-tested); kernel-check imported content by default (M1+) |
| Remote cache entries (M2+) | Cache operator / network | Content-addressed hashes; kernel-check unless signed by a trusted key |
| `lakefile.lean` execution (M4+) | Package author | Arbitrary code execution **by design** (same as lake); documented, not hidden |
| Cargo dependencies | Upstream maintainers | `cargo deny` in CI (advisories, sources, licenses); minimal dependency policy |
| Committed secrets | Contributors | gitleaks in CI over full history |

## Resource bounds (memory/DoS)

`leanr check` structurally interns (hash-conses) decoded constants
AT INPUT: as of the direct-to-id decode flip
(`docs/superpowers/specs/2026-07-10-direct-to-id-decode-design.md`),
`leanr_olean`'s `interp` decodes each module's `.olean` bytes straight
into the kernel's id-native term bank (`crates/leanr_kernel/src/bank/`)
via the bank's typed intern-constructors — there is no intermediate
`Arc` tree and no separate bridge pass. Every name/level/expr is
deduplicated into a shared row as it is decoded, one module at a time.
This replaced two earlier, now-deleted stages: a post-decode batch-
interning pass (`intern.rs`, deleted by the term-bank kernel migration)
and, after that, a decode-into-`Arc`-then-bridge pass
(`Environment::intern_module`, deleted as a production path by the
direct-to-id decode flip and now `#[cfg(test)]` kernel test support
only). The decode walk is explicit-stack (no unguarded recursion on
untrusted `.olean`-derived structure; kernel-side term recursion
elsewhere stays under `RecGuard`'s `MAX_REC_DEPTH` cap), and interning
only merges rows identical in every field, so it is verdict-preserving
— it exists purely to reduce the resident footprint of a
whole-environment check.

**Direct-interning posture.** Untrusted `.olean` bytes now drive
interning directly into the kernel's persistent store, so the
argument for why this stays safe is restated explicitly: the `raw`
phase remains the *entire* untrusted-bytes surface (every byte
bounds-checked, fuzzed via `mise run fuzz`) — `interp`'s decode walk
checks only shape, never trusts offsets or lengths beyond what `raw`
already validated. The bank's interning API that `interp` calls into
is panic-free on arbitrary shapes (bounds-checked accessors, errors
instead of panics), contains no `unsafe` code, and mints ids only by
interning, so a stored id is valid by construction — there is no way
for decoded bytes to forge an id. The decode walk itself is
explicit-stack (no recursion keyed on attacker-controlled depth). A
module that fails shape-decoding partway through leaves already-
interned rows behind in the persistent store; this is sound because
interning is append-only and canonical, so the unreachable partial
rows are inert residue, not a corrupted or exploitable state.

## Parallel checker resource/DoS surface (M1-final)

`leanr check`'s default path (`crates/leanr_check`) replaces sequential
`replay` with a worker pool over a dependency DAG built from decoded
(untrusted) declarations, so the DoS surface a hostile `.olean` can
reach through scheduling is threat-modeled explicitly:

- **Cyclic dependency graphs cannot hang the checker.** A well-formed
  `.olean` never has one, but an attacker can forge declaration
  references that do. A cycle leaves its tasks permanently un-ready:
  once the ready queue drains and no task is in flight, the worker pool
  joins, and `done != n_tasks` is detected and reported as
  `KernelError::DependencyCycle` naming a still-pending declaration —
  never a hang, deadlock, or livelock. This is the parallel scheduler's
  twin of `RecGuard`'s `MAX_REC_DEPTH` bound on sequential recursion:
  both convert an attacker-controlled unbounded structure into a
  reported error instead of unbounded resource consumption.
- **Per-task scratch cannot accumulate.** Each task (declaration or
  inductive/quotient block) checks against a fresh per-worker scratch
  `Store` that is dropped when the task finishes, so a hostile module
  set with many large or many failing declarations cannot grow scratch
  state across tasks — peak scratch memory is bounded by the largest
  single task, not by the number of tasks.
- **The persistent store is read-only during checking.** The `Store` is
  frozen behind an `Arc` after decode and never mutated again for the
  rest of the check — no promotion step, no interior mutability, no
  `unsafe`. Inductive/quotient survivors are canonicalized by *looking
  up* their regenerated ids in the frozen store (`resolve_constant_info`,
  read-only; a miss rejects the check) rather than by writing them in.
  Because nothing writes to the shared store while workers read it
  concurrently, there is no store-corruption surface introduced by
  parallelism.
- **Task-graph memory is bounded by the input it derives from.** The
  DAG (one node per def/axiom/theorem/opaque, one per mutual-inductive
  block, one for quotient init) plus its dependency counters and
  reverse-adjacency lists are O(total term size) — the same order as
  the decode pass that already ran over the same `.olean` bytes, so the
  scheduler adds no new order of magnitude to the resource bound
  established in "Resource bounds" above.

## M2a: package resolution surface

New in M2a (`leanr build --dry-run`), all matching lake's own trust
posture:

- **Executing lakefiles.** The translate-config bridge runs pinned
  official `lake` on a package's `lakefile.lean` — arbitrary code
  execution by design, exactly as `lake build` would. leanr adds no
  sandbox in M2a (the M4 VM is the natural place for one). Subprocesses
  get explicit argument vectors, captured stderr, and a timeout.
- **Manifest-supplied git URLs.** `lake-manifest.json` is trusted like
  the lakefile (it lives in the project), but URLs are validated before
  reaching git: no leading `-` (option injection), scheme whitelist
  (https/http/ssh/git/file, scp-like, local paths), `--` separator on
  `git clone`. Materialization never overwrites local modifications.
  Beyond the URL, every manifest field leanr composes into a filesystem
  path or subprocess argument is validated the same way before use:
  package `name` and `rev` (no path separators, no leading `-`, no
  NUL — `fetch::validate_package_name`/`validate_rev`) and a git
  dependency's `subDir` (must be relative, no `..` components, no
  leading `-`, no NUL — `manifest::validate_sub_dir`), since `subDir`
  is joined onto the materialized checkout directory in `resolve()`.
- **`packagesDir` and per-package `configFile` are not traversal-
  validated.** Both are consumed as paths straight from the same
  committed, root-trusted `lake-manifest.json` (joined onto the
  workspace root and the package directory respectively) without the
  relative/no-`..` checks applied to `subDir` above. Accepted on the
  same root-trusted basis as lakefile execution above (the manifest's
  author already controls what code runs); revisit if
  `lake-manifest.json` ever becomes untrusted input.
- **Header scanning.** `scan_header` is a total function over arbitrary
  bytes (property-tested): never panics, never recurses, allocation
  bounded by input size — same discipline as the `.olean` decoder.

## M2b — build orchestrator

**Surface.** `leanr build` runs the official `lean` on package sources:
elaboration executes metaprograms, so building a package is arbitrary
code execution by design — the same posture as the M2a bridge and as
lake itself. Stated, not mitigated.

**Shared source cache.** Dependency checkouts move to a per-user cache
(`$XDG_CACHE_HOME/leanr/src/<name>/<rev>/`) shared across projects — a
new cross-project surface. Entries are keyed by `<name>/<rev>` and HEAD
is re-verified (`git rev-parse`) on every use: a tampered checkout
fails verification and errors rather than being trusted; a checkout is
never repaired or overwritten in place. Creation is guarded by an
advisory `flock` (unix; the non-unix fallback is best-effort, matching
the subprocess process-group cfg split). The bridge cache is
content-keyed (blake3 of the lakefile), so cross-project sharing cannot
serve stale or foreign config. Residual, accepted: running the bridge
(`lake translate-config`) inside a shared checkout lets lake drop its
own `.lake` cache dir there — a benign side effect; the content-keyed
bridge cache makes repeats no-ops.

**Subprocess hygiene.** As established (M2a): explicit argv vectors, no
shell, drained pipes. Build workers get no timeout (a Mathlib module
legitimately elaborates for minutes) and are NOT detached into their
own process group — a terminal Ctrl-C kills leanr and its workers
together. lean's outputs are never parsed by leanr in M2b (decoding
stays in `leanr_olean`, used only by test oracles); setup files are
leanr-written, never read back.

## Out of scope (for now)

- Sandboxing `lakefile.lean`/tactic execution (revisit at M4).
- Signature infrastructure for caches (revisit at M2).

Revisit this document at every milestone boundary.
