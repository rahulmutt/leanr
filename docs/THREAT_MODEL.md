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

## Out of scope (for now)

- Sandboxing `lakefile.lean`/tactic execution (revisit at M4).
- Signature infrastructure for caches (revisit at M2).

Revisit this document at every milestone boundary.
