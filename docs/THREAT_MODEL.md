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

`leanr check` structurally interns (hash-conses) decoded constants in one
bounded batch pass before replay, collapsing structurally-identical subterms
shared across the whole module set into a single `Arc` each. Like all term
recursion, the pass runs under `RecGuard` (`MAX_REC_DEPTH` cap, no unguarded
recursion on untrusted `.olean`-derived structure) and only merges terms
identical in every field, so it is verdict-preserving — it exists purely to
reduce the resident footprint of a whole-environment check.

## Out of scope (for now)

- Sandboxing `lakefile.lean`/tactic execution (revisit at M4).
- Signature infrastructure for caches (revisit at M2).

Revisit this document at every milestone boundary.
