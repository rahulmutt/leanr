# Agent instructions for leanr

leanr is a pure-Rust Lean 4 toolchain. Read `ARCHITECTURE.md` before
touching crate boundaries, and the design spec in
`docs/superpowers/specs/` before architectural changes.

## Rules that are not derivable from the code

- **Oracle discipline:** correctness is defined by differential testing
  against the pinned official Lean toolchain (`lean-toolchain` file =
  the version Mathlib pins). Never bump the pin outside a milestone
  boundary. Regenerate fixtures with `mise run fixtures:regen`.
- **Kernel TCB (future):** `leanr_kernel` must depend on no other
  workspace crate. Soundness bugs live there; keep it minimal.
- **Untrusted input:** `.olean` bytes and (later) remote-cache entries
  are untrusted. Parsers must never panic on arbitrary bytes — see
  `docs/THREAT_MODEL.md`.
- **Environment:** tools are mise-pinned (`mise use --pin`, never bare
  `mise use`). App deps via cargo only; every new dependency needs
  justification.
- **Workflows:** use the named mise tasks (`mise tasks` lists them); CI
  runs `mise run ci` — the same tasks you run locally.
