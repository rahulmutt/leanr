# The oracle toolchain

leanr's correctness is defined differentially: the official Lean
toolchain pinned in `lean-toolchain` (the version Mathlib pins) is the
oracle, and leanr must match its observable behavior.

- **The pin changes only at milestone boundaries** (spec: "Compatibility
  target"). Bumping it invalidates every golden fixture.
- Golden fixtures live in `tests/fixtures/`, generated from the oracle by
  `mise run fixtures:regen` and committed, so the test suite is hermetic:
  CI does not install Lean.
- After any pin bump: re-run `mise run fixtures:regen`, review the diff,
  and expect parser/format constants (e.g. in `leanr_olean`) to need
  re-verification against the new Lean source tag.
