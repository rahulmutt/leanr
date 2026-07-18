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
- **Mathlib verification is two tiers**, not one sweep. They ask different
  questions and have very different costs:
  - `mise run parse:mathlib:fast` — regression gate. "Nothing that used to
    parse broke." Sweeps ONLY the committed pass-list
    (`tests/fixtures/syntax/mathlib-passlist.txt`, 23 entries) — exact, not a
    sample, since a file that never parsed green can't regress. No corpus
    walk, no olean closure decode outside the pass-list's own import sets.
    Seconds, not hours. Run this in the dev loop.
  - `mise run parse:mathlib` / `passlist:update` / `parse:mathlib:nightly` —
    discovery. "What newly parses." Inherently full-corpus: walks all of
    Mathlib and decodes an olean closure per distinct import set (~8,221
    sets). ~35h at `RAYON_NUM_THREADS=5` on 8 effective cores, dominated by
    closure decode, not the oracle — ONE such sweep, not two: `parse:mathlib`
    (gate only) and `passlist:update` (gate then rewrite) both do this same
    ~35h walk, so `parse:mathlib:nightly` runs `passlist:update` alone rather
    than `parse:mathlib` followed by `passlist:update` (that would be two
    full sweeps back to back, ~70h, and cannot fit a daily cron). Within that
    one sweep, `mathlib_sweep.rs` checks for regressions before it rewrites
    the pass-list, so a regression fails before the baseline is touched.
    A committed entry whose file was deleted/renamed upstream is corpus
    churn, not a regression: the update path (`passlist:update` /
    `parse:mathlib:nightly`) drops it from the gate — loudly, logging every
    dropped path — and reconciles it out of the rewritten pass-list. The
    plain gate (`parse:mathlib`, no rewrite) has no rewrite to reconcile
    into, so it still fails loudly on a missing file with no exceptions;
    that asymmetry (gate reports churn, update absorbs it) is deliberate.
    Never run any of these outside a dedicated nightly job.
  - There is no GitHub Actions workflow for the discovery tier: CI runs
    hosted `ubuntu-latest` (no Lean toolchain, ~14GB disk, 6h job cap) and
    `.mathlib` is a ~25GB local checkout — it cannot run there. Instead,
    `scripts/nightly-sweep.sh` wraps `parse:mathlib:nightly` in the same
    memory-watchdog pattern used elsewhere in this repo (27G anon-memory
    kill guard for a 32Gi container) and refuses to start a second sweep
    while one is already running. Logs land in `target/` (repo-ignored).
    Cron line (adjust the path):
    ```
    0 2 * * * /path/to/leanr/scripts/nightly-sweep.sh
    ```
