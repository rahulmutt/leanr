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
    full sweeps back to back, ~70h, and cannot fit a nightly). Within that
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
  - **The nightly is `.github/workflows/nightly-sweep.yml`** — one
    canonical scheduled path, no crontab. A single hosted job cannot hold a
    ~35h sweep (6h cap), so the workflow shards it: 12 `sweep` jobs, each
    sweeping the import sets with `index % 12 == I-1`
    (`mise run parse:mathlib:shard`, `LEANR_SWEEP_SHARD=I/12`) and
    uploading its green list, then one `merge` job
    (`mise run parse:mathlib:merge`) that unions them and runs the SAME
    gate + reconcile + rewrite as a full `passlist:update`. Sharding
    changes only where the parsing happens, never what is gated.
    - A shard NEVER gates. It sees 1/12 of the import sets, so a pass-list
      entry in another shard's slice is trivially not-green there; gating a
      shard is not a stricter check, it is a meaningless one.
      `mathlib_sweep.rs` asserts shard mode is incompatible with
      `LEANR_PASSLIST_UPDATE`/passlist-only, and returns before the gate.
    - Each shard also uploads a MANIFEST (`LEANR_SWEEP_MANIFEST_OUT`): its
      spec, how much it swept, and which committed pass-list entries it
      observed present on disk. That last one is the merge job's only
      existence oracle — merge has no Mathlib tree, and must not grow one:
      mathlib4's git tree does not contain the lake-materialized
      `.lake/packages/`, where every pass-list entry currently lives, so a
      filesystem test there would call every true parse regression an
      upstream deletion and reconcile it out of the baseline while
      reporting zero regressions.
    - The merge job refuses to run unless all 12 shard artifacts are
      present. A partial union would report every import set in a missing
      shard as a parse regression, or silently drop those entries from the
      rewritten pass-list. It validates the manifests as a SET — exactly
      one per shard `1..=N`, none of them vacuous — because a count alone
      cannot tell 12 manifests from "shard 7 twice, shard 4 missing", and
      because a shard that swept 0 import sets (e.g. an empty
      `LEANR_OLEAN_PATH`) exits 0 with an empty green list that no
      count-based guard can distinguish from a mass regression.
    - A true regression fails the workflow. Otherwise a changed pass-list
      is proposed as a PR on the stable `nightly/mathlib-passlist` branch
      (force-updated nightly, so it is one PR, not one per night) — never
      pushed to main. Note that a PR opened by `GITHUB_TOKEN` does not
      itself trigger CI; re-run CI on it manually before merging.
  - `scripts/nightly-sweep.sh` is the MANUAL local escape hatch, not a
    scheduled job: an unsharded `parse:mathlib:nightly` under a
    memory-watchdog (`RAYON_NUM_THREADS=5`, 27G anon-memory kill guard for
    a 32Gi container) with an flock so two sweeps can't stack. Genuinely
    useful on a big local box; run it by hand, don't cron it.
- **fmt gate:** `leanr fmt` self-consistency is gated by `mise run
  fmt:mathlib` — a separate, FAST pass-list tier (same 23-entry committed
  pass-list as `parse:mathlib:fast`), not the nightly discovery sweep.
