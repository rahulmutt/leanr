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
- **Typeclass-synthesis verification is also two tiers**, mirroring the
  parse sweep above, but a genuinely separate pair of pipelines with their
  own pass-list and their own nightly workflow so the two never race:
  - `mise run meta:fast` — regression gate. Runs BOTH `oracle_fast` (every
    committed whnf/infer/defeq query) and `oracle_synth` (every committed
    typeclass-synthesis query) against the oracle. Hermetic — committed
    `.olean` + `.jsonl` fixtures only, no Mathlib checkout, no network.
    Seconds, not hours. Run this in the dev loop; it also runs inside plain
    `mise run test`.
  - `mise run meta:nightly` / `meta:nightly:shard` / `meta:nightly:merge` —
    discovery. "What `synthInstance` queries mined out of real Mathlib
    declarations does leanr's tabled resolver answer the same way as the
    real elaborator." Each shard first runs the C1 Lean oracle dumper
    (`tests/fixtures/meta/dump_synth_mathlib.lean`) to mine `synthInstance`
    queries directly out of real Mathlib constants and record the oracle's
    verdict + instance term for each, THEN the Rust sweep
    (`crates/leanr_meta/tests/synth_sweep.rs`) runs leanr's own
    `synth_instance` on the same queries and diffs against that JSONL —
    green per constant means EVERY query for it agrees with the oracle on
    BOTH the verdict AND (when `ok`) the canonical instance term, not just
    yes/no. `meta:nightly` is the local unsharded dump-then-diff-then-update
    convenience (Mathlib-scale; do not run it in the dev loop).
    - Shards here stride by CONSTANT INDEX, not import set: after loading
      the full pinned Mathlib closure (`load_closure`, so every shard's
      environment and constant list is identical), constants are sorted by
      rendered name and a shard `I/N` takes `idx % N == I-1`. This is
      deliberately different from the parse sweep's per-import-set
      sharding above — synthesis queries are mined from individual
      constants' binders and application sites, not from whole files, so
      the natural unit of work (and thus the natural shard key) is the
      constant, not the import set a file pulls in. The dumper mines two
      kinds of query per constant: each of its own `instImplicit` binder
      positions (a hypothesis the constant demands of a caller), and — the
      higher-signal source — instance arguments already saturated at
      application sites inside its type/value, where the real elaborator
      already solved that exact goal once.
    - The pass-list (`tests/fixtures/meta/synth-passlist.txt`) and
      re-baseline branch (`nightly/mathlib-synth-passlist`) are DISTINCT
      from the parse sweep's (`tests/fixtures/syntax/mathlib-passlist.txt`,
      `nightly/mathlib-passlist`) — same reasoning as the parse sweep's own
      committed-vs-discovery split, just for a different pass-list: keeping
      them separate means a synthesis regression/re-baseline can never be
      confused with, or block on, a parse one, and the two nightly
      workflows never need to touch the same branch or file.
    - **The nightly is `.github/workflows/nightly-synth-sweep.yml`** —
      structurally the same shard/merge/re-baseline shape as
      `nightly-sweep.yml` (12 shards, a merge job that refuses to run
      unless all 12 shard artifacts are present, gate-before-rewrite, a
      force-updated re-baseline PR rather than a push to main), but a
      genuinely separate workflow: distinct cron (`41 6 * * *`, offset from
      the parse sweep's `17 2 * * *` so the two never queue for runners or
      race at the same wall-clock moment) and a distinct concurrency group
      (`nightly-synth-sweep`, vs. the parse sweep's `nightly-sweep`) so the
      two workflows can run concurrently with each other and only ever
      serialize against themselves. Unlike the parse sweep, each shard job
      does two steps, not one: run the C1 dumper to produce this shard's
      oracle JSONL, then run `meta:nightly:shard` over it in the same job —
      the JSONL (~683MiB/shard) never leaves the runner; only the green
      list + manifest are uploaded.
- **fmt gate:** `leanr fmt` self-consistency is gated by `mise run
  fmt:mathlib` — a separate, FAST pass-list tier (same 23-entry committed
  pass-list as `parse:mathlib:fast`), not the nightly discovery sweep.
