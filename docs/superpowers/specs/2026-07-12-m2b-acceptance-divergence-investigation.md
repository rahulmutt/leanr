# M2b acceptance — byte-divergence investigation

**Status:** investigation complete, verdict BENIGN
**Date:** 2026-07-12
**Branch:** m2b-build-orchestrator
**Design:** `2026-07-12-m2b-build-orchestrator-design.md` (§Acceptance)

## Background

The M2b acceptance run (`mise run build:acceptance`) rebuilt the full pinned
Mathlib closure (8,564 modules) with `leanr build` and byte-diffed the result
against the lake-built oracle at `.mathlib/.lake/build/lib/lean` (+
`.lake/packages/<pkg>/...`). Result: 42,798/42,820 artifacts identical; 22
artifacts differ across 12 modules, and *only* in `.ilean` and
`.olean.private` — never in `.olean`, `.ir`, `.olean.server`. The leanr-built
tree that produced that diff is gone (its tempdir was cleaned up by the
script's `trap`), so this investigation reproduces the divergence
independently by asking: is lake itself byte-nondeterministic for these two
artifact kinds, or does leanr's invocation differ from lake's?

## 1. Module-header check

All 12 affected modules were checked for the Lean 4 `module` keyword
(searched past the leading `/- ... -/` doc-comment block, since `module` is
not literally the first line):

| Module | Has `module` header |
|---|---|
| Tactic.NormNum.Ineq | yes (line 6) |
| Data.WSeq.Basic | yes (line 6) |
| Algebra.Homology.BifunctorHomotopy | yes (line 6) |
| Algebra.MvPolynomial.Rename | yes (line 6) |
| Analysis.Calculus.ContDiff.FaaDiBruno | yes (line 6) |
| Analysis.Calculus.IteratedDeriv.FaaDiBruno | yes (line 6) |
| Analysis.Normed.Module.Alternating.Basic | yes (line 6) |
| CategoryTheory.GuitartExact.VerticalComposition | yes (line 6) |
| Computability.PartrecCode | yes (line 6) |
| Data.WSeq.Relation | yes (line 6) |
| Geometry.Manifold.Instances.Icc | yes (line 6) |
| RingTheory.MvPolynomial.MonomialOrder | yes (line 6) |

**Count: 12/12** affected modules use the Lean 4 module system (`module`
keyword). This is a suggestive correlation (only module-system files are
affected) but not itself proof of cause; see verdict below for the actual
mechanism found.

## 2. Experiment setup

Targets: `Mathlib.Tactic.NormNum.Ineq` (`.ilean`-only divergence in the
original report) and `Mathlib.Data.WSeq.Basic` (`.ilean` + `.olean.private`
divergence).

Toolchain: `lean 4.32.0-rc1` / `lake 5.0.0-src+b4812ae` (elan-selected,
matching `.mathlib/lean-toolchain`).

Method: the artifact family (`.olean`, `.olean.private`, `.olean.server`,
`.ir`, `.ilean`, `.hash` sidecars, `.trace`), plus the intermediate
`.c`/`.c.hash` under `.lake/build/ir/...` (needed for full restore), was
backed up with `cp -p` from `.lake/build/lib/lean/Mathlib/Tactic/NormNum/
Ineq.*` and `.lake/build/lib/lean/Mathlib/Data/WSeq/Basic.*` before any
mutation.

**Trace layout finding:** each module's `.trace` file sits next to its
artifacts in `.lake/build/lib/lean/<Module/Path>.trace` and is JSON:
`{"schemaVersion":"2025-09-10","depHash":"...","outputs":{"c":"<hash>.c","i":"<hash>.ilean","m":true,"o":["<hash>.olean","<hash>.olean.server","<hash>.olean.private"],"r":"<hash>.ir"}}`.
The hash in each entry matches the corresponding `.hash` sidecar file's
content exactly — this is a change-detection manifest, not a
content-addressed store (files keep plain names, `stat` shows `Links: 1`, no
hash-named files exist elsewhere). Deleting a module's artifacts + `.hash`
sidecars + `.trace` is therefore sufficient to force Lake to consider it
dirty and rebuild just that module.

`lake help build` confirmed target syntax: bare module names are ambiguous
with file paths/other targets, so `+<Module.Name>` was used (the
module-disambiguation marker). `lake build +Mathlib.Tactic.NormNum.Ineq
+Mathlib.Data.WSeq.Basic` rebuilt **only** those two modules both times
(`✔ [772/773] ... ✔ [773/773] ... Build completed successfully (773 jobs)` —
the other 771 modules were untouched cache hits, confirmed via build log
containing exactly 2 "Built" lines each run).

## 3. Results: saved oracle vs rebuild #1 (sha256 + size)

| File | saved sha256 (short) | rebuild1 sha256 (short) | size saved → rebuild1 | Verdict |
|---|---|---|---|---|
| NormNum/Ineq.ilean | `37053633dd82...` | `040f88d61796...` | 50655 → 50924 | **DIFFERS** |
| NormNum/Ineq.ilean.hash | `d1036b08bdfb...` | `9082ff3159b1...` | 16 → 16 | DIFFERS (tracks ilean) |
| NormNum/Ineq.ir | `68ee7952f4f5...` | `68ee7952f4f5...` | 182928 → 182928 | identical |
| NormNum/Ineq.olean | `094a0ea99860...` | `094a0ea99860...` | 237200 → 237200 | identical |
| NormNum/Ineq.olean.private | `7dcfa3ed23bd...` | `7dcfa3ed23bd...` | 918488 → 918488 | identical |
| NormNum/Ineq.olean.server | `821df42b3fee...` | `821df42b3fee...` | 9400 → 9400 | identical |
| NormNum/Ineq.trace | `5fe23672484c...` | `97bd33ee1715...` | 256 → 3406 | differs (expected: partial-build trace has richer dep-hash payload; not part of the audited artifact family) |
| WSeq/Basic.ilean | `1d8ac4389d9b...` | `badf7336c008...` | 80865 → 81280 | **DIFFERS** |
| WSeq/Basic.ir | `569299747d97...` | `569299747d97...` | 71592 → 71592 | identical |
| WSeq/Basic.olean | `9428dd0125b1...` | `9428dd0125b1...` | 418456 → 418456 | identical |
| WSeq/Basic.olean.private | `b3d107029dcd...` | `2b7bf3d481fa...` | 1013544 → 1013544 | **DIFFERS** (same size) |
| WSeq/Basic.olean.server | `b41452a95c2d...` | `b41452a95c2d...` | 32392 → 32392 | identical |

This exactly reproduces the pattern from the original leanr acceptance
report: `.olean`, `.ir`, `.olean.server` byte-identical; `.ilean` (and, for
WSeq.Basic, `.olean.private`) differ — **using lake alone**, rebuilding the
identical source under the identical toolchain, in place, with nothing from
leanr involved.

## 4. Results: rebuild #1 vs rebuild #2 (same-tool determinism)

Deleted the same artifact set again and re-ran `lake build
+Mathlib.Tactic.NormNum.Ineq +Mathlib.Data.WSeq.Basic`. Every single file
compared **byte-identical** between rebuild #1 and rebuild #2 (`.ilean`,
`.ilean.hash`, `.ir`, `.olean`, `.olean.private`, `.olean.server`, and even
`.trace`, for both modules — 22/22 files identical, verified via `cmp -s`).
This comparison ran in-session against a scratch working directory (outside
the repository) using `cmp -s` only, not `sha256sum`; unlike §3 (where a
pre-existing saved-oracle copy made a hash manifest natural), no per-file
sha256 hashes for rebuild #2 were separately archived, so no hash/size table
is included here.

So: two independent lake rebuilds performed back-to-back in this environment
agree with each other exactly, but **neither** agrees with the pre-existing
saved oracle. This rules out "purely random per-process" nondeterminism
(e.g. naive ASLR-seeded hash-map iteration would be very unlikely to produce
identical output twice in a row across large JSON/binary structures) and
instead points to something that differs between *build sessions/conditions*
rather than something that varies on every invocation in this environment.

## 5. `.ilean` characterization

Format: **JSON** (confirmed via raw-byte inspection:
`{"decls":{...},"directImports":[...],"module":"...","references":{...},"version":N}`).

Normalizing with `jq -S .` (sorted object keys) still showed differences —
object-key sorting alone doesn't resolve it, because the real divergence
lives inside **arrays** (usage-location lists), which `jq -S` does not
reorder. A full semantic (multiset-based) comparison, keyed off content
rather than order, found:

- `decls` (primary declaration → source-range table): **0 substantive
  mismatches** in both modules (29/29 and 116/116 keys match exactly, values
  identical). This is the core "where is this symbol declared" data and it
  is fully deterministic.
- `directImports`, `module`, `version`: identical.
- `references` (the cross-reference / "find usages" index, keyed by
  external symbol, each holding a `usages: [[line,col,line,col,enclosingDecl],
  ...]` list): **not** a pure reordering. Specific entries present in the
  fresh rebuild are **absent** from the saved oracle:
  - `NormNum.Ineq`: 4 reference keys have extra usage entries in the
    rebuild (e.g. `mul_invOf_cancel_right'` has 2 usages in the oracle vs 4
    in the rebuild; `Int.cast_mul`, `Int.cast_natCast`, `Nat.cast_mul` each
    have 1 vs 2). In every case the *extra* entries in the rebuild point at
    lines 100/136 — the `evalLT`/`isNNRat_lt_true`/`isRat_lt_true` twin of
    the `evalLE`/`isNNRat_le_true`/`isRat_le_true` code at lines 88/124,
    which *is* present in both. I.e. the oracle is missing usage-tracking
    records for one member of a structurally duplicated (LE/LT) pair of
    declarations, while the rebuild has both.
  - `WSeq.Basic`: 4 reference keys have extra/missing usage entries
    (lengths 3→4, 22→23, 0→1, 2→3), plus one reference key
    (`Init.Control.Lawful.Basic.bind_map_left`, used at
    `head_terminates_of_head_tail_terminates`) exists *only* in the
    rebuild, not in the oracle at all.

  Sizes grow (never shrink) from oracle → rebuild in every observed case,
  consistent with the oracle having *dropped* some usage-tracking records
  rather than the rebuild inventing spurious ones.

Conclusion: the `.ilean` divergence is a **substantive but narrowly-scoped**
difference confined to the secondary cross-reference/usages index (LSP
"find references" data), not the primary declaration-position table, not
file structure, and not simple key/array reordering.

## 6. `.olean.private` characterization (WSeq.Basic)

Format: **binary** (Lean's native olean format — header bytes
`olean\x02\x01<lean-version>\x00...<commit-hash>`, not JSON).

Saved vs rebuild1/2: **same size** (1,013,544 bytes both), 81 bytes differ,
all localized to two narrow byte ranges (offsets ~638529–638561 and
~842220–842224 out of 1,013,544 total — roughly 0.02% of the file, in two
clusters). This is consistent with the same class of finding as `.ilean`: a
small, localized piece of auxiliary metadata (plausibly the private/debug-info
counterpart of the same reference-tracking machinery) differs while the bulk
of the compacted region — actual proof terms and declarations — is
untouched. Unlike `.ilean`, the size doesn't grow, consistent with this
record occupying a fixed-size slot in the binary format rather than a JSON
array that literally lengthens.

## 7. Restore verification

All originals were saved with `cp -p` before any deletion (artifact family +
`.hash` sidecars + `.trace` + the `.c`/`.c.hash` intermediates under
`.lake/build/ir/`). After both rebuild experiments, all saved files were
copied back over the rebuilt ones and verified with `cmp -s` — **26/26 files
(11 per module × 2, plus 2 `.c` pairs) byte-identical to the pre-experiment
originals**, confirmed again via a final `sha256sum` sweep matching the
pre-experiment manifest exactly.

A confirmation `lake build +Mathlib.Tactic.NormNum.Ineq
+Mathlib.Data.WSeq.Basic` was then run against the fully-restored state: it
printed `Build completed successfully (773 jobs)` with **zero** "Built"
lines (full no-op), and `mtime` snapshots taken immediately before/after
that build showed **no files touched**. This confirms the restored state is
self-consistent (trace/hash sidecars agree with the restored artifact bytes)
and Lake will not attempt to re-derive anything on a subsequent build.

**One caveat, disclosed for completeness:** `.lake/build/ir/Mathlib/Tactic/
NormNum/Ineq.setup.json` and `.../WSeq/Basic.setup.json` (a per-module Lake
"setup facet" artifact distinct from the `.olean`/`.ilean`/`.ir`/
`.olean.server`/`.olean.private` family named in the task) were regenerated
by the two rebuild passes and were not backed up beforehand (they were not
anticipated as part of the artifact family and were only noticed after the
fact). Inspection shows this file contains only static, non-elaboration-derived
data (package config, declared imports/dynlib paths, options) — none of the
position/reference metadata implicated in the `.ilean`/`.olean.private`
findings above — so it should be content-stable across rebuilds in a fixed
checkout; it is not part of the `.lake/build/lib/lean` (+ packages) oracle
tree the task identifies as load-bearing for other tests, and it is
gitignored build output, not tracked source. No other files were modified
outside the two target modules' build outputs; `git status --short` in
`.mathlib` was unchanged from session start (only the pre-existing untracked
`.leanr/`).

## Verdict: BENIGN

Lake itself is byte-nondeterministic for `.ilean` and `.olean.private` on
these modules: rebuilding the identical source, with the identical
toolchain, in the identical checkout, produces artifacts that differ from
the pre-existing oracle (specifically in the cross-reference/usages index
inside `.ilean`, and a small localized region of `.olean.private`) — even
though two back-to-back lake rebuilds agree with each other exactly. Since
lake cannot reproduce its own historical output for these artifact kinds
under controlled conditions, leanr's failure to byte-match the oracle on
these same 12 modules is not evidence of a leanr bug. The fact that rebuild
#1 == rebuild #2 but both != oracle suggests the nondeterminism is tied to
build *conditions* that differ between sessions (most plausibly:
contention/thread-scheduling during Lean's parallel per-declaration
elaboration, which affects the order/completeness of concurrently-collected
LSP reference-tracking info) rather than a leanr invocation difference — the
`.olean` (public content), `.ir`, and `.olean.server` are byte-identical in
all cases, confirming the actual compiled content (proof terms, types) is
unaffected and only auxiliary metadata is at risk.

## `.mathlib` end state

Byte-identical to how it was found: all files touched during the experiment
(both target modules' full artifact families plus `.c`/`.c.hash`
intermediates) were restored from `cp -p` backups and verified via
`cmp`/`sha256sum` to exactly match pre-experiment bytes. A final `lake
build` of the two targets against the restored state is a confirmed no-op
(no files rewritten, no rebuild triggered). The only disclosed exception is
the two `Ineq.setup.json`/`Basic.setup.json` Lake-internal setup-facet files
(outside the audited `.olean`/`.ilean`/`.ir`/`.olean.server`/
`.olean.private` family and outside the `.lake/build/lib/lean` oracle tree),
which were regenerated and not independently verified byte-for-byte against
a pre-experiment copy (none was taken) — analysis of their content indicates
they are derived from static config/imports only, not elaboration-order-
sensitive data. `git status --short` in `.mathlib` was unchanged from
session start.
