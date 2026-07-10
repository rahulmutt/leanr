# Direct-to-id decode (term-bank phase 3) — design spec

Date: 2026-07-10. Parent:
`2026-07-06-compact-expr-term-bank-design.md` (§4 sketches this phase);
predecessor: `2026-07-06-term-bank-kernel-migration-design.md` (phase 2,
which flipped the kernel to ids and left the decoder as the last
Arc-producing boundary).

## Problem

`leanr_olean` still decodes `.olean` bytes into `Arc`-based kernel
types (`ArcConstantInfo` and friends), which `Environment::
intern_module`/`intern_declaration` then bridge into the term bank.
Every module is therefore represented twice per run — an Arc tree that
exists only to be walked once and dropped, plus the bridge walk itself
— and the kernel crate carries a whole parallel declaration family and
bridge layer whose only consumer is this boundary.

The parent spec set phase 3's bar as the ≤ 6 GiB sweep target. That
bar is already met: after the Nat.brecOn fix
(`2026-07-09-nat-brecon-reduction-divergence-findings.md`), the full
stdlib sweep peaks at 2 GiB with the bridge still in place. Memory is
no longer the motivation.

## Goal

**Simplification by deletion.** One term representation end-to-end:
the decoder writes bank ids directly, and the Arc decoder-boundary
machinery is removed. Success is measured in deleted code and an
unchanged verdict surface; any wall-clock or memory win is a recorded
side effect, not a gate.

Deleted after the flip:

- the Arc declaration family: `ArcConstantInfo`, `ArcDeclaration`, the
  `Arc*Val` structs (`decl.rs` Arc side);
- the bridges: `decl.rs::intern_constant_info` /
  `decl.rs::intern_declaration`, `Environment::intern_module`,
  `Environment::intern_declaration`, and the Arc-input form of
  `Environment::from_modules`;
- interp's Arc-emitting decode logic and the temporary differential
  gate harness (see below).

Kept:

- the `Syntax` family (`Syntax`, `SourceInfo`, `Substring`,
  `Preresolved`), including its internal `Arc<Name>`s — it is an
  opaque payload the kernel never inspects, with documented ptr-eq
  semantics (user-decided scope);
- tree `Arc<Name>` / `Arc<Level>` as render/export forms
  (`KernelError` carries `Arc<Name>`; the store's `to_name` /
  `to_level` / `to_kvmap` exporters produce them);
- tree `Expr` only if post-flip reachability still needs it (in-crate
  property tests use it as the shadow reference); if it becomes
  test-only, demote it to test support.

**Deletion rule for the plan:** any Arc-side item unreachable from
non-test code after the flip is deleted.

## Non-goals

- Migrating `Syntax` to ids or changing its ptr-eq semantics.
- Parallel decoding or checking (M1-final).
- Changing kernel algorithms, verdicts, or the raw phase's validation
  surface.
- Performance targets beyond no-regression recording.

## Approach (decided)

Three options were considered: (A) build the id-emitting decode path
beside the Arc path, prove them equivalent with a differential gate,
then flip and delete; (B) rewrite interp in place, gated by goldens
and verdicts only; (C) migrate type-family-by-family. (C) fails
because the types compose (`Arc<Expr>` contains `Arc<Name>`) and
intermediate hybrids don't exist. (B) yields the same end state as
(A) with weaker decode-fidelity evidence. **Chosen: (A)** — the
phase-2 playbook (dual paths, differential gate, flip, delete), cheap
here because the "old path" already exists and only its deletion is
deferred.

## Architecture

Interp gains an id-emitting decode: the same explicit-stack,
post-order walk over the validated `RawValue` DAG, but each conversion
calls the `Store`'s typed intern-constructors (`name_str`,
`level_succ`, the expr constructors, `intern_kvmap`, …) instead of
allocating Arc nodes. The per-type memos change value type: olean
offset → `NameId`/`LevelId`/`ExprId` instead of offset → `Arc`.
Sharing is preserved the same way it is today — via the offset memo —
and bank canonicalization makes it exact rather than best-effort.
Decode targets what the bridge writes today: the `Environment`'s
persistent store (`&mut env.store`, `base = None`). `Syntax` subtrees
are still built as Arc trees and land in the spill pool unchanged.

The driver shape changes to match: the loader/sweep/CLI loop decodes
each module against a `&mut Environment` (or its store) and folds the
returned id-form `ConstantInfo`s into the replay input map;
`Environment::from_modules` moves to this shape. Layering is
unchanged — `leanr_olean` already depends on `leanr_kernel`; the
kernel still depends on nothing in the workspace.

A module that fails shape-decoding mid-way leaves already-interned
rows in the persistent store. This is sound — interning is append-only
and canonical, so unreachable ids are inert — and decode failure is
fatal for the run, so no rollback machinery is warranted.

## Differential gate (pre-flip)

The comparison runs **in a single store**, which makes it exact: for
each module,

1. direct-decode into `&mut store`, yielding id-form constants;
2. Arc-decode the same bytes and bridge them via `intern_module` into
   the *same* store;
3. assert the two id-form `ConstantInfo`s are equal field-for-field.

Interning is canonical within one store, so id equality ⇔ structural
equality and the comparison is insensitive to interleaving or intern
order. A disagreement pinpoints module and constant immediately.

Coverage: all fixture modules in CI, plus one full-stdlib run (2,433
modules) as acceptance evidence before the flip. The harness is
temporary: it lands with the new decode path, its full-stdlib run is
recorded below, and it is deleted in the flip commit.

## Trust boundary & error handling

Untrusted bytes now drive interning directly into the kernel's
persistent store; the posture is restated, not assumed:

- The `raw` phase remains the entire untrusted-*bytes* surface (every
  byte bounds-checked, fuzzed via `mise run fuzz`); interp still
  checks only shape.
- The bank's interning API is already panic-free on arbitrary shapes:
  bounds-checked accessors, errors instead of panics, no `unsafe`,
  ids minted only by interning.
- The decode walk stays explicit-stack, so attacker-controlled depth
  cannot overflow.

No new invariants are required; `THREAT_MODEL.md` gets a paragraph
making this argument explicit.

Errors: interp returns `OleanError`; intern-constructors return
`KernelError` (e.g. u32 exhaustion). `OleanError` gains a variant
wrapping `KernelError` so the decode signature keeps a single error
type. No panics anywhere on the decode path.

## Testing

- **Golden fixtures:** fixture `.txt` files stay byte-identical; only
  the renderer's input changes (id-form constants rendered via the
  store's `to_*` exporters). Unchanged goldens are themselves a
  migration gate.
- **Verdict suite:** `check_fixtures.rs` (including the
  mutation-differential harness) re-plumbs to id forms —
  `mutant_to_declaration` becomes id-`ConstantInfo` →
  id-`Declaration` — and must stay green unmodified in spirit.
- **Differential gate:** fixtures in CI; full stdlib once pre-flip.
- **Unit/property:** existing bank suites unchanged; new decode path
  covered by the fixture goldens plus the gate.

## Acceptance

1. Differential gate green over all fixtures and the full stdlib
   sweep (pre-flip; record the run).
   - **Recorded 2026-07-10** (`mise run gate:direct-decode`, pinned
     toolchain v4.32.0-rc1): `gate: 2433 modules, 158608 constants
     id-for-id identical across decode paths`; wall time 11.63 s
     (release build pre-warmed); exit status 0.
2. Post-flip: full fixture suite and goldens green; `check --all`
   exits 0 with the same coverage figures (2,433 modules / 203,134
   declarations checked); peak RSS and wall-clock recorded against
   the 2 GiB / 367.62 s baseline — flat-or-better expected, the pod
   memory limit is the only hard bound.
   - **Recorded 2026-07-10** (`mise run check:stdlib:watched`,
     pinned toolchain v4.32.0-rc1, 30 GiB watchdog): exit 0;
     `checked 2433 modules, 203134 declarations (skipped 3611
     unsafe/partial)` — coverage figures match the baseline exactly.
     Peak RSS 1 GiB (1,072,356 kB) vs the 2 GiB (2,669,156 kB)
     baseline — a ~60% reduction, consistent with the per-module
     Arc transient and bridge walk being gone. Wall time 337.00 s
     vs 367.62 s. Flat-or-better on every axis; the win is a
     recorded side effect per the Goal, not a gate.
3. Deletion verified: the Arc declaration family and bridges are
   gone; `leanr_kernel` still has zero workspace deps; the build
   proves nothing reached for the deleted types.
   - **Recorded 2026-07-10** (from Task 7, commit `8dedb19`):
     **DELETED** — `leanr_olean`'s Arc-emitting interp decode fns,
     `InterpId::with_arc`, the differential-gate test harness
     (`collect_oleans`/`stdlib_paths_agree`/fixture gate tests),
     the Arc `ModuleData` struct + `parse`/`parse_parts` (renamed:
     `ModuleDataId` → `ModuleData`), the `gate:direct-decode` mise
     task, `OleanError::DeepRecursion`. **GATED `#[cfg(test)]`** —
     the kernel Arc declaration family (`ArcConstantInfo`,
     `ArcDeclaration`, the `Arc*Val` structs), its `intern_*`/`to_*`
     bridges, `arc_constant_info_eq`/`to_constant_info`,
     `Environment::{from_modules, intern_module,
     intern_declaration}` — now kernel test support only (fixture
     `Environment`s in `testenv.rs`, `quot`/`inductive` unit tests,
     the replay differential harness). **KEPT UNGATED** —
     `Store::{to_expr, intern_kvmap}` and tree `Expr` (production
     callers: `quot.rs`'s `alpha_eq` via `to_expr`,
     `scratch.rs`'s promotion walk via `intern_kvmap`);
     `Store::intern_expr` has no non-test caller found but was left
     ungated, flagged for a future reachability pass. `leanr_kernel`
     still has zero workspace deps (verified: `cargo build
     --workspace` clean, `cargo tree` unchanged).

## Sequencing (for writing-plans)

1. `OleanError` ↔ `KernelError` plumbing.
2. Id-emitting interp beside the Arc one, fixture-tested.
3. Differential gate harness, fixture-level in CI.
4. Full-stdlib gate run; record the result.
5. Flip callers (loader, sweep, CLI, tests) to the id path.
6. Delete the Arc path, bridges, and gate harness; reachability pass
   on remaining Arc types per the deletion rule.
7. Acceptance sweep; record figures; close out the parent spec's
   phase-3 disposition.
