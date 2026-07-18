# M3b3 — naming and activation: namespace-qualified kinds, `local`/`scoped`, and the remaining surface mechanics — design spec

Status: approved (brainstormed 2026-07-18)
Predecessor: [2026-07-16-m3b2b-general-surface-design.md](2026-07-16-m3b2b-general-surface-design.md)

## Problem

M3b2b left the derived-kind naming rule half-ported and activation
semantics unimplemented, both recorded as explicit gaps:

- `stxNodeKind := currNamespace ++ name` is documented in
  `notation.rs`'s module doc as the oracle rule, but every derivation
  path returns the local (category-scoped) name only. A `syntax` or
  `notation` declared inside a `namespace` block derives the wrong kind
  name, so its uses diverge from the oracle tree byte-for-byte.
- `local syntax`/`local macro` derive the plain non-private name
  (`surface.rs:111-119` records the unapplied `mkPrivateName` gate);
  `scoped` is excluded everywhere.
- Imported scoped parser extensions are decoded with their activation
  namespace but unconditionally skipped in `assemble.rs`
  (`SkipReason::ScopedInactive`, comment "activation semantics are
  M3b3"). Files using `open Foo` to activate scoped notation cannot go
  green.
- A cluster of independent mechanics stayed skip-and-record:
  non-`","` separator suffix tokens (documented silent-misparse path),
  `sepByIndent`, the `elab`/`binderPredicate` derivation arms, raw
  `Parser`-function shims, and the overlay-fingerprint imprecision
  (failed antiquot attempts intern kinds before save/restore).

## Goal

Implement the known deferred naming/activation semantics and the
recorded mechanics gaps. Success is the M3b2b pattern: hermetic
oracle-pinned fixtures for every new semantic, all existing gates
green, and Mathlib pass-list growth recorded as evidence — **no numeric
pass-rate target**. Sweep divergence data (full-closure run) ranks and
caps the data-driven items (shims) but does not add scope.

## Scope decisions (agreed in brainstorming)

- **Packaging:** one milestone, one branch, one spec/plan cycle
  (M3b2b-style), single final whole-branch review.
- **Ordering: naming-first.** The naming context lands before the
  mechanics items so nothing pins fixtures against kind names that a
  later task would change. Raw-`Parser` shims land last, scoped by
  sweep divergence data.
- **Oracle-first discipline unchanged:** exact name shapes
  (qualification order, `_private` interaction with namespaces,
  `scoped` naming) are dump-forced via probe fixtures; this spec fixes
  mechanisms, the oracle fixes bytes.
- Elaboration semantics remain out of scope: `elab`-family arms derive
  grammar only; no elaborator is built.

## Architecture

### Naming context (core unit)

`Ps` gains a **scope stack**: the current namespace path plus the
open-set. The command loop (`parse.rs:216-230`) already recognizes
every command and is the same place grammar growth hooks in
(`derive_delta` → `overlay.register`), so scope updates and their only
consumer are co-located. `namespace`/`section`/`end`/`open` (all five
`open` sub-forms parse today in `command_open.rs`) update the stack;
`withWeakNamespace` is skip-and-record unless the sweep shows it
matters.

Kind naming threads the current namespace through the derivation chain
as one new parameter: `derive_delta` → `derive_surface` /
`derive_syntax_cmd` / `derive_macro_cmd` → `build_from_items` →
`mangle_items`, and the notation.rs path symmetrically. Assembly
prepends the namespace as escaped `Name` components ahead of the
category prefix (the same mechanism `mangle_private_kind` uses for
`_private.0.`). `local` routes surface.rs derivations through the
existing `mangle_private_kind` (shared helper hoisted from
`notation.rs:674`'s `is_local_attr_kind` + `mangle_private_kind`);
notation/mixfix already do this and must not change behavior.

### Activation model (`scoped` + `open`)

One shared **activation predicate** — *is this entry active under the
current open-set?* — consulted at the grammar read points
(`category_delta`, token lookup). Two producers feed it:

- **Same-file:** `NotationSpec` and the stored category-delta entries
  gain a scope tag (`Global` / `Scoped(ns)`); `scoped syntax` registers
  with its declaration namespace.
- **Imported:** `assemble.rs` replaces the blanket
  `EntryScope::Scoped(_) → continue` with emission of
  present-but-inactive entries carrying their activation namespace.

Activation events: `open Ns`, and entering `namespace Ns` (which
implicitly opens `Ns` per the oracle). Deactivation on `end`/section
close follows the stack. Same-file and imported scoped entries go
through the identical predicate so there is one semantics to pin, not
two. The activation check must be cheap on the hot path (entries
partitioned or filtered per category snapshot, not re-scanned per
token) — exact representation is a plan-time decision benchmarked
against the sweep smoke run.

Fingerprint interaction: scope tags and activation state are part of
grammar identity and must feed the overlay fingerprint deterministically
(same rules as category fingerprints: byte-tagged sections).

### Mechanics items (independent tasks)

- **Intern-on-commit fingerprint:** failed antiquot attempts must not
  leave kinds interned in the overlay. Either defer interning to
  event-commit or roll back the overlay interner alongside
  `Savepoint::restore`. Kills both the widened `fingerprint_into`
  semantics (documented in PR #13) and the interner-clone tax failed
  antiquots impose on later commands.
- **Separator suffix tokens:** register the derived `<sep>*` suffix
  tokens for non-`","` separators, closing the documented
  silent-misparse path in `builtin/mod.rs`.
- **`sepByIndent`:** wire the alias and its splice behavior.
- **`elab`/`binderPredicate` arms:** implement grammar derivation in
  surface.rs; the two names rejoin `GRAMMAR_GROWING_KINDS` (reverting
  PR #13's temporary drop).
- **Small pins:** precedence-interaction fixture, `macro_arg`
  `checkNoWsBefore`, and the unexercised nuances recorded in the
  M3b2b ledger where a cheap fixture pins them.

### Raw-`Parser` shims (data-driven, last)

Single insertion point: `alias::lookup`'s miss path (`alias.rs:76`) —
all three `stx_item` consumer arms funnel through it and its
`AliasPrim` arity split (`Const`/`Unary`/`Binary`/`Transparent`) is
preserved by construction. Shim entries are keyed by fully-qualified
raw-parser name. Selection is data-driven: the sweep's skip-reason
counts rank candidates by files-blocked; the plan caps the initial set
(order ~10, exact list at plan time). Everything else stays
skip-and-record.

## Error handling & edge cases

Scope-stack updates are total: stray `end`, unclosed `namespace`,
`section`/`namespace` interleavings, `end` with mismatched name — none
may panic or hang. Worst case the stack is wrong and derivations
produce oracle-divergent names, which the ratchet reports as non-green;
never a crash. The never-hang storm suite and both fuzz targets extend
to namespace/open nesting (including `namespace`-inside-quotation,
which must NOT touch the scope stack — quotation depth already gates
grammar growth). Cache keys: if activation state can differ at the
same position (open-set changes mid-file), the memo key must include
it — same discipline as `CatCacheKey.quot_depth` in M3b2b Task 9.

## Acceptance harness

The M3b2b pattern, unchanged in kind:

- Hermetic probe fixtures covering the matrix: namespace × `local` ×
  `scoped` × explicit `(name := ...)`, `open` activating imported and
  same-file scoped notation, nested/reopened namespaces, plus fixtures
  per mechanics item. All dump-pinned via the elaborating dumper.
- All existing gates green: workspace tests, lint, deps,
  parse-acceptance (globs extended to new fixtures), fuzz both
  targets, never-hang storms.
- Full-closure sweep at milestone end: 0 regressions, growth recorded
  in this spec's Goal section with the divergence-class breakdown
  (the M3b3 close-out mirrors M3b2b's Task 10).

## Out of scope (and where it lands)

- Elaborator semantics for `elab`/`macro` bodies → M4.
- `withWeakNamespace` scope semantics → skip-and-record unless sweep
  data promotes it.
- Shims beyond the capped initial set → later M3 iterations, ranked by
  the ratchet.
- `leanr fmt` (M3's second half) → its own brainstorm after M3b3.
