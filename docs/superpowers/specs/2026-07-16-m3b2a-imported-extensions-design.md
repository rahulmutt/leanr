# M3b2a — imported extensions: the grammar arrives from `.olean`s — design spec

Date: 2026-07-16. Milestone: M3 ("Parser + formatter"), sub-milestone
M3b ("the extensible grammar"), **second slice, first half**. Parent:
`2026-07-15-m3b1-samefile-notation-design.md` (§M3b decomposition);
predecessor: M3b1 (complete as of `4f30f5a`, same-file notation
acceptance recorded). This spec also records the agreed split of M3b2
into two halves (§M3b2 decomposition).

## Problem

M3b1 proved the extensible grammar end-to-end for the same-file case:
a `notation`/mixfix command parses, derives a production, and the
threaded snapshot makes it live on the next line. But every real Lean
file gets most of its grammar from its **imports**: parser-extension
entries persisted in the dependency closure's `.olean`s — including
everything `Init` itself declares with `syntax`/`notation`. M3a's
builtin port deliberately excluded that surface (builtins are the
*compiled* `@[builtin_*_parser]` set; `Init`-declared syntax arrives
only via these entries, `2026-07-13-m3a-builtin-surface.md` line 6),
and `leanr_olean` today validates environment-extension entries but
keeps them opaque (`ModuleData::num_entries` counts them; nothing
decodes them). So leanr cannot yet parse a single real Mathlib file:
the grammar those files are written against never reaches the parser.

M3b2a closes that gap: decode the parser-extension entries from an
import closure and fold them into the base snapshot before the command
loop starts, using exactly the M3b1 growth mechanism.

## Goal

After M3b2a, `leanr parse` can parse a `.lean` file **using notation
declared in its imports**: it resolves the file's header imports
against a search path, decodes the parser-extension entries from the
imported `.olean` closure, and folds them into the base grammar
snapshot. This is the first time leanr's effective grammar matches
official Lean's for real files. M3b2a delivers:

- typed decode of `parserExtension` entries in `leanr_olean`;
- a new `leanr_grammar` crate: the `ParserDescr` Expr interpreter and
  import-closure snapshot assembly;
- import-aware `leanr parse` (header-import resolution via the
  existing loader machinery);
- the Mathlib sweep + pass-list ratchet gate, plus a hermetic
  synthetic-import corpus for CI.

**Acceptance:** the sweep harness (§Acceptance) runs byte round-trip +
structural oracle-tree equality over the fetched Mathlib closure and
gates on a checked-in pass-list; CI gates on the synthetic corpus with
the same comparison. The M3b2a bar is a non-trivial pass-list of real
Mathlib-closure files that use imported notation — the exact set is
whatever parses green, recorded and ratcheted, not predicted here.

## M3b2 decomposition (agreed in brainstorming)

M3b2 as recorded in the M3b1 spec bundles three subsystems: (a)
imported-extension decode from `.olean`s; (b) the general
`syntax`/`syntaxCat`/`syntaxAbbrev`/`binderPredicate`/`macro`/`elab`
command surface and its derivation; (c) quotation/antiquotation
parsing, a prerequisite for the `macro`-family shapes (their
patterns/RHS are quotations, and Lean gates an antiquotation
alternative into essentially every node parser inside quotations —
pervasive, M3a deferred the whole family). Together that is 2–3× an
M3b1-sized slice, so M3b2 splits:

- **M3b2a (this spec) — imported extensions.** Sources productions
  from `.olean`s into the M3b1 snapshot-growth mechanism. Acceptance:
  oracle-green on real Mathlib-closure files that *use* imported
  notation.
- **M3b2b — the general surface.** Quotation/antiquotation term
  parsing, then the general commands + shape-only
  `macro_rules`/`elab_rules`, reusing M3b2a's descr machinery for the
  surface→parser derivation. Gets its own spec.

Imports come first because they unlock real-file acceptance
immediately (files that only *use* imported notation need none of the
general surface), they exercise the M3b1 mechanism from a second
source as the M3b1 spec intended, and the sweep infrastructure built
here measures M3b2b/M3b3 progress for free.

## Scope decisions (agreed in brainstorming)

- **Bridge crate, not a new dependency edge.** The work has to walk
  `ParserDescr` constant Exprs (term-bank ids in the `leanr_kernel`
  `Store`, decoded by `leanr_olean`) and produce `leanr_syntax`
  grammar deltas — something must see both sides. A new crate
  **`leanr_grammar`** (deps: `leanr_olean`, `leanr_kernel`,
  `leanr_syntax`) holds the interpreter and snapshot assembly.
  Rejected: interpretation inside `leanr_olean` behind an
  `olean → syntax` edge (grows the threat-model-sensitive decoder
  crate with interpretation logic and a strange dependency — the
  untrusted-bytes decoder should not know about parsing Lean source);
  glue in `leanr_check` (wrong purpose — kernel-check orchestration)
  or `leanr_cli` (logic in the CLI is a bug by ARCHITECTURE.md's own
  words). `leanr_syntax` keeps zero workspace deps; `leanr_olean`
  keeps its decode-only charter.
- **Mathlib gate is local-only; CI is hermetic.** The real-Mathlib
  sweep needs the `.mathlib` checkout (`mise run mathlib:fetch`,
  network) and stays an `--ignored` test, like M2's `mathlib_oracle`.
  CI covers the same code paths with vendored synthetic fixtures
  (§Acceptance). Rejected: vendoring Mathlib source + dependency
  `.olean`s into the repo (closure size).
- **Corpus = sweep + pass-list ratchet, not a curated list.** The
  local gate sweeps *every* `.lean` file in the fetched closure and
  gates on a checked-in pass-list of files that parse oracle-green.
  Honest coverage number from day one; regressions on previously-green
  files fail; the same harness ratchets toward M3b3's stated 100%
  full-closure gate — it *is* that gate, built early. Rejected:
  hand-curated leaf-module list (anecdotal coverage, measures nothing);
  curated gate + non-gating coverage report (two mechanisms).

## Architecture

### `leanr_olean`: typed entry decode (pure decode, no interpretation)

`ModuleData` today records `num_entries` after generic validation.
It gains decoding of the `Lean.Parser.parserExtension` entry payload
into typed values mirroring Lean's `ParserExtension.Entry`
(`Lean/Parser/Extension.lean`):

- `token(val: String)` — a token-table entry;
- `kind(val: Name)` — a syntax-node-kind registration;
- `category(cat_name: Name, decl_name: Name, behavior)` — a new
  parser category with its leading-identifier behavior;
- `parser(cat_name: Name, decl_name: Name, prio: Nat)` — a parser
  registration into a category, by constant name.

Entries of *other* environment extensions stay opaque (elaborator
territory, M4). Entry bytes are untrusted input: every malformed shape
is an `OleanError`, never a panic, under the crate's existing fuzz
discipline (§Acceptance).

### `leanr_grammar`: the descr interpreter (new crate)

A `parser` entry names a constant whose *value* is a `ParserDescr`
constructor tree (elaborated from the source `syntax`/`notation`
command; `ParserDescr` is defined in `Init/Prelude.lean`). The
interpreter walks that Expr structurally:

- Constructor applications map ~1:1 onto
  `leanr_syntax::grammar::Prim` — `node`→`Node`,
  `trailingNode`→`TrailingNode`, `symbol`→`Symbol`,
  `nonReservedSymbol`→`NonReservedSymbol`, `cat`→`Category`,
  `sepBy`/`sepBy1`→`SepBy`/`SepBy1`, `nodeWithAntiquot`→its inner
  parser's mapping (antiquotation behavior itself is M3b2b). The M3b1
  engine was built ParserDescr-shaped precisely so this mapping is
  direct.
- `const`/`unary`/`binary` carry Lean *parser-alias* names
  (`optional`, `many`, `many1`, `orelse`, `andthen`, `group`,
  `atomic`, `lookahead`, `notFollowedBy`, `ppSpace`/`ppLine`-style
  formatting aliases, …) resolved against a ported alias table to the
  matching `Prim`. The alias table is ported from Lean's
  `parserAliases` registrations and is the enumerable, fixture-pinned
  part of the interpreter.
- A reference to another constant of type `ParserDescr` unfolds on
  demand (recursively, cycle-guarded).
- Anything else — `parser(constName)` referencing a raw compiled
  `Parser` function, an alias not in the table, a value that is not a
  literal constructor tree — is **skipped and recorded** (§Error
  handling), never guessed.

The interpreter lives in its own module with unit goldens over
hand-built term-bank exprs, isolated from snapshot assembly.

### `leanr_grammar`: snapshot assembly

Folds an import closure's entries, in Lean's import order, onto the
M3a builtin snapshot via M3b1's `extend(delta)`:

- `token` entries into the delta token table (idempotent
  re-registration, M3b1 semantics);
- `kind` entries interned;
- `category` entries create **new categories** — a small
  `GrammarSnapshot`/overlay extension: deltas can introduce categories
  (with their leading-ident behavior), not just extend existing ones;
- `parser` entries become leading/trailing category entries from the
  interpreted `Prim` (leading vs. trailing falls out of the descr
  shape, as in M3b1's derivation).

The assembled base snapshot is cached per import set. `fingerprint()`
folds the ordered entry digest into the base hash, so import-derived
grammar participates in the M5 firewall seam exactly like same-file
deltas. Same-file M3b1 commands then thread *on top of* this imported
base, unchanged.

### CLI: import-aware `leanr parse`

`leanr parse` parses the module header, resolves imports against
`LEAN_PATH`-style search paths using `leanr_olean`'s existing
`SearchPath`/loader (the same machinery `leanr check` uses), loads the
closure, and obtains the snapshot through one `leanr_grammar` entry
point. Argument plumbing only; no logic in the CLI. Files without
resolvable imports (or `parse` invoked without a search path) keep
today's builtin-snapshot behavior.

## Error handling & edge cases

- **Skip-and-record, never guess.** An uninterpretable `parser` entry
  is skipped and recorded on the assembled snapshot (constant name +
  reason). Its **tokens are still folded** — Lean has them in its
  table regardless, so maximal-munch tokenization stays oracle-faithful
  even when the parser is unavailable. A file that *uses* a skipped
  parser gets an error node / diverges from the oracle and stays off
  the pass-list; a verbose parse mode lists the skipped entries so the
  divergence is diagnosable. Raw-`Parser` shims that shrink this set
  are M3b3.
- **Activation-gated entries.** Fold exactly the entries official
  Lean activates unconditionally at import. Entries whose activation
  is namespace-gated (`scoped`) are skipped like uninterpretable ones
  — folding them as global would poison parses of files that don't
  open the namespace. The precise `.olean` representation of scoped
  registration is pinned down during implementation against the
  oracle; activation *semantics* are M3b3. (`local` declarations do
  not persist to `.olean`s at all.)
- **Untrusted input, never panic.** Malformed entry bytes →
  `OleanError` (existing `leanr_olean` discipline). A well-formed
  `.olean` whose `ParserDescr` value is semantic garbage →
  skip-and-record; the parse continues under whatever grammar did
  fold. Panics stay reserved for leanr-authored invariants (e.g. the
  builtin snapshot), per M3a policy.
- **Duplicates & overloads.** Same-key parser entries append (M3a
  dispatch resolves multiple `FirstTok` entries by longest match);
  token re-registration is idempotent; import-order folding matches
  Lean's, so diamond imports fold each module's entries once in
  closure order.

## Acceptance harness

- **Local gate (the ratchet).** An `--ignored` sweep over every
  `.lean` file in the fetched `.mathlib` closure (Mathlib + its ~15
  packages): byte round-trip + structural oracle-tree equality, the
  same canonicalization and comparison as M3a/M3b1. Oracle dumps come
  from `dump_syntax.lean` extended to load the file's imports from the
  prebuilt `.olean` cache before parsing; dumps are cached keyed by
  (toolchain pin, file hash), so only the first full run pays the
  elaboration cost. The checked-in pass-list
  (`tests/fixtures/syntax/mathlib-passlist.txt`, sorted) is the gate:
  a listed file going non-green fails the sweep; newly-green files are
  reported and adopted via a `mise` task (`passlist:update`-style,
  alongside `fixtures:regen`).
- **CI (hermetic).** Synthetic two-package fixtures: tiny dependency
  packages declaring notation/tokens/categories, built at
  `fixtures:regen` time with the pinned toolchain, their (small)
  `.olean`s vendored alongside oracle dumps. The test decodes the
  vendored `.olean`, folds its entries, parses the importer file, and
  runs the standard comparison — the full pipeline minus network.
  Coverage targets: each mixfix fixity via import; an imported token
  that changes tokenization of the importer (the maximal-munch
  cross-check, now cross-module); a new category declared by a
  dependency; an imported token overloaded by a same-file M3b1
  declaration (imported base + threaded overlay composing); and one
  dependency registering a raw-`Parser` entry to pin skip-and-record.
  Importer fixtures avoid `Init`-declared notation so their oracle
  dumps match without folding the full `Init` closure (the same
  self-containment discipline as the M3a/M3b1 corpora).
- **Unit + fuzz.** Interpreter goldens over hand-built term-bank
  exprs (per-constructor and alias-table cases, cycle guard,
  skip-and-record reasons); `parserExtension` entry decode added to
  the existing olean fuzz coverage; the M3a/M3b1 gates keep running
  unchanged (same-file threading is untouched).

## Out of scope (and where it lands)

Explicitly **out of scope** for M3b2a:

- Quotations/antiquotations and the general
  `syntax`/`macro`/`elab`/`syntaxAbbrev`/`syntaxCat`/`binderPredicate`
  commands + shape-only `macro_rules`/`elab_rules` → **M3b2b**.
- `scoped`/`open`/section activation semantics, raw-`Parser`-function
  shims, parsing-relevant `set_option`s → **M3b3** (the sweep built
  here becomes its 100% gate).
- Interpreting any environment extension other than
  `parserExtension`, and macro *expansion*/elaboration → **M4**.
- `leanr fmt` and all formatting → **M3c**.
- salsa/query wiring → **M5** (the fingerprint seam is preserved and
  now covers import-derived grammar).
