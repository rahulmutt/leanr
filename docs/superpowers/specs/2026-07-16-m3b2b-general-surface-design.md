# M3b2b — the general surface: quotations, antiquotations, and the `syntax` command family — design spec

Date: 2026-07-16. Milestone: M3 ("Parser + formatter"), sub-milestone
M3b ("the extensible grammar"), **second slice, second half**. Parent:
`2026-07-16-m3b2a-imported-extensions-design.md` (§M3b2
decomposition); predecessor: M3b2a (complete, acceptance recorded
2026-07-16). Also absorbs M3b2a's recorded follow-up: parallelize the
Mathlib sweep and re-run the full closure.

## Problem

After M3b2a, leanr parses real Mathlib files that *use* imported
notation, but any file that *declares* syntax with the general
surface — `syntax`, `declare_syntax_cat`, `syntax … := …`
(syntaxAbbrev), `binder_predicate`, `macro`, `elab`, `macro_rules`,
`elab_rules` — fails at that command: the command shapes are not in
the builtin grammar. M3a deferred the whole family as one unit
because their bodies contain **quotations** (`` `(...) ``,
`(cat| ...)`), and Lean gates an **antiquotation** alternative
(`$x`, `$(e)`, splices, …) into essentially every node parser inside
quotations — pervasive, not a per-command patch. Quotations also
pervade Mathlib's tactic-adjacent code far beyond declaration
commands, so this surface blocks a large class of files from the
pass-list.

## Goal

After M3b2b, `leanr parse` handles the full quotation/antiquotation
term surface oracle-faithfully, and parses + derives grammar from the
general declaration commands the same way M3b1 does for
`notation`/mixfix: a file can declare a category, declare syntax in
it, and use it (via quotations in `macro_rules` or directly) all
in-file. Deliverables:

- engine-level antiquotation gating (quotation depth in parser
  state) plus the quotation term/command shapes;
- the general command shapes and a generalized surface→`Prim`
  derivation (superset of M3b1's `notation.rs`);
- shape-only `macro`/`elab`/`macro_rules`/`elab_rules` (expansion
  RHS parsed as terms/quotations, never expanded);
- the parallelized Mathlib sweep (M3b2a's recorded follow-up), a
  full-closure re-baseline, and pass-list growth from the above.

**Acceptance** (same pattern as M3b1/M3b2a; agreed in brainstorming):
hermetic synthetic corpus green in CI (byte round-trip + structural
oracle-tree equality), plus the full-closure Mathlib sweep with
pass-list growth recorded and ratcheted — the exact set is whatever
parses green, not predicted here. No numeric target: M3b3's
activation semantics still gate many files, so a number would not be
honest.

## Scope decisions (agreed in brainstorming)

- **Full antiquot surface, not a subset.** All quotation kinds
  (term/tactic/command/level quotations and dynamic `(cat| ...)`)
  and all antiquot forms (simple `$x`, `$_`, term `$(e)`, typed
  `$x:cat`, `$$` escaping at nested depth, splices `$xs,*` in
  sepBy/many positions, optional groups `$[...]?`). Rejected: a
  core subset (simple + typed antiquots only) — real
  `macro_rules`/`macro` definitions use splices and typed antiquots
  constantly, so a subset would parse the command shapes while
  leaving most macro-defining files red, deferring the hard part
  anyway and revisiting the same engine code twice.
- **Engine-level antiquot gating, not a grammar transform.** The
  antiquot alternative lives in the parse engine, gated on a
  quotation-depth counter in parser state — mirroring how Lean
  itself structures it (`withAntiquot` wrapping + `incQuotDepth`).
  Rejected: materializing `antiquot <|> original` alternatives into
  every registered production at snapshot build (still needs runtime
  depth-gating anyway, bloats every snapshot and its fingerprint,
  touches the M3b1 overlay path); a separate derived "quotation
  grammar" (duplicates dispatch machinery, drifts from oracle
  tokenization inside quotations).
- **Sweep parallelization folded in, first.** The single-threaded
  full sweep was stopped at 4.5h during M3b2a. It gains a worker
  pool and the full closure re-baselines the pass-list *before* the
  M3b2b engine work lands, so the ratchet measures M3b2b's
  contribution honestly.
- **Acceptance pattern unchanged.** Hermetic CI corpus + local
  ratchet, as in M3b1/M3b2a. Rejected: committing to a numeric
  full-closure pass-rate (unpredictable while M3b3 semantics are
  missing).

## Architecture

### Engine: quotation depth and the uniform antiquot alternative

`Ps` (the parser state, `leanr_syntax/src/parse.rs`) gains a
quotation-depth counter. Quotation parsers (`Term.quot`
`` `(...) ``, `Term.dynamicQuot` `(cat| ...)`, and the
tactic/command/level quotation shapes) wrap their body the way
Lean's `incQuotDepth` does; `$(e)` nested term escapes decrement it,
mirroring `decQuotDepth`.

Lean wraps every node parser in `withAntiquot (mkAntiquot …)`,
active only at depth > 0. leanr mirrors this in the **engine**, not
the grammar: the places a node begins — category dispatch
(`Ps::category`) and `Prim::Node`/`Prim::TrailingNode` execution —
first offer the antiquot alternative when depth > 0. One central
implementation makes the entire grammar (builtin port, imported
productions, same-file-derived productions) antiquot-capable with
zero changes to existing `Prim` trees and untouched snapshot
fingerprints. The `nodeWithAntiquot` / `withoutAnonymousAntiquot` /
`withAntiquotSpliceAndSuffix` descr constructors in `leanr_grammar`
stop being pass-throughs and map to real flags (anonymous-antiquot
allowed or not, splice suffix).

Antiquot forms follow `mkAntiquot`/`mkAntiquotSplice`
(`Lean/Parser/Extra.lean`), producing Lean's `<kind>.antiquot` /
`<kind>.antiquot_scope` node kinds; exact tree shapes are pinned
during implementation against oracle dumps, the same discipline as
every prior slice. The sepBy/many-family prims consult depth for the
splice alternative — inside `many_impl`/`sep_by_impl`, again
engine-level. Tokenization: `$` stays an ordinary token; antiquots
need `$` + no-whitespace juxtaposition checks (Lean's
`checkNoWsBefore` inside `mkAntiquot`) — parser-level lookahead over
existing tokens, not a lexer change.

Quotation bodies parse with the *normal* category machinery at
depth+1 — that is the point of engine-level gating — so the only new
grammar vocabulary is what the quotation shapes themselves need
(depth-increment/decrement wrapping and the dynamic-quot
category-by-name body). No grammar-wide transformation.

### Command surface and generalized derivation

The deferred **builtin** commands — `syntax` (with precedence,
`(name := …)`, `(priority := …)` args), `syntax … := …`
(syntaxAbbrev), `declare_syntax_cat` (with leading-behavior arg),
`macro_rules`, `macro` — join the builtin command grammar in
`command_notation.rs` style, oracle-shape-pinned. The
`elab`/`elab_rules`/`binder_predicate` family is *not* builtin in
Lean — it is declared in Lean's own source with `syntax`, so its
command grammar already arrives through the M3b2a imported-extension
path; M3b2b adds derivation recognition for it (below). The exact
builtin-vs-imported split of the family is pinned during
implementation against the oracle; a member landing on the other
side just moves between these two lists.

M3b1's `notation.rs` derives from a restricted surface (atoms + term
placeholders). M3b2b generalizes to the full combinator surface:
quoted atoms and `&"tok"`, category refs with precedence
(`term:60`), grouping, `?`/`*`/`+`/`,*` postfix combinators,
`sepBy`/parser-alias applications (`ident`, `num`, `ppSpace`, …),
leading/trailing detection (body starting with a same-category ref ⇒
trailing production), and Lean-exact kind mangling (extending
`mangle_kind`). The derivation is keyed on command node kind, so it
fires identically whether the command shape came from the builtin
grammar (`syntax`, `macro`) or from imports (`elab`,
`binder_predicate`) — same-file growth flows through the unchanged
M3b1 overlay threading.

**One shared alias table.** The source-level combinator names are
the same `parserAliases` names `leanr_grammar/src/alias.rs` already
maps to `Prim`s. The table moves to `leanr_syntax::grammar` (pure
`Prim` construction, no new deps; `leanr_syntax` keeps zero
workspace deps) and `leanr_grammar` consumes it from there — one
pinned table, two consumers, no drift.

**`declare_syntax_cat` extends the overlay with categories.** The
M3b1 overlay deliberately cannot introduce categories. M3b2b extends
`Overlay` to carry new categories; category lookup falls back to
overlay categories only on base-lookup miss, so the base-category
dispatch hot path is untouched. Quotations over a same-file category
(dynamic `(mycat| ...)`) then work through normal lookup.

**`macro`/`elab` desugar to declarations; rules commands are
shape-only.** `macro`/`elab` derive the implied syntax declaration
(pattern atoms, precedence, explicit or mangled kind name) and
register it; their RHS parses as a term (quotations, now supported)
and is otherwise ignored. `macro_rules`/`elab_rules` attach
expansions to *existing* kinds — they parse (their patterns are
quotations) with zero grammar effect.

**Known divergence source, deferred:** Lean qualifies auto-generated
kind names by the current namespace. Structural namespace tracking
is M3b3; files declaring syntax inside `namespace` blocks may stay
off the pass-list until then (recorded like every skip; the corpus
stays self-contained like M3b1's).

## Error handling & edge cases

- **Skip-and-record continues.** A `syntax` body using a combinator
  outside the ported alias table, or any shape the derivation cannot
  handle, is skipped and recorded (same mechanism and verbose-mode
  reporting as M3b2a's uninterpretable imported entries); its atoms
  still register as tokens so tokenization stays oracle-faithful.
  Never guess.
- **Antiquots outside quotations stay errors.** Depth 0 offers no
  antiquot alternative — `$x` at top level fails exactly as the
  oracle fails it.
- **Nested quotation depth.** `$$…` escaping and `$(e)`
  depth-decrement are pinned by oracle dumps of nested `macro_rules`
  (the classic hard case); the never-hang gate (`never_hang.rs`)
  extends over quotation inputs.
- **Duplicates.** Same-key entries append and longest-match dispatch
  resolves, per M3b1; redeclaring an existing category is an error
  node per oracle behavior.
- **Untrusted input discipline unchanged.** All new surface parses
  source text through the existing engine; no new `.olean` decode
  paths. Panics stay reserved for leanr-authored invariants.

## Acceptance harness

- **Sweep parallelization first (the M3b2a follow-up).** The
  `--ignored` Mathlib sweep gains a worker pool over files (`rayon`
  as a dev-dependency of `leanr_grammar` — test-only, justified per
  AGENTS.md's dependency rule); the oracle-dump cache is already
  keyed by (toolchain pin, file hash), so parallel dump generation
  is the main win. A full-closure run then re-baselines the
  pass-list before the engine work lands.
- **Hermetic CI corpus additions:** declare-and-use files per
  command (`syntax` across the combinator classes,
  `declare_syntax_cat` + dynamic quot, syntaxAbbrev, `macro`,
  `macro_rules`; imported `elab`/`binder_predicate` via the
  synthetic-import fixtures); each quotation/antiquot form pinned
  (simple/typed/term/anonymous antiquots, splices, optional groups,
  nested `$$`); byte round-trip + structural oracle equality,
  self-contained like the M3b1 corpus.
- **Unit + fuzz.** Derivation goldens (surface→`Prim`, kind
  mangling, skip reasons); the moved alias table keeps
  `leanr_grammar`'s existing goldens green; both fuzz targets keep
  running; the pass-list ratchet gates as today; all M3a/M3b1/M3b2a
  gates unchanged.

## Out of scope (and where it lands)

- Macro *expansion*/elaboration and every environment extension
  other than `parserExtension` → **M4**.
- `scoped`/`open`/section/namespace tracking (including
  namespace-qualified auto-generated kind names) and
  raw-`Parser`-function shims → **M3b3** (the parallel sweep built
  here is its 100% gate, now fast enough to run routinely).
- `leanr fmt` and all formatting → **M3c**.
- salsa/query wiring → **M5** (the fingerprint seam is preserved;
  overlay categories participate in the existing overlay
  fingerprint).
