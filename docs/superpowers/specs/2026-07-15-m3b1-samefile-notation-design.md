# M3b1 — same-file notation: the grammar grows mid-file — design spec

Date: 2026-07-15. Milestone: M3 ("Parser + formatter"), sub-milestone
M3b ("the extensible grammar"), **first slice**. Parent:
`2026-07-13-m3a-parser-foundations-design.md` (§M3 decomposition, which
names M3b as one slice); predecessor: M3a (complete as of
`01eb4d8`, parser foundations acceptance recorded). This spec also
records the agreed decomposition of M3b itself into three slices
(§M3b decomposition), of which this is the first.

## Problem

M3a built the parser foundations — lossless green/red trees, the
table-driven lexer, the category/Pratt machinery, the Rust builtin
parsers, and the `GrammarSnapshot` value — but the grammar it parses
is *fixed*. `parse_module` pins one immutable `&GrammarSnapshot` for
the whole file and parses every command under it. Lean's grammar is
not fixed: a `notation` or `infix` command on line 10 adds tokens and
a parser that change how line 11 tokenizes and parses. M3a's own spec
names "the snapshot is per-command state threaded through the file
parse" as the intended design and built the seam for it (an explicit,
fingerprintable snapshot value; a per-command command loop), but M3a
only needed builtins, so it shipped the constant-snapshot special
case. The `notation`/`mixfix` command *shapes* are not even parsed yet
— M3a deferred all ten `ParserDescr`-registration commands in
`Syntax.lean` to M3b, so today a `notation` command lands in a
recovery error node.

M3b1 closes the smallest end-to-end gap that proves the extensible
grammar works: same-file `notation` and mixfix commands that declare a
production and use it later in the same file.

## Goal

After M3b1, a `.lean` file can declare `notation`/`infixl`/`infixr`/
`infix`/`prefix`/`postfix` and the tokens and parser it introduces are
live for the rest of the module — matching official Lean's
parse-one-elaborate-one loop, restricted to the notation surface.
M3b1 delivers:

- the command loop threading an **evolving** snapshot (the M3a seam,
  now actually exercised by a changing grammar);
- the `notation`/`mixfix` command shapes in the builtin grammar;
- the surface→parser derivation that turns a declared notation into a
  registered production, with Lean-exact node-kind names and
  precedence;
- an oracle-green acceptance corpus of declare-and-use files.

**Acceptance** (same harness and gate as M3a): `text(parse(src)) ==
src` byte-exact, plus structural oracle-tree equality against the
pinned toolchain, over a curated corpus of self-contained files that
declare notation and then use it — no imports beyond the auto-imported
`Init`.

## M3b decomposition (agreed in brainstorming)

M3b is decomposed into three independently-landable slices, each with
a recorded acceptance gate, following the M2a–M2d / M3a–M3c pattern:

- **M3b1 (this spec) — same-file notation.** The `ParserDescr`
  interpreter engine exercised on the notation surface, plus
  per-command snapshot threading, `notation`/`mixfix` command shapes,
  and the surface→parser derivation. Acceptance: oracle-tree equality
  on a synthetic declare-and-use corpus.
- **M3b2 — imported extensions + the general surface.** Decode
  parser-extension entries from imported `.olean`s (via `leanr_olean`,
  which today validates but does not decode extension entries) and
  fold them into the snapshot at import time; add the general
  `syntax`/`macro`/`elab`/`syntaxAbbrev`/`syntaxCat`/`binderPredicate`
  commands and shape-only `macro_rules`/`elab_rules`. Acceptance:
  oracle-green on real Mathlib leaf modules — the first time leanr
  parses actual Mathlib source using its dependencies' notation.
- **M3b3 — activation semantics + the full-corpus gate.** Structural
  `namespace`/`open`/`end`/`open … in`/section tracking, `scoped`
  notation activation, parsing-relevant `set_option`s, and enumerated
  raw-`Parser`-function shims. Culminates in M3's stated acceptance
  gate: byte round-trip + oracle-tree equality over the whole pinned
  Mathlib dependency closure.

Load-bearing boundary: M3b1 establishes the *mechanism* by which the
grammar snapshot grows during a parse (the overlay layer and the
threaded command loop, §Architecture). M3b2 reuses that exact
mechanism, sourcing productions from `.olean`s instead of same-file
commands; M3b3 layers activation gating on top. Getting the growth
mechanism right and cheap here is why M3b1 exists as its own slice.

## Scope decisions (agreed in brainstorming)

- **Notation + mixfix only.** M3b1 covers `notation` and the mixfix
  family (`infixl`/`infixr`/`infix`/`prefix`/`postfix`) — the
  highest-frequency extension surface, producing a *restricted*
  `ParserDescr` (a symbol plus precedences plus term placeholders).
  The fully-general `syntax`/`macro`/`elab` combinator surface and
  custom categories defer to M3b2. Rationale: this is the thinnest
  slice that still drives the whole engine — parse a command, derive a
  `ParserDescr`, register a token and parser into the snapshot, thread
  it, parse the next line under it — while keeping the `ParserDescr`
  subset bounded. Rejected: `+ general syntax` (pulls most of the
  general interpreter into slice 1); `all ten defer commands`
  (recreates the monolith the decomposition avoids, and needs
  quotation/antiquotation term parsing that M3a itself deferred).

- **Layered-overlay snapshot growth.** The base snapshot (builtins
  now; imports at M3b2) stays `Arc`-shared and immutable. Same-file
  `notation`/`mixfix` commands push a production onto a small **delta**
  layer that dispatch consults first; the snapshot's `fingerprint()`
  becomes `hash(base_fp ‖ delta_chain)`. Extension is O(1) per
  command, dispatch churn is one "check overlay before base tables"
  step, and the M5 query-firewall fingerprint seam stays intact and is
  now exercised by a per-command-changing grammar. Rejected: a fully
  persistent `GrammarSnapshot` (rewrites M3a's `Vec`/`HashMap` tables
  for structure-sharing maps and slows the dispatch hot path — churn
  for value-semantics aesthetics M3b1 doesn't need); rebuild-per-command
  (O(grammar × commands), quadratic on real Mathlib, thrown away at
  M3b2).

- **Acceptance = bytes AND oracle trees, on a synthetic corpus.** Same
  merciless gate as M3a. Losslessness alone is weak — a notation tree
  can round-trip while binding at the wrong precedence, and a
  formatter on a wrong tree corrupts meaning silently — so structural
  oracle equality (including node-kind names and atom spans) is
  required. The corpus is hand-authored declare-and-use files rather
  than real Mathlib because real files depend on *imported* notation
  (M3b2); M3b1 controls both the declaration and the use so it can
  stay within `Init`.

## Architecture

All work is inside `crates/leanr_syntax`; no new crate, and no
`leanr_kernel`/`leanr_olean` dependency yet (imported-notation decode
is M3b2).

### Snapshot growth: the overlay layer (`grammar.rs`)

`GrammarSnapshot` gains a cheap `extend(delta) -> GrammarSnapshot`.
Internally the returned snapshot shares the base's `Arc`-held tables
and carries a small appended **delta** (new tokens; new
leading/trailing category entries; new interned kinds). Dispatch in
`parse.rs` consults the delta first, then the base tables — so a
same-file production shadows/extends the builtins without rebuilding
them. `fingerprint()` folds the delta chain into the base hash, so
each per-command snapshot fingerprints distinctly and deterministically
(the M5 firewall seam). The token table used by the lexer is likewise
the base table plus the delta's new tokens, so maximal-munch
tokenization sees same-file tokens on the very next line.

### Threaded command loop (`parse.rs`)

`Ps` holds the active snapshot behind a cheap-to-swap `Arc<GrammarSnapshot>`
handle rather than a `&'a GrammarSnapshot` borrow. The command loop
becomes: parse command *N* under the current snapshot; if it was a
`notation`/`mixfix` command that parsed cleanly, compute its delta
(§derivation) and install `snap' = snap.extend(delta)`; parse command
*N+1* under `snap'`. A command that fails to parse registers nothing
(§Error handling). This is the M3a "per-command state threaded through
the file parse" design, made real.

### notation/mixfix command shapes (`builtin/command/`)

A straight M3a-style port of the five productions (`notation`,
`infixl`, `infixr`, `infix`, `prefix`, `postfix` — `Syntax.lean:92-95`)
into the builtin command tables: optional precedence (`:65`), optional
attributes/name, the quoted symbol atom(s), the term placeholders, and
`=> rhs`. This half is mechanical and oracle-checkable independently of
the derivation below — the command's own tree must match Lean's.

### Surface→parser derivation (`grammar/notation.rs`, new module)

The one genuinely new subsystem, kept in its own module so
"interpret a declared notation into a parser" is testable in isolation.
It maps a cleanly-parsed `notation`/`mixfix` command tree to a delta:

- **Tokens.** Each quoted symbol becomes a new token in the delta's
  token table.
- **Node kind — the sharp correctness point.** Lean auto-generates the
  syntax *kind name* from the notation's atoms (e.g. `` `«term_+_» ``).
  Oracle-tree equality compares kind names, so our mangling must
  reproduce Lean's exactly, character for character. This is *ported*
  from Lean's notation elaborator (`Lean/Elab/Syntax.lean`,
  `Lean/Elab/BuiltinNotation.lean`), not invented; it is the first
  thing the oracle corpus pins.
- **`Prim` body + category.** The placeholders and symbols become a
  `Seq` of `Symbol`s interleaved with `Category { name: "term", rbp }`
  recursions; the whole is wrapped in a `Node`/`TrailingNode` (below)
  registered as a leading/trailing entry in the `term` category.
- **Precedence & associativity** (ported from Lean, oracle-verified —
  precedence bugs round-trip silently, so this is fixture-heavy):
  - `notation:p …` → `Prim::Node { prec: Some(p), … }`; placeholder
    `rbp`s per Lean's rules.
  - `infixl:p` (left-assoc) → `TrailingNode { prec: p, lhs_prec: p, … }`.
  - `infixr:p` (right-assoc) → `TrailingNode { prec: p, lhs_prec: p+1, … }`.
  - `prefix:p` → leading `Node` with operand `rbp = p`.
  - `postfix:p` → `TrailingNode` with `lhs_prec = p`.

## Error handling & edge cases

- **Failed declaration registers nothing.** A malformed
  `notation`/`mixfix` command yields an error node and resyncs at the
  next command keyword (M3a policy); it must **not** mutate the
  threaded snapshot. Registration happens only after a clean parse of
  the command, so a broken notation on one line cannot corrupt parsing
  of the rest of the file.
- **Overloaded notation** (same leading token, multiple parsers) is
  supported for free: M3a dispatch already holds multiple entries per
  `FirstTok` and resolves by longest match. The delta appends another
  entry under the same key.
- **`local notation`** is *included*: it parses and activates for the
  rest of the file. Its *deactivation at section `end`* requires the
  structural section tracking that lands in M3b3, so the M3b1 corpus
  contains no section-scoped `local`-deactivation cases (within a
  single section `local notation` parses identically to `notation`).
- **`scoped notation`** is *excluded* — it requires namespace-open
  tracking, explicitly M3b3.
- **Internal invariant violations panic** with the report-this-bug
  message (M3a policy) — e.g. a derivation that produces a `Prim`
  referencing an unregistered token is a leanr bug, not untrusted
  input, and must fail loudly rather than silently register a broken
  parser.

## Oracle harness & acceptance

Reuses the M3a oracle harness unchanged (the pinned-toolchain Lean
script under `scripts/` that dumps each command's `Syntax` tree; the
same canonicalization and structural comparison). The M3b1 corpus is a
new set of curated `.lean` fixtures, each self-contained within `Init`,
each declaring one or more notations/mixfix operators and then using
them. Coverage targets: each mixfix form and its associativity; a
multi-token `notation` with interior placeholders; overloaded notation;
`local notation`; a same-file token that changes tokenization of a
later line (the maximal-munch cross-check); and at least one
intentionally-malformed declaration whose failure leaves the rest of
the file parsing cleanly. Gate: byte round-trip + oracle-tree equality
across the whole corpus, wired into the same CI task as M3a's parser
gate.

## Out of scope (and where it lands)

Explicitly **out of scope** for M3b1:

- The general `syntax`/`macro`/`elab`/`syntaxAbbrev`/`syntaxCat`/
  `binderPredicate` commands and shape-only `macro_rules`/`elab_rules`
  → **M3b2**.
- Imported-notation `.olean` parser-extension decode → **M3b2**.
- `scoped` notation, structural `namespace`/`open`/`end`/`open … in`/
  section tracking, and parsing-relevant `set_option`s → **M3b3**.
- Macro *expansion* and elaboration (M3b1 parses and registers the
  notation *parser*; it never expands anything) → **M4**.
- `leanr fmt` and all formatting → **M3c**.
- salsa/query wiring → **M5** (the fingerprint seam is preserved but
  not wired).
