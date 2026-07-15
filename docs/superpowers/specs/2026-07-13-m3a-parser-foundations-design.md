# M3a — parser foundations: lossless trees, lexer, builtin grammar — design spec

Date: 2026-07-13. Milestone: M3 ("Parser + formatter — full
extensible-grammar parser, lossless trees, `leanr fmt`") — first
slice. Parent: `2026-07-04-leanr-architecture-design.md` (§Milestones,
M3); predecessor milestone: M2 (complete as of
`2026-07-13-m2d-remote-cache-design.md`, acceptance recorded).

## Problem

Nothing in leanr can read a `.lean` source file. M1 checks compiled
`.olean`s; M2 orchestrates the official `lean` binary over them. The
roadmap's next deliverables — the first Lean formatter, and the parse
tier M4's elaborator will consume — both need Lean's extensible
grammar realized in Rust over lossless syntax trees. Lean's grammar is
extensible all the way down (even `def` is a parser registered in the
`command` category, and Mathlib defines hundreds of notations that
change how later files tokenize and parse), so "a parser" is really
three subsystems: tree/lexer/machinery foundations, the extensibility
tier, and the formatter on top.

## Goal

M3 ships `leanr fmt` — the first Lean formatter — with parser fidelity
proven by round-tripping all of pinned Mathlib against the official
parser. M3a, this slice, builds the foundations: the `leanr_syntax`
crate with lossless green/red trees, the table-driven tokenizer, the
category/Pratt parsing machinery, the hand-written Rust builtin
parsers official Lean itself bootstraps from, and the oracle harness
that makes "our tree equals Lean's tree" a checkable gate.

## M3 decomposition (agreed in brainstorming)

Three sub-milestones, each independently landable with a recorded
acceptance gate, following the M2a–M2d pattern:

- **M3a (this spec) — foundations.** `leanr_syntax`: lossless
  green/red trees, table-driven lexer, category/Pratt machinery,
  Rust builtin parsers, the grammar-snapshot value, the oracle dump
  harness. Acceptance: byte round-trip + oracle-tree equality on a
  curated builtin-grammar fixture corpus.
- **M3b — the extensible grammar.** `ParserDescr` interpreter,
  parser-extension entry decoding from imported `.olean`s (via
  `leanr_olean`, which today validates but does not decode extension
  entries), same-file `syntax`/`notation`/`macro`/`infix` commands,
  scoped-notation activation via structural `namespace`/`open`
  tracking, parsing-relevant `set_option`s, and enumerated Rust shims
  for the rare raw-`Parser`-function cases. Acceptance: the full M3
  parser bar — byte round-trip + oracle-tree equality over the whole
  pinned Mathlib dependency closure.
- **M3c — `leanr fmt`.** `leanr_fmt`: pretty-printing engine over the
  lossless trees, opinionated style rules for high-value constructs,
  preserve-fallback everywhere else. Acceptance over all of Mathlib:
  total on parseable input, idempotent (`fmt(fmt(x)) == fmt(x)`),
  semantics-preserving (output re-parses to an equivalent canonical
  tree); ships `leanr fmt` / `leanr fmt --check`.

Load-bearing boundaries: M3a's tree types plus the **grammar
snapshot** (an explicit, fingerprintable parser-state value) are the
interface M3b populates; M3c consumes trees only and never re-lexes
source. Style-rule breadth keeps growing after M3c behind the
preserve-fallback — deliberate, not scope creep.

## Scope decisions (agreed in brainstorming)

- **Formatter-first priorities.** `leanr fmt` is the shippable users
  adopt (nothing else exists for Lean); lossless trees and trivia
  handling are first-class from day one, and M4-readiness is a
  byproduct. Rejected: elaborator-foundation-first (would defer
  trivia/formatting concerns that are cheap now and churn later).
- **Oracle-fed grammar via `.olean` (the M3b strategy, fixed now
  because M3a's interfaces serve it).** Official Lean stores every
  `syntax`/`notation`/`macro` declaration as *data* — declarative
  `ParserDescr` values plus parser-extension entries (token tables,
  category registrations) in the `.olean`s we already decode. leanr
  interprets `ParserDescr` at parse time; the finite builtin-parser
  set is hand-written Rust — exactly how official Lean bootstraps.
  Needs no elaborator and no VM. Costs, stated honestly: parsing a
  file requires its imports' `.olean`s to exist (the same constraint
  official Lean has; M2's orchestrator guarantees it), and raw
  `Parser`-function extensions need per-case Rust shims with a loud
  error otherwise. Rejected: source-order bootstrap (parse the whole
  import closure from source — slow, needs elaboration in corner
  cases, duplicates M4); snapshotting the pinned grammar into static
  tables (not extensible — breaks on any downstream project's own
  notation, all throwaway at M4, fails the independently-useful bar).
- **Acceptance = bytes AND oracle trees.** `text(parse(src)) == src`
  byte-exact, plus structural equality against official Lean's parse
  trees dumped by a pinned-toolchain script. Losslessness alone is
  weak — a tree can round-trip perfectly while grouping by the wrong
  precedence, and a formatter on a wrong tree corrupts meaning
  silently. Matches the project's oracle-merciless posture.
- **Opinionated, gofmt-style formatter (M3c).** One canonical style,
  aligned with the Mathlib style guide (that's the corpus and the
  community); minimal/no config. Deterministic, idempotent,
  semantics-preserving. Rejected: conservative normalizer (weaker
  product), configurable engine (most work, dilutes the
  one-true-style value; config can come later if demanded).
- **fmt total via preserve-fallback (M3c).** Constructs with style
  rules get reformatted; everything else preserves the author's
  layout verbatim (free with lossless trees). Rejected: full style
  coverage before shipping (hundreds-of-notations long tail);
  core-only fmt (useless on real Mathlib-adjacent projects).
- **Batch now, query-ready by design.** M3 parses in parallel like
  `leanr check`; no salsa wiring. The grammar snapshot is an
  explicit, hash-fingerprintable value passed into the parser (never
  global), so wrapping `parse(file)` in a salsa query with the
  architecture's parser-state firewall fingerprint at M5 is
  mechanical. Rejected: wiring salsa now (orthogonal to fmt/round-trip
  and unproven fit); deferring the state shape (rework later).

## Architecture: `crates/leanr_syntax`

New crate; no `leanr_kernel` dependency for parsing itself (M3b will
read decoded `.olean` data via the same store types `leanr_olean`
emits). Four modules plus the oracle harness:

- **`tree` — lossless green/red syntax trees.** Green nodes are the
  immutable, position-independent value (kind + children + text
  lengths); red nodes are lazily-materialized cursors carrying
  absolute offsets and parent pointers. Every source byte — including
  whitespace and comments — is a trivia token in the tree, so
  `text(parse(src)) == src` holds *by construction*; round-trip
  failures can then only mean lost or duplicated tokens, never lost
  trivia. Implementation: the `rowan` crate (rust-analyzer's
  battle-tested green/red trees) rather than hand-rolling. Lean's
  node kinds are an open set of hierarchical names
  (`Lean.Parser.Term.app`, Mathlib's own kinds, …) while rowan kinds
  are `u16`; a per-session kind interner bridges (name ↔ u16 —
  Mathlib needs a few thousand kinds, far under 65k). The tree API
  exposed to the rest of the crate is our own trait-shaped boundary,
  so if rowan's model fights us we swap in a hand-rolled bank-style
  tree — the same escape hatch the architecture reserves for salsa.
- **`lex` — a table-driven tokenizer, not a fixed lexer.** Lean has
  no static token set: `notation` commands add tokens, and
  tokenization is maximal-munch against the *current token table*.
  The tokenizer is a pure function of `(source, token table)` invoked
  per-token as the parser advances, exactly as in official Lean. The
  fixed part: identifiers (including French-quote `«...»` and
  hygiene-marked forms), string/char/nat/scientific literals, and
  comments (line + properly-nested block).
- **`parse` — category/Pratt machinery.** Parser categories
  (`command`, `term`, `tactic`, `level`, …) each hold
  leading/trailing parser tables indexed by first token; a Pratt loop
  with precedence thresholds drives them; backtracking with
  furthest-error tracking mirrors Lean's longest-match semantics.
  Positional combinators (`withPosition`, `checkColGt` — the
  whitespace-sensitivity that makes `by` blocks work) are part of the
  machinery from day one; Mathlib is unparseable without them.
- **`builtin` — the Rust-native bootstrap parsers**, enumerated from
  the pinned toolchain's `@[builtin_*_parser]` set: leaf parsers and
  combinators official Lean implements in compiled code (ident,
  literals, and the `leading_parser`/`trailing_parser` definitions
  for `def`, `theorem`, term syntax, etc.). The finite hand-written
  surface everything declarative sits on.
- **`grammar` — the snapshot.** One explicit value: token table +
  categories + registered parsers + precedences. Passed into `parse`,
  never global, hash-fingerprintable. M3a constructs it from builtins
  only; M3b populates it from `.olean`s and same-file commands.
  Within a file, command *N* parses under the snapshot produced after
  command *N−1* (a `notation` on line 10 changes tokenization on line
  11), matching official Lean's parse-one-elaborate-one loop — the
  snapshot is per-command state threaded through the file parse.

`leanr_cli` gains dev-facing `leanr parse --dump <file>` (print the
canonical tree) for eyeballing against the oracle. Thin as always:
parsing and printing only.

## Oracle harness & comparison semantics

A small Lean program (committed under `scripts/`, run with the pinned
toolchain — same pattern as `fixtures:regen`) drives official Lean's
own parser over a `.lean` file and serializes each command's `Syntax`
tree: node kind names, atom/ident text, child structure, atom source
spans. Parsing is cheap relative to elaboration, so dumping all of
Mathlib is a minutes-scale batch job — the full-corpus tree gate
(M3b) is affordable.

Comparison is defined precisely, since "equal trees" does the
acceptance work. Official Lean attaches trivia as leading/trailing
`SourceInfo` on atoms; our trees hold trivia as tokens. Both sides
canonicalize to the same form before diffing: a tree of
`(kind name, children)` with atoms as `(text, source span)`. Equality
is structural over that form. Trivia does not participate in oracle
equality — the byte round-trip gate owns trivia fidelity; spans *do*
participate, because they catch tokens attributed to the wrong node.

## Error handling & edge cases

- **Parse errors are values, not aborts.** A failed parse still
  yields a lossless tree: unparseable text lands in error nodes, and
  recovery resyncs at the next command keyword (Lean's own policy),
  so one bad proof doesn't destroy the rest of the file's tree.
  Diagnostics carry the furthest-failure position and expected-token
  set, rendered as span + message; parse errors get stable error
  codes from day one (the architecture commits to them; retrofitting
  is churn). Internal invariant violations panic with the
  report-this-bug message, never degrade silently.
- **`fmt` safety gates (M3c behavior, fixed now because they shape
  the tree API):** `fmt` refuses to rewrite any file whose parse has
  errors — exit nonzero, report, leave the file untouched. Before
  writing, `fmt` re-parses its own output and verifies canonical-tree
  equivalence with the input; a mismatch is a formatter bug, so it
  refuses and says so. Writes are atomic (temp + rename, the M2
  pattern).
- **Scoped notation (M3b).** `scoped notation`/`scoped syntax`
  activate only when their namespace is opened, so
  `namespace`/`open`/`end`/`open … in` must be interpreted
  structurally *during parsing* to know which extensions are live.
  M3b's subtlest requirement; gets its own acceptance fixtures.
- **Parsing-relevant `set_option`s (M3b).** Enumerated from the
  pinned toolchain; any option that changes parser behavior is
  honored or loudly rejected — never silently ignored.
- **Input hygiene.** Files must be valid UTF-8 (clean error
  otherwise); positions are byte offsets internally, converted at the
  diagnostic boundary.

## Testing

Layers, cheapest first (standing strategy):

1. **Unit tests** — lexer cases (maximal munch against a custom token
   table, nested block comments, French-quote idents, literal edge
   cases), tree invariants, precedence-loop behavior on hand-built
   grammars.
2. **Property tests** — `text(parse(s)) == s` for arbitrary `s`
   (losslessness is total: files with parse errors must round-trip
   byte-exact via error nodes); parse→print→parse stability on
   generated syntax.
3. **Fuzzing** — the parser consumes arbitrary user bytes, so it
   joins `mise run fuzz` alongside the `.olean` raw walker: no
   panics, no non-termination on adversarial input. `THREAT_MODEL.md`
   gains a source-text section: lower-trust input than `.olean`s, but
   the no-panic bar is identical.
4. **Golden fixtures** — a committed corpus of representative files
   with oracle dumps in `tests/fixtures/`, regenerated by
   `mise run fixtures:regen`; PR-gating.
5. **Differential sweep** — the milestone acceptance script: byte
   round-trip + oracle-tree equality over the M3a fixture corpus
   (M3a), then the full pinned Mathlib closure (M3b), results
   recorded in the spec as with M1–M2d.

## Dependencies

`rowan` (lossless green/red trees), pinned and vetted through
`deny.toml` like all M2 additions. Property/fuzz tooling reuses the
existing proptest/cargo-fuzz infrastructure.

## Acceptance (the M3a bar; results recorded here on completion)

1. Over a curated fixture corpus exercising the builtin grammar
   (module headers, `def`/`theorem`/`structure`/`instance`,
   match/do/by blocks, binder forms, literals, attributes): byte-exact
   round-trip **and** oracle-tree equality, zero diffs.
2. Losslessness is total: error-containing fixtures round-trip
   byte-exact through error nodes, with resync demonstrated (commands
   after the error parse normally).
3. Property gates green; parser fuzz target wired into
   `mise run fuzz` with a clean soak.
4. `leanr parse --dump` ships in `leanr_cli`; `ARCHITECTURE.md` gains
   the `leanr_syntax` entry; `THREAT_MODEL.md` gains the source-text
   section; oracle dump script + fixtures committed.

Explicitly **out of scope** for M3a (and where it lands):
`ParserDescr` interpretation, `.olean` extension-entry decoding,
same-file `syntax`/`notation` commands, scoped notation,
parsing-relevant options (M3b); all formatting (M3c); salsa wiring
(M5); macro *expansion* and elaboration (M4 — M3 parses `macro_rules`
but never runs them).

## Next step

Invoke the writing-plans skill to produce the M3a implementation plan.

## Acceptance results (recorded 2026-07-15)

`scripts/parse-acceptance.sh` against the pinned toolchain (`lean`
4.32.0-rc1):

- Fixture corpus: 15 `.lean` files under `tests/fixtures/syntax/`, 12
  oracle-compared (`AttrWide`, `ByTac`, `Cmds`, `CmdsWide`, `Decls`,
  `MatchDo`, `Micro`, `StructMultiLine`, `TermsExtra`, `Terms`,
  `Types`, `Unicode`); `dump_syntax.lean` is the oracle script itself
  (skipped); `Errors0.lean`/`Errors1.lean` are round-trip-only (no
  dump). Fresh `lean --run dump_syntax.lean` output diffed
  byte-for-byte against every committed `.stx.jsonl`: zero diffs on
  all 12.
- Error fixtures: total losslessness confirmed
  (`r.tree.text() == src` on both `Errors0.lean` and `Errors1.lean`);
  resync demonstrated on `Errors0.lean` — 2 `declaration` commands
  (`good1`, `good2`) parse normally on either side of the 1
  garbage-text `<error>` node.
- Property gates green: `cargo test --release -p leanr_syntax` — 97
  lib unit tests, 4 `lossless.rs` proptest properties
  (`lexer_is_total_and_lossless`, `parse_round_trips_arbitrary_input`,
  `parse_round_trips_lean_shaped_soup`, `reparse_is_stable`; 256 cases
  each, proptest default), 5 `never_hang.rs` depth/stack tests, 4
  `oracle_golden.rs` integration tests — 110/110 passed, 0 failed.
  Fuzz soak (`mise run fuzz:syntax`, `parse_module`, 60s,
  `ASAN_OPTIONS=detect_leaks=0`): 3464 runs, cov 2147 / ft 11884, ran
  to completion (`DONE`) with zero crashes/timeouts/OOMs.
- `leanr parse --dump` (release build) byte-identical to the oracle
  dump on all 12 oracle-compared fixtures (`diff -u` clean on every
  one).
- Grammar snapshot fingerprint: `snapshot_fingerprint_is_stable_and_grammar_sensitive`
  passed (deterministic blake3 fingerprint, changes under a grammar
  edit — regression-tested since Task 6/10's `LeadingIdentBehavior`
  field bump to `leanr-m3a-grammar-v2`).
- `mise run ci` (lint, test, lint:deps, scan:secrets,
  cache:incremental, cache:remote): green — `cargo fmt --all --check`
  clean, `cargo clippy --workspace --all-targets -- -D warnings`
  clean, `cargo deny check` "advisories ok, bans ok, licenses ok,
  sources ok" (one pre-existing `getrandom` duplicate-version
  warning, `bans=warn`, not new to this task), `gitleaks detect`
  "no leaks found", full workspace test suite green.
- Divergences discovered and fixed along the way (real list, from the
  milestone's own tasks, not invented): tab/CR are lexed as
  single-byte `ErrorTok` under new codes E0307/E0308 rather than
  treated as whitespace, matching Lean's trivia set of exactly
  `{' ', '\n'}` (Task 2); `1.foo`/`1e`/`0x` intentionally clean-split
  with no diagnostic where Lean hard-errors via backtracking (Task 3,
  documented as valid-input-safe); `leading_parser` default `lhsPrec`
  is 0 (not the surrounding precedence) for 8 registrations
  (`completion`/`proj`/`explicitUniv`/`namedPattern`/`pipeProj`/
  `pipeCompletion`/`subst`/level `addLit`) — the brief's draft had
  this wrong and valid Lean like `x |>.f.1` hard-errored until fixed
  (Task 8); `structInstFields` initially approximated the oracle's
  `sepByIndent` with a plain `SepBy` (multi-line struct instances
  diverged), closed by porting real indent-sensitive `sep_by_indent`
  machinery (Task 8→9); a new `LeadingIdentBehavior` (Default/Symbol/
  Both) field was added to `Category` because the oracle has no
  dispatch tie to break the way the brief assumed — `attr` is
  `.symbol`-keyed, so pre-fix `@[extern foo]`/`@[recursor]`/
  `@[default_instance foo]` were silently accepted as `Attr.simple`
  though Lean rejects them (Task 10, fingerprint bumped v1→v2); lex
  diagnostics are *dropped* (not duplicated) when their token loses a
  `longest_match` race — e.g. `def x := ["a, "b]` reports only E0301,
  the unterminated-string E0302 from the losing branch is not
  surfaced — tracked as a diagnostic-completeness gap, not a
  losslessness or acceptance-blocking one (Task 11, evidence-based
  decline of a proposed BTreeSet dedup whose premise was inverted).

No stale dumps were found on this run — all 12 committed
`.stx.jsonl` fixtures matched a freshly regenerated dump from the
pinned toolchain byte-for-byte on the first attempt.
