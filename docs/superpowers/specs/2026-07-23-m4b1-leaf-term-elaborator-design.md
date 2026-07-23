# M4b-1 — the leaf term elaborator and its differential oracle harness — design spec

## Where this sits

M4a shipped the `MetaM` core: `leanr_meta`'s `whnf`, `infer_type`,
`is_def_eq`, and tabled typeclass synthesis, differentially verified
against the pinned oracle. Nothing above it exists yet — there is no
`leanr_elab` crate.

M4b is the **term elaborator** (`TermElabM` over `MetaM`): the layer
that turns `Syntax` into `Expr`. It is the largest and highest-fidelity-
risk milestone in all of M4 — the accepted language is a fixpoint of an
undocumented elaboration schedule — so it is sliced, exactly as M4a was
(meta-core → reduction/inference → defeq → synthesis). The sequence:

| Slice | Content |
|---|---|
| **M4b-1** (this spec) | `leanr_elab` skeleton, minimal `TermElabM`, the syntax-kind→elaborator dispatch table, the elaboration oracle harness, and the **leaf** elaborators |
| M4b-2 | binders (`fun`/`forall`/`let`/`have`/`show`) + the postponement / synthetic-mvar ladder |
| M4b-3 | the application elaborator (`elabApp`: implicit/instance-implicit insertion, named/optional args, `@`) + coercion insertion |
| M4b-4 | `elabAsElim`, dot notation, `binop%`, anonymous constructor `⟨⟩` |
| later M4 | structure instances, match/equation compiler, `do`, tactics |

**This spec is M4b-1 only.** It stands up the crate seam, the dispatch
model, the `ensure_has_type`→`is_def_eq` integration, and the differential
harness on the simplest real terms — before any of the scheduling work
that is the actual fidelity risk. It is the analogue of M4a plan 2
(whnf/infer + the tier-1 oracle harness): infrastructure plus the
smallest verifiable surface.

## Scope

**Leaf forms only.** A leaf is a term with no binder and no application:

- literals — `num` / `str` / `char`
- sorts — `Sort` / `Type` / `Prop`
- identifiers resolving to a **global constant**
- type ascription — `(e : T)`
- the hole — `_`

No binders, no application, no postponement, no coercions, no macro
expansion, no `open`/alias/`export`/dot-notation resolution. Each
exclusion names the slice that owns it (see *Out of scope*).

## What M4b-1 ships — and a stated exception

Every milestone after M0 ships something independently useful. Like all
of M4a, **M4b-1 does not**, and this is recorded rather than papered
over: a `leanr elab` subcommand that elaborates a bare leaf term would
be a contrivance, not a tool anyone would run. What M4b-1 delivers is a
`leanr_elab` term elaborator for leaf forms, **independently verified**
against the oracle by a hermetic regression gate. User-facing value
arrives when the elaborator can handle enough of the language to
elaborate a real declaration — an M4 milestone-level claim, not a
per-slice one.

## Crate and module layout

A new `leanr_elab` crate. Dependencies: `leanr_meta` (the `MetaM`
core), `leanr_kernel` (the `Expr` bank / `Store` / `NameId`),
`leanr_syntax` (`SyntaxNode`, the rowan lossless tree), and the env
view the two already share. It depends on nothing the kernel TCB
forbids; `leanr_kernel` continues to depend on no workspace crate.

Modules:

| Module | Responsibility |
|---|---|
| `elab.rs` | `TermElabM` state; `elab_term` / `elab_term_ensuring_type` entry points |
| `dispatch.rs` | the `SyntaxKind → elaborator` table and lookup |
| `builtin/sort.rs` | `Sort` / `Type` / `Prop` |
| `builtin/lit.rs` | `num` / `str` / `char` |
| `builtin/ident.rs` | identifier → global constant |
| `builtin/ascription.rs` | `(e : T)` |
| `builtin/hole.rs` | `_` |
| `resolve.rs` | global-name resolution (§ Name resolution) |
| `error.rs` | `ElabError`, including `UnsupportedSyntax(kind)` |

## `TermElabM` state

`TermElabM` wraps `leanr_meta`'s `MetaCtx` (the `MetaM` state — mvar
context, defeq config, caches) and adds only what the leaf elaborators
need:

- `level_names: Vec<Name>` — universe parameters in scope, for `Sort u`.

The **expected type is a parameter**, not state: it is threaded through
`elab_term(stx, expected_type: Option<ExprId>)`, mirroring Lean, where
`expectedType?` is an argument to `elabTerm`, not a field of
`Term.State`.

Fields the slice-2 scheduling ladder will need — `synthetic_mvars`,
`mvar_error_infos`, `let_recs_to_lift` — are **deliberately not added
yet.** No slice-1 elaborator postpones, so empty scaffolding would be
speculative surface with no test exercising it. They arrive in M4b-2
with the code that populates them.

## Dispatch and the leaf elaborators

`elab_term` looks up an elaborator in a table keyed on the term's
interned `SyntaxKind` **name** (leanr's parser already emits Lean's
own node-kind names, e.g. `Lean.Parser.Term.type`, so the key is the
same string the oracle dispatches on).

**No macro expansion in slice 1.** Every leaf form is builtin syntax,
not a macro, so `elab_term` does not run an `expandMacro?` step. A
syntax kind absent from the table is a hard `UnsupportedSyntax(kind)`
error — never a silent fallthrough. This keeps "the elaborator does not
handle X yet" loud and attributable, in the spirit of the project's
"internal errors never swallowed" rule; macro expansion enters the
dispatch path in the slice that first needs it.

The elaborators:

- **literals** — `num`/`str`/`char` build the corresponding literal
  `Expr` (`Nat`/`String`/`Char`). `num` with an expected type stays a
  `Nat` literal in slice 1; `OfNat`-driven numeric literals route
  through coercion/app machinery and are that slice's concern.
- **sorts** — `Prop` = `Sort 0`; `Type` = `Sort (u+1)` with a fresh
  level metavariable; `Sort u` reads its level argument. Universe
  metavariables so produced are representable in the harness (see
  *Universe metavariables*).
- **identifiers** — resolve to a global constant (§ Name resolution),
  emitting `mkConst name levels` with fresh level metavariables for the
  constant's universe parameters.
- **type ascription `(e : T)`** — elaborate `T` (as a type),
  then `elab_term_ensuring_type(e, Some T)`.
- **hole `_`** — a fresh expression metavariable at the expected type
  (or a fresh type metavariable if none is given).

`elab_term_ensuring_type(stx, expected)` elaborates `stx`, then, if
`expected` is `Some`, runs `is_def_eq(infer_type(result), expected)`.
**On a defeq mismatch it errors.** Real Lean would insert a coercion
here; coercion insertion is M4b-3, so slice 1 has no coercion path and
the corpus is chosen so every leaf matches its expected type without
one. An `IsDefEqStuck` from `is_def_eq` also errors in slice 1 (nothing
can later unstick it without the synthetic-mvar ladder).

## Name resolution

Full Lean `resolveName` handles current-namespace prefixes, `open`,
aliases, `export`, `_root_`, and dot-notation, resolving ambiguity into
an overload set. Slice 1 implements a strict subset:

- resolve **global constants only** — the name as written, plus
  current-namespace prefixes, against the environment;
- **ambiguity is an error**, not an overload set;
- no `open` / alias / `export` / `_root_` handling;
- no dot-notation (M4b-4);
- no fvar resolution — there are no binders, so no local context to
  resolve against.

The corpus uses qualified names to stay inside this subset. `open`,
aliases, and overload resolution enter in the slices whose elaborators
require them; recording the boundary here keeps a later "why did this
name resolve differently" from being mis-attributed to the elaborator
core.

## The differential oracle harness

The shape mirrors M4a's tier-1 gate exactly: a `dump_*.lean`
meta-program emits canonical Expr-JSON queries; a hermetic
`oracle_*.rs` test replays them against the Rust crate using committed
`.olean` + `.jsonl`, with CI never installing Lean (`docs/ORACLE.md`).
The one structural difference from M4a is the input: an elaboration
query is `syntax → Expr`, where M4a's queries were `Expr → Expr`.

### Input model — source-text, end-to-end

The corpus is **Lean source snippets** (`(source, expected_type?)`
against a committed env). The oracle parses and elaborates each; leanr
parses the **same source through its own `leanr_syntax` parser** and
elaborates. Both canonicalize to Expr-JSON and are compared.

This is defensible precisely because leanr's parser is **already**
independently gated against the oracle's `Syntax`
(`crates/leanr_syntax/tests/oracle_golden.rs` via `dump_syntax.lean`):
a parse divergence fails *that* gate first, so a failure in the
elaboration gate attributes to the elaborator. The alternative —
deserializing the oracle's serialized `Syntax` into a `SyntaxNode` to
bypass leanr's parser — would build a second faithful-reconstruction
surface duplicating the parser, itself a thing that can diverge, for an
isolation the parser's own gate already provides. Source-text also
tests the real user pipeline and keeps the corpus format minimal.

### Components

- **`tests/fixtures/elab/Elab0.lean` (+ committed `Elab0.olean`)** — a
  prelude-mode fixture environment supplying exactly the constants the
  corpus references (`Nat`, `Int`, `String`, `Char`, …) and nothing
  else, so the environment leanr replays is the one the oracle dumped
  from. Follows the `Meta0` / `Synth0` precedent.
- **`tests/fixtures/elab/dump_elab.lean`** — for each query:
  `runParserCategory … \`term` → `elabTerm (expectedType? := …)` →
  `instantiateMVars` → canonical Expr-JSON. Emits `elab-queries.jsonl`.
  Reuses the canonical scheme and `toCanon` machinery the meta dumpers
  already established.
- **`leanr_syntax`: a new `pub fn parse_term(src, snap) -> ParseResult`**
  driving the existing `Prim::Category { name: "term" }` path — the
  same category machinery `parse_module` already uses, exposed for a
  single term. The elaboration harness (and later slices) parse a term
  through it.
- **`leanr_elab/tests/oracle_elab.rs`** — hermetic (committed
  `.olean` + `.jsonl`, no Lean, no network): for each query,
  `parse_term(source)` → `elab_term_ensuring_type` → `instantiate_mvars`
  → canonicalize → assert byte-equal to the expected JSON. Shares the
  `tests/support` decode/encode helpers with the meta gates.
- **Gate: `mise run elab:fast`** runs `oracle_elab`, and is added to
  `test` and `ci`. It is a **regression** gate — "every leaf term that
  used to elaborate to the oracle's result still does" — in the same
  spirit as `meta:fast`. There is **no nightly and no Mathlib sweep**
  in this slice: leaf terms over a fixed fixture env have no
  discovery dimension. Mathlib-scale elaboration is a later M4 slice,
  once the elaborator handles real declarations.

### Universe metavariables in the output

Elaborating a universe-polymorphic constant (e.g. `List`) yields a
term carrying an **unassigned level metavariable** that
`instantiateMVars` does not close. The M4a canonical Expr-JSON scheme
cannot represent it: its level grammar is `zero` / `succ` / `max` /
`imax` / `param`, with no level-metavariable node.

The scheme is **extended** with one node,
`{"k":"lmvar","i":N}`, numbered in first-occurrence order per query
record exactly as expression mvars already are. Both the dumper's
canonicalizer (`dump_elab.lean`, and the shared scheme header) and the
Rust `decode`/`encode` in `tests/support` gain the single new case.
The alternative — restricting the corpus to universe-monomorphic leaves
so no level-mvar ever surfaces — was rejected: it only defers the same
gap to M4b-2 and biases the corpus away from ordinary polymorphic
constants that leaf identifiers routinely denote.

## Testing

Per devkit testing-practices, tiered:

- **Unit tests** (in-crate): each leaf elaborator in isolation
  (`sort`, `lit`, `ident`, `ascription`, `hole`); `dispatch` returns
  `UnsupportedSyntax` for an unregistered kind; `resolve` errors on
  ambiguity and on an unknown name; `parse_term` round-trips a term's
  source text (losslessness) independently of elaboration.
- **The differential gate** (`oracle_elab`, hermetic): the corpus of
  leaf queries, byte-for-byte against the oracle. This is the
  acceptance surface; TDD each elaborator against a failing oracle
  fixture first.
- **Never-panic**: `parse_term` and `elab_term` never panic on the
  committed corpus; malformed/`missing` syntax nodes produce an
  `ElabError`, never an unwrap.

## Risks and mitigations

- **Parser/elaborator conflation in the gate.** Mitigated by the input
  model: the parser is separately gated (`oracle_golden.rs`), so a
  parse divergence is caught there, upstream of this gate.
- **Canonicalization completeness.** The `lmvar` extension must be
  applied on *both* the dumper and the Rust decode/encode, or the two
  sides serialize the same term differently and every polymorphic-leaf
  query fails spuriously. Covered by a unit test that round-trips a
  term containing a level mvar through `encode`∘`decode`.
- **Fixture-env drift.** `Elab0.olean` must be regenerable from
  `Elab0.lean` under the pinned toolchain (`mise run fixtures:regen`);
  a hand-edited `.olean` is a silent-divergence trap. The regen path
  covers it.
- **Universe defaulting divergence.** Whether the oracle leaves a
  top-level universe mvar unassigned or defaults it depends on the
  elaboration entry point `dump_elab.lean` uses. The dumper must call
  the same entry (`elabTerm` + `instantiateMVars`, no extra
  universe-defaulting pass) that leanr models, or an assigned-vs-mvar
  mismatch appears as a spurious regression. Pinned by using one
  documented entry point in the dumper and matching it in `elab_term`.

## Out of scope (and where it lands)

- **Binders (`fun`/`forall`/`let`/`have`/`show`) and the postponement /
  synthetic-mvar ladder** → M4b-2. The ladder is the highest fidelity
  risk in M4 and is cleaner designed as one piece with the binders that
  first exercise it.
- **The application elaborator (`elabApp`), implicit/instance-implicit
  argument insertion, named/optional args, `@`** → M4b-3. Coercion
  insertion (`mkCoe`) enters here — hence slice 1's ascription errors
  rather than coerces on a type mismatch.
- **`elabAsElim`, dot notation, `binop%`, anonymous constructor `⟨⟩`**
  → M4b-4.
- **`open` / alias / `export` / `_root_` name resolution and overload
  sets** → the slices whose elaborators require them.
- **Macro expansion in the dispatch path** → the first slice with a
  macro-defined term form.
- **Structure instances, the match/equation compiler, `do`, tactics**
  → later M4 slices.
- **Mathlib-scale elaboration discovery and any nightly** → a later M4
  slice, once the elaborator handles real declarations.

## Next step

Invoke the writing-plans skill to produce the M4b-1 implementation
plan, applying the devkit skills (developer-environment,
testing-practices, writing-clean-code, security-practices,
navigable-codebases). The plan sequences: the `leanr_elab` crate
skeleton and `TermElabM`; `parse_term` in `leanr_syntax`; the `lmvar`
scheme extension in the dumper and `tests/support`; the `Elab0`
fixture + `dump_elab.lean`; the dispatch table and each leaf
elaborator, TDD against the oracle; and wiring `elab:fast` into `test`
and `ci`.
