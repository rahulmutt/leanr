# M3c — `leanr fmt`, thin vertical slice: the pretty-printing engine, a preserve-fallback formatter, and the self-consistency harness — design spec

Status: approved (brainstormed 2026-07-19)
Predecessor: [2026-07-13-m3a-parser-foundations-design.md](2026-07-13-m3a-parser-foundations-design.md) (§ M3c, scope decisions)

## Problem

M3's parser half (M3a, M3b1–b3) is done: `leanr_syntax` produces
lossless rowan trees where `text(parse(src)) == src` by construction,
validated against the oracle over the pinned Mathlib closure. M3's
second half — `leanr fmt`, the first Lean formatter — has no
implementation and only a strategy sketch (the M3a spec's § M3c and
scope decisions).

The strategy is already fixed at the M3-parent level and is **not**
reopened here:

- Opinionated, gofmt-style; one canonical style aligned with the
  Mathlib style guide; minimal/no config.
- Total via **preserve-fallback**: constructs with style rules get
  reformatted, everything else preserves the author's layout verbatim
  (free with lossless trees).
- Correctness is **self-consistency, not differential** — official Lean
  has no source formatter, so there is no byte-level oracle to diff
  against. Acceptance is total + idempotent + semantics-preserving.
- New crate `leanr_fmt`, consumes trees only, never re-lexes source.
- Ships `leanr fmt` / `leanr fmt --check`.

What is undecided — and what this spec fixes — is the *internals*: the
pretty-printing engine, which constructs get style rules in the first
shippable cut, how comments are kept safe, and the shape of the
self-consistency harness.

## Goal

Ship a **thin vertical slice**: a small, high-value style-rule set that
proves the engine, the comment-safety mechanism, and the
total/idempotent/semantics-preserving harness end-to-end on the whole
parser pass-list corpus. Breadth grows later behind the preserve-
fallback. Success is the M3b pattern: hermetic oracle-independent
fixtures for every rule, all existing gates green, and the four
acceptance invariants gating on the pass-list corpus — **no numeric
formatting-coverage target**.

## Scope decisions (agreed in brainstorming)

- **Ambition: thin vertical slice.** The first cut reformats a handful
  of inherently-safe constructs; everything else is preserve-fallback.
  Rejected: broad style coverage (larger surface, longer milestone,
  rule churn); engine + harness only with a near-empty rule set (a
  near-no-op formatter is not adoptable).
- **Engine: hand-rolled Wadler/Leijen `Doc`.** Purpose-built
  `Doc` combinator (`Text`/`Line`/`Nest`/`Group`/`Concat`, group-
  flattening against a target width) — the same model as Lean's own
  `Std.Format`, gofmt, and prettier. In-crate, no dependency (satisfies
  the deps-need-justification rule), full control over the width and
  idempotence edge cases the harness is strict about. Rejected: porting
  Lean's `Std.Format` exactly (fidelity to a value we never consume,
  larger port); an external `pretty` crate (dependency, cedes control).
- **Comments: conservative fallback + a hard invariant.** A node is
  reformattable only if all its comments are boundary trivia; any
  interior comment routes it to preserve-fallback. Separately, a file-
  level invariant — the *ordered* sequence of comment tokens is byte-
  identical in ↔ out — is harness-enforced across the corpus. This is
  the only guard against a dropped/moved comment, because the semantics
  check excludes trivia (see Architecture). Rejected: rustfmt-style
  attach-and-reflow now (the classic formatter bug-farm, against the
  thin-slice choice); invariant-only with no fallback (a failing
  invariant means fmt bails on the file, breaking totality).
- **First-slice rules: trivia baseline + single-line token spacing +
  import normalize/sort.** Indentation normalization and all multi-line
  construct rules are deferred — indentation is meaningless without
  multi-line construct rules to act on, and it is the one place Lean's
  layout-sensitive parser bites; doing it well is essentially the whole
  multi-line formatting problem, not a thin slice.
- **Packaging:** one milestone (**M3c**, the name the M3a spec
  reserved), one branch, one spec/plan cycle, single final whole-branch
  review — the M3b3 pattern.

## Architecture

### Crate & module structure — `crates/leanr_fmt`

New crate. Depends on `leanr_syntax` (`tree`, `kind`, `canon`) and
nothing that pulls in the kernel. `format_tree(&SyntaxTree) ->
FormatResult` is a **pure function** `tree → String`; the CLI wraps it.

```
leanr_fmt/src/
  lib.rs      // format_tree(&SyntaxTree) -> FormatResult
  doc.rs      // the Wadler Doc IR + layout(width)
  rules/
    mod.rs    // dispatch: &SyntaxNode -> Option<Doc>; None = preserve-fallback
    trivia.rs // trailing-ws, final newline, blank-line runs
    spacing.rs// single-line token spacing (bail if multiline)
    imports.rs// import block normalize + sort
  comments.rs // boundary-comment classification + the invariant check
```

Target width is fixed at **100 columns** (Mathlib convention), not
configurable.

### The Doc engine (`doc.rs`)

Minimal Wadler/Leijen:

```
Doc = Text(str) | Line | Nest(n, Doc) | Group(Doc) | Concat(Vec<Doc>)
```

`layout(width)` walks the `Doc` choosing flat-vs-broken per `Group`
against the remaining width, emitting the string. ~200–400 LOC, no
dependency. Idempotence rests on `layout` being a deterministic
function of the `Doc` value.

### Rule dispatch + preserve-fallback (the spine)

The formatter walks the red tree top-down. For each node,
`rules::dispatch(node)` returns `Option<Doc>`:

- **`Some(doc)`** — the node has a style rule; emit its `Doc`.
- **`None`** — **preserve-fallback**: emit the node's exact source
  bytes verbatim (`node.text()`, free with lossless trees).

Fallback granularity is **per-node**: an unformatted construct nested
inside a formatted one keeps its bytes while the parent's layout is
normalized. This same seam is the comment escape hatch — a rule that
detects an interior comment returns `None`.

The **trivia baseline** is *not* a dispatch rule — it is a final whole-
output normalization pass (below), applied uniformly to formatted and
fallback regions alike, so that verbatim fallback text is also trailing-
whitespace- and blank-line-normalized. Only single-line spacing and
import handling are `dispatch` rules.

### The first-slice rules

1. **Trivia baseline** (`trivia.rs`) — a final pass over the assembled
   output string (after the tree walk), applied uniformly to formatted
   and fallback regions: strip trailing whitespace per line, ensure
   exactly one final newline, collapse blank-line runs to ≤1 (Mathlib
   convention). Parse-safe by construction — it only mutates non-
   significant trivia. One deliberate interaction: trailing-whitespace
   stripping also trims trailing whitespace that falls *inside* a line-
   comment token (a Lean line comment runs to end of line), so the
   comment invariant is defined **modulo trailing whitespace** — see
   Comments.
2. **Single-line token spacing** (`spacing.rs`) — normalize intra-line
   spacing (`( x : T )`→`(x : T)`, `:=`/`→` spacing) for structured
   nodes **only when the node occupies a single line**; the rule
   returns `None` (fallback) the moment the node spans lines, where
   indentation may be significant. Needs the full grammar snapshot to
   have parsed the construct.
3. **Import block normalize + sort** (`imports.rs`) — one `import` per
   line, sorted alphabetically. Works off the header parse (builtin
   snapshot); needs no import closure.

### Comments (`comments.rs`)

- **Fallback trigger:** a node is reformattable only if all its comment
  tokens are boundary trivia (leading, before the first token; or
  trailing, after the last). Any *interior* comment → `dispatch`
  returns `None` → verbatim. Boundary comments travel with the node for
  free, being outside the reformatted span.
- **Hard invariant (harness-enforced):** the **ordered** sequence of
  comment tokens in the output equals the input's, **byte-identical
  modulo trailing whitespace** (each comment right-trimmed on both
  sides before comparison — the trivia baseline intentionally trims
  trailing whitespace inside line comments; nothing else about a
  comment may change). Ordered, not just a multiset — order-
  preservation is cheap to check and catches reordering a multiset
  would miss. This is the only guard against a dropped/moved/edited
  comment, since the semantics check (`canon_jsonl`) excludes trivia. A
  failure is a release-blocking bug, same posture as the project's
  under-invalidation rule.

### Data flow & CLI (`leanr fmt`, sibling of `Parse`)

`leanr fmt` is a new `clap` subcommand beside `Parse` in `leanr_cli`.

- `leanr fmt <files...>` — rewrites in place. `--path <olean>` supplies
  the grammar snapshot, same as `leanr parse`. `-` / stdin → stdout.
- `leanr fmt --check <files...>` — writes nothing; exits non-zero and
  lists files that would change (gofmt convention).
- **Precondition:** fmt requires a successful full parse (import
  closure available). If the file does not parse, fmt **errors loudly**
  — it never formats a broken/error tree. This is what makes "total on
  parseable input" well-defined.

## Error handling & edge cases

- Empty file, comment-only file, already-formatted file (must be a
  fixed point), CRLF/tabs in trivia, a construct that parses with error
  nodes (→ that command falls back). Idempotence + preserve-fallback
  mean these degrade to verbatim, never crash.
- A file whose import closure is unavailable, or that does not parse, is
  a loud CLI error, not a silent partial format.
- The formatter never panics on any pass-list input (a totality gate,
  below); an internal rule failure degrades to fallback for that node.

## Acceptance harness

Corpus reuse: the pass-list (`tests/fixtures/syntax/mathlib-passlist.txt`,
files known to parse green — only parseable files can be formatted).
Over that corpus, four invariants, each a gate:

1. **Total** — `format_tree` returns `Ok` on every pass-list file
   (never panics, never bails).
2. **Idempotent** — `fmt(fmt(x)) == fmt(x)`, byte-exact.
3. **Semantics-preserving** —
   `canon_semantic(parse(fmt(x))) == canon_semantic(parse(x))`.
   `canon_semantic` (in `leanr_fmt::verify`) is `canon_jsonl` with two
   changes, and MUST be used here instead of raw `canon_jsonl`: (a) the
   `"s":[start,stop]` byte spans are omitted — formatting legitimately
   moves token positions, so absolute offsets are layout, not meaning;
   (b) the header's import-command siblings are emitted in sorted order —
   import sorting is semantics-neutral. Raw `canon_jsonl` equality was
   found (during implementation) to fail on *every* format change, because
   it embeds byte spans (shift on any length change) and preserves import
   order — so the invariant is defined against `canon_semantic`, which
   still catches real corruption (dropped/renamed/restructured token,
   corrupted import name) while tolerating exactly layout + import order.
4. **Comment invariant** — ordered comment tokens equal in ↔ out,
   byte-identical modulo trailing whitespace.

Plus **hermetic probe fixtures** (M3b-style) per rule: trivia cases; the
single-line-spacing matrix including the multiline→fallback boundary;
import sort/dedup/one-per-line; and boundary-vs-interior comment cases.
All existing gates stay green (workspace tests, lint, deps, parse-
acceptance with globs extended to fmt fixtures, fuzz both targets,
never-hang storms). A new mise task (e.g. `fmt:mathlib`) runs the corpus
sweep as a **fast pass-list gate** — not the ~35h full-closure discovery
sweep.

## Out of scope (and where it lands)

- **Indentation normalization + all multi-line construct rules** → the
  next M3 slice (indentation is meaningless without multi-line rules and
  is the layout-sensitive danger zone).
- **Comment attachment/reflow** → later, behind the fallback + the
  byte-identical comment invariant that already guards it.
- **Config / alternate line widths** → not unless demanded; one true
  style, fixed 100-column width.
- **salsa wiring** → M5; the grammar snapshot already threads as an
  explicit value, so wrapping `parse`/`format` in a query is mechanical.

### Fast-follows discovered during M3c implementation

Addressed by [2026-07-20-m3c-fast-follows-design.md](2026-07-20-m3c-fast-follows-design.md), except as noted.

- **Apply the token-aware walk to import-bearing bodies.** Files WITH
  imports currently emit the head/tail as raw source slices, so trivia
  baseline + operator spacing do NOT run on their bodies (only import
  sort + EOF `finalize` do). Since essentially every real corpus file has
  imports, the corpus gate mainly exercises the import-splice + invariant
  machinery; trivia/spacing are covered by the import-free hermetic
  fixtures. Route the non-import spans through `render_tokens` so all
  three rules apply uniformly.
- **`fmt:mathlib` snapshot reuse.** The gate rebuilds a full snapshot per
  file (~10 min release over the pass-list — the baseline cited from the
  previous milestone, not re-measured here). Reuse snapshots per distinct
  import set (as `mathlib_sweep.rs` does) to make the "fast" tier live up
  to the name. **Only partially addressed:** snapshots are now reused per
  distinct import set, but the curated 23-file pass-list has 22 distinct
  import sets, so there is almost nothing to group and the reuse buys
  little. Measured gate wall-clock is ~8m45s (a prior run earlier this
  milestone measured ~9m1s) — a modest improvement over the cited
  baseline above, not the step change grouping was meant to deliver. The
  real cost driver, per-closure olean decoding, is untouched. Revisit in
  a later slice.
- **Share `canon_semantic`'s despan with `canon.rs`.** `canon_semantic`
  duplicates `canon_jsonl`'s node shape + `json_str`; export a span-less
  core from `leanr_syntax::canon` to remove the schema-drift risk (it is
  only ever compared against itself, so drift can only false-negative).
- **CLI edge combos:** `leanr fmt --check -` (stdin) currently always
  exits 0 without flagging a would-change; `leanr fmt` with zero file
  args exits 0 silently. Define and handle these deliberately.
