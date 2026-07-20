# M3c fast-follows — the unified permuted walk, a fast corpus gate, and a defined `leanr fmt` CLI — design spec

Status: approved (brainstormed 2026-07-20)
Predecessor: [2026-07-19-m3c-fmt-thin-slice-design.md](2026-07-19-m3c-fmt-thin-slice-design.md) (§ Fast-follows discovered during M3c implementation)

## Problem

M3c shipped `leanr fmt`: the Wadler `Doc` engine, three style rules
(trivia baseline, single-line token spacing, import normalize/sort), the
preserve-fallback spine, and the four-invariant self-consistency harness
gating the parser pass-list corpus. Implementing it surfaced four
follow-ups, recorded at the end of that spec as "next slice". This spec
designs all four.

The first is the load-bearing one. The formatter spine has two mutually
exclusive rendering paths, and the one that fires on essentially every
real file is the weaker one: when `imports::detect` finds an import
block, the head and tail are emitted as **raw source slices**, so the
trivia and spacing rules never run on them. Only the import sort and the
EOF `finalize` apply. Since virtually every corpus file has imports, the
corpus gate today mainly exercises the import-splice and invariant
machinery; trivia and spacing are covered only by the import-free
hermetic fixtures.

The other three are smaller: the corpus gate rebuilds a full grammar
snapshot per file (~10 min in release over 23 files, which is not what a
"fast tier" should mean); the semantics oracle duplicates
`leanr_syntax::canon`'s node shape and escaping, where drift can only
false-negative; and two `leanr fmt` CLI paths silently do nothing
(`--check -` always exits 0, and zero file arguments exits 0 silently).

## Goal

Make the formatter apply its rules uniformly to real files, make the
fast gate live up to its name, remove the oracle's drift risk, and give
the CLI a defined surface. No new style rules — indentation and
multi-line construct rules remain deferred to the next slice. Success is
the M3c pattern: hermetic fixtures for each behavior, all existing gates
green, and the four acceptance invariants holding over the pass-list
corpus — which, for the first time, actually exercises the rule engine
on head/tail content.

## Scope decisions (agreed in brainstorming)

- **All four fast-follows in one slice.** They are small, mutually
  independent, and were called out together as the next slice.
- **Unified permuted walk**, not a range-restricted splice. Rejected:
  keeping verbatim sorted imports and token-walking only the head/tail
  spans — the smallest change, but it preserves the two-path special
  case permanently and every future rule inherits the same gap.
- **Zero CLI args = recursive `.gitignore`-respecting walk.** Rejected:
  erroring with usage (safe but less useful); reading stdin by default
  (a bare `leanr fmt` would hang on a TTY).
- **`--check` prints a unified diff for all inputs**, files and stdin
  alike. Rejected: name-only listing for files with a diff only for
  stdin (two behaviors to document and test); rejecting `--check -`
  outright (breaks editor and CI wrappers for no reason).
- **Two new dependencies, `leanr_cli` only:** `ignore` (the walker
  ripgrep uses) and `similar` (the diff library behind insta). See
  § Dependency justification.
- **Packaging:** one slice, one branch, one spec/plan cycle, single
  final whole-branch review — the M3b3/M3c pattern.

## Architecture

### 1. The unified permuted walk (`leanr_fmt::render`, `rules::imports`)

Delete the second rendering path. `imports::detect` stops returning
source offsets plus pre-rendered strings (`start`, `end`,
`sorted: Vec<String>`) and instead returns the import command **nodes**
together with their sorted order. The spine builds one token sequence
for the whole file — a permutation of `tokens_of(root)`:

- tokens before the first import's first significant token: unchanged,
  in place;
- then, in sorted order, each import's token run from its first through
  its last significant token — **interior whitespace included**, so
  intra-import spacing survives exactly as it does today — with a
  synthesized `"\n"` between consecutive imports;
- then tokens from the last import's end onward, unchanged.

That single sequence feeds `render_tokens`, so trivia, spacing, and every
future rule apply uniformly across the whole file.

Discarding the between-import whitespace is safe precisely because
`detect` already bails to preserve-fallback whenever a comment sits
anywhere in the import span (`has_interior_comment` +
`between_import_comment`). The only trivia dropped is whitespace, and it
is replaced by the one-import-per-line separator the rule already
mandates.

Two properties are preserved rather than changed:

- **Spacing lookups.** `render_tokens`'s `prev`/`next` significant-token
  scans now run over the emitted order rather than the source order.
  That is what they always meant; the permutation makes it true.
- **Idempotence.** After one pass the imports are already sorted, so the
  permutation is the identity on the second pass.

The sort key (`import_sort_key`, which skips the `all` modifier) and the
verbatim preservation of each import's own text (`public` modifiers, the
`import` keyword) are unchanged — those were corpus-driven fixes and
this slice must not regress them.

**The risk this opens, stated plainly:** head and tail content of
import-bearing files — `module`, `prelude`, docstrings, and every
declaration in every Mathlib file — passes through the rule engine for
the first time. The corpus gate's four invariants over the pass-list are
exactly the instrument for that, and this is the first slice where they
genuinely bite.

### 2. `fmt:mathlib` snapshot reuse (`leanr_fmt/tests/mathlib_corpus.rs`)

Group pass-list files by import set instead of building a snapshot per
file. Each file is keyed by its `parse_header_imports` result, sorted and
deduplicated; one snapshot is built per distinct key and reused for every
file in that group. Files with no imports share the single builtin
snapshot. The key derives from the same `parse_header_imports` call the
snapshot build already makes, so there is no second notion of "this
file's imports" that could drift from the one that resolves the closure.

This mirrors `leanr_grammar/tests/mathlib_sweep.rs`'s per-import-set
snapshot build, deliberately, rather than inventing a second way to
build snapshots for the same corpus.

Both existing failure-mode guards carry over unchanged:

- The `LEANR_OLEAN_PATH`-empty assert stays where it is, ahead of any
  grouping — an empty search path must fail loudly, never make the gate
  vacuously green.
- A present-but-unloadable file stays a hard failure, not a skip. A
  failed closure load is now recorded once **per file in the group**,
  not once per group, so a broken closure cannot silently shrink the
  checked count. The `checked > 0` assert keeps counting files, not
  groups. A file absent from disk remains upstream churn, skipped as
  today.

### 3. Shared despan core (`leanr_syntax::canon`, `leanr_fmt::verify`)

`canon_semantic` duplicates `canon_jsonl`'s node shape and its private
`json_str` escaping. Because that copy is only ever compared against
itself, drift can only false-negative — the gate quietly stops catching
corruption. Replace both with one parameterized renderer exported from
`leanr_syntax::canon`:

```rust
pub struct CanonOpts<'a> {
    pub spans: bool,                  // false = despanned
    pub sort_kind: Option<&'a str>,   // normalize sibling order for this node kind
}
pub fn canon_to_string(tree: &SyntaxTree, opts: CanonOpts) -> String;
```

- `canon_jsonl(tree)` becomes
  `canon_to_string(tree, CanonOpts { spans: true, sort_kind: None })` and
  **must stay byte-identical** — it is the oracle-comparison path, and
  the existing oracle fixtures prove it.
- `canon_semantic(tree)` becomes `canon_to_string(tree, CanonOpts {
  spans: false, sort_kind: Some("Lean.Parser.Module.import") })`.

`sort_kind` is phrased generically — normalize sibling order for a given
node kind — so no formatter concept leaks into the syntax crate.
`leanr_fmt` keeps its own tests proving the oracle still tolerates
exactly layout and import order while catching a corrupted literal or a
corrupted import name.

### 4. The `leanr fmt` CLI surface (`leanr_cli`)

- **Zero file arguments** means "format this project": walk the current
  directory recursively for `*.lean`, respecting `.gitignore`, via the
  `ignore` crate. Its defaults are the wanted behavior — hidden
  directories are skipped (so `.lake`, `.git`, and `.mathlib` are
  excluded regardless of any ignore file), symlinks are not followed,
  and nested `.gitignore` files compose. A walk that finds no `.lean`
  files exits 0; an empty project is not an error.
- **`--check` prints a unified diff** for every input that would change —
  file arguments and stdin alike — and exits 1. The diff header names the
  input: its path, or `<stdin>` for `-`. This replaces the current
  name-only listing for files and the current always-exit-0 silence for
  `--check -`. Diffs go to **stdout**; check mode writes nothing else to
  stdout — in particular `--check -` never emits the formatted text,
  which would otherwise be indistinguishable from the non-check output —
  and modifies no file.
- **Non-check stdin** (`leanr fmt -`) is unchanged: format, write to
  stdout.
- Existing exit-code semantics are otherwise unchanged: any read/parse/
  write error is a failure, and in check mode any would-change input is a
  failure.

Deliberately omitted: no `--recursive` flag and no directory arguments.
Bare `leanr fmt` walking the project is the whole behavior; accepting a
directory path is additive later if it is actually wanted.

## Dependency justification

Two dependencies, both confined to `leanr_cli`, so `leanr_fmt` and
everything below it stay dependency-free.

- **`ignore`** — gitignore semantics (nested ignore files, negation,
  precedence) are a specification someone else already implements
  correctly; a hand-rolled subset would be wrong in exactly the cases
  users notice.
- **`similar`** — unified diff hunk generation with context.

The `Doc` engine was hand-rolled deliberately, and that precedent does
not extend to these. Rejecting an external pretty-printer was about
owning the width and idempotence edge cases the acceptance invariants
are strict about. Neither of these feeds an invariant: one is an
external spec, the other is cosmetic output. Owning them would buy no
correctness control and cost two classic bug farms.

## Acceptance

All four M3c invariants are unchanged and keep gating: total,
idempotent, semantics-preserving (modulo layout + import order), and the
byte-identical ordered comment sequence. The change is what they now
cover — with the permuted walk, head and tail content of import-bearing
corpus files runs through the rule engine, so the pass-list sweep tests
the rules rather than only the splice.

New hermetic fixtures:

- **Permuted walk:** trivia and spacing rules take effect in the body of
  an import-bearing file (the case that silently did nothing before);
  imports still sort with `public` and `all` modifiers preserved
  verbatim; an interior or between-imports comment still routes to
  preserve-fallback with the block byte-identical; `prelude` and
  `module` headers stay on their own lines and re-parse clean;
  idempotence across all of the above.
- **Canon sharing:** `canon_jsonl` output is byte-identical to its
  pre-refactor form (existing oracle fixtures); `canon_semantic`
  tolerates layout and import reorder and catches a corrupted literal
  and a corrupted import name (existing tests, retargeted).
- **CLI** (`crates/leanr_cli/tests/fmt_cli.rs`, `assert_cmd` +
  `tempfile`): the walk finds nested files and skips both a gitignored
  directory and a dot-directory; `--check` on a would-change file exits
  1 with a diff naming the path; `--check -` on would-change input exits
  1 with a `<stdin>` diff on stdout and never the formatted text;
  `--check` on
  already-formatted input exits 0 silently; a walk finding zero `.lean`
  files exits 0.

Existing gates stay green: workspace tests, lint, `cargo deny`,
parse-acceptance, both fuzz targets, the never-hang storms, and
`mise run fmt:mathlib` — the last of which should now complete in a
fraction of its current ~10 minutes.

## Out of scope (and where it lands)

- **Indentation normalization + all multi-line construct rules** → the
  next M3 slice. Unchanged from M3c: indentation is meaningless without
  multi-line rules to act on, and it is the layout-sensitive danger zone.
- **Comment attachment/reflow** → later, behind the fallback and the
  comment invariant that already guards it.
- **Config / alternate line widths** → not unless demanded; one true
  style, fixed 100-column width.
- **Directory arguments / `--recursive`** → additive later if wanted.
- **salsa wiring** → M5.
