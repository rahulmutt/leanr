# M3c — `leanr fmt` thin-slice Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship the first Lean source formatter — `leanr fmt` / `leanr fmt --check` — as a thin vertical slice: a hand-rolled Wadler `Doc` engine, a preserve-fallback renderer, three inherently-safe style rules (trivia baseline, single-line operator spacing, import normalize+sort), and a self-consistency harness (total · idempotent · semantics-preserving · comment-invariant) over the parser pass-list corpus.

**Architecture:** New crate `leanr_fmt` consumes `leanr_syntax` lossless trees only and never re-lexes. `format_tree` walks the tree emitting an ordered token stream; the import block is restructured (sorted) and whitespace-trivia is normalized by rules, everything else is emitted verbatim (preserve-fallback). A final line-oriented trivia pass strips trailing whitespace, collapses blank runs, and fixes the final newline. Correctness is self-consistency, not differential (official Lean has no source formatter): output re-parses to a canonically-equal tree, `fmt` is idempotent, and comments survive byte-for-byte modulo trailing whitespace.

**Tech Stack:** Rust (edition 2021), `rowan` green/red trees via `leanr_syntax`, `clap` for the CLI, `mise` tasks, no new external dependencies.

## Global Constraints

- **No new external dependency** without justification (AGENTS.md); `leanr_fmt` depends only on `leanr_syntax` for its library code. Dev-dependencies for tests may add `leanr_grammar`/`leanr_olean` (corpus snapshot build) — these are workspace crates, not external.
- **`leanr_fmt` never re-lexes source** — it consumes `leanr_syntax` trees only (M3a spec, load-bearing boundary).
- **Target width fixed at 100 columns**, not configurable (Mathlib convention).
- **Tools are mise-pinned** (`mise use --pin`); workflows run via named mise tasks; CI runs `mise run ci`.
- **Semantics oracle is self-consistency**, not differential — there is no official Lean source formatter to diff against.
- **Comment invariant** — the ordered sequence of comment tokens in output equals input, byte-identical **modulo trailing whitespace** (each comment right-trimmed on both sides before comparison). A failure is release-blocking.
- **`leanr fmt` requires parseable input** — a file that does not parse clean is a loud error, never a partial format.
- **Every fixture round-trips** and hermetic fixtures use `builtin::snapshot()` only (no import closure) — mirror `crates/leanr_syntax/tests/oracle_golden.rs`.

## Relevant existing APIs (verified in-tree)

- `leanr_syntax::parse_module(src: &str, snap: &GrammarSnapshot) -> ParseResult`; `ParseResult { pub tree: SyntaxTree, pub errors: Vec<ParseError> }`.
- `leanr_syntax::SyntaxTree { pub green: GreenNode, pub kinds: Arc<KindInterner> }`, `tree.root() -> SyntaxNode`, `tree.text() -> String`.
- `leanr_syntax::tree::{SyntaxNode, SyntaxToken}` (rowan). Iterate leaves in source order: `node.descendants_with_tokens()` → `rowan::NodeOrToken<SyntaxNode, SyntaxToken>`; `token.kind() -> SyntaxKind`, `token.text() -> &str`, `token.text_range()` (`rowan::TextRange`, `.start()/.end()` are `TextSize`, `u32::from(..)`), `node.text_range()`.
- `leanr_syntax::kind::{SyntaxKind, KindInterner, is_trivia, KIND_WHITESPACE, KIND_LINE_COMMENT, KIND_BLOCK_COMMENT, KIND_IDENT, KIND_ATOM}`; `interner.name(k) -> &str`.
- `leanr_syntax::canon::canon_jsonl(tree: &SyntaxTree) -> String` — the trivia-excluded canonical form used for the semantics check.
- `leanr_syntax::builtin::snapshot() -> GrammarSnapshot` (owned); `leanr_syntax::parse_header_imports(src: &str) -> Vec<String>`.
- CLI snapshot build seam: `crates/leanr_cli/src/main.rs::parse_cmd` (import closure → `leanr_grammar::assemble(&loaded, &st).snapshot`).
- Pass-list corpus: `tests/fixtures/syntax/mathlib-passlist.txt` (one path per line, `#` comments); heavy-tier task pattern in `mise.toml` (`parse:mathlib:fast`) and `crates/leanr_grammar/tests/mathlib_sweep.rs`.

---

### Task 1: Crate skeleton + the Wadler `Doc` engine

**Files:**
- Create: `crates/leanr_fmt/Cargo.toml`
- Create: `crates/leanr_fmt/src/lib.rs` (module declarations only, this task)
- Create: `crates/leanr_fmt/src/doc.rs`
- Modify: `Cargo.toml` (workspace `members`)

**Interfaces:**
- Produces: `leanr_fmt::doc::Doc` enum and `leanr_fmt::doc::layout(doc: &Doc, width: usize) -> String`.
  - `Doc::text(s: impl Into<String>) -> Doc`, `Doc::line() -> Doc` (soft line: space when flat, newline when broken), `Doc::hardline() -> Doc` (always newline), `Doc::nest(indent: u16, d: Doc) -> Doc`, `Doc::group(d: Doc) -> Doc`, `Doc::concat(ds: Vec<Doc>) -> Doc`, `Doc::nil() -> Doc`.

- [ ] **Step 1: Create the crate manifest**

`crates/leanr_fmt/Cargo.toml`:
```toml
[package]
name = "leanr_fmt"
version.workspace = true
edition.workspace = true
license.workspace = true
repository.workspace = true

[dependencies]
leanr_syntax = { path = "../leanr_syntax" }

[dev-dependencies]
leanr_grammar = { path = "../leanr_grammar" }
leanr_olean = { path = "../leanr_olean" }
leanr_kernel = { path = "../leanr_kernel" }
```

- [ ] **Step 2: Register the crate in the workspace**

Modify `Cargo.toml` `members` to append `"crates/leanr_fmt"`:
```toml
members = ["crates/leanr_kernel", "crates/leanr_check", "crates/leanr_cli", "crates/leanr_query", "crates/leanr_syntax", "crates/leanr_olean", "crates/leanr_grammar", "crates/leanr_build", "crates/leanr_fmt"]
```

- [ ] **Step 3: Stub `lib.rs`**

`crates/leanr_fmt/src/lib.rs`:
```rust
//! The `leanr fmt` engine (M3c): a preserve-fallback source formatter
//! over `leanr_syntax` lossless trees. Consumes trees only; never
//! re-lexes source. See docs/superpowers/specs/2026-07-19-m3c-fmt-thin-slice-design.md.

pub mod doc;
```

- [ ] **Step 4: Write the failing test for `layout`**

`crates/leanr_fmt/src/doc.rs` (test module at the bottom):
```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flat_group_fits_uses_spaces() {
        let d = Doc::group(Doc::concat(vec![
            Doc::text("a"),
            Doc::line(),
            Doc::text("b"),
        ]));
        assert_eq!(layout(&d, 80), "a b");
    }

    #[test]
    fn broken_group_over_width_uses_newlines_and_nest() {
        let d = Doc::group(Doc::nest(
            2,
            Doc::concat(vec![
                Doc::text("aaaa"),
                Doc::line(),
                Doc::text("bbbb"),
            ]),
        ));
        // width 6 cannot fit "aaaa bbbb" (9), so the group breaks.
        assert_eq!(layout(&d, 6), "aaaa\n  bbbb");
    }

    #[test]
    fn hardline_always_breaks_even_when_it_would_fit() {
        let d = Doc::group(Doc::concat(vec![
            Doc::text("a"),
            Doc::hardline(),
            Doc::text("b"),
        ]));
        assert_eq!(layout(&d, 80), "a\nb");
    }
}
```

- [ ] **Step 5: Run test to verify it fails**

Run: `cargo test -p leanr_fmt --lib doc::tests`
Expected: FAIL — `Doc`/`layout` not defined.

- [ ] **Step 6: Implement `doc.rs`**

Prepend to `crates/leanr_fmt/src/doc.rs` (above the test module):
```rust
//! Hand-rolled Wadler/Leijen pretty-printer IR (spec §Engine). No
//! external dependency. `layout` chooses flat-vs-broken per `Group`
//! against the remaining width; `Line` is a space when flat and a
//! newline (+ current indent) when broken; `Hardline` always breaks.

#[derive(Clone, Debug)]
pub enum Doc {
    Nil,
    Text(String),
    Line,
    Hardline,
    Nest(u16, Box<Doc>),
    Group(Box<Doc>),
    Concat(Vec<Doc>),
}

impl Doc {
    pub fn nil() -> Doc {
        Doc::Nil
    }
    pub fn text(s: impl Into<String>) -> Doc {
        Doc::Text(s.into())
    }
    pub fn line() -> Doc {
        Doc::Line
    }
    pub fn hardline() -> Doc {
        Doc::Hardline
    }
    pub fn nest(indent: u16, d: Doc) -> Doc {
        Doc::Nest(indent, Box::new(d))
    }
    pub fn group(d: Doc) -> Doc {
        Doc::Group(Box::new(d))
    }
    pub fn concat(ds: Vec<Doc>) -> Doc {
        Doc::Concat(ds)
    }
}

// A `Hardline` anywhere in a group forces the group to break.
fn contains_hardline(d: &Doc) -> bool {
    match d {
        Doc::Hardline => true,
        Doc::Nil | Doc::Text(_) | Doc::Line => false,
        Doc::Nest(_, inner) | Doc::Group(inner) => contains_hardline(inner),
        Doc::Concat(ds) => ds.iter().any(contains_hardline),
    }
}

// Would `d` fit flat in `remaining` columns? `Line` counts as one space;
// `Hardline` makes it not fit (forces a break).
fn fits(d: &Doc, mut remaining: isize) -> bool {
    let mut stack = vec![d];
    while let Some(top) = stack.pop() {
        if remaining < 0 {
            return false;
        }
        match top {
            Doc::Nil => {}
            Doc::Text(s) => remaining -= s.chars().count() as isize,
            Doc::Line => remaining -= 1,
            Doc::Hardline => return false,
            Doc::Nest(_, inner) | Doc::Group(inner) => stack.push(inner),
            Doc::Concat(ds) => {
                for sub in ds.iter().rev() {
                    stack.push(sub);
                }
            }
        }
    }
    remaining >= 0
}

pub fn layout(doc: &Doc, width: usize) -> String {
    let mut out = String::new();
    let mut col: usize = 0;
    // (indent, flat?, doc)
    let mut stack: Vec<(u16, bool, &Doc)> = vec![(0, false, doc)];
    while let Some((indent, flat, top)) = stack.pop() {
        match top {
            Doc::Nil => {}
            Doc::Text(s) => {
                out.push_str(s);
                col += s.chars().count();
            }
            Doc::Line => {
                if flat {
                    out.push(' ');
                    col += 1;
                } else {
                    out.push('\n');
                    for _ in 0..indent {
                        out.push(' ');
                    }
                    col = indent as usize;
                }
            }
            Doc::Hardline => {
                out.push('\n');
                for _ in 0..indent {
                    out.push(' ');
                }
                col = indent as usize;
            }
            Doc::Nest(n, inner) => stack.push((indent + n, flat, inner)),
            Doc::Concat(ds) => {
                for sub in ds.iter().rev() {
                    stack.push((indent, flat, sub));
                }
            }
            Doc::Group(inner) => {
                let remaining = width as isize - col as isize;
                let flat_here = !contains_hardline(inner) && fits(inner, remaining);
                stack.push((indent, flat_here, inner));
            }
        }
    }
    out
}
```

- [ ] **Step 7: Run tests to verify they pass**

Run: `cargo test -p leanr_fmt --lib doc::tests`
Expected: PASS (3 tests).

- [ ] **Step 8: Commit**

```bash
git add crates/leanr_fmt/Cargo.toml crates/leanr_fmt/src/lib.rs crates/leanr_fmt/src/doc.rs Cargo.toml
git commit -m "feat(fmt): leanr_fmt crate skeleton + Wadler Doc engine"
```

---

### Task 2: `format_tree` spine — pure preserve-fallback + `format_src`

**Files:**
- Modify: `crates/leanr_fmt/src/lib.rs`
- Create: `crates/leanr_fmt/src/render.rs`

**Interfaces:**
- Consumes: `leanr_syntax::{parse_module, builtin, SyntaxTree}`, `Doc`/`layout` (Task 1).
- Produces:
  - `leanr_fmt::FormatError` (enum: `Unparseable(Vec<String>)`).
  - `leanr_fmt::format_tree(tree: &SyntaxTree) -> String` — total; at this task every node falls back to verbatim, so output == `tree.text()`.
  - `leanr_fmt::format_src(src: &str, snap: &leanr_syntax::grammar::GrammarSnapshot) -> Result<String, FormatError>` — parse then `format_tree`; `Err(Unparseable)` when the parse has errors.
  - `leanr_fmt::render::render_verbatim(tree: &SyntaxTree) -> Doc` — the fallback renderer (emits every token's text as `Doc::text`).

- [ ] **Step 1: Write the failing test**

`crates/leanr_fmt/src/render.rs` (test module):
```rust
#[cfg(test)]
mod tests {
    use leanr_syntax::{builtin, parse_module};

    #[test]
    fn all_fallback_round_trips_byte_exact() {
        let src = "namespace Foo\ndef  x :=   1\nend Foo\n";
        let snap = builtin::snapshot();
        let tree = parse_module(src, &snap).tree;
        // No rules wired yet: output is byte-identical to input.
        assert_eq!(crate::format_tree(&tree), src);
    }

    #[test]
    fn format_src_errors_on_unparseable_input() {
        let snap = builtin::snapshot();
        // A stray `)` with no matching command is a parse error.
        let err = crate::format_src(")", &snap).unwrap_err();
        matches!(err, crate::FormatError::Unparseable(_));
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p leanr_fmt --lib render::tests`
Expected: FAIL — `format_tree`/`format_src`/`FormatError` not defined.

- [ ] **Step 3: Implement the render spine**

`crates/leanr_fmt/src/render.rs` (above the test module):
```rust
//! The formatter spine (spec §Rule dispatch + preserve-fallback). Walks
//! the tree's leaf tokens in source order and emits a `Doc`. At this
//! layer every token is emitted verbatim (preserve-fallback); later
//! tasks intercept the import block and whitespace-trivia.

use leanr_syntax::tree::{SyntaxNode, SyntaxToken};
use leanr_syntax::SyntaxTree;
use rowan::NodeOrToken;

use crate::doc::Doc;

/// Every leaf token in source order, verbatim. Losslessness makes this a
/// byte-exact reproduction of the source.
pub fn render_verbatim(tree: &SyntaxTree) -> Doc {
    let mut parts = Vec::new();
    for el in tree.root().descendants_with_tokens() {
        if let NodeOrToken::Token(t) = el {
            parts.push(Doc::text(t.text().to_string()));
        }
    }
    Doc::concat(parts)
}

/// Leaf tokens of a subtree in source order (shared by later rules).
pub(crate) fn tokens_of(node: &SyntaxNode) -> Vec<SyntaxToken> {
    node.descendants_with_tokens()
        .filter_map(|el| match el {
            NodeOrToken::Token(t) => Some(t),
            NodeOrToken::Node(_) => None,
        })
        .collect()
}
```

`crates/leanr_fmt/src/lib.rs`:
```rust
//! The `leanr fmt` engine (M3c): a preserve-fallback source formatter
//! over `leanr_syntax` lossless trees. Consumes trees only; never
//! re-lexes source. See docs/superpowers/specs/2026-07-19-m3c-fmt-thin-slice-design.md.

pub mod doc;
pub mod render;

use leanr_syntax::grammar::GrammarSnapshot;
use leanr_syntax::{parse_module, SyntaxTree};

pub const WIDTH: usize = 100;

#[derive(Debug)]
pub enum FormatError {
    /// The input did not parse clean; fmt never formats a broken tree.
    Unparseable(Vec<String>),
}

/// Format a parsed tree. Total: never panics, never bails.
pub fn format_tree(tree: &SyntaxTree) -> String {
    let doc = render::render_verbatim(tree);
    doc::layout(&doc, WIDTH)
}

/// Parse then format. Enforces the "parseable input" precondition.
pub fn format_src(src: &str, snap: &GrammarSnapshot) -> Result<String, FormatError> {
    let result = parse_module(src, snap);
    if !result.errors.is_empty() {
        let msgs = result
            .errors
            .iter()
            .map(|e| leanr_syntax::parse::render_error(src, e))
            .collect();
        return Err(FormatError::Unparseable(msgs));
    }
    Ok(format_tree(&result.tree))
}
```

> NOTE: confirm `GrammarSnapshot` is exported at `leanr_syntax::grammar::GrammarSnapshot`. If it is re-exported elsewhere (e.g. `leanr_syntax::parse::GrammarSnapshot`), adjust the `use`. Check with: `grep -rn "pub use\|pub struct GrammarSnapshot\|pub type GrammarSnapshot" crates/leanr_syntax/src`.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p leanr_fmt --lib render::tests`
Expected: PASS (2 tests). If the `format_src` error test's input `)` happens to parse clean, replace with `"def"` (truncated declaration) — any input that yields a non-empty `errors` vec.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_fmt/src/lib.rs crates/leanr_fmt/src/render.rs
git commit -m "feat(fmt): format_tree/format_src spine with pure preserve-fallback"
```

---

### Task 3: Trivia baseline — the final whole-output normalization pass

**Files:**
- Create: `crates/leanr_fmt/src/trivia.rs`
- Modify: `crates/leanr_fmt/src/lib.rs` (declare module; call `trivia::normalize` in `format_tree`)

**Interfaces:**
- Consumes: nothing from other tasks (pure string→string).
- Produces: `leanr_fmt::trivia::normalize(s: &str) -> String` — strip trailing whitespace per line (including whitespace that falls inside a line comment, i.e. right-trim every line), collapse runs of 2+ blank lines to a single blank line, ensure the output ends in exactly one `\n` (empty input stays empty).

- [ ] **Step 1: Write the failing test**

`crates/leanr_fmt/src/trivia.rs` (test module):
```rust
#[cfg(test)]
mod tests {
    use super::normalize;

    #[test]
    fn strips_trailing_whitespace_including_after_line_comments() {
        assert_eq!(normalize("def x := 1   \n-- note   \n"), "def x := 1\n-- note\n");
    }

    #[test]
    fn collapses_blank_line_runs_to_one() {
        assert_eq!(normalize("a\n\n\n\nb\n"), "a\n\nb\n");
    }

    #[test]
    fn ensures_single_trailing_newline() {
        assert_eq!(normalize("a"), "a\n");
        assert_eq!(normalize("a\n\n\n"), "a\n");
        assert_eq!(normalize(""), "");
    }

    #[test]
    fn is_idempotent() {
        let messy = "a  \n\n\n\nb -- x  \n\n";
        let once = normalize(messy);
        assert_eq!(normalize(&once), once);
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p leanr_fmt --lib trivia::tests`
Expected: FAIL — `normalize` not defined.

- [ ] **Step 3: Implement `trivia.rs`**

```rust
//! Trivia baseline (spec §The first-slice rules, rule 1): a final,
//! line-oriented normalization applied uniformly to formatted AND
//! preserve-fallback output. Only mutates non-significant trivia, so it
//! is parse-safe by construction. Trailing-whitespace stripping also
//! trims trailing whitespace inside line comments (a Lean line comment
//! runs to end of line) — see the comment invariant in verify.rs.

pub fn normalize(s: &str) -> String {
    let mut lines: Vec<&str> = s.lines().map(str::trim_end).collect();
    // Collapse runs of 2+ blank lines to a single blank line.
    let mut collapsed: Vec<&str> = Vec::with_capacity(lines.len());
    let mut prev_blank = false;
    for line in lines.drain(..) {
        let blank = line.is_empty();
        if blank && prev_blank {
            continue;
        }
        collapsed.push(line);
        prev_blank = blank;
    }
    // Drop trailing blank lines.
    while collapsed.last() == Some(&"") {
        collapsed.pop();
    }
    if collapsed.is_empty() {
        return String::new();
    }
    let mut out = collapsed.join("\n");
    out.push('\n');
    out
}
```

- [ ] **Step 4: Wire into `format_tree`**

In `crates/leanr_fmt/src/lib.rs`, add `pub mod trivia;` and change `format_tree`:
```rust
pub fn format_tree(tree: &SyntaxTree) -> String {
    let doc = render::render_verbatim(tree);
    let laid_out = doc::layout(&doc, WIDTH);
    trivia::normalize(&laid_out)
}
```

- [ ] **Step 5: Update the Task 2 round-trip test expectation**

The all-fallback test in `render.rs` now normalizes trivia. Its input `"namespace Foo\ndef  x :=   1\nend Foo\n"` has no trailing ws / blank runs, so it is already a trivia-fixed-point and still equals the input — no change needed. Re-run to confirm:

Run: `cargo test -p leanr_fmt --lib`
Expected: PASS (all lib tests).

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_fmt/src/trivia.rs crates/leanr_fmt/src/lib.rs
git commit -m "feat(fmt): trivia baseline normalization pass"
```

---

### Task 4: Comments — interior detection + verify::comment_seq

**Files:**
- Create: `crates/leanr_fmt/src/comments.rs`
- Create: `crates/leanr_fmt/src/verify.rs` (partial — `comment_seq` only, this task)
- Modify: `crates/leanr_fmt/src/lib.rs` (declare modules)

**Interfaces:**
- Consumes: `leanr_syntax::kind::{is_trivia, KIND_LINE_COMMENT, KIND_BLOCK_COMMENT}`, `render::tokens_of` (Task 2), `SyntaxTree`.
- Produces:
  - `leanr_fmt::comments::has_interior_comment(node: &SyntaxNode) -> bool` — true if a comment token appears strictly between the node's first and last non-trivia leaf tokens.
  - `leanr_fmt::verify::comment_seq(tree: &SyntaxTree) -> Vec<String>` — every comment token's text, in source order, right-trimmed (`trim_end`).

- [ ] **Step 1: Write the failing tests**

`crates/leanr_fmt/src/comments.rs` (test module):
```rust
#[cfg(test)]
mod tests {
    use leanr_syntax::{builtin, parse_module};

    fn first_command(src: &str) -> leanr_syntax::tree::SyntaxNode {
        let snap = builtin::snapshot();
        let tree = parse_module(src, &snap).tree;
        // root children: header node, then command nodes.
        tree.root().children().nth(1).expect("a command")
    }

    #[test]
    fn detects_interior_comment() {
        let node = first_command("def x /- mid -/ := 1\n");
        assert!(super::has_interior_comment(&node));
    }

    #[test]
    fn boundary_comment_is_not_interior() {
        // Trailing comment after the last token is a boundary comment.
        let node = first_command("def x := 1 -- trailing\n");
        assert!(!super::has_interior_comment(&node));
    }
}
```

`crates/leanr_fmt/src/verify.rs` (test module):
```rust
#[cfg(test)]
mod tests {
    use leanr_syntax::{builtin, parse_module};

    #[test]
    fn comment_seq_is_ordered_and_right_trimmed() {
        let snap = builtin::snapshot();
        let src = "-- a   \ndef x := 1 /- b -/\n";
        let tree = parse_module(src, &snap).tree;
        assert_eq!(super::comment_seq(&tree), vec!["-- a", "/- b -/"]);
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_fmt --lib comments::tests verify::tests`
Expected: FAIL — functions not defined.

- [ ] **Step 3: Implement `comments.rs`**

```rust
//! Comment safety (spec §Comments). A node is only reformattable when
//! all its comments are boundary trivia; an interior comment routes it
//! to preserve-fallback. `has_interior_comment` is the guard the import
//! rule (and future construct rules) consult.

use leanr_syntax::kind::{is_trivia, SyntaxKind, KIND_BLOCK_COMMENT, KIND_LINE_COMMENT};
use leanr_syntax::tree::SyntaxNode;

use crate::render::tokens_of;

fn is_comment(k: SyntaxKind) -> bool {
    k == KIND_LINE_COMMENT || k == KIND_BLOCK_COMMENT
}

pub fn has_interior_comment(node: &SyntaxNode) -> bool {
    let toks = tokens_of(node);
    let first = toks.iter().position(|t| !is_trivia(t.kind()));
    let last = toks.iter().rposition(|t| !is_trivia(t.kind()));
    let (Some(first), Some(last)) = (first, last) else {
        return false; // no significant tokens: nothing to reformat around
    };
    toks[first..=last].iter().any(|t| is_comment(t.kind()))
}
```

- [ ] **Step 4: Implement `verify.rs` (comment_seq)**

```rust
//! Self-consistency checks (spec §Acceptance harness). Shared by the
//! hermetic fixture tests and the Mathlib corpus sweep.

use leanr_syntax::kind::{KIND_BLOCK_COMMENT, KIND_LINE_COMMENT};
use leanr_syntax::SyntaxTree;
use rowan::NodeOrToken;

/// Every comment token, in source order, right-trimmed. The comment
/// invariant compares this sequence modulo trailing whitespace.
pub fn comment_seq(tree: &SyntaxTree) -> Vec<String> {
    let mut out = Vec::new();
    for el in tree.root().descendants_with_tokens() {
        if let NodeOrToken::Token(t) = el {
            if t.kind() == KIND_LINE_COMMENT || t.kind() == KIND_BLOCK_COMMENT {
                out.push(t.text().trim_end().to_string());
            }
        }
    }
    out
}
```

- [ ] **Step 5: Declare modules**

In `crates/leanr_fmt/src/lib.rs` add:
```rust
pub mod comments;
pub mod verify;
```

- [ ] **Step 6: Run tests to verify they pass**

Run: `cargo test -p leanr_fmt --lib comments::tests verify::tests`
Expected: PASS (3 tests).

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_fmt/src/comments.rs crates/leanr_fmt/src/verify.rs crates/leanr_fmt/src/lib.rs
git commit -m "feat(fmt): interior-comment detection + comment_seq"
```

---

### Task 5: Import block normalize + sort

**Files:**
- Create: `crates/leanr_fmt/src/rules/mod.rs`
- Create: `crates/leanr_fmt/src/rules/imports.rs`
- Modify: `crates/leanr_fmt/src/render.rs` (splice the import block into the walk)
- Modify: `crates/leanr_fmt/src/lib.rs` (declare `rules`)

**Interfaces:**
- Consumes: `render::tokens_of`, `comments::has_interior_comment`, `SyntaxTree`, `Doc`, `parse_header_imports` semantics (import command shape).
- Produces:
  - `leanr_fmt::rules::imports::ImportBlock { start: usize, end: usize, sorted: Vec<String> }` and `leanr_fmt::rules::imports::detect(tree: &SyntaxTree) -> Option<ImportBlock>`.
    - `detect` returns `None` when: there are no import commands; OR the import span contains an interior comment (→ preserve the block verbatim, never reorder across a comment). `start`/`end` are byte offsets bounding the contiguous import commands (excluding leading/trailing trivia outside the block).
  - `render_verbatim` is extended: when an `ImportBlock` is present, emit `src[..start]` verbatim, the sorted imports (one `import <name>` per line, `\n`-joined), then the remaining tokens from `end` onward — so imports are the only reordered content.

- [ ] **Step 1: Write the failing test**

`crates/leanr_fmt/src/rules/imports.rs` (test module):
```rust
#[cfg(test)]
mod tests {
    use leanr_syntax::{builtin, parse_module};

    fn fmt(src: &str) -> String {
        let snap = builtin::snapshot();
        let tree = parse_module(src, &snap).tree;
        crate::format_tree(&tree)
    }

    #[test]
    fn sorts_and_one_per_line() {
        let src = "import Foo.B\nimport Foo.A\n\ndef x := 1\n";
        assert_eq!(fmt(src), "import Foo.A\nimport Foo.B\n\ndef x := 1\n");
    }

    #[test]
    fn preserves_block_when_interior_comment_present() {
        let src = "import Foo.B\n-- keep me here\nimport Foo.A\ndef x := 1\n";
        // Interior comment in the import span → verbatim (no reorder).
        assert_eq!(fmt(src), src);
    }

    #[test]
    fn no_imports_is_unchanged() {
        let src = "def x := 1\n";
        assert_eq!(fmt(src), src);
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p leanr_fmt --lib rules::imports::tests`
Expected: FAIL — `format_tree` still emits verbatim, so `sorts_and_one_per_line` fails.

- [ ] **Step 3: Implement `rules/imports.rs`**

```rust
//! Import normalize + sort (spec §The first-slice rules, rule 3). One
//! `import` per line, alphabetically sorted. Reordering is semantics-
//! neutral for Lean imports. Bails (returns None) if a comment sits
//! inside the import span, so comments are never reordered.

use leanr_syntax::tree::SyntaxNode;
use leanr_syntax::SyntaxTree;

use crate::comments::has_interior_comment;
use crate::render::tokens_of;

pub struct ImportBlock {
    pub start: usize,
    pub end: usize,
    pub sorted: Vec<String>,
}

/// An import command node is one whose kind name is Lean's module-import
/// command. Verify the exact interned kind name against an oracle dump
/// (`import Foo`): run `cargo run -p leanr_cli -- parse --dump <file>`
/// on a one-line `import Foo` and read the top command's `"k"`.
/// It is `Lean.Parser.Module.import`.
fn is_import_command(node: &SyntaxNode, tree: &SyntaxTree) -> bool {
    tree.kinds.name(node.kind()) == "Lean.Parser.Module.import"
}

/// The module name a single import command names, e.g. "Foo.Bar".
fn import_name(node: &SyntaxNode) -> String {
    // Significant (non-trivia) tokens after the `import` keyword joined
    // verbatim reproduce the dotted name (idents + `.` atoms).
    let mut name = String::new();
    let mut seen_kw = false;
    for t in tokens_of(node) {
        if leanr_syntax::kind::is_trivia(t.kind()) {
            continue;
        }
        if !seen_kw {
            seen_kw = true; // skip the `import` keyword atom
            continue;
        }
        name.push_str(t.text());
    }
    name
}

pub fn detect(tree: &SyntaxTree) -> Option<ImportBlock> {
    let root = tree.root();
    let imports: Vec<SyntaxNode> = root
        .children()
        .filter(|n| is_import_command(n, tree))
        .collect();
    if imports.is_empty() {
        return None;
    }
    let start = u32::from(imports.first().unwrap().text_range().start()) as usize;
    let end = u32::from(imports.last().unwrap().text_range().end()) as usize;
    // If any import command carries an interior comment, or a comment sits
    // between imports, preserve the block verbatim. `has_interior_comment`
    // covers within-command; a between-imports comment would be leading
    // trivia of the next import command's first token — detect by checking
    // each import node's own leading comment beyond the first.
    if imports.iter().any(|n| has_interior_comment(n)) || between_import_comment(&imports) {
        return None;
    }
    let mut sorted: Vec<String> = imports.iter().map(import_name).collect();
    sorted.sort();
    Some(ImportBlock { start, end, sorted })
}

// A comment attached as leading trivia to any import after the first
// lives inside the block span and must block reordering.
fn between_import_comment(imports: &[SyntaxNode]) -> bool {
    imports.iter().skip(1).any(|n| {
        tokens_of(n).iter().take_while(|t| leanr_syntax::kind::is_trivia(t.kind())).any(|t| {
            t.kind() == leanr_syntax::kind::KIND_LINE_COMMENT
                || t.kind() == leanr_syntax::kind::KIND_BLOCK_COMMENT
        })
    })
}
```

- [ ] **Step 4: Splice into the render walk**

Replace `render_verbatim` in `crates/leanr_fmt/src/render.rs` with an import-aware renderer (keep `tokens_of` as-is):
```rust
use crate::rules::imports;

pub fn render_verbatim(tree: &SyntaxTree) -> Doc {
    let src = tree.text();
    match imports::detect(tree) {
        Some(block) => {
            let mut parts = Vec::new();
            parts.push(Doc::text(src[..block.start].to_string()));
            let joined = block
                .sorted
                .iter()
                .map(|m| format!("import {m}"))
                .collect::<Vec<_>>()
                .join("\n");
            parts.push(Doc::text(joined));
            parts.push(Doc::text(src[block.end..].to_string()));
            Doc::concat(parts)
        }
        None => {
            let mut parts = Vec::new();
            for el in tree.root().descendants_with_tokens() {
                if let NodeOrToken::Token(t) = el {
                    parts.push(Doc::text(t.text().to_string()));
                }
            }
            Doc::concat(parts)
        }
    }
}
```

> The `src[block.end..]` tail begins at the end of the last import command — its leading newline/blank-line trivia is preserved and later normalized by `trivia::normalize`. The `sorts_and_one_per_line` expectation (`...B\n\ndef`) reflects that the blank line between imports and `def` survives as one blank line.

- [ ] **Step 5: Declare `rules`**

In `crates/leanr_fmt/src/lib.rs` add `pub mod rules;`. Create `crates/leanr_fmt/src/rules/mod.rs`:
```rust
//! Style rules (spec §Rule dispatch). Each rule either restructures a
//! node (imports) or is applied by the renderer (spacing); everything
//! without a rule is preserve-fallback.

pub mod imports;
```

- [ ] **Step 6: Verify the import kind name**

Run: `printf 'import Foo\n' > /tmp/imp.lean && cargo run -q -p leanr_cli -- parse --dump /tmp/imp.lean`
Expected: a JSON line whose `"k"` is `Lean.Parser.Module.import`. If the name differs, update `is_import_command`'s string literal to match, then re-run tests.

- [ ] **Step 7: Run tests to verify they pass**

Run: `cargo test -p leanr_fmt --lib rules::imports::tests`
Expected: PASS (3 tests).

- [ ] **Step 8: Commit**

```bash
git add crates/leanr_fmt/src/rules crates/leanr_fmt/src/render.rs crates/leanr_fmt/src/lib.rs
git commit -m "feat(fmt): import block normalize + sort rule"
```

---

### Task 6: Single-line operator spacing

**Files:**
- Create: `crates/leanr_fmt/src/rules/spacing.rs`
- Modify: `crates/leanr_fmt/src/render.rs` (apply spacing to whitespace-trivia in the fallback walk)
- Modify: `crates/leanr_fmt/src/rules/mod.rs` (declare `spacing`)

**Interfaces:**
- Consumes: `leanr_syntax::kind::{KIND_WHITESPACE, is_trivia}`, token stream from `render`.
- Produces: `leanr_fmt::rules::spacing::normalize_ws(prev_significant: Option<&str>, ws_text: &str, next_significant: Option<&str>) -> Option<String>` — given a whitespace-trivia token's text and the atom texts of the nearest significant tokens on either side, return `Some(normalized)` when the spacing rule applies, else `None` (keep verbatim). Rule: applies only when `ws_text` contains no `\n` (single-line) AND one neighbor is a target operator (`:=` or `→`); the normalized form is a single space.

- [ ] **Step 1: Write the failing test**

`crates/leanr_fmt/src/rules/spacing.rs` (test module):
```rust
#[cfg(test)]
mod tests {
    use super::normalize_ws;

    #[test]
    fn collapses_multiple_spaces_around_assign() {
        assert_eq!(normalize_ws(Some("x"), "   ", Some(":=")).as_deref(), Some(" "));
        assert_eq!(normalize_ws(Some(":="), "   ", Some("1")).as_deref(), Some(" "));
    }

    #[test]
    fn leaves_multiline_whitespace_untouched() {
        assert_eq!(normalize_ws(Some("x"), "\n  ", Some(":=")), None);
    }

    #[test]
    fn ignores_non_target_neighbors() {
        assert_eq!(normalize_ws(Some("a"), "  ", Some("b")), None);
    }
}
```

Add an end-to-end test in `render.rs`'s test module:
```rust
    #[test]
    fn single_line_assign_spacing_normalized() {
        let src = "def x :=   1\n";
        let snap = leanr_syntax::builtin::snapshot();
        let tree = leanr_syntax::parse_module(src, &snap).tree;
        assert_eq!(crate::format_tree(&tree), "def x := 1\n");
    }
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p leanr_fmt --lib rules::spacing::tests render::tests`
Expected: FAIL — `normalize_ws` not defined; the end-to-end spacing test fails.

- [ ] **Step 3: Implement `rules/spacing.rs`**

```rust
//! Single-line operator spacing (spec §The first-slice rules, rule 2).
//! Normalizes whitespace-trivia adjacent to target operators to a single
//! space, but ONLY on a single line — the moment the whitespace spans
//! lines (indentation may be significant), it is left verbatim.

const TARGET_OPERATORS: &[&str] = &[":=", "→"];

fn is_target(tok: Option<&str>) -> bool {
    matches!(tok, Some(t) if TARGET_OPERATORS.contains(&t))
}

pub fn normalize_ws(
    prev_significant: Option<&str>,
    ws_text: &str,
    next_significant: Option<&str>,
) -> Option<String> {
    if ws_text.contains('\n') {
        return None; // multi-line: leave verbatim (layout-sensitive)
    }
    if is_target(prev_significant) || is_target(next_significant) {
        Some(" ".to_string())
    } else {
        None
    }
}
```

- [ ] **Step 4: Apply spacing in the fallback walk**

In `render.rs`, replace the `None => { ... }` verbatim arm of `render_verbatim` with a walk that tracks the previous significant token and normalizes whitespace trivia. Extract a helper so both the no-imports case and the import tail could reuse it later:
```rust
fn render_tokens_with_spacing(tree: &SyntaxTree) -> Doc {
    use leanr_syntax::kind::is_trivia;
    let toks: Vec<SyntaxToken> = tokens_of(&tree.root());
    let mut parts = Vec::with_capacity(toks.len());
    for (i, t) in toks.iter().enumerate() {
        if t.kind() == leanr_syntax::kind::KIND_WHITESPACE {
            let prev = toks[..i].iter().rev().find(|p| !is_trivia(p.kind())).map(|p| p.text());
            let next = toks[i + 1..].iter().find(|p| !is_trivia(p.kind())).map(|p| p.text());
            match crate::rules::spacing::normalize_ws(prev, t.text(), next) {
                Some(s) => parts.push(Doc::text(s)),
                None => parts.push(Doc::text(t.text().to_string())),
            }
        } else {
            parts.push(Doc::text(t.text().to_string()));
        }
    }
    Doc::concat(parts)
}
```
and call `render_tokens_with_spacing(tree)` in the `None` arm. (`tokens_of` takes `&SyntaxNode`; pass `&tree.root()`.)

> The import-present arm keeps emitting `src[..start]` / imports / `src[block.end..]` verbatim; the tail's spacing is a known thin-slice gap — imports precede all operators, so the tail spacing loss only affects files WITH imports. Record this in the spec's "Out of scope" fast-follow if it matters after the corpus run (it is caught as under-formatting, never a correctness break).

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p leanr_fmt --lib`
Expected: PASS (all lib tests).

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_fmt/src/rules/spacing.rs crates/leanr_fmt/src/rules/mod.rs crates/leanr_fmt/src/render.rs
git commit -m "feat(fmt): single-line operator spacing rule"
```

---

### Task 7: The four-invariant checker + hermetic fixture golden harness

**Files:**
- Modify: `crates/leanr_fmt/src/verify.rs` (add `check_invariants`)
- Create: `crates/leanr_fmt/tests/fixtures_golden.rs`
- Create: `crates/leanr_fmt/tests/fixtures/` fixtures (`*.lean` input + `*.expected` output)

**Interfaces:**
- Consumes: `format_tree`, `format_src`, `comment_seq`, `parse_module`, `canon_jsonl`.
- Produces: `leanr_fmt::verify::check_invariants(src: &str, snap: &GrammarSnapshot) -> Result<(), String>` — runs all four invariants and returns `Err(description)` on the first failure:
  1. **Total** — `format_src` returns `Ok` (else the file was unparseable; caller filters those out of the corpus).
  2. **Idempotent** — `format_tree(parse(fmt(x))) == fmt(x)`.
  3. **Semantics** — `canon_jsonl(parse(fmt(x))) == canon_jsonl(parse(x))`.
  4. **Comment invariant** — `comment_seq(parse(fmt(x))) == comment_seq(parse(x))`.

- [ ] **Step 1: Write the failing test (fixture harness)**

`crates/leanr_fmt/tests/fixtures_golden.rs`:
```rust
//! Hermetic fixture gate (mirrors leanr_syntax/tests/oracle_golden.rs).
//! Each `<name>.lean` parses with the builtin snapshot; its formatted
//! output must equal the committed `<name>.expected`, and all four
//! self-consistency invariants must hold.

use leanr_syntax::builtin;

fn fixture_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

#[test]
fn fixtures_format_to_expected_and_hold_invariants() {
    let snap = builtin::snapshot();
    let mut checked = 0;
    for entry in std::fs::read_dir(fixture_dir()).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("lean") {
            continue;
        }
        let src = std::fs::read_to_string(&path).unwrap();
        let got = leanr_fmt::format_src(&src, &snap)
            .unwrap_or_else(|e| panic!("{path:?}: unparseable fixture: {e:?}"));
        let expected = std::fs::read_to_string(path.with_extension("expected")).unwrap();
        assert_eq!(got, expected, "format mismatch: {path:?}");
        leanr_fmt::verify::check_invariants(&src, &snap)
            .unwrap_or_else(|e| panic!("{path:?}: invariant failed: {e}"));
        checked += 1;
    }
    assert!(checked > 0, "no fixtures found — harness wiring broken");
}
```

- [ ] **Step 2: Create the fixtures**

`crates/leanr_fmt/tests/fixtures/Imports.lean`:
```
import Foo.B
import Foo.A

def x := 1
```
`crates/leanr_fmt/tests/fixtures/Imports.expected`:
```
import Foo.A
import Foo.B

def x := 1
```

`crates/leanr_fmt/tests/fixtures/Spacing.lean` (note trailing spaces after `:=`):
```
def a :=   1
def b := 2
```
`crates/leanr_fmt/tests/fixtures/Spacing.expected`:
```
def a := 1
def b := 2
```

`crates/leanr_fmt/tests/fixtures/CommentBoundary.lean`:
```
import Foo.B
-- keep this comment and order
import Foo.A
```
`crates/leanr_fmt/tests/fixtures/CommentBoundary.expected` (interior comment → block preserved verbatim, trivia baseline still applies):
```
import Foo.B
-- keep this comment and order
import Foo.A
```

> Author `.expected` by running the formatter once the checker exists (Step 4), then eyeballing — do NOT invent bytes. The values above are the intended results; confirm them against actual output.

- [ ] **Step 3: Run test to verify it fails**

Run: `cargo test -p leanr_fmt --test fixtures_golden`
Expected: FAIL — `verify::check_invariants` not defined.

- [ ] **Step 4: Implement `check_invariants`**

Append to `crates/leanr_fmt/src/verify.rs`:
```rust
use leanr_syntax::canon::canon_jsonl;
use leanr_syntax::grammar::GrammarSnapshot;
use leanr_syntax::parse_module;

use crate::{format_src, format_tree};

pub fn check_invariants(src: &str, snap: &GrammarSnapshot) -> Result<(), String> {
    // 1. Total.
    let once = format_src(src, snap).map_err(|e| format!("not total: {e:?}"))?;

    // Re-parse the formatted output once; reused by 2–4.
    let after = parse_module(&once, snap);
    if !after.errors.is_empty() {
        return Err("formatted output does not re-parse clean".to_string());
    }

    // 2. Idempotent.
    let twice = format_tree(&after.tree);
    if twice != once {
        return Err("not idempotent: fmt(fmt(x)) != fmt(x)".to_string());
    }

    // 3. Semantics-preserving.
    let before = parse_module(src, snap);
    if canon_jsonl(&after.tree) != canon_jsonl(&before.tree) {
        return Err("semantics changed: canonical tree differs".to_string());
    }

    // 4. Comment invariant (ordered, modulo trailing whitespace).
    if comment_seq(&after.tree) != comment_seq(&before.tree) {
        return Err("comment invariant violated".to_string());
    }
    Ok(())
}
```

- [ ] **Step 5: Reconcile `.expected` files with real output**

Run: `cargo test -p leanr_fmt --test fixtures_golden -- --nocapture`
If a `format mismatch` panic shows the actual bytes differ from the `.expected` you wrote, inspect via `cargo run -p leanr_cli -- fmt -` (available after Task 8) or a scratch test printing `format_src` output, confirm the difference is intended, and correct the `.expected` file. Re-run until green.

- [ ] **Step 6: Run test to verify it passes**

Run: `cargo test -p leanr_fmt --test fixtures_golden`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_fmt/src/verify.rs crates/leanr_fmt/tests/fixtures_golden.rs crates/leanr_fmt/tests/fixtures
git commit -m "feat(fmt): four-invariant checker + hermetic fixture golden harness"
```

---

### Task 8: CLI — `leanr fmt` and `leanr fmt --check` + shared snapshot loader

**Files:**
- Modify: `crates/leanr_cli/src/main.rs` (add `Fmt` variant + `fmt_cmd`; extract `SnapshotHolder`/`load_snapshot` shared by `parse_cmd` and `fmt_cmd`)
- Modify: `crates/leanr_cli/Cargo.toml` (add `leanr_fmt` dependency)
- Create: `crates/leanr_cli/tests/fmt_cli.rs`

**Interfaces:**
- Consumes: `leanr_fmt::{format_src, FormatError}`, the existing snapshot-build seam in `parse_cmd`.
- Produces: `leanr fmt [--check] [--path <olean>]... <files...>`:
  - default: format each file and rewrite it in place; stdin (`-`) formats to stdout.
  - `--check`: write nothing; exit non-zero and list files that would change (one per line to stderr).
  - unparseable / unreadable / non-UTF-8 file: loud error to stderr, non-zero exit; never a partial write.

- [ ] **Step 1: Extract the shared snapshot loader**

In `crates/leanr_cli/src/main.rs`, add above `parse_cmd`:
```rust
/// Owns whatever backs a grammar snapshot so callers can borrow it.
enum SnapshotHolder {
    Assembled(leanr_grammar::Assembled),
    Builtin(leanr_syntax::grammar::GrammarSnapshot),
}

impl SnapshotHolder {
    fn snapshot(&self) -> &leanr_syntax::grammar::GrammarSnapshot {
        match self {
            SnapshotHolder::Assembled(a) => &a.snapshot,
            SnapshotHolder::Builtin(s) => s,
        }
    }
}

/// Build the grammar snapshot for `src` from its import closure (or the
/// builtin snapshot when there are no imports / no roots). Mirrors the
/// logic previously inline in `parse_cmd`.
fn load_snapshot(src: &str, path: Vec<PathBuf>, verbose: bool) -> Result<SnapshotHolder, String> {
    let imports = leanr_syntax::parse_header_imports(src);
    if imports.is_empty() {
        return Ok(SnapshotHolder::Builtin(leanr_syntax::builtin::snapshot()));
    }
    let roots = discover_roots(path);
    if roots.is_empty() {
        return Ok(SnapshotHolder::Builtin(leanr_syntax::builtin::snapshot()));
    }
    let sp = SearchPath::new(roots);
    let targets: Vec<_> = imports.iter().map(|m| parse_module_name(m)).collect();
    let mut st = leanr_kernel::bank::Store::persistent();
    let loaded = leanr_olean::load_closure(&sp, &targets, &mut st)
        .map_err(|e| format!("error[E0306]: cannot load imports: {e}"))?;
    let assembled = leanr_grammar::assemble(&loaded, &st);
    if verbose {
        for s in &assembled.skipped {
            eprintln!("skipped parser entry {} ({:?})", s.decl, s.reason);
        }
    }
    Ok(SnapshotHolder::Assembled(assembled))
}
```

Then refactor `parse_cmd`'s snapshot block to use it:
```rust
    let holder = match load_snapshot(&src, path, verbose) {
        Ok(h) => h,
        Err(msg) => {
            eprintln!("{msg}");
            return ExitCode::FAILURE;
        }
    };
    let snap = holder.snapshot();
    let result = leanr_syntax::parse_module(&src, snap);
```
(Delete the old inline `imports`/`assembled`/`builtin` snapshot dance in `parse_cmd`.)

> Confirm the assembled type name: `grep -n "pub struct Assembled\|pub fn assemble" crates/leanr_grammar/src/*.rs`. If it is not `leanr_grammar::Assembled`, adjust the enum variant type and `.snapshot` field access accordingly.

- [ ] **Step 2: Add the `Fmt` subcommand and `leanr_fmt` dep**

`crates/leanr_cli/Cargo.toml` — add under `[dependencies]`:
```toml
leanr_fmt = { path = "../leanr_fmt" }
```

In `main.rs`, add to the `Command` enum:
```rust
    /// Format Lean source files (leanr fmt).
    Fmt {
        /// Files to format; `-` reads stdin and writes stdout.
        files: Vec<PathBuf>,
        /// Check mode: write nothing, exit non-zero if any file would change.
        #[arg(long)]
        check: bool,
        /// Root(s) to resolve the import closure for the grammar snapshot.
        #[arg(long)]
        path: Vec<PathBuf>,
    },
```
and to the `match cli.command` in `main`:
```rust
        Command::Fmt { files, check, path } => fmt_cmd(files, check, path),
```

- [ ] **Step 3: Write the failing CLI test**

`crates/leanr_cli/tests/fmt_cli.rs`:
```rust
use std::process::Command;

fn leanr() -> Command {
    Command::new(env!("CARGO_BIN_EXE_leanr"))
}

#[test]
fn fmt_check_flags_unformatted_file() {
    let dir = tempfile::tempdir().unwrap();
    let f = dir.path().join("A.lean");
    std::fs::write(&f, "import Foo.B\nimport Foo.A\n").unwrap();
    let out = leanr().arg("fmt").arg("--check").arg(&f).output().unwrap();
    assert!(!out.status.success(), "check should fail on unformatted file");
}

#[test]
fn fmt_rewrites_in_place() {
    let dir = tempfile::tempdir().unwrap();
    let f = dir.path().join("A.lean");
    std::fs::write(&f, "import Foo.B\nimport Foo.A\n").unwrap();
    let out = leanr().arg("fmt").arg(&f).output().unwrap();
    assert!(out.status.success());
    assert_eq!(
        std::fs::read_to_string(&f).unwrap(),
        "import Foo.A\nimport Foo.B\n"
    );
}
```

> If `tempfile` is not already a `dev-dependency` of `leanr_cli`, add it pinned: check `crates/leanr_cli/Cargo.toml` and other crates' dev-deps first; reuse the workspace's existing version. If absent anywhere, `mise` note: prefer an existing test tempdir helper used by `build_cli.rs` — inspect `crates/leanr_cli/tests/build_cli.rs` and match its approach rather than adding a dependency.

- [ ] **Step 4: Implement `fmt_cmd`**

In `main.rs`:
```rust
fn fmt_cmd(files: Vec<PathBuf>, check: bool, path: Vec<PathBuf>) -> ExitCode {
    let mut any_would_change = false;
    let mut had_error = false;
    for file in &files {
        let is_stdin = file.as_os_str() == "-";
        let src = if is_stdin {
            let mut s = String::new();
            use std::io::Read;
            if std::io::stdin().read_to_string(&mut s).is_err() {
                eprintln!("error: stdin is not valid UTF-8");
                had_error = true;
                continue;
            }
            s
        } else {
            match std::fs::read(file) {
                Ok(b) => match String::from_utf8(b) {
                    Ok(s) => s,
                    Err(_) => {
                        eprintln!("{}: error[E0305]: file is not valid UTF-8", file.display());
                        had_error = true;
                        continue;
                    }
                },
                Err(e) => {
                    eprintln!("error: cannot read {}: {e}", file.display());
                    had_error = true;
                    continue;
                }
            }
        };
        let holder = match load_snapshot(&src, path.clone(), false) {
            Ok(h) => h,
            Err(msg) => {
                eprintln!("{}: {msg}", file.display());
                had_error = true;
                continue;
            }
        };
        let formatted = match leanr_fmt::format_src(&src, holder.snapshot()) {
            Ok(s) => s,
            Err(leanr_fmt::FormatError::Unparseable(msgs)) => {
                eprintln!("{}: error: cannot format unparseable file:", file.display());
                for m in msgs {
                    eprintln!("  {m}");
                }
                had_error = true;
                continue;
            }
        };
        if is_stdin {
            print!("{formatted}");
            continue;
        }
        if formatted != src {
            any_would_change = true;
            if check {
                eprintln!("{}", file.display());
            } else if let Err(e) = std::fs::write(file, &formatted) {
                eprintln!("error: cannot write {}: {e}", file.display());
                had_error = true;
            }
        }
    }
    if had_error || (check && any_would_change) {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p leanr_cli --test fmt_cli && cargo test -p leanr_cli --test build_cli`
Expected: PASS (new fmt tests + existing CLI tests still green after the `parse_cmd` refactor).

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_cli/src/main.rs crates/leanr_cli/Cargo.toml crates/leanr_cli/tests/fmt_cli.rs
git commit -m "feat(cli): leanr fmt + --check; share snapshot loader with parse"
```

---

### Task 9: Mathlib corpus gate (mise task + sweep test) + docs

**Files:**
- Create: `crates/leanr_fmt/tests/mathlib_corpus.rs`
- Modify: `mise.toml` (add `fmt:mathlib` task)
- Modify: `ARCHITECTURE.md` (crate list: add `leanr_fmt`), `AGENTS.md` (workflows note)

**Interfaces:**
- Consumes: `leanr_fmt::verify::check_invariants`, the pass-list `tests/fixtures/syntax/mathlib-passlist.txt`, per-file snapshot build (same seam as `crates/leanr_grammar/tests/mathlib_sweep.rs`).
- Produces: `mise run fmt:mathlib` — a fast pass-list gate (NOT the ~35h discovery sweep) asserting all four invariants on every green file.

- [ ] **Step 1: Write the corpus test**

`crates/leanr_fmt/tests/mathlib_corpus.rs`:
```rust
//! The fmt self-consistency gate over the parser pass-list (spec
//! §Acceptance harness). Only runs when the Mathlib checkout is present
//! (env LEANR_FMT_CORPUS=1, set by `mise run fmt:mathlib`); otherwise it
//! is a no-op so `cargo test` in a bare checkout stays green. Mirrors the
//! per-file snapshot build in leanr_grammar/tests/mathlib_sweep.rs.

use std::path::{Path, PathBuf};

fn passlist_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/syntax/mathlib-passlist.txt")
}

fn mathlib_root() -> PathBuf {
    // The pass-list paths are relative to the Mathlib checkout root.
    // Reuse the same location leanr_grammar's sweep uses.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.mathlib")
}

#[test]
fn fmt_holds_all_invariants_over_passlist() {
    if std::env::var("LEANR_FMT_CORPUS").as_deref() != Ok("1") {
        eprintln!("skipping fmt corpus gate (set LEANR_FMT_CORPUS=1 via `mise run fmt:mathlib`)");
        return;
    }
    let list = std::fs::read_to_string(passlist_path()).unwrap();
    let root = mathlib_root();
    let mut checked = 0;
    let mut failures = Vec::new();
    for rel in list.lines() {
        let rel = rel.trim();
        if rel.is_empty() || rel.starts_with('#') {
            continue;
        }
        let file = root.join(rel);
        let src = match std::fs::read_to_string(&file) {
            Ok(s) => s,
            Err(_) => continue, // upstream churn: absent file, not a fmt regression
        };
        // Build the grammar snapshot for this file's import closure.
        // Reuse the sweep's helper; see mathlib_sweep.rs::snapshot_for.
        let snap = match support::snapshot_for(&src, &root) {
            Some(s) => s,
            None => continue, // imports unavailable: not formattable here
        };
        if let Err(e) = leanr_fmt::verify::check_invariants(&src, snap.snapshot()) {
            failures.push(format!("{rel}: {e}"));
        }
        checked += 1;
    }
    assert!(checked > 0, "corpus empty — pass-list or checkout wiring broken");
    assert!(failures.is_empty(), "fmt invariants failed:\n{}", failures.join("\n"));
}

mod support {
    //! Snapshot build for a source file's import closure. Port the exact
    //! logic from crates/leanr_grammar/tests/mathlib_sweep.rs (search
    //! path, load_closure, assemble) — do NOT invent a new one; keep the
    //! two in sync. Return a holder that owns the assembled snapshot.
    pub struct Holder(/* leanr_grammar::Assembled or builtin */);
    impl Holder {
        pub fn snapshot(&self) -> &leanr_syntax::grammar::GrammarSnapshot {
            unimplemented!("port from mathlib_sweep.rs snapshot build")
        }
    }
    pub fn snapshot_for(_src: &str, _root: &std::path::Path) -> Option<Holder> {
        unimplemented!("port from mathlib_sweep.rs snapshot build")
    }
}
```

> IMPLEMENTATION NOTE (not a placeholder in the shipped code): before writing `support`, open `crates/leanr_grammar/tests/mathlib_sweep.rs` and copy its snapshot-build path verbatim (search-path roots, `leanr_olean::load_closure`, `leanr_grammar::assemble`). The `unimplemented!()` bodies MUST be replaced with that ported code in this step — they exist here only to name the seam. Confirm the `.mathlib` root and pass-list-relative path convention against how `mathlib_sweep.rs` joins them; match it exactly.

- [ ] **Step 2: Add the mise task**

In `mise.toml`, add (namespaced so it does not collide with the existing rustfmt `[tasks.fmt]`):
```toml
[tasks."fmt:mathlib"]
description = "M3c fmt self-consistency gate over the parser pass-list (needs mathlib:fetch). FAST pass-list tier — NOT the ~35h discovery sweep. Asserts total + idempotent + semantics-preserving + comment-invariant on every green file."
env = { LEANR_FMT_CORPUS = "1" }
run = "cargo test -p leanr_fmt --test mathlib_corpus -- --nocapture"
```

- [ ] **Step 3: Run the corpus gate locally (if the checkout is present)**

Run: `mise run fmt:mathlib`
Expected: PASS with `checked > 0`. If `.mathlib` is absent, run `mise run mathlib:fetch` first (per AGENTS.md). In a bare checkout without the corpus, `cargo test -p leanr_fmt` still passes (the gate no-ops without `LEANR_FMT_CORPUS=1`).

- [ ] **Step 4: Update docs**

In `ARCHITECTURE.md`, add a `leanr_fmt` bullet to the "Crates (current)" list:
```
- `crates/leanr_fmt` — the `leanr fmt` engine (M3c): a preserve-fallback
  source formatter over `leanr_syntax` lossless trees (hand-rolled
  Wadler `Doc`). Consumes trees only, never re-lexes. Thin first slice:
  trivia baseline, single-line operator spacing, import normalize+sort;
  everything else preserves the author's layout verbatim. Correctness is
  self-consistency — total, idempotent, semantics-preserving (canonical
  tree unchanged), comments byte-identical modulo trailing whitespace —
  gated over the parser pass-list by `mise run fmt:mathlib`. Spec:
  docs/superpowers/specs/2026-07-19-m3c-fmt-thin-slice-design.md.
```
In `AGENTS.md`, under the workflows bullets, add one line:
```
- `leanr fmt` self-consistency is gated by `mise run fmt:mathlib` (fast
  pass-list tier, not the nightly discovery sweep).
```

- [ ] **Step 5: Full CI gate**

Run: `mise run ci`
Expected: PASS (workspace tests incl. new `leanr_fmt`, lint, deps). Fix any `clippy`/`fmt` (rustfmt) findings the new crate introduces.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_fmt/tests/mathlib_corpus.rs mise.toml ARCHITECTURE.md AGENTS.md
git commit -m "test(fmt): pass-list self-consistency gate (fmt:mathlib) + docs"
```

---

## Self-Review

**1. Spec coverage:**
- Crate `leanr_fmt`, trees-only, no external dep → Task 1, 2. ✓
- Hand-rolled Wadler Doc engine → Task 1. ✓
- Per-node preserve-fallback spine → Task 2 (verbatim), extended by rules. ✓
- Trivia baseline as a whole-output pass (incl. line-comment trailing-ws, modulo-ws comment invariant) → Task 3, 4. ✓
- Single-line token spacing, bail on multiline → Task 6. ✓
- Import normalize+sort, bail on interior comment → Task 5. ✓
- Interior-comment → fallback; ordered comment invariant modulo trailing ws → Task 4, 7. ✓
- Four acceptance invariants (total/idempotent/semantics/comment) → Task 7 (`check_invariants`), Task 9 (corpus). ✓
- Hermetic probe fixtures → Task 7. ✓
- `leanr fmt` / `--check`, parseable-input precondition (loud error) → Task 8. ✓
- Fast pass-list corpus gate, not the ~35h sweep → Task 9. ✓
- Out-of-scope items (indentation, reflow, config, salsa) → not implemented; the import-tail spacing gap is recorded in Task 6. ✓

**2. Placeholder scan:** The only `unimplemented!()` bodies are in Task 9's `support` module, explicitly flagged to be replaced by ported `mathlib_sweep.rs` code in the same step (a named seam, not shipped code). All other steps carry complete code. Kind-name and type-name lookups (`Lean.Parser.Module.import`, `leanr_grammar::Assembled`, `GrammarSnapshot` path) have explicit verification commands rather than assumptions.

**3. Type consistency:** `format_tree(&SyntaxTree) -> String`, `format_src(&str, &GrammarSnapshot) -> Result<String, FormatError>`, `verify::comment_seq(&SyntaxTree) -> Vec<String>`, `verify::check_invariants(&str, &GrammarSnapshot) -> Result<(), String>`, `comments::has_interior_comment(&SyntaxNode) -> bool`, `rules::imports::{ImportBlock, detect}`, `rules::spacing::normalize_ws(Option<&str>, &str, Option<&str>) -> Option<String>`, `SnapshotHolder::snapshot(&self) -> &GrammarSnapshot` — names and signatures are consistent across Tasks 2–9.
