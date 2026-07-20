# M3c Fast-Follows Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `leanr fmt` apply its style rules uniformly to import-bearing files, make the `fmt:mathlib` gate fast, remove the semantics oracle's duplication, and give the `leanr fmt` CLI a defined surface.

**Architecture:** The formatter spine's two rendering paths collapse into one — `imports::detect` returns token-index runs instead of pre-rendered source slices, and the spine emits a single permuted token sequence that every rule walks. Separately, the corpus gate groups files by import set to build one grammar snapshot per set, the semantics oracle becomes a parameterized call into `leanr_syntax::canon`, and the CLI gains a `.gitignore`-respecting project walk plus unified-diff check output.

**Tech Stack:** Rust (workspace, edition 2021), `rowan` lossless trees, `mise` task runner, `assert_cmd` + `tempfile` for CLI tests. Two new `leanr_cli`-only dependencies: `ignore` (project walk) and `similar` (unified diff).

**Spec:** [docs/superpowers/specs/2026-07-20-m3c-fast-follows-design.md](../specs/2026-07-20-m3c-fast-follows-design.md)

## Global Constraints

- **Branch:** `m3c-fast-follows`, already checked out with the spec committed. All work lands here; single whole-branch review at the end.
- **No new style rules.** Indentation and multi-line construct rules stay deferred to the next slice. This plan changes *where* the existing three rules apply, never *what* they do.
- **The four acceptance invariants are unchanged and keep gating:** total, idempotent, semantics-preserving (modulo layout + import order), byte-identical ordered comment sequence.
- **`canon_jsonl` output must stay byte-identical.** It is the oracle-comparison path; `crates/leanr_syntax/tests/oracle_golden.rs` and `crates/leanr_grammar/tests/import_golden.rs` prove it.
- **New dependencies are confined to `crates/leanr_cli`.** `leanr_fmt`, `leanr_syntax`, and everything below stay dependency-free for this slice.
- **Fixed format width:** `leanr_fmt::WIDTH = 100`. Not configurable.
- **Preserve-fallback is never weakened.** Any comment inside the import span still routes the whole block to verbatim preservation.
- **Verification after every task:** `mise run test` and `mise run lint` must both pass before committing.
- **Commit style:** conventional commits (`feat:`, `fix:`, `refactor:`, `docs:`, `test:`), matching the existing history.

---

### Task 1: Shared despan core in `leanr_syntax::canon`

Removes the duplicated node-shape and JSON-escaping logic in `leanr_fmt::verify::canon_semantic`. That copy is only ever compared against itself, so drift can only false-negative — the gate silently stops catching corruption. This task is independent of every other task; doing it first keeps it out of the way of the render changes.

**Files:**
- Modify: `crates/leanr_syntax/src/canon.rs` (add `CanonOpts` + `canon_to_string`; rewrite `canon_jsonl` and `node_json` in terms of them)
- Modify: `crates/leanr_fmt/src/verify.rs:32-133` (delete `canon_semantic`'s body and the private `json_str`; call into `canon_to_string`)
- Test: `crates/leanr_syntax/src/canon.rs` (inline `mod tests`), `crates/leanr_fmt/src/verify.rs` (inline `mod tests`)

**Interfaces:**
- Consumes: nothing from earlier tasks.
- Produces:
  ```rust
  // crates/leanr_syntax/src/canon.rs
  pub struct CanonOpts<'a> {
      pub spans: bool,                  // false = despanned
      pub sort_kind: Option<&'a str>,   // normalize sibling order for this node kind
  }
  pub fn canon_to_string(tree: &SyntaxTree, opts: CanonOpts) -> String;
  pub fn canon_jsonl(tree: &SyntaxTree) -> String;  // unchanged signature and output
  ```
  `leanr_fmt::verify::canon_semantic(tree: &SyntaxTree) -> String` keeps its signature; only its body changes.

- [ ] **Step 1: Write the failing test for `canon_to_string`**

Add to the inline `mod tests` in `crates/leanr_syntax/src/canon.rs`:

```rust
    #[test]
    fn canon_to_string_despans_and_sorts_named_kind() {
        use crate::{builtin, parse_module};
        let snap = builtin::snapshot();
        let despanned = CanonOpts {
            spans: false,
            sort_kind: Some("Lean.Parser.Module.import"),
        };
        let a = parse_module("import Foo.B\nimport Foo.A\n", &snap).tree;
        let b = parse_module("import Foo.A\nimport Foo.B\n", &snap).tree;
        // Despanned + import-order-normalized: reordering is invisible.
        assert_eq!(
            canon_to_string(&a, despanned),
            canon_to_string(&b, despanned)
        );
        // No span keys survive when spans: false.
        assert!(
            !canon_to_string(&a, despanned).contains("\"s\":"),
            "despanned form must not emit span keys"
        );
        // A corrupted import name is still caught.
        let c = parse_module("import Foo.C\n", &snap).tree;
        let d = parse_module("import Foo.D\n", &snap).tree;
        assert_ne!(
            canon_to_string(&c, despanned),
            canon_to_string(&d, despanned)
        );
    }

    #[test]
    fn canon_jsonl_equals_spanned_unsorted_canon_to_string() {
        use crate::{builtin, parse_module};
        let snap = builtin::snapshot();
        let tree = parse_module("import Foo.B\nimport Foo.A\ndef x := 1\n", &snap).tree;
        assert_eq!(
            canon_jsonl(&tree),
            canon_to_string(
                &tree,
                CanonOpts {
                    spans: true,
                    sort_kind: None
                }
            ),
            "canon_jsonl must be exactly the spanned, unsorted configuration"
        );
    }
```

`CanonOpts` must derive `Clone` + `Copy` so the test can pass `despanned` more than once.

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_syntax --lib canon 2>&1 | tail -20`
Expected: FAIL — compile error, `cannot find struct CanonOpts` / `cannot find function canon_to_string in this scope`.

- [ ] **Step 3: Implement `CanonOpts` and `canon_to_string`**

In `crates/leanr_syntax/src/canon.rs`, replace `canon_jsonl` and `node_json` (lines 15–68) with:

```rust
/// How to render the canonical form.
///
/// - `spans: true` emits `"s":[start,stop]` on every atom/ident — the
///   oracle-comparison form. `false` omits them: formatting legitimately
///   moves token positions, so offsets are layout, not semantics.
/// - `sort_kind: Some(k)` renders the sibling nodes of kind `k` in sorted
///   order of their own rendering, making a reordering of those siblings
///   invisible. Used for import commands, whose order is semantics-neutral
///   in Lean.
#[derive(Clone, Copy)]
pub struct CanonOpts<'a> {
    pub spans: bool,
    pub sort_kind: Option<&'a str>,
}

/// One JSON line per immediate child of the root (header node, then each
/// command) — the exact line structure the oracle dump emits.
pub fn canon_jsonl(tree: &SyntaxTree) -> String {
    canon_to_string(
        tree,
        CanonOpts {
            spans: true,
            sort_kind: None,
        },
    )
}

/// The canonical form under `opts`. `canon_jsonl` is the
/// `spans: true, sort_kind: None` configuration and MUST stay
/// byte-identical to it — it is what the oracle fixtures compare.
pub fn canon_to_string(tree: &SyntaxTree, opts: CanonOpts) -> String {
    let mut out = String::new();
    for child in tree.root().children() {
        node_json_opts(&child, &tree.kinds, opts, &mut out);
        out.push('\n');
    }
    out
}

pub fn node_json(node: &SyntaxNode, kinds: &KindInterner, out: &mut String) {
    node_json_opts(
        node,
        kinds,
        CanonOpts {
            spans: true,
            sort_kind: None,
        },
        out,
    );
}

/// Render one node. Children are rendered into their own strings first so
/// that `opts.sort_kind` can reorder a subset of them in place without
/// disturbing any other child's position.
fn node_json_opts(node: &SyntaxNode, kinds: &KindInterner, opts: CanonOpts, out: &mut String) {
    let mut parts: Vec<String> = Vec::new();
    let mut sort_slots: Vec<usize> = Vec::new();
    for el in node.children_with_tokens() {
        match el {
            rowan::NodeOrToken::Node(n) => {
                if let Some(k) = opts.sort_kind {
                    if kinds.name(n.kind()) == k {
                        sort_slots.push(parts.len());
                    }
                }
                let mut s = String::new();
                node_json_opts(&n, kinds, opts, &mut s);
                parts.push(s);
            }
            rowan::NodeOrToken::Token(t) => {
                let k = t.kind();
                if is_trivia(k) {
                    continue;
                }
                let mut s = String::new();
                if k == KIND_MISSING {
                    s.push_str("{\"k\":\"<missing>\"}");
                } else {
                    if k == KIND_IDENT {
                        s.push_str("{\"i\":");
                    } else {
                        // KIND_ATOM and (never oracle-compared) KIND_ERROR_TOKEN.
                        debug_assert!(k == KIND_ATOM || k == KIND_ERROR_TOKEN);
                        s.push_str("{\"a\":");
                    }
                    json_str(t.text(), &mut s);
                    if opts.spans {
                        let range = t.text_range();
                        push_span(u32::from(range.start()), u32::from(range.end()), &mut s);
                    } else {
                        s.push('}');
                    }
                }
                parts.push(s);
            }
        }
    }
    if sort_slots.len() > 1 {
        let mut rendered: Vec<String> = sort_slots.iter().map(|&i| parts[i].clone()).collect();
        rendered.sort();
        for (slot, &i) in sort_slots.iter().enumerate() {
            parts[i] = rendered[slot].clone();
        }
    }
    out.push_str("{\"c\":[");
    out.push_str(&parts.join(","));
    out.push_str("],\"k\":");
    json_str(kinds.name(node.kind()), out);
    out.push('}');
}
```

Note `push_span` already emits the closing `}`, which is why the `spans: false` branch pushes it explicitly. `node_json` stays `pub` with its existing signature — nothing outside `canon.rs` calls it today, but removing it would be an unrelated API change.

`json_str` stays private in this module and is unchanged.

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p leanr_syntax --lib canon 2>&1 | tail -20`
Expected: PASS — including the pre-existing `canon_skips_trivia_and_orders_keys_alphabetically`, which pins the exact `canon_jsonl` byte output.

- [ ] **Step 5: Verify the oracle fixture gates still pass**

Run: `cargo test -p leanr_syntax --test oracle_golden && cargo test -p leanr_grammar --test import_golden`
Expected: PASS both. These compare `canon_jsonl` against committed oracle dumps — they are the real proof that the refactor is byte-identical.

- [ ] **Step 6: Retarget `leanr_fmt::verify::canon_semantic`**

In `crates/leanr_fmt/src/verify.rs`, delete `node_semantic` (lines 60–113) and the private `json_str` (lines 115–133), and replace `canon_semantic` (lines 32–58) with:

```rust
/// Semantics oracle for invariant 3: `leanr_syntax::canon`'s canonical
/// form, despanned and with import commands order-normalized.
///
///  1. **Spans omitted** — formatting legitimately moves token positions
///     (spacing collapse, trailing-ws strip), so those offsets are layout,
///     not semantics. The token KIND + TEXT are the semantic content and
///     are kept.
///  2. **Import commands order-normalized** — so the formatter's
///     alphabetical import sort is invisible here.
///
/// This still catches a dropped/renamed/restructured token, a corrupted
/// import name, or a changed command body. It tolerates exactly what the
/// formatter is allowed to change: layout and import order. Sharing
/// `canon`'s renderer (rather than mirroring it) removes the drift risk —
/// a divergence in a private copy could only ever false-negative.
pub fn canon_semantic(tree: &SyntaxTree) -> String {
    leanr_syntax::canon::canon_to_string(
        tree,
        leanr_syntax::canon::CanonOpts {
            spans: false,
            sort_kind: Some(IMPORT_KIND),
        },
    )
}
```

Remove the now-unused imports from the `use` block at the top of `verify.rs`: `KIND_IDENT`, `KIND_MISSING`, `SyntaxNode`, and `is_trivia` if nothing else in the file uses them (`comment_seq` still needs `NodeOrToken`, `KIND_BLOCK_COMMENT`, and `KIND_LINE_COMMENT`). Keep the `IMPORT_KIND` constant at line 16.

- [ ] **Step 7: Run the fmt tests to verify the oracle still behaves**

Run: `cargo test -p leanr_fmt`
Expected: PASS — in particular `canon_semantic_tolerates_layout_and_import_order_catches_corruption` and `check_invariants_holds_for_reordering_and_spacing`, both unchanged, now exercising the shared renderer.

- [ ] **Step 8: Full verification and commit**

Run: `mise run test && mise run lint`
Expected: PASS both.

```bash
git add crates/leanr_syntax/src/canon.rs crates/leanr_fmt/src/verify.rs
git commit -m "refactor(syntax): parameterized canon renderer; fmt's semantics oracle shares it"
```

---

### Task 2: The unified permuted walk

The load-bearing change. Today `render_verbatim` emits raw source slices for the head and tail of any import-bearing file, so trivia and spacing never run on them — and essentially every real file has imports. This task deletes that second path: imports become a permutation of the file's token sequence, and one walk applies every rule to the whole file.

**Files:**
- Modify: `crates/leanr_fmt/src/rules/imports.rs:12-16` (`ImportBlock` shape), `:76-123` (`detect` signature and body)
- Modify: `crates/leanr_fmt/src/render.rs:12-74` (`render_verbatim`, `render_tokens`)
- Test: `crates/leanr_fmt/src/render.rs` (inline `mod tests`), `crates/leanr_fmt/src/rules/imports.rs` (inline `mod tests`), `crates/leanr_fmt/tests/fixtures/` (new golden fixture pair)

**Interfaces:**
- Consumes: `crate::render::tokens_of(&SyntaxNode) -> Vec<SyntaxToken>` (unchanged), `crate::comments::has_interior_comment(&SyntaxNode) -> bool` (unchanged), `crate::rules::spacing::normalize_ws(Option<&str>, &str, Option<&str>) -> Option<String>` (unchanged), `crate::trivia::normalize_ws_trivia(&str) -> String` (unchanged).
- Produces:
  ```rust
  // crates/leanr_fmt/src/rules/imports.rs
  pub struct ImportBlock {
      pub head_end: usize,          // token index of the first import's first significant token
      pub tail_start: usize,        // one past the last import's last significant token
      pub runs: Vec<(usize, usize)>, // per-import [start, end) token-index runs, in SORTED order
  }
  pub fn detect(tree: &SyntaxTree, toks: &[SyntaxToken]) -> Option<ImportBlock>;

  // crates/leanr_fmt/src/render.rs
  pub fn render_verbatim(tree: &SyntaxTree) -> Doc;  // signature unchanged
  ```
  `ImportBlock`'s old fields (`start: usize`, `end: usize`, `sorted: Vec<String>`) are gone — nothing outside `render.rs` reads them.

- [ ] **Step 1: Write the failing test that proves rules reach import-bearing bodies**

Add to the inline `mod tests` in `crates/leanr_fmt/src/render.rs`:

```rust
    // The whole point of the permuted walk: before it, a file WITH imports
    // emitted its body as a raw source slice, so neither the spacing rule
    // nor the trivia rule ran there. `:=   1` survived uncollapsed and the
    // trailing spaces survived unstripped. Both must now be normalized.
    #[test]
    fn rules_apply_to_body_of_import_bearing_file() {
        assert_eq!(
            fmt("import Foo.B\nimport Foo.A\n\ndef x :=   1  \ndef y := 2\n"),
            "import Foo.A\nimport Foo.B\n\ndef x := 1\ndef y := 2\n"
        );
    }

    // The head span (before the first import) goes through the walk too.
    #[test]
    fn rules_apply_to_head_of_import_bearing_file() {
        assert_eq!(
            fmt("module\n\n\n\nimport Foo.B\nimport Foo.A\n\ndef x := 1\n"),
            "module\n\nimport Foo.A\nimport Foo.B\n\ndef x := 1\n"
        );
    }

    // Idempotence across the permutation: the second pass sees sorted
    // imports, so the permutation is the identity.
    #[test]
    fn permuted_walk_is_idempotent() {
        let messy = "import Foo.B\nimport Foo.A\n\n\n\ndef x :=   1  \n";
        let once = fmt(messy);
        assert_eq!(fmt(&once), once);
    }

    // The blank-line run between the last import and the body is trivia in
    // the TAIL span, so it collapses to a single blank line like any other.
    #[test]
    fn blank_run_after_imports_collapses() {
        assert_eq!(
            fmt("import Foo.A\n\n\n\ndef x := 1\n"),
            "import Foo.A\n\ndef x := 1\n"
        );
    }
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_fmt --lib render 2>&1 | tail -30`
Expected: FAIL — `rules_apply_to_body_of_import_bearing_file` reports left `"import Foo.A\nimport Foo.B\n\ndef x :=   1\ndef y := 2\n"` (the `:=   1` uncollapsed), and `rules_apply_to_head_of_import_bearing_file` reports the blank run before `import` uncollapsed. These two failures are the bug this task exists to fix — confirm both before continuing.

- [ ] **Step 3: Rewrite `imports::detect` to return token-index runs**

In `crates/leanr_fmt/src/rules/imports.rs`, replace the `ImportBlock` struct (lines 12–16) and `detect` (lines 76–123) with:

```rust
/// A detected, reorderable import block, expressed as token-index runs
/// into the file's flat token list (`render::tokens_of` of the root).
/// Byte offsets are deliberately NOT used: the spine emits a permutation
/// of the token sequence, so indices are the natural currency.
pub struct ImportBlock {
    /// Token index of the first import's first significant token. Tokens
    /// `[0, head_end)` are emitted unchanged, in place.
    pub head_end: usize,
    /// One past the last import's last significant token. Tokens
    /// `[tail_start, len)` are emitted unchanged, in place.
    pub tail_start: usize,
    /// Per-import `[start, end)` token-index runs, in SORTED order. Each
    /// run spans one import's first through last significant token
    /// INCLUSIVE of its interior whitespace, so intra-import spacing
    /// survives reordering exactly as before.
    pub runs: Vec<(usize, usize)>,
}

/// The token index whose token starts at byte `offset`. `toks` is in
/// source order, so token start offsets are strictly increasing and a
/// binary search is exact.
fn tok_index_at(toks: &[SyntaxToken], offset: usize) -> Option<usize> {
    let i = toks.partition_point(|t| (u32::from(t.text_range().start()) as usize) < offset);
    (i < toks.len() && u32::from(toks[i].text_range().start()) as usize == offset).then_some(i)
}

/// The `[start, end)` token-index run of one import command: its first
/// through its last significant token, inclusive.
fn import_run(node: &SyntaxNode, toks: &[SyntaxToken]) -> Option<(usize, usize)> {
    let own = tokens_of(node);
    let sig: Vec<_> = own
        .iter()
        .filter(|t| !leanr_syntax::kind::is_trivia(t.kind()))
        .collect();
    let first = sig.first()?;
    let last = sig.last()?;
    let s = tok_index_at(toks, u32::from(first.text_range().start()) as usize)?;
    let e = tok_index_at(toks, u32::from(last.text_range().start()) as usize)?;
    Some((s, e + 1))
}

/// Detect a reorderable import block. `toks` must be
/// `render::tokens_of(&tree.root())` — the same list the spine emits from.
/// Returns `None` (preserve-fallback) when there are no imports, when a
/// comment sits anywhere in the block, or when any run cannot be located.
pub fn detect(tree: &SyntaxTree, toks: &[SyntaxToken]) -> Option<ImportBlock> {
    let root = tree.root();
    // Import commands are not direct children of the module root: they live
    // under `Lean.Parser.Module.header` -> `null`. Walk descendants (preorder
    // = source order) and keep the import command nodes.
    let imports: Vec<SyntaxNode> = root
        .descendants()
        .filter(|n| is_import_command(n, tree))
        .collect();
    if imports.is_empty() {
        return None;
    }
    // If any import command carries an interior comment, or a comment sits
    // between imports, preserve the block verbatim. `has_interior_comment`
    // covers comments between an import's own significant tokens; a
    // between-imports comment is the leading trivia of a later import's
    // first token, caught by `between_import_comment`.
    if imports.iter().any(has_interior_comment) || between_import_comment(&imports) {
        return None;
    }
    let mut keyed: Vec<(String, (usize, usize))> = Vec::with_capacity(imports.len());
    for n in &imports {
        keyed.push((import_sort_key(n), import_run(n, toks)?));
    }
    // Source-order extent, taken BEFORE sorting.
    let head_end = keyed.iter().map(|(_, (s, _))| *s).min()?;
    let tail_start = keyed.iter().map(|(_, (_, e))| *e).max()?;
    keyed.sort_by(|a, b| a.0.cmp(&b.0));
    Some(ImportBlock {
        head_end,
        tail_start,
        runs: keyed.into_iter().map(|(_, run)| run).collect(),
    })
}
```

Update the `use` block at the top of the file to add `SyntaxToken`:

```rust
use leanr_syntax::tree::{SyntaxNode, SyntaxToken};
```

`is_import_command`, `import_sort_key`, `between_import_comment`, and `has_interior_comment` are unchanged. `import_original_text` (lines 32–47) is now dead — delete it.

Note the sort is by `import_sort_key` only, exactly as before: it skips both the `import` keyword and an `all` modifier so `import all Apple` keys as `"Apple"`, and each import's own text is never reconstructed, so `public` modifiers survive verbatim.

- [ ] **Step 4: Rewrite the spine to emit a permuted token sequence**

In `crates/leanr_fmt/src/render.rs`, replace `render_verbatim` (lines 12–34) and `render_tokens` (lines 36–74) with:

```rust
/// One emission slot in the output order: either a token from the file's
/// flat token list, or a synthesized separator.
enum Emit {
    /// Index into the file's token list.
    Tok(usize),
    /// A synthesized newline between two reordered imports. The
    /// between-import whitespace is NOT carried over (it is excluded from
    /// every run), and this replaces it — the one-import-per-line rule.
    /// Safe because `imports::detect` bails to preserve-fallback whenever
    /// a comment sits anywhere in the block, so the only trivia dropped is
    /// whitespace.
    Newline,
}

/// The formatter spine. Builds ONE emission order over the file's tokens
/// and walks it: there is no second rendering path. When
/// `imports::detect` finds a reorderable block, the order is a
/// permutation — head tokens in place, then each import's token run in
/// sorted order separated by a synthesized newline, then tail tokens in
/// place. Otherwise it is the identity order. Either way every token
/// flows through the same rule application, so trivia, spacing, and every
/// future rule cover the whole file — including the head and tail of
/// import-bearing files, which earlier revisions emitted as raw source
/// slices and never normalized.
///
/// Idempotence: after one pass the imports are sorted, so the permutation
/// is the identity on the second pass.
pub fn render_verbatim(tree: &SyntaxTree) -> Doc {
    let toks = tokens_of(&tree.root());
    let order = match imports::detect(tree, &toks) {
        Some(block) => permute(toks.len(), &block),
        None => (0..toks.len()).map(Emit::Tok).collect(),
    };
    render_tokens(&toks, &order)
}

/// head ++ sorted runs (newline-separated) ++ tail.
fn permute(len: usize, block: &imports::ImportBlock) -> Vec<Emit> {
    let mut order = Vec::with_capacity(len + block.runs.len());
    order.extend((0..block.head_end).map(Emit::Tok));
    for (i, &(s, e)) in block.runs.iter().enumerate() {
        if i > 0 {
            order.push(Emit::Newline);
        }
        order.extend((s..e).map(Emit::Tok));
    }
    order.extend((block.tail_start..len).map(Emit::Tok));
    order
}

/// Emit the order, with each token's text chosen by KIND (see
/// `emit_token_text`). Whitespace-trivia routes through the spacing rule
/// first (`rules::spacing::normalize_ws`): a single-line gap adjacent to a
/// target operator (`:=`, `→`) normalizes to one space; every other
/// whitespace case (multi-line, or single-line but not near a target)
/// falls back to `trivia::normalize_ws_trivia`.
///
/// The `prev`/`next` significant-token scans walk the EMISSION order, not
/// the source order. That is what they always meant — spacing is a
/// property of what ends up adjacent in the output.
fn render_tokens(toks: &[SyntaxToken], order: &[Emit]) -> Doc {
    use leanr_syntax::kind::{is_trivia, KIND_WHITESPACE};
    let sig_text = |slot: &Emit| -> Option<&str> {
        match slot {
            Emit::Newline => None,
            Emit::Tok(i) => (!is_trivia(toks[*i].kind())).then(|| toks[*i].text()),
        }
    };
    let mut parts = Vec::with_capacity(order.len());
    for (i, slot) in order.iter().enumerate() {
        match slot {
            Emit::Newline => parts.push(Doc::text("\n".to_string())),
            Emit::Tok(ti) => {
                let t = &toks[*ti];
                if t.kind() == KIND_WHITESPACE {
                    let prev = order[..i].iter().rev().find_map(sig_text);
                    let next = order[i + 1..].iter().find_map(sig_text);
                    let ws = t.text();
                    let out = match crate::rules::spacing::normalize_ws(prev, ws, next) {
                        Some(s) => s,
                        None => crate::trivia::normalize_ws_trivia(ws),
                    };
                    parts.push(Doc::text(out));
                } else {
                    parts.push(Doc::text(emit_token_text(t)));
                }
            }
        }
    }
    Doc::concat(parts)
}
```

`Emit::Newline` yields `None` from `sig_text` deliberately: a synthesized separator is not a significant token, so it must not become a spacing neighbor. `sig_text` captures `toks` by shared reference, so the closure is `Copy` and can be passed to `find_map` twice; if the borrow checker disagrees on your toolchain, pass `&sig_text` instead. Update the file's `use` block to import `SyntaxToken` alongside the existing items if it is not already in scope (`use leanr_syntax::tree::{NodeOrToken, SyntaxNode, SyntaxToken};`). `emit_token_text` and `tokens_of` are unchanged.

- [ ] **Step 5: Run the fmt tests to verify they pass**

Run: `cargo test -p leanr_fmt 2>&1 | tail -30`
Expected: PASS — the four new tests from Step 1, plus every pre-existing test. Watch specifically for these, which pin behavior the permutation must not regress:
- `preserves_block_when_interior_comment_present` (preserve-fallback intact)
- `public_imports_sorted_and_preserved` and `import_all_sorts_by_module_name_not_all_prefix` (corpus-driven sort/verbatim fixes)
- `prelude_header_stays_parseable` and `module_header_with_public_imports`
- `leading_comment_before_first_import_preserved`
- `fixtures_format_to_expected_and_hold_invariants` (the golden fixtures)

If a golden `.expected` file now legitimately differs because a rule reaches content it previously skipped, update the `.expected` and say so in the commit message — but confirm the change is a rule correctly applying, not a corruption, by checking the invariants still hold.

- [ ] **Step 6: Add a golden fixture for the permuted walk**

Create `crates/leanr_fmt/tests/fixtures/ImportsWithBody.lean`:

```lean
import Foo.B
import Foo.A


def x :=   1  
def y := 2 -- note  
```

(Note the trailing spaces after `1` and after `note` — they are the point of the fixture.)

Create `crates/leanr_fmt/tests/fixtures/ImportsWithBody.expected`:

```lean
import Foo.A
import Foo.B

def x := 1
def y := 2 -- note
```

- [ ] **Step 7: Run the golden gate**

Run: `cargo test -p leanr_fmt --test fixtures_golden`
Expected: PASS — the new fixture formats to its `.expected` and holds all four invariants.

- [ ] **Step 8: Full verification and commit**

Run: `mise run test && mise run lint`
Expected: PASS both.

```bash
git add crates/leanr_fmt/src/render.rs crates/leanr_fmt/src/rules/imports.rs crates/leanr_fmt/tests/fixtures/
git commit -m "feat(fmt): unified permuted token walk so rules reach import-bearing bodies"
```

---

### Task 3: `fmt:mathlib` snapshot reuse

The corpus gate builds a full grammar snapshot per pass-list file — each one decoding that file's whole olean import closure, ~10 minutes in release over 23 files. Group by import set instead, mirroring `leanr_grammar/tests/mathlib_sweep.rs`.

**Files:**
- Modify: `crates/leanr_fmt/tests/mathlib_corpus.rs:41-85` (the sweep loop)
- Modify: `mise.toml:210-217` (description wording only, if it claims a per-file build)

**Interfaces:**
- Consumes: `support::snapshot_for(src: &str, root: &Path) -> Option<Holder>` and `Holder::snapshot(&self) -> &GrammarSnapshot` (both unchanged, already in the file's `mod support`); `leanr_fmt::verify::check_invariants(src: &str, snap: &GrammarSnapshot) -> Result<(), String>` (unchanged); `leanr_syntax::parse_header_imports(src: &str) -> Vec<String>`.
- Produces: nothing consumed by later tasks.

- [ ] **Step 1: Rewrite the sweep loop to group by import set**

In `crates/leanr_fmt/tests/mathlib_corpus.rs`, replace the loop body and the surrounding accounting (lines 41–84, from `let list = ...` through the two closing asserts) with:

```rust
    let list = std::fs::read_to_string(passlist_path()).unwrap();
    let root = mathlib_root();

    // Group pass-list files by import set so one grammar snapshot is built
    // per DISTINCT set rather than per file — the same per-import-set reuse
    // `leanr_grammar/tests/mathlib_sweep.rs` does. The key is derived from
    // the same `parse_header_imports` call the snapshot build itself makes,
    // so there is no second notion of "this file's imports" to drift.
    let mut groups: std::collections::BTreeMap<String, Vec<(String, String)>> =
        std::collections::BTreeMap::new();
    let mut checked = 0;
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
        // The file is confirmed PRESENT, so it is now counted — a
        // present-but-unloadable file must never be silently dropped from
        // the gate (that would let a "green" run quietly check fewer files
        // than it claims).
        checked += 1;
        let mut imports = leanr_syntax::parse_header_imports(&src);
        imports.sort();
        imports.dedup();
        groups
            .entry(imports.join("\0"))
            .or_default()
            .push((rel.to_string(), src));
    }

    let mut failures = Vec::new();
    for (key, files) in &groups {
        // Any file in the group resolves the same closure; use the first.
        let (_, probe_src) = &files[0];
        let snap = match support::snapshot_for(probe_src, &root) {
            Some(s) => s,
            None => {
                // Record ONE failure PER FILE, not per group: a broken
                // closure must not shrink the effective checked count.
                for (rel, _) in files {
                    failures.push(format!(
                        "{rel}: import closure unavailable (LEANR_OLEAN_PATH / load_closure \
                         failed; import set {key:?})"
                    ));
                }
                continue;
            }
        };
        for (rel, src) in files {
            if let Err(e) = leanr_fmt::verify::check_invariants(src, snap.snapshot()) {
                failures.push(format!("{rel}: {e}"));
            }
        }
    }

    eprintln!(
        "fmt corpus gate: {checked} file(s) across {} distinct import set(s)",
        groups.len()
    );
    assert!(
        checked > 0,
        "corpus empty — pass-list or checkout wiring broken"
    );
    assert!(
        failures.is_empty(),
        "fmt invariants failed:\n{}",
        failures.join("\n")
    );
```

The `LEANR_OLEAN_PATH`-empty assert (lines 25–40) stays exactly where it is, ahead of all grouping — an empty search path must fail loudly rather than make the gate vacuously green.

- [ ] **Step 2: Verify it compiles and is a no-op without the corpus env**

Run: `cargo test -p leanr_fmt --test mathlib_corpus`
Expected: PASS with `skipping fmt corpus gate (set LEANR_FMT_CORPUS=1 via 'mise run fmt:mathlib')` on stderr — the gate is inert without `LEANR_FMT_CORPUS=1`, so a bare checkout stays green.

- [ ] **Step 3: Run the real gate and record the speedup**

Run: `time mise run fmt:mathlib 2>&1 | tail -20`
Expected: PASS, with the new `fmt corpus gate: N file(s) across M distinct import set(s)` line showing `M < N`, and a wall-clock materially below the previous ~10 minutes.

This step needs the Mathlib checkout (`mise run mathlib:fetch`) and a working `lake env printenv LEAN_PATH` in `.mathlib`. If the checkout is unavailable in this environment, say so explicitly rather than marking the step done — the grouping logic is unverified until this runs, and Task 2's permuted walk means this sweep is exercising the rule engine on real files for the first time.

- [ ] **Step 4: Update the mise task description if it overstates the cost**

Read `mise.toml:210-217`. If the `fmt:mathlib` description implies a per-file snapshot build, amend it to note the per-import-set reuse. Leave the "FAST pass-list tier — NOT the ~35h discovery sweep" wording intact; that distinction is load-bearing.

- [ ] **Step 5: Full verification and commit**

Run: `mise run test && mise run lint`
Expected: PASS both.

```bash
git add crates/leanr_fmt/tests/mathlib_corpus.rs mise.toml
git commit -m "perf(fmt): one grammar snapshot per import set in the corpus gate"
```

---

### Task 4: `leanr fmt` with no arguments walks the project

Bare `leanr fmt` currently exits 0 silently. Make it format the project: walk the current directory for `*.lean`, respecting `.gitignore`.

**Files:**
- Modify: `crates/leanr_cli/Cargo.toml:11-21` (add `ignore`)
- Modify: `crates/leanr_cli/src/main.rs:112-122` (help text), `:376-445` (`fmt_cmd`)
- Test: `crates/leanr_cli/tests/fmt_cli.rs`

**Interfaces:**
- Consumes: `leanr_fmt::format_src(&str, &GrammarSnapshot) -> Result<String, FormatError>` (unchanged); `load_snapshot(&str, Vec<PathBuf>, bool)` in `main.rs` (unchanged).
- Produces:
  ```rust
  // crates/leanr_cli/src/main.rs
  /// The inputs to format. Empty `files` means "walk the project".
  fn resolve_inputs(files: Vec<PathBuf>) -> Vec<PathBuf>;
  ```
  Task 5 calls `resolve_inputs` unchanged and modifies only the reporting inside `fmt_cmd`.

- [ ] **Step 1: Add the `ignore` dependency**

In `crates/leanr_cli/Cargo.toml`, add to `[dependencies]` (keeping the list alphabetical):

```toml
ignore = "0.4"
```

Justification, recorded in the spec: gitignore semantics (nested ignore files, negation, precedence) are a specification someone else already implements correctly; a hand-rolled subset would be wrong in exactly the cases users notice. Confined to `leanr_cli`.

- [ ] **Step 2: Verify the dependency passes the license gate**

Run: `mise run lint:deps`
Expected: PASS. If `cargo deny` flags a license or advisory, stop and report it rather than adding an exception — the dependency choice is revisitable.

- [ ] **Step 3: Write the failing tests for the project walk**

Add to `crates/leanr_cli/tests/fmt_cli.rs`:

```rust
#[test]
fn fmt_with_no_args_walks_project_and_respects_gitignore() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    std::fs::create_dir_all(root.join("src/nested")).unwrap();
    std::fs::create_dir_all(root.join("vendored")).unwrap();
    std::fs::create_dir_all(root.join(".lake/packages")).unwrap();
    std::fs::write(root.join(".gitignore"), "vendored/\n").unwrap();

    let unformatted = "import Foo.B\nimport Foo.A\n";
    let formatted = "import Foo.A\nimport Foo.B\n";
    std::fs::write(root.join("src/A.lean"), unformatted).unwrap();
    std::fs::write(root.join("src/nested/B.lean"), unformatted).unwrap();
    std::fs::write(root.join("vendored/C.lean"), unformatted).unwrap();
    std::fs::write(root.join(".lake/packages/D.lean"), unformatted).unwrap();

    let out = leanr().arg("fmt").current_dir(root).output().unwrap();
    assert!(out.status.success(), "project walk should succeed");

    // Walked and rewritten, including nested.
    assert_eq!(
        std::fs::read_to_string(root.join("src/A.lean")).unwrap(),
        formatted
    );
    assert_eq!(
        std::fs::read_to_string(root.join("src/nested/B.lean")).unwrap(),
        formatted
    );
    // Gitignored: untouched.
    assert_eq!(
        std::fs::read_to_string(root.join("vendored/C.lean")).unwrap(),
        unformatted
    );
    // Hidden directory (.lake, .git, .mathlib): untouched.
    assert_eq!(
        std::fs::read_to_string(root.join(".lake/packages/D.lean")).unwrap(),
        unformatted
    );
}

#[test]
fn fmt_with_no_args_and_no_lean_files_succeeds() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("README.md"), "# nothing here\n").unwrap();
    let out = leanr().arg("fmt").current_dir(dir.path()).output().unwrap();
    assert!(
        out.status.success(),
        "an empty project is not an error: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}
```

- [ ] **Step 4: Run the tests to verify they fail**

Run: `cargo test -p leanr_cli --test fmt_cli 2>&1 | tail -30`
Expected: FAIL — `fmt_with_no_args_walks_project_and_respects_gitignore` fails on the first assertion, because bare `leanr fmt` exits 0 having formatted nothing, so `src/A.lean` still holds the unformatted text. (`fmt_with_no_args_and_no_lean_files_succeeds` passes already — it pins behavior that must survive.)

- [ ] **Step 5: Implement `resolve_inputs` and wire it into `fmt_cmd`**

In `crates/leanr_cli/src/main.rs`, add above `fmt_cmd`:

```rust
/// The inputs to format. Explicit arguments win; with none, walk the
/// current directory for `*.lean`, respecting `.gitignore`.
///
/// `ignore::WalkBuilder`'s defaults are exactly the wanted behavior:
/// hidden entries are skipped (so `.lake`, `.git`, and `.mathlib` are
/// excluded regardless of any ignore file), symlinks are not followed,
/// and nested `.gitignore` files compose. Results are sorted so output
/// order does not depend on filesystem iteration order.
fn resolve_inputs(files: Vec<PathBuf>) -> Vec<PathBuf> {
    if !files.is_empty() {
        return files;
    }
    let mut found: Vec<PathBuf> = ignore::WalkBuilder::new(".")
        .build()
        .filter_map(Result::ok)
        .filter(|e| e.file_type().is_some_and(|ft| ft.is_file()))
        .map(|e| e.into_path())
        .filter(|p| p.extension().and_then(|x| x.to_str()) == Some("lean"))
        .collect();
    found.sort();
    found
}
```

Then change the head of `fmt_cmd` (line 376–379) from iterating `&files` to iterating the resolved list:

```rust
fn fmt_cmd(files: Vec<PathBuf>, check: bool, path: Vec<PathBuf>) -> ExitCode {
    let inputs = resolve_inputs(files);
    let mut any_would_change = false;
    let mut had_error = false;
    for file in &inputs {
```

The rest of the loop body (lines 380–439) is unchanged.

- [ ] **Step 6: Update the `--help` text for the `files` argument**

In `crates/leanr_cli/src/main.rs`, replace the doc comment on `Fmt`'s `files` field (line 114):

```rust
        /// Files to format; `-` reads stdin and writes stdout. With no
        /// files, walks the current directory for `*.lean`, respecting
        /// `.gitignore` and skipping hidden directories.
        files: Vec<PathBuf>,
```

- [ ] **Step 7: Run the tests to verify they pass**

Run: `cargo test -p leanr_cli --test fmt_cli 2>&1 | tail -30`
Expected: PASS — both new tests plus the pre-existing `fmt_check_flags_unformatted_file` and `fmt_rewrites_in_place`.

- [ ] **Step 8: Full verification and commit**

Run: `mise run test && mise run lint && mise run lint:deps`
Expected: PASS all three.

```bash
git add crates/leanr_cli/Cargo.toml crates/leanr_cli/src/main.rs crates/leanr_cli/tests/fmt_cli.rs Cargo.lock
git commit -m "feat(cli): bare 'leanr fmt' walks the project, respecting .gitignore"
```

---

### Task 5: `--check` prints a unified diff for every input

`--check` currently prints a bare filename for files and does nothing at all for stdin — `leanr fmt --check -` always exits 0, silently passing input that would change. Replace both with a unified diff on stdout and exit 1.

**Files:**
- Modify: `crates/leanr_cli/Cargo.toml:11-21` (add `similar`)
- Modify: `crates/leanr_cli/src/main.rs:376-445` (`fmt_cmd`'s reporting)
- Test: `crates/leanr_cli/tests/fmt_cli.rs`

**Interfaces:**
- Consumes: `resolve_inputs(files: Vec<PathBuf>) -> Vec<PathBuf>` from Task 4.
- Produces: nothing consumed by later tasks.

- [ ] **Step 1: Add the `similar` dependency**

In `crates/leanr_cli/Cargo.toml`, add to `[dependencies]` (keeping the list alphabetical):

```toml
similar = "2"
```

Justification, recorded in the spec: unified diff hunk generation with context. It feeds no acceptance invariant — diff output is cosmetic — so hand-rolling it would buy no correctness control. Confined to `leanr_cli`.

- [ ] **Step 2: Verify the dependency passes the license gate**

Run: `mise run lint:deps`
Expected: PASS.

- [ ] **Step 3: Write the failing tests for check-mode diffs**

Add to `crates/leanr_cli/tests/fmt_cli.rs`:

```rust
use std::io::Write;
use std::process::Stdio;

#[test]
fn fmt_check_prints_unified_diff_naming_the_file() {
    let dir = tempfile::tempdir().unwrap();
    let f = dir.path().join("A.lean");
    let unformatted = "import Foo.B\nimport Foo.A\n";
    std::fs::write(&f, unformatted).unwrap();

    let out = leanr().arg("fmt").arg("--check").arg(&f).output().unwrap();
    assert!(!out.status.success(), "check must fail on a would-change file");

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("A.lean"),
        "diff must name the input: {stdout}"
    );
    assert!(
        stdout.contains("-import Foo.B") && stdout.contains("+import Foo.A"),
        "diff must show the change: {stdout}"
    );
    // Check mode never writes the file.
    assert_eq!(std::fs::read_to_string(&f).unwrap(), unformatted);
}

#[test]
fn fmt_check_stdin_diffs_and_fails_without_emitting_formatted_text() {
    let mut child = leanr()
        .arg("fmt")
        .arg("--check")
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(b"import Foo.B\nimport Foo.A\n")
        .unwrap();
    let out = child.wait_with_output().unwrap();

    assert!(
        !out.status.success(),
        "check on would-change stdin must exit non-zero"
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("<stdin>"),
        "diff must name the input as <stdin>: {stdout}"
    );
    assert!(
        stdout.contains("-import Foo.B") && stdout.contains("+import Foo.A"),
        "diff must show the change: {stdout}"
    );
    // The formatted text itself must NOT be emitted — that is the
    // non-check behavior and would be indistinguishable from it.
    assert!(
        !stdout.contains("\nimport Foo.A\nimport Foo.B\n"),
        "check mode must not emit the formatted output: {stdout}"
    );
}

#[test]
fn fmt_check_is_silent_and_succeeds_on_formatted_input() {
    let dir = tempfile::tempdir().unwrap();
    let f = dir.path().join("A.lean");
    std::fs::write(&f, "import Foo.A\nimport Foo.B\n").unwrap();
    let out = leanr().arg("fmt").arg("--check").arg(&f).output().unwrap();
    assert!(out.status.success(), "already-formatted input must pass");
    assert!(
        out.stdout.is_empty(),
        "no diff for unchanged input: {}",
        String::from_utf8_lossy(&out.stdout)
    );
}
```

- [ ] **Step 4: Run the tests to verify they fail**

Run: `cargo test -p leanr_cli --test fmt_cli 2>&1 | tail -40`
Expected: FAIL on two of the three. `fmt_check_prints_unified_diff_naming_the_file` fails because the filename goes to stderr and no diff is produced, so stdout is empty. `fmt_check_stdin_diffs_and_fails_without_emitting_formatted_text` fails on the exit-status assertion — this is the always-exits-0 bug. `fmt_check_is_silent_and_succeeds_on_formatted_input` should already pass.

- [ ] **Step 5: Implement diff reporting in `fmt_cmd`**

In `crates/leanr_cli/src/main.rs`, add above `fmt_cmd`:

```rust
/// A unified diff of `before` → `after`, headed by `name` (a file path,
/// or `<stdin>`). Printed by `--check` for every input that would change.
fn unified_diff(name: &str, before: &str, after: &str) -> String {
    similar::TextDiff::from_lines(before, after)
        .unified_diff()
        .context_radius(3)
        .header(name, name)
        .to_string()
}
```

Then replace `fmt_cmd`'s output handling — the `if is_stdin { ... }` block and the `if formatted != src { ... }` block (lines 426–438) — with:

```rust
        let name = if is_stdin {
            "<stdin>".to_string()
        } else {
            file.display().to_string()
        };
        if check {
            // Check mode: never write a file, never emit the formatted
            // text (that is the non-check stdin behavior and would be
            // indistinguishable from it). Only diffs go to stdout.
            if formatted != src {
                any_would_change = true;
                print!("{}", unified_diff(&name, &src, &formatted));
            }
            continue;
        }
        if is_stdin {
            print!("{formatted}");
            continue;
        }
        if formatted != src {
            if let Err(e) = std::fs::write(file, &formatted) {
                eprintln!("error: cannot write {}: {e}", file.display());
                had_error = true;
            }
        }
```

The trailing exit-code block (lines 440–444) is unchanged: `had_error || (check && any_would_change)` is still the failure condition.

- [ ] **Step 6: Run the tests to verify they pass**

Run: `cargo test -p leanr_cli --test fmt_cli 2>&1 | tail -30`
Expected: PASS — all five tests in the file, including Task 4's two and the pre-existing `fmt_check_flags_unformatted_file` (which asserts only a non-zero exit, still true) and `fmt_rewrites_in_place`.

- [ ] **Step 7: Update the `--check` help text**

In `crates/leanr_cli/src/main.rs`, replace the doc comment on `Fmt`'s `check` field (line 116):

```rust
        /// Check mode: write nothing, print a unified diff for each input
        /// that would change, exit non-zero if any would.
        #[arg(long)]
        check: bool,
```

- [ ] **Step 8: Full verification and commit**

Run: `mise run test && mise run lint && mise run lint:deps`
Expected: PASS all three.

```bash
git add crates/leanr_cli/Cargo.toml crates/leanr_cli/src/main.rs crates/leanr_cli/tests/fmt_cli.rs Cargo.lock
git commit -m "feat(cli): 'leanr fmt --check' prints unified diffs for files and stdin"
```

---

### Task 6: Whole-branch verification

Every gate the spec's acceptance section names, run once against the finished branch. Task 2 changed what the corpus gate covers — head and tail content of real files now flows through the rule engine — so this is not a formality.

**Files:**
- Modify: `docs/superpowers/specs/2026-07-19-m3c-fmt-thin-slice-design.md:247-267` (mark the fast-follows section as addressed)

- [ ] **Step 1: Run the full CI gate**

Run: `mise run ci`
Expected: PASS — this is `lint`, `test`, `lint:deps`, `scan:secrets`, `cache:incremental`, and `cache:remote`.

- [ ] **Step 2: Run the fuzz smoke targets**

Run: `mise run fuzz`
Expected: PASS both the olean and syntax targets. Task 2 changed the formatter's token handling, and the syntax target exercises adjacent machinery.

- [ ] **Step 3: Run the parse acceptance gate**

Run: `mise run parse:acceptance`
Expected: PASS. Needs the pinned toolchain (`mise run elan:bootstrap`) and nightly. If unavailable in this environment, report that explicitly rather than marking the step done.

- [ ] **Step 4: Run the fmt corpus gate**

Run: `mise run fmt:mathlib`
Expected: PASS, with all four invariants holding across the pass-list. Needs `mise run mathlib:fetch`. This is the gate that now genuinely exercises the rules; if it fails, the failure is real signal about Task 2, not flakiness — debug it rather than routing around it.

- [ ] **Step 5: Cross off the fast-follows in the M3c spec**

In `docs/superpowers/specs/2026-07-19-m3c-fmt-thin-slice-design.md`, change the heading at line 247 from:

```markdown
### Fast-follows discovered during M3c implementation (next slice)
```

to:

```markdown
### Fast-follows discovered during M3c implementation

Addressed by [2026-07-20-m3c-fast-follows-design.md](2026-07-20-m3c-fast-follows-design.md).
```

Leave the four bullet items in place — they are the record of what was found and why.

- [ ] **Step 6: Commit and open the PR**

```bash
git add docs/superpowers/specs/2026-07-19-m3c-fmt-thin-slice-design.md
git commit -m "docs: mark M3c fast-follows as addressed"
git push -u origin m3c-fast-follows
gh pr create --title "M3c fast-follows: unified permuted walk, fast corpus gate, defined fmt CLI" --body "Implements docs/superpowers/specs/2026-07-20-m3c-fast-follows-design.md"
```

- [ ] **Step 7: Request review**

Use the `superpowers:requesting-code-review` skill for the whole-branch review — the M3b3/M3c packaging pattern is a single final review, not per-task reviews.

---

## Notes for the implementer

**Where the risk actually is.** Task 2 is the one that can break things. Head and tail content of import-bearing files passes through the rule engine for the first time — that is the entire point, and it means the corpus gate may surface genuine formatter bugs that were previously invisible because those spans were emitted as raw source. If `mise run fmt:mathlib` fails after Task 2, treat it as a real finding: the invariants are the instrument, and this is the first slice where they bite.

**What must not regress.** The import rule's corpus-driven fixes are load-bearing and were each a real bug: `public import Foo` must keep its modifier (it once became `import importFoo.B`), `import all Apple` must sort by `Apple` not `allApple`, and any comment in the import span must still route the whole block to verbatim preservation. Each has a named test — do not "clean up" past them.

**Why the between-import whitespace can be dropped.** `detect` returns `None` whenever a comment sits anywhere in the block, so the only trivia the permutation discards is whitespace, replaced by the synthesized newline the one-import-per-line rule mandates. If you ever relax the comment bail, this reasoning stops holding.
