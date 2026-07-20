//! Import normalize + sort (spec §The first-slice rules, rule 3). One
//! `import` per line, alphabetically sorted. Reordering is semantics-
//! neutral for Lean imports. Bails (returns None) if a comment sits
//! inside the import span, so comments are never reordered.

use leanr_syntax::tree::{SyntaxNode, SyntaxToken};
use leanr_syntax::SyntaxTree;

use crate::comments::has_interior_comment;
use crate::render::tokens_of;

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

/// An import command node is one whose kind name is Lean's module-import
/// command. Verified against an oracle dump (`import Foo`): the node's
/// interned kind name is `Lean.Parser.Module.import`. This also matches
/// `public import Foo` (the module-system modifier prefixes the same
/// command node; the kind name is unchanged).
fn is_import_command(node: &SyntaxNode, tree: &SyntaxTree) -> bool {
    tree.kinds.name(node.kind()) == "Lean.Parser.Module.import"
}

/// The token index whose token starts at byte `offset`. `toks` is in
/// source order, so token start offsets are strictly increasing and a
/// binary search is exact.
fn tok_index_at(toks: &[SyntaxToken], offset: usize) -> Option<usize> {
    let i = toks.partition_point(|t| (u32::from(t.text_range().start()) as usize) < offset);
    (i < toks.len() && u32::from(toks[i].text_range().start()) as usize == offset).then_some(i)
}

/// The `[start, end)` token-index run of one import command: its first
/// through its last significant token, inclusive. The run is never
/// rendered from reconstructed text — only reordered — so any modifier
/// (`public`, …), the `import` keyword itself, and exact intra-import
/// spacing survive reordering untouched.
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

/// The module name a single import command names, e.g. "Foo.Bar". Used
/// ONLY as a sort key — never emitted. Finds the significant token whose
/// text is the `import` keyword and joins the significant tokens after
/// it; falls back to joining all significant tokens if no `import`
/// keyword is found (so a sort key always exists even under unexpected
/// input shapes). The grammar allows an `all` modifier directly after
/// `import` (`import all Foo`, ORACLE-PORT `Lean.Parser.Module.all`); skip
/// it too so it keys as "Foo", not "allFoo" — this only affects sort
/// order, never the emitted text (see `import_run`).
fn import_sort_key(node: &SyntaxNode) -> String {
    let sig: Vec<_> = tokens_of(node)
        .into_iter()
        .filter(|t| !leanr_syntax::kind::is_trivia(t.kind()))
        .collect();
    let kw_idx = sig.iter().position(|t| t.text() == "import");
    let mut rest = match kw_idx {
        Some(i) => &sig[i + 1..],
        None => &sig[..],
    };
    if let Some(first) = rest.first() {
        if first.text() == "all" {
            rest = &rest[1..];
        }
    }
    rest.iter().map(|t| t.text()).collect()
}

/// Detect a reorderable import block. `toks` must be
/// `render::tokens_of(&tree.root())` — the same list the spine emits from.
/// Returns `None` (preserve-fallback) when there are no imports, when a
/// comment sits anywhere in the block, or when any run cannot be located.
pub fn detect(tree: &SyntaxTree, toks: &[SyntaxToken]) -> Option<ImportBlock> {
    // `tok_index_at` locates a token by binary search on start offsets, which
    // is exact only while those offsets strictly increase. That holds for a
    // clean parse (`format_src` rejects anything else), but a zero-width token
    // sharing a start offset would silently shift a run boundary by one, so
    // check the precondition once here rather than assume it.
    debug_assert!(
        toks.windows(2)
            .all(|w| w[0].text_range().start() < w[1].text_range().start()),
        "imports::detect: token start offsets are not strictly increasing, so \
         the binary search in `tok_index_at` cannot locate run boundaries \
         reliably — a zero-width token has entered the token list."
    );
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

// A comment attached as leading trivia to any import after the first lives
// inside the block span and must block reordering.
fn between_import_comment(imports: &[SyntaxNode]) -> bool {
    imports.iter().skip(1).any(|n| {
        tokens_of(n)
            .iter()
            .take_while(|t| leanr_syntax::kind::is_trivia(t.kind()))
            .any(|t| {
                t.kind() == leanr_syntax::kind::KIND_LINE_COMMENT
                    || t.kind() == leanr_syntax::kind::KIND_BLOCK_COMMENT
            })
    })
}

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

    #[test]
    fn leading_comment_before_first_import_preserved() {
        let src = "-- top comment\nimport Foo.B\nimport Foo.A\ndef x := 1\n";
        // The comment sits before the import block's first significant
        // token and must survive verbatim, above the sorted imports.
        assert_eq!(
            fmt(src),
            "-- top comment\nimport Foo.A\nimport Foo.B\ndef x := 1\n"
        );
    }

    #[test]
    fn prelude_header_stays_parseable() {
        let src = "prelude\nimport Foo.B\nimport Foo.A\ndef x := 1\n";
        let formatted = fmt(src);
        // `prelude` must stay on its own line, not get glued to the
        // following import (which would corrupt the token stream).
        assert_eq!(
            formatted,
            "prelude\nimport Foo.A\nimport Foo.B\ndef x := 1\n"
        );
        // Totality guard: the output must re-parse clean.
        let snap = builtin::snapshot();
        let reparsed = parse_module(&formatted, &snap);
        assert!(
            reparsed.errors.is_empty(),
            "formatted output failed to re-parse cleanly: {:?}",
            reparsed.errors
        );
    }

    // REGRESSION (Mathlib corpus gate, Task 5): `public import Foo` is the
    // module-system form real Mathlib package files use. The import rule
    // must preserve the `public` modifier verbatim and sort by module name
    // — not reconstruct `import <name>` from scratch (that dropped `public`
    // and duplicated `import` into the name: `public import Foo.B` used to
    // become `import importFoo.B`).
    #[test]
    fn public_imports_sorted_and_preserved() {
        let src = "public import Foo.B\npublic import Foo.A\n";
        assert_eq!(fmt(src), "public import Foo.A\npublic import Foo.B\n");

        let snap = builtin::snapshot();
        assert!(
            crate::verify::check_invariants(src, &snap).is_ok(),
            "semantics invariant must hold once `public` is preserved"
        );
    }

    // REGRESSION (Task 9 gate-integrity review): `import all Foo` puts the
    // `all` modifier (ORACLE-PORT `Lean.Parser.Module.all`) AFTER `import`
    // and before the module name, so the sort key must skip it too — else
    // `import all Foo` keys as "allFoo" instead of "Foo", sorting it out of
    // module-name order relative to plain imports of the same prefix.
    #[test]
    fn import_all_sorts_by_module_name_not_all_prefix() {
        // Without the fix, `import all Apple` keys as "allApple", which
        // sorts AFTER "Banana" (lowercase 'a' > uppercase 'B' in ASCII) —
        // so this case only passes once the sort key skips `all` and keys
        // by "Apple" instead, sorting it BEFORE "Banana" as expected.
        let src = "import Banana\nimport all Apple\n";
        assert_eq!(fmt(src), "import all Apple\nimport Banana\n");

        let snap = builtin::snapshot();
        assert!(
            crate::verify::check_invariants(src, &snap).is_ok(),
            "semantics invariant must hold for `import all`"
        );
    }

    #[test]
    fn module_header_with_public_imports() {
        let src = "module\n\npublic import Foo.B\npublic import Foo.A\n";
        assert_eq!(
            fmt(src),
            "module\n\npublic import Foo.A\npublic import Foo.B\n"
        );

        let snap = builtin::snapshot();
        assert!(
            crate::verify::check_invariants(src, &snap).is_ok(),
            "semantics invariant must hold once `public` is preserved"
        );
    }
}
