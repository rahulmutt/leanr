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
/// command. Verified against an oracle dump (`import Foo`): the node's
/// interned kind name is `Lean.Parser.Module.import`. This also matches
/// `public import Foo` (the module-system modifier prefixes the same
/// command node; the kind name is unchanged).
fn is_import_command(node: &SyntaxNode, tree: &SyntaxTree) -> bool {
    tree.kinds.name(node.kind()) == "Lean.Parser.Module.import"
}

/// The full original source text of a single import command, spanning its
/// first significant token through its last significant token. This is
/// what gets EMITTED — verbatim, byte-for-byte — so any modifier
/// (`public`, …), the `import` keyword itself, and exact intra-import
/// spacing survive reordering untouched.
fn import_original_text<'a>(node: &SyntaxNode, src: &'a str) -> &'a str {
    let toks = tokens_of(node);
    let sig: Vec<_> = toks
        .iter()
        .filter(|t| !leanr_syntax::kind::is_trivia(t.kind()))
        .collect();
    let start = sig
        .first()
        .map(|t| u32::from(t.text_range().start()) as usize)
        .unwrap_or_else(|| u32::from(node.text_range().start()) as usize);
    let end = sig
        .last()
        .map(|t| u32::from(t.text_range().end()) as usize)
        .unwrap_or_else(|| u32::from(node.text_range().end()) as usize);
    &src[start..end]
}

/// The module name a single import command names, e.g. "Foo.Bar". Used
/// ONLY as a sort key — never emitted. Finds the significant token whose
/// text is the `import` keyword and joins the significant tokens after
/// it; falls back to joining all significant tokens if no `import`
/// keyword is found (so a sort key always exists even under unexpected
/// input shapes).
fn import_sort_key(node: &SyntaxNode) -> String {
    let sig: Vec<_> = tokens_of(node)
        .into_iter()
        .filter(|t| !leanr_syntax::kind::is_trivia(t.kind()))
        .collect();
    let kw_idx = sig.iter().position(|t| t.text() == "import");
    let rest = match kw_idx {
        Some(i) => &sig[i + 1..],
        None => &sig[..],
    };
    rest.iter().map(|t| t.text()).collect()
}

pub fn detect(tree: &SyntaxTree) -> Option<ImportBlock> {
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
    // `text_range()` on a node includes its leading trivia (comments,
    // blank lines, a preceding `prelude`'s trailing newline). Anchoring
    // `start` there would delete that trivia when the caller replaces
    // `src[start..end]` with the sorted block. Anchor instead to the
    // first import's first SIGNIFICANT token (the `import` keyword), so
    // `src[..start]` retains all leading trivia verbatim.
    let first = imports.first().unwrap();
    let start = tokens_of(first)
        .iter()
        .find(|t| !leanr_syntax::kind::is_trivia(t.kind()))
        .map(|t| u32::from(t.text_range().start()) as usize)
        .unwrap_or_else(|| u32::from(first.text_range().start()) as usize);
    // `end` is left as-is: trailing trivia after the last import attaches
    // as LEADING trivia of the following node, so the last import's own
    // `text_range().end()` already stops cleanly at its last token.
    let end = u32::from(imports.last().unwrap().text_range().end()) as usize;
    // If any import command carries an interior comment, or a comment sits
    // between imports, preserve the block verbatim. `has_interior_comment`
    // covers comments between an import's own significant tokens; a
    // between-imports comment is the leading trivia of a later import's
    // first token, caught by `between_import_comment`.
    if imports.iter().any(has_interior_comment) || between_import_comment(&imports) {
        return None;
    }
    let src = tree.text();
    let mut keyed: Vec<(String, &str)> = imports
        .iter()
        .map(|n| (import_sort_key(n), import_original_text(n, &src)))
        .collect();
    keyed.sort_by(|a, b| a.0.cmp(&b.0));
    let sorted: Vec<String> = keyed
        .into_iter()
        .map(|(_, text)| text.to_string())
        .collect();
    Some(ImportBlock { start, end, sorted })
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
