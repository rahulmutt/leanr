//! The formatter spine (spec §Rule dispatch + preserve-fallback). Walks
//! the tree's leaf tokens in source order and emits a `Doc`. At this
//! layer every token is emitted verbatim (preserve-fallback); later
//! tasks intercept the import block and whitespace-trivia.

use leanr_syntax::tree::{NodeOrToken, SyntaxNode, SyntaxToken};
use leanr_syntax::SyntaxTree;

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

/// Leaf tokens of a subtree in source order (shared by later rules — no
/// caller yet at this task, hence `allow(dead_code)`; the import-block
/// and whitespace-trivia rules land in later M3c tasks).
#[allow(dead_code)]
pub(crate) fn tokens_of(node: &SyntaxNode) -> Vec<SyntaxToken> {
    node.descendants_with_tokens()
        .filter_map(|el| match el {
            NodeOrToken::Token(t) => Some(t),
            NodeOrToken::Node(_) => None,
        })
        .collect()
}

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
        assert!(matches!(err, crate::FormatError::Unparseable(_)));
    }
}
