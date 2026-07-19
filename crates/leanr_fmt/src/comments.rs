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
