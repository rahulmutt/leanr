//! Self-consistency checks (spec §Acceptance harness). Shared by the
//! hermetic fixture tests and the Mathlib corpus sweep.

use leanr_syntax::kind::{KIND_BLOCK_COMMENT, KIND_LINE_COMMENT};
use leanr_syntax::tree::NodeOrToken;
use leanr_syntax::SyntaxTree;

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
