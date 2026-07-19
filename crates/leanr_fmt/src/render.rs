//! The formatter spine (spec §Rule dispatch + preserve-fallback). Walks
//! the tree's leaf tokens in source order and emits a `Doc`. At this
//! layer every token is emitted verbatim (preserve-fallback); later
//! tasks intercept the import block and whitespace-trivia.

use leanr_syntax::tree::{NodeOrToken, SyntaxNode, SyntaxToken};
use leanr_syntax::SyntaxTree;

use crate::doc::Doc;

/// Every leaf token in source order, with each token's emitted text
/// chosen by KIND (see `emit_token_text`). Whitespace-trivia and line
/// comments are normalized; every other token — including string literals
/// and block/doc comments — is emitted verbatim.
pub fn render_verbatim(tree: &SyntaxTree) -> Doc {
    let mut parts = Vec::new();
    for el in tree.root().descendants_with_tokens() {
        if let NodeOrToken::Token(t) = el {
            parts.push(Doc::text(emit_token_text(&t)));
        }
    }
    Doc::concat(parts)
}

/// Choose a token's emitted text by KIND. No reliance on byte-offset
/// alignment, so it composes with later reordering/spacing tasks.
///
/// - Whitespace trivia → `normalize_ws_trivia`.
/// - Line comment → `trim_end` (a Lean line comment runs to EOL, so its
///   trailing whitespace is genuinely trailing and the comment invariant
///   compares modulo trailing whitespace).
/// - Everything else (STRING literals, BLOCK/DOC comments, idents,
///   atoms, …) → emitted verbatim, byte-for-byte. NEVER trimmed.
fn emit_token_text(t: &SyntaxToken) -> String {
    use leanr_syntax::kind::{KIND_LINE_COMMENT, KIND_WHITESPACE};
    let k = t.kind();
    if k == KIND_WHITESPACE {
        crate::trivia::normalize_ws_trivia(t.text())
    } else if k == KIND_LINE_COMMENT {
        // The lexer folds the trailing newline INTO the line-comment token
        // (a line comment runs to EOL inclusive). Strip only trailing horizontal
        // whitespace; preserve the terminating newline (the line separator).
        // A line comment holds at most one '\n', always at the very end.
        let s = t.text();
        let trimmed = s.trim_end();
        if s.ends_with('\n') {
            format!("{trimmed}\n")
        } else {
            trimmed.to_string()
        }
    } else {
        t.text().to_string()
    }
}

/// Leaf tokens of a subtree in source order (shared by later rules; used
/// by `comments::has_interior_comment` and the import-block and
/// whitespace-trivia rules landing in later M3c tasks).
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

    fn fmt(src: &str) -> String {
        let tree = parse_module(src, &builtin::snapshot()).tree;
        crate::format_tree(&tree)
    }

    #[test]
    fn strips_trailing_ws_after_line_comment() {
        assert_eq!(fmt("def x := 1   \n-- note   \n"), "def x := 1\n-- note\n");
    }

    #[test]
    fn collapses_blank_line_runs_to_one() {
        assert_eq!(
            fmt("def x := 1\n\n\n\ndef y := 2\n"),
            "def x := 1\n\ndef y := 2\n"
        );
    }

    #[test]
    fn is_idempotent() {
        let messy = "def x := 1  \n\n\n\ndef y := 2 -- x  \n\n";
        let once = fmt(messy);
        assert_eq!(fmt(&once), once);
    }

    // REGRESSION: a multi-line STRING literal's interior trailing spaces
    // MUST survive byte-for-byte. Uses a plain string with an embedded
    // real newline — this grammar's string lexer terminates only on `"`,
    // so `"a   \nb"` is a single token that parses clean (verified).
    #[test]
    fn preserves_multiline_string_interior_ws() {
        let out = fmt("def s := \"a   \nb\"\n");
        assert!(
            out.contains("a   \nb"),
            "string interior ws corrupted: {out:?}"
        );
    }

    // REGRESSION: a multi-line BLOCK comment's interior trailing spaces
    // MUST survive byte-for-byte. Leading standalone block comment.
    #[test]
    fn preserves_multiline_block_comment_interior_ws() {
        let out = fmt("/- a   \n b -/\ndef x := 1\n");
        assert!(
            out.contains("a   \n b"),
            "block comment interior ws corrupted: {out:?}"
        );
    }

    // REGRESSION: the lexer folds the trailing newline INTO a line-comment
    // token (a line comment runs to EOL inclusive). `emit_token_text` must
    // preserve that newline — trimming only trailing horizontal whitespace —
    // or the following declaration gets glued onto the comment line.
    #[test]
    fn mid_file_line_comment_preserves_following_code() {
        let snap = leanr_syntax::builtin::snapshot();
        let tree = leanr_syntax::parse_module("def x := 1\n-- note   \ndef y := 2\n", &snap).tree;
        assert_eq!(
            crate::format_tree(&tree),
            "def x := 1\n-- note\ndef y := 2\n"
        );
    }
}
