//! The formatter spine (spec §Rule dispatch + preserve-fallback). Walks
//! the tree's leaf tokens in source order and emits a `Doc`. At this
//! layer every token is emitted verbatim (preserve-fallback); later
//! tasks intercept the import block and whitespace-trivia.

use leanr_syntax::tree::{NodeOrToken, SyntaxNode, SyntaxToken};
use leanr_syntax::SyntaxTree;

use crate::doc::Doc;
use crate::rules::imports;

/// The formatter spine. Imports are the ONLY reordered content in this
/// slice: when `imports::detect` finds a contiguous import block, emit
/// everything before it verbatim (raw source slice), the sorted imports
/// (each import's ORIGINAL source text, verbatim — including any
/// `public`/modifier prefix and the `import` keyword itself — one per
/// line, reordered by module name only), then everything after it
/// verbatim. Otherwise (no imports, or a comment inside the import span)
/// fall back to the token-aware verbatim walk (`render_tokens`),
/// byte-identical to the pre-import-rule behavior.
pub fn render_verbatim(tree: &SyntaxTree) -> Doc {
    match imports::detect(tree) {
        Some(block) => {
            let src = tree.text();
            let joined = block.sorted.join("\n");
            Doc::concat(vec![
                Doc::text(src[..block.start].to_string()),
                Doc::text(joined),
                Doc::text(src[block.end..].to_string()),
            ])
        }
        None => render_tokens(tree),
    }
}

/// Every leaf token in source order, with each token's emitted text
/// chosen by KIND (see `emit_token_text`). Whitespace-trivia is routed
/// through the spacing rule first (`rules::spacing::normalize_ws`): for a
/// single-line gap adjacent to a target operator (`:=`, `→`) spacing wins
/// and normalizes it to one space; every other whitespace-trivia case
/// (multi-line, or single-line but not near a target) falls back to
/// `trivia::normalize_ws_trivia` (Task 3's indentation/blank-run
/// handling and single-line passthrough). Line comments and every other
/// token — including string literals and block/doc comments — are
/// emitted verbatim/trimmed exactly as before (`emit_token_text`). This
/// is the no-imports path; its behavior must stay byte-identical to the
/// earlier spine for everything spacing does not touch.
fn render_tokens(tree: &SyntaxTree) -> Doc {
    use leanr_syntax::kind::{is_trivia, KIND_WHITESPACE};
    let toks = tokens_of(&tree.root());
    let mut parts = Vec::with_capacity(toks.len());
    for (i, t) in toks.iter().enumerate() {
        if t.kind() == KIND_WHITESPACE {
            let prev = toks[..i]
                .iter()
                .rev()
                .find(|p| !is_trivia(p.kind()))
                .map(|p| p.text());
            let next = toks[i + 1..]
                .iter()
                .find(|p| !is_trivia(p.kind()))
                .map(|p| p.text());
            let ws = t.text();
            let out = match crate::rules::spacing::normalize_ws(prev, ws, next) {
                Some(s) => s,                                   // single-line near :=/→  -> one space
                None => crate::trivia::normalize_ws_trivia(ws), // Task 3 fallback
            };
            parts.push(Doc::text(out));
        } else {
            parts.push(Doc::text(emit_token_text(t)));
        }
    }
    Doc::concat(parts)
}

/// Choose a NON-whitespace token's emitted text by KIND. `render_tokens`
/// handles `KIND_WHITESPACE` itself (spacing rule, then `normalize_ws_trivia`
/// fallback) before it ever reaches here, so this function never sees that
/// kind. No reliance on byte-offset alignment, so it composes with later
/// reordering/spacing tasks.
///
/// - Line comment → `trim_end` (a Lean line comment runs to EOL, so its
///   trailing whitespace is genuinely trailing and the comment invariant
///   compares modulo trailing whitespace).
/// - Everything else (STRING literals, BLOCK/DOC comments, idents,
///   atoms, …) → emitted verbatim, byte-for-byte. NEVER trimmed.
fn emit_token_text(t: &SyntaxToken) -> String {
    use leanr_syntax::kind::KIND_LINE_COMMENT;
    let k = t.kind();
    if k == KIND_LINE_COMMENT {
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
        // `:=` already single-spaced on both sides, so none of the wired
        // rules (imports/trivia/spacing) change anything here; `def  x`'s
        // 2-space gap is untouched too (not adjacent to a target operator).
        // This pins byte-identical passthrough for content no rule touches
        // (Task 6 added a fixture-collision hazard here: an earlier draft
        // of this fixture had `:=   1`, which the spacing rule now
        // legitimately collapses — see `single_line_assign_spacing_normalized`
        // for that behavior).
        let src = "namespace Foo\ndef  x := 1\nend Foo\n";
        let snap = builtin::snapshot();
        let tree = parse_module(src, &snap).tree;
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

    // Task 6: single-line whitespace adjacent to `:=` collapses to one space.
    #[test]
    fn single_line_assign_spacing_normalized() {
        let src = "def x :=   1\n";
        let snap = leanr_syntax::builtin::snapshot();
        let tree = leanr_syntax::parse_module(src, &snap).tree;
        assert_eq!(crate::format_tree(&tree), "def x := 1\n");
    }

    // Task 6 idempotence: already single-spaced stays single-spaced.
    #[test]
    fn already_single_spaced_assign_stays_single_spaced() {
        assert_eq!(fmt("def x := 1\n"), "def x := 1\n");
    }

    // Task 6 guard: multi-line whitespace near `:=` must NOT be collapsed
    // by the spacing rule — it must still route to `normalize_ws_trivia`
    // (proves the bail-to-trivia composition, not a regression of Task 3).
    #[test]
    fn multiline_ws_near_assign_not_collapsed() {
        assert_eq!(fmt("def x :=\n  1\n"), "def x :=\n  1\n");
    }

    // Task 6 guard: a line comment adjacent to a spacing-affected region
    // still keeps its terminating newline (Task 3's line-comment handling
    // is untouched by the spacing branch).
    #[test]
    fn line_comment_near_spacing_change_keeps_newline() {
        assert_eq!(
            fmt("def x :=   1 -- note   \ndef y := 2\n"),
            "def x := 1 -- note\ndef y := 2\n"
        );
    }
}
