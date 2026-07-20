//! The formatter spine (spec §Rule dispatch + preserve-fallback). Walks
//! the tree's leaf tokens in source order and emits a `Doc`. At this
//! layer every token is emitted verbatim (preserve-fallback); later
//! tasks intercept the import block and whitespace-trivia.

use leanr_syntax::tree::{NodeOrToken, SyntaxNode, SyntaxToken};
use leanr_syntax::SyntaxTree;

use crate::doc::Doc;
use crate::rules::imports;

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
                        Some(s) => s,                                   // single-line near :=/→  -> one space
                        None => crate::trivia::normalize_ws_trivia(ws), // Task 3 fallback
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
