//! Trivia normalization (spec §The first-slice rules, rule 1). Applied
//! PER-TOKEN by kind in the render walk (`render::emit_token_text`), NOT
//! as a whole-output string pass: only genuine whitespace-trivia tokens
//! and the trailing-to-EOL text of line comments are normalized. String
//! literals and block/doc-comment token interiors are emitted verbatim
//! and are NEVER touched, preserving the semantics-preserving and comment
//! invariants (the comment invariant is consumed by `comments.rs`).
//!
//! `finalize` is the only whole-string operation, and only because it
//! provably touches just the trailing whitespace run at EOF.

/// Normalize a whitespace-trivia token. The caller guarantees `text` is a
/// whitespace-trivia token (only space / tab / `\r` / `\n`).
///
/// - No `\n` → returned unchanged (a single-line inter-token gap; the
///   spacing rule, Task 6, owns those).
/// - Otherwise: split on `\n`; every segment BEFORE a newline is
///   line-trailing horizontal whitespace (of a real or blank line) and is
///   DROPPED; the FINAL segment (after the last `\n`) is the following
///   line's indentation and is KEPT verbatim. Blank-line runs collapse to
///   at most 2 newlines (= at most 1 blank line).
///
/// If `\r` were present it would land at the end of a dropped pre-newline
/// segment (i.e. get dropped along with it), but in practice `\r` never
/// reaches this function: the lexer rejects an isolated `\r` as an error
/// token (lex.rs:235-242), so a `KIND_WHITESPACE` token can never contain
/// one, and CRLF source fails to parse before `format_src` ever calls this
/// helper. The `\r`-handling here is defensive only, not a real code path.
pub fn normalize_ws_trivia(text: &str) -> String {
    if !text.contains('\n') {
        // Single-line inter-token gap: leave to the spacing rule.
        return text.to_string();
    }
    let parts: Vec<&str> = text.split('\n').collect();
    let last = *parts.last().unwrap(); // indentation of the following line
    let newlines = parts.len() - 1;
    let kept = newlines.min(2); // 2+ blank lines -> 1 blank line
    let mut out = String::with_capacity(kept + last.len());
    for _ in 0..kept {
        out.push('\n');
    }
    out.push_str(last);
    out
}

/// Whole-output final-newline fixup. SAFE as a whole-string op because it
/// only touches the trailing whitespace run: a significant token never
/// ends in raw unquoted whitespace at EOF (strings end in `"`, block
/// comments in `-/`, idents/atoms in non-whitespace).
///
/// Empty / whitespace-only input → `""`. Non-empty → exactly one trailing
/// `\n`, with any trailing blank lines dropped.
pub fn finalize(s: &str) -> String {
    let trimmed = s.trim_end();
    if trimmed.is_empty() {
        String::new()
    } else {
        format!("{trimmed}\n")
    }
}

#[cfg(test)]
mod tests {
    use super::{finalize, normalize_ws_trivia};

    #[test]
    fn ws_no_newline_passthrough() {
        assert_eq!(normalize_ws_trivia("   "), "   ");
    }

    #[test]
    fn ws_strips_pre_newline_hspace() {
        assert_eq!(normalize_ws_trivia("  \n"), "\n");
    }

    #[test]
    fn ws_preserves_indentation() {
        assert_eq!(normalize_ws_trivia("   \n  "), "\n  ");
    }

    #[test]
    fn ws_collapses_blank_runs() {
        assert_eq!(normalize_ws_trivia("\n\n\n\n"), "\n\n");
    }

    // Defensive-only coverage: the lexer rejects an isolated `\r` as an
    // error token, so a KIND_WHITESPACE token can never actually contain
    // `\r\n` in the real pipeline (CRLF source fails to parse before this
    // helper is ever called). This test exercises the helper directly,
    // bypassing the lexer, to pin the defensive behavior.
    #[test]
    fn ws_crlf_becomes_lf_when_called_directly_bypassing_lexer() {
        assert_eq!(normalize_ws_trivia("\r\n"), "\n");
    }

    #[test]
    fn finalize_ensures_single_trailing_newline() {
        assert_eq!(finalize("a"), "a\n");
    }

    #[test]
    fn finalize_drops_trailing_blank_lines() {
        assert_eq!(finalize("a\n\n\n"), "a\n");
    }

    #[test]
    fn finalize_empty_stays_empty() {
        assert_eq!(finalize(""), "");
    }

    #[test]
    fn finalize_whitespace_only_stays_empty() {
        assert_eq!(finalize("   "), "");
    }
}
