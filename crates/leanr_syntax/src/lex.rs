//! Table-driven tokenizer (spec §Architecture / lex). Lean has NO static
//! token set: `notation` commands add tokens, and tokenization is
//! maximal-munch against the CURRENT token table — so `next_token` is a
//! pure function of (source, position, table), called per-token as the
//! parser advances. ORACLE-PORT: Lean/Parser/Basic.lean (`whitespace`,
//! `finishCommentBlock`, token munch). Totality: on ANY byte sequence
//! the lexer returns a token with len ≥ 1 (except Eof) and never panics.

use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Whitespace,
    LineComment,
    BlockComment,
    /// Keyword or symbol from the token table.
    Atom,
    Ident,
    /// Natural-number literal (incl. 0x/0b/0o).
    Num,
    /// Decimal/scientific literal (`2.5`, `1e-3`).
    Scientific,
    /// String literal, incl. raw `r"…"`/`r#"…"#` forms.
    Str,
    Char,
    /// Name literal: `` `foo `` / ``` ``foo ```.
    NameLit,
    /// Unlexable byte run — untrusted-input totality.
    ErrorTok,
    Eof,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub len: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexError {
    pub code: &'static str,
    pub msg: String,
}

/// The dynamic token set. `max_len` bounds the munch scan.
#[derive(Clone, Debug, Default)]
pub struct TokenTable {
    toks: BTreeSet<String>,
    max_len: usize,
}

impl TokenTable {
    pub fn insert(&mut self, tok: &str) {
        self.max_len = self.max_len.max(tok.len());
        self.toks.insert(tok.to_string());
    }

    pub fn contains(&self, tok: &str) -> bool {
        self.toks.contains(tok)
    }

    pub fn iter(&self) -> impl Iterator<Item = &str> {
        self.toks.iter().map(|s| s.as_str())
    }

    /// Longest table entry that prefixes `rest` (maximal munch).
    pub fn munch<'a>(&self, rest: &'a str) -> Option<&'a str> {
        let mut best = None;
        for (i, c) in rest.char_indices() {
            let end = i + c.len_utf8();
            if end > self.max_len {
                break;
            }
            if self.toks.contains(&rest[..end]) {
                best = Some(&rest[..end]);
            }
        }
        best
    }
}

fn tok(kind: TokenKind, len: usize) -> (Token, Option<LexError>) {
    (
        Token {
            kind,
            len: len as u32,
        },
        None,
    )
}

fn tok_err(
    kind: TokenKind,
    len: usize,
    code: &'static str,
    msg: impl Into<String>,
) -> (Token, Option<LexError>) {
    (
        Token {
            kind,
            len: len as u32,
        },
        Some(LexError {
            code,
            msg: msg.into(),
        }),
    )
}

/// ORACLE-PORT `Lean/Parser/Basic.lean`, `whitespace`: the chars accepted
/// as ordinary whitespace are exactly those for which `Char.isWhitespace`
/// holds (`Init/Data/Char/Basic.lean`: `' ' || '\t' || '\r' || '\n'`) MINUS
/// `'\t'`/`'\r'`, which `whitespace` special-cases as errors *before* the
/// `isWhitespace` check (see below). So the effective accepted set is just
/// `{' ', '\n'}` — NOT Rust's `char::is_whitespace` (which additionally
/// accepts tab, CR, and various Unicode spaces like NBSP/EM SPACE; Lean
/// accepts none of those as trivia).
fn is_lean_whitespace(c: char) -> bool {
    c == ' ' || c == '\n'
}

/// Lex one token at `pos`. Trivia (whitespace/comments) are returned as
/// ordinary tokens; the parser loops. Returns Eof (len 0) at end.
pub fn next_token(src: &str, pos: usize, table: &TokenTable) -> (Token, Option<LexError>) {
    let rest = &src[pos..];
    let mut chars = rest.chars();
    let Some(c) = chars.next() else {
        return tok(TokenKind::Eof, 0);
    };

    // --- trivia ---------------------------------------------------
    // ORACLE-PORT `whitespace`: checks `'\t'` and `'\r'` FIRST (both are
    // errors, not whitespace — Lean forbids tabs and lone/CRLF carriage
    // returns in source text), then `curr.isWhitespace` for the rest. We
    // surface these as single-byte ErrorTok + a stable-coded LexError:
    // Lean's own `mkUnexpectedError (pushMissing := false)` leaves the
    // parser position UNCHANGED (i.e. it doesn't actually terminate — a
    // caller must special-case the error), which would violate our
    // totality rule (every call must consume ≥1 byte); consuming the
    // single offending byte here is the deliberate, documented divergence
    // that keeps `next_token` total while preserving "not treated as
    // whitespace, and it's an error" behavior.
    if c == '\t' {
        return tok_err(
            TokenKind::ErrorTok,
            1,
            "E0307",
            "tabs are not allowed; please configure your editor to expand them",
        );
    }
    if c == '\r' {
        return tok_err(
            TokenKind::ErrorTok,
            1,
            "E0308",
            "isolated carriage returns are not allowed",
        );
    }
    if is_lean_whitespace(c) {
        let end = rest
            .char_indices()
            .find(|&(_, c)| !is_lean_whitespace(c))
            .map(|(i, _)| i)
            .unwrap_or(rest.len());
        return tok(TokenKind::Whitespace, end);
    }
    if rest.starts_with("--") {
        // ORACLE-PORT Basic.lean whitespace: `--` runs to end of line.
        // The newline is included in the trivia token (leading-trivia
        // attachment is ours; byte-losslessness is what matters).
        let end = rest.find('\n').map(|i| i + 1).unwrap_or(rest.len());
        return tok(TokenKind::LineComment, end);
    }
    if rest.starts_with("/-") && !rest.starts_with("/--") && !rest.starts_with("/-!") {
        // Nested block comment. `/--`/`/-!` open DOC comments — tokens,
        // not trivia (they reach the munch below via the table).
        return match block_comment_end(rest) {
            Some(end) => tok(TokenKind::BlockComment, end),
            None => (
                Token {
                    kind: TokenKind::BlockComment,
                    len: rest.len() as u32,
                },
                Some(LexError {
                    code: "E0303",
                    msg: "unterminated block comment".to_string(),
                }),
            ),
        };
    }

    // --- table munch (symbols, keywords-as-symbols) ----------------
    // Idents/literals are handled in Task 3; munch result competes with
    // them by length there. For now: munch, else single-char ErrorTok.
    if let Some(m) = table.munch(rest) {
        return tok(TokenKind::Atom, m.len());
    }
    tok(TokenKind::ErrorTok, c.len_utf8())
}

/// Byte offset just past the matching `-/`, honoring nesting.
fn block_comment_end(rest: &str) -> Option<usize> {
    debug_assert!(rest.starts_with("/-"));
    let bytes = rest.as_bytes();
    let mut depth = 1usize;
    let mut i = 2;
    while i < bytes.len() {
        if bytes[i..].starts_with(b"/-") {
            depth += 1;
            i += 2;
        } else if bytes[i..].starts_with(b"-/") {
            depth -= 1;
            i += 2;
            if depth == 0 {
                return Some(i);
            }
        } else {
            // Advance one UTF-8 char (never split a code point).
            i += 1;
            while i < bytes.len() && (bytes[i] & 0xC0) == 0x80 {
                i += 1;
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_all<'a>(src: &'a str, table: &TokenTable) -> Vec<(TokenKind, &'a str)> {
        let mut out = Vec::new();
        let mut pos = 0;
        loop {
            let (tok, _err) = next_token(src, pos, table);
            if tok.kind == TokenKind::Eof {
                break;
            }
            out.push((tok.kind, &src[pos..pos + tok.len as usize]));
            pos += tok.len as usize;
            assert!(tok.len > 0, "lexer must always make progress");
        }
        out
    }

    #[test]
    fn maximal_munch_prefers_the_longest_table_entry() {
        let mut t = TokenTable::default();
        t.insert(":");
        t.insert(":=");
        t.insert("=");
        t.insert("=>");
        assert_eq!(
            lex_all(":= = => :", &t),
            vec![
                (TokenKind::Atom, ":="),
                (TokenKind::Whitespace, " "),
                (TokenKind::Atom, "="),
                (TokenKind::Whitespace, " "),
                (TokenKind::Atom, "=>"),
                (TokenKind::Whitespace, " "),
                (TokenKind::Atom, ":"),
            ]
        );
    }

    #[test]
    fn line_comments_run_to_newline_exclusive_of_nothing() {
        let t = TokenTable::default();
        let toks = lex_all("-- hi\n", &t);
        assert_eq!(toks[0], (TokenKind::LineComment, "-- hi\n"));
    }

    #[test]
    fn block_comments_nest() {
        let t = TokenTable::default();
        let toks = lex_all("/- a /- b -/ c -/x", &t);
        assert_eq!(toks[0], (TokenKind::BlockComment, "/- a /- b -/ c -/"));
    }

    #[test]
    fn doc_comments_are_not_trivia() {
        // `/--` and `/-!` open DOC comments — tokens, not trivia
        // (Lean: whitespace's block-comment case explicitly excludes
        // a following '-' or '!'). With "/--" in the table they lex as
        // atoms; the docComment parser (Task 10) consumes the body.
        let mut t = TokenTable::default();
        t.insert("/--");
        let toks = lex_all("/-- doc -/", &t);
        assert_eq!(toks[0], (TokenKind::Atom, "/--"));
    }

    #[test]
    fn unterminated_block_comment_is_an_error_not_a_hang() {
        let t = TokenTable::default();
        let (tok, err) = next_token("/- never closed", 0, &t);
        assert_eq!(tok.kind, TokenKind::BlockComment);
        assert_eq!(tok.len as usize, "/- never closed".len());
        assert_eq!(err.unwrap().code, "E0303");
    }

    #[test]
    fn unlexable_bytes_become_error_tokens_and_progress() {
        // No table entries: a stray symbol byte can't match anything.
        let t = TokenTable::default();
        let toks = lex_all("⊕", &t);
        assert_eq!(toks[0].0, TokenKind::ErrorTok);
    }

    // --- ORACLE-PORT divergence checks (Step 5) --------------------
    // Lean's `whitespace` special-cases '\t' and '\r' as errors BEFORE
    // the general `isWhitespace` check — they are never treated as
    // trivia, unlike Rust's `char::is_whitespace`.

    #[test]
    fn tabs_are_rejected_not_treated_as_whitespace() {
        let t = TokenTable::default();
        let (tok, err) = next_token("\tx", 0, &t);
        assert_eq!(tok.kind, TokenKind::ErrorTok);
        assert_eq!(tok.len, 1);
        assert_eq!(err.unwrap().code, "E0307");
    }

    #[test]
    fn isolated_carriage_returns_are_rejected_not_treated_as_whitespace() {
        let t = TokenTable::default();
        // Even as part of a CRLF pair: Lean's whitespace() checks '\r'
        // unconditionally, with no lookahead for a following '\n'.
        let (tok, err) = next_token("\r\nx", 0, &t);
        assert_eq!(tok.kind, TokenKind::ErrorTok);
        assert_eq!(tok.len, 1);
        assert_eq!(err.unwrap().code, "E0308");
    }

    #[test]
    fn whitespace_run_stops_before_a_tab() {
        let t = TokenTable::default();
        let (tok, err) = next_token(" \tx", 0, &t);
        assert_eq!(tok.kind, TokenKind::Whitespace);
        assert_eq!(tok.len, 1);
        assert!(err.is_none());
    }

    #[test]
    fn other_unicode_space_characters_are_not_lean_whitespace() {
        // U+00A0 NO-BREAK SPACE is Unicode-whitespace (Rust's
        // `char::is_whitespace` accepts it) but is NOT one of the four
        // chars `Char.isWhitespace` recognizes in the oracle, so it must
        // NOT be treated as trivia here.
        let t = TokenTable::default();
        let (tok, _err) = next_token("\u{00A0}x", 0, &t);
        assert_ne!(tok.kind, TokenKind::Whitespace);
    }
}
