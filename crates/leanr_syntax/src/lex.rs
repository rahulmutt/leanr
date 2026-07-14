//! Table-driven tokenizer (spec §Architecture / lex). Lean has NO static
//! token set: `notation` commands add tokens, and tokenization is
//! maximal-munch against the CURRENT token table — so `next_token` is a
//! pure function of (source, position, table), called per-token as the
//! parser advances. ORACLE-PORT: Lean/Parser/Basic.lean (`whitespace`,
//! `finishCommentBlock`, token munch). Totality: on ANY byte sequence
//! the lexer returns a token with len ≥ 1 (except Eof) and never panics.

use std::collections::BTreeSet;

/// ORACLE-PORT `Init/Meta/Defs.lean:101` (v4.32.0-rc1) — verbatim ranges.
pub fn is_letter_like(c: char) -> bool {
    let v = c as u32;
    (0x3b1..=0x3c9).contains(&v) && v != 0x3bb                    // lower Greek, not λ
        || (0x391..=0x3A9).contains(&v) && v != 0x3A0 && v != 0x3A3 // upper Greek, not Π Σ
        || (0x3ca..=0x3fb).contains(&v)                            // Coptic
        || (0x1f00..=0x1ffe).contains(&v)                          // polytonic Greek
        || (0x2100..=0x214f).contains(&v)                          // letterlike block
        || (0x1d49c..=0x1d59f).contains(&v)                        // script/fraktur/double-struck
        || (0x00c0..=0x00ff).contains(&v) && v != 0x00d7 && v != 0x00f7 // Latin-1, not × ÷
        || (0x0100..=0x017f).contains(&v) // Latin Extended-A
}

/// ORACLE-PORT `Init/Meta/Defs.lean:114`.
fn is_subscript_alnum(c: char) -> bool {
    let v = c as u32;
    (0x2080..=0x2089).contains(&v)      // isNumericSubscript ₀-₉
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
        || v == 0x2c7c
}

/// ORACLE-PORT `Init/Meta/Defs.lean:120`: `isIdFirst c = c.isAlpha || c ==
/// '_' || isLetterLike c`. Checked against the pinned toolchain source:
/// `Char.isAlpha` (`Init/Data/Char/Basic.lean:121`) is `isUpper ||
/// isLower`, both **ASCII-only** range checks — NOT Rust's
/// `char::is_alphabetic` (which is Unicode-aware and would accept e.g.
/// Cyrillic/CJK/Devanagari as identifier starts, none of which Lean
/// accepts). So this is `is_ascii_alphabetic`, not `is_alphabetic`.
pub fn is_id_first(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || is_letter_like(c)
}

/// ORACLE-PORT `Init/Meta/Defs.lean:133`: `isIdRest c = c.isAlphanum ||
/// c=='_' || c=='\'' || c=='!' || c=='?' || isLetterLike c ||
/// isSubScriptAlnum c`. `Char.isAlphanum = isAlpha || isDigit`
/// (`Init/Data/Char/Basic.lean:146`), both ASCII-only — same divergence
/// as `is_id_first`: `is_ascii_alphanumeric`, not `is_alphanumeric`.
/// Note `!` and `?` ARE idRest in this pin.
pub fn is_id_rest(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || c == '_'
        || c == '\''
        || c == '!'
        || c == '?'
        || is_letter_like(c)
        || is_subscript_alnum(c)
}

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

    // --- idents & literals ------------------------------------------
    // ORACLE-PORT `tokenFnAux` (Basic.lean:1027): dispatch order is
    // `"` → string, `'` (guarded) → char, digit → number, `` ` ``
    // (guarded) → name literal, `r` (guarded) → raw string, else →
    // ident/symbol. Each of the first four takes UNCONDITIONAL priority
    // over any token-table match — there is no munch competition for
    // them, only for the final ident-vs-symbol case (`isToken`/
    // `mkIdResult`, ported below as the `munched`-vs-`len` compare).
    let munched = table.munch(rest).map(str::len).unwrap_or(0);

    if c == '"' {
        return match string_lit_len(rest) {
            Ok(len) => tok(TokenKind::Str, len),
            Err(e) => (
                Token {
                    kind: TokenKind::Str,
                    len: e.0 as u32,
                },
                Some(e.1),
            ),
        };
    }
    if c == '\'' {
        if let Some(len) = char_lit_len(rest) {
            return tok(TokenKind::Char, len);
        }
        // Disambiguation guard failed (e.g. `''`) or no closing quote:
        // fall through — a bare `'` may be a table symbol.
    }
    if c.is_ascii_digit() {
        let (len, kind) = number_len(rest);
        return tok(kind, len);
    }
    if c == '`' {
        match name_lit_len(rest) {
            Some(Ok(len)) => return tok(TokenKind::NameLit, len),
            Some(Err((elen, err))) => {
                return (
                    Token {
                        kind: TokenKind::NameLit,
                        len: elen as u32,
                    },
                    Some(err),
                );
            }
            None => {}
        }
    }
    if c == 'r' {
        match raw_string_len(rest) {
            RawStr::Ok(len) => return tok(TokenKind::Str, len),
            RawStr::Unterminated => {
                return (
                    Token {
                        kind: TokenKind::Str,
                        len: rest.len() as u32,
                    },
                    Some(LexError {
                        code: "E0302",
                        msg: "unterminated raw string literal".to_string(),
                    }),
                );
            }
            RawStr::NotRaw => {} // plain ident starting with `r`
        }
    }
    if is_id_first(c) || c == '«' {
        match ident_len(rest) {
            Ok(len) => {
                // Munch competition (ORACLE-PORT `isToken`/`mkIdResult`):
                // a token-table match at least as long as the ident wins
                // (ident-shaped keyword lexes as `Atom`); a strictly
                // longer symbol match also wins even when it isn't
                // itself an exact ident boundary.
                if munched > len {
                    return tok(TokenKind::Atom, munched);
                }
                if table.contains(&rest[..len]) {
                    return tok(TokenKind::Atom, len); // ident-shaped keyword
                }
                return tok(TokenKind::Ident, len);
            }
            Err(e) => {
                return (
                    Token {
                        kind: TokenKind::ErrorTok,
                        len: e.0 as u32,
                    },
                    Some(e.1),
                );
            }
        }
    }
    if munched > 0 {
        return tok(TokenKind::Atom, munched);
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

type LexFail = (usize, LexError);

/// Length of a hierarchical identifier at the start of `rest`:
/// `part ('.' part)*` where `part = idFirst idRest* | «…»`. The dot
/// continues ONLY if followed by another part start. ORACLE-PORT
/// `Basic.lean` `identFnAux` / `isIdCont`.
fn ident_len(rest: &str) -> Result<usize, LexFail> {
    let mut i = 0;
    loop {
        i += ident_part_len(&rest[i..], i)?;
        let after = &rest[i..];
        let mut it = after.chars();
        if it.next() == Some('.') {
            if let Some(c2) = it.next() {
                if is_id_first(c2) || c2 == '«' {
                    i += 1; // consume '.' and loop for the next part
                    continue;
                }
            }
        }
        return Ok(i);
    }
}

fn ident_part_len(rest: &str, base: usize) -> Result<usize, LexFail> {
    let mut chars = rest.char_indices();
    let (_, c) = chars.next().expect("caller checked non-empty");
    if c == '«' {
        // Escaped part: everything to the matching '»' (no nesting —
        // ORACLE-PORT `takeUntilFn isIdEndEscape`, a flat scan).
        for (i, c2) in chars {
            if c2 == '»' {
                return Ok(i + '»'.len_utf8());
            }
        }
        return Err((
            base + rest.len(),
            LexError {
                code: "E0306",
                msg: "unterminated «identifier escape".into(),
            },
        ));
    }
    debug_assert!(is_id_first(c));
    let end = rest
        .char_indices()
        .skip(1)
        .find(|&(_, c)| !is_id_rest(c))
        .map(|(i, _)| i)
        .unwrap_or(rest.len());
    Ok(end)
}

/// ORACLE-PORT `Basic.lean` `numberFnAux`/`decimalNumberFn`: `0x`/`0X`
/// hex, `0b`/`0B` bin, `0o`/`0O` octal, else decimal; decimal may
/// continue `.digits` and/or `[eE][+-]?digits` → `Scientific`. Digit
/// runs may contain `_` separators (`takeDigitsFn`), e.g. `1_000_000`.
/// A `.` NOT followed by a digit is not consumed (so `1.foo` / `1..2`
/// leave the `.` for the next token).
///
/// Divergence (documented, not fixed here): the oracle *errors* on a
/// malformed numeral it has committed to — `0x` with no hex digits
/// ("unexpected character; expected hexadecimal number"), `1e`/`1efoo`
/// with no exponent digit ("missing exponent digits in scientific
/// literal") — verified against the pinned v4.32.0-rc1 toolchain
/// (`lean --check` on those inputs). Those are lex-time errors in real
/// Lean because `numberFnAux` is a backtracking `ParserFn` that can
/// reset to `startPos` and report there. Our `next_token` is a pure,
/// always-progressing `(source, pos) -> Token` function with no
/// backtracking (the crate's totality contract), so we instead take the
/// maximal valid numeric prefix and leave the rest for the next token
/// (`1e` lexes as `Num "1"` then `Ident "e"`; `0x` alone lexes as `Num
/// "0x"` with zero hex digits). No new stable error code is minted for
/// this in Task 3 — E0301..E0308 is the complete set this task is
/// scoped to; a dedicated "malformed numeral" code is a follow-up if the
/// parser layer needs one.
fn number_len(rest: &str) -> (usize, TokenKind) {
    let b = rest.as_bytes();

    // ORACLE-PORT `takeDigitsFn`: digits may be `_`-separated. We don't
    // enforce "at least one digit after a trailing `_`" (the oracle
    // errors there); malformed runs just consume what maximal-munch
    // finds, per the divergence note above.
    fn digits(b: &[u8], mut i: usize, is_digit: fn(u8) -> bool) -> usize {
        while i < b.len() && (is_digit(b[i]) || b[i] == b'_') {
            i += 1;
        }
        i
    }

    if b.len() > 1 && b[0] == b'0' && matches!(b[1], b'x' | b'X' | b'b' | b'B' | b'o' | b'O') {
        let is_digit: fn(u8) -> bool = match b[1] {
            b'x' | b'X' => |c: u8| c.is_ascii_hexdigit(),
            b'b' | b'B' => |c: u8| c == b'0' || c == b'1',
            _ => |c: u8| (b'0'..=b'7').contains(&c),
        };
        let i = digits(b, 2, is_digit);
        return (i, TokenKind::Num);
    }

    let mut i = digits(b, 0, |c| c.is_ascii_digit());
    let mut scientific = false;
    if i + 1 < b.len() && b[i] == b'.' && b[i + 1].is_ascii_digit() {
        scientific = true;
        i = digits(b, i + 1, |c| c.is_ascii_digit());
    }
    if i < b.len() && (b[i] == b'e' || b[i] == b'E') {
        let mut j = i + 1;
        if j < b.len() && (b[j] == b'+' || b[j] == b'-') {
            j += 1;
        }
        if j < b.len() && b[j].is_ascii_digit() {
            scientific = true;
            i = digits(b, j, |c| c.is_ascii_digit());
        }
    }
    (
        i,
        if scientific {
            TokenKind::Scientific
        } else {
            TokenKind::Num
        },
    )
}

/// ORACLE-PORT `Basic.lean` `quotedCharCoreFn`/`strLitFn`: escapes `\\
/// \" \' \n \t \r \xHH \uHHHH`, plus STRING GAPS (backslash-newline
/// consumes the newline and following leading whitespace).
fn string_lit_len(rest: &str) -> Result<usize, LexFail> {
    debug_assert!(rest.starts_with('"'));
    let mut it = rest.char_indices().skip(1).peekable();
    while let Some((i, c)) = it.next() {
        match c {
            '"' => return Ok(i + 1),
            '\\' => match it.next() {
                Some((_, '\n')) => {
                    // String gap: skip following spaces/tabs. Divergence
                    // (documented): the oracle's `stringGapFn` also
                    // accepts `\r` in the gap and errors on a *second*
                    // newline; we just stop the skip at the first
                    // non-space/tab (harmless — the char is then
                    // consumed as ordinary string content on the next
                    // iteration, still total, just not diagnosed).
                    while matches!(it.peek(), Some((_, ' ')) | Some((_, '\t'))) {
                        it.next();
                    }
                }
                Some((j, e)) if !valid_escape_head(e) => {
                    return Err((
                        j + e.len_utf8(),
                        LexError {
                            code: "E0304",
                            msg: format!("invalid escape '\\{e}'"),
                        },
                    ));
                }
                Some(_) => {}
                None => break,
            },
            _ => {}
        }
    }
    Err((
        rest.len(),
        LexError {
            code: "E0302",
            msg: "unterminated string literal".into(),
        },
    ))
}

fn valid_escape_head(c: char) -> bool {
    matches!(c, '\\' | '"' | '\'' | 'n' | 't' | 'r' | 'x' | 'u')
    // \xHH / \uHHHH hex-digit COUNT/validity checking: the oracle
    // (`hexDigitFn` via `quotedCharCoreFn`) validates these at lex time,
    // not deferred to elaboration as an earlier draft of this comment
    // claimed — verified in `Lean/Parser/Basic.lean`. We still don't
    // enforce the exact digit count/hex-ness here (untested by this
    // task's fixtures; a malformed `\x"` just ends the string slightly
    // early, which is total but not bit-for-bit oracle-faithful) — a
    // documented simplification, not an oversight.
}

/// Outcome of probing a `r"…"` / `r#…#"…"#…#` raw string opener.
enum RawStr {
    /// Not a raw-string opener at all (plain ident starting with `r`).
    NotRaw,
    /// A well-formed raw string of this total length.
    Ok(usize),
    /// A raw-string opener (`r`+`#`*+`"`) with no matching close before
    /// EOF. ORACLE-PORT `rawStrLitFnAux`'s `errorUnterminated`.
    Unterminated,
}

/// `r"…"` / `r#"…"#` — no escapes; N hashes close with `"` + N `#`s.
/// ORACLE-PORT `Basic.lean` `isRawStrLitStart`/`rawStrLitFnAux`.
fn raw_string_len(rest: &str) -> RawStr {
    debug_assert!(rest.starts_with('r'));
    let b = rest.as_bytes();
    let mut hashes = 0usize;
    let mut i = 1;
    while i < b.len() && b[i] == b'#' {
        hashes += 1;
        i += 1;
    }
    if i >= b.len() || b[i] != b'"' {
        return RawStr::NotRaw;
    }
    i += 1;
    while i < b.len() {
        if b[i] == b'"' {
            let after = i + 1;
            if b[after..].len() >= hashes && b[after..after + hashes].iter().all(|&c| c == b'#') {
                return RawStr::Ok(after + hashes);
            }
        }
        // Advance one UTF-8 char (never split a code point).
        i += 1;
        while i < b.len() && (b[i] & 0xC0) == 0x80 {
            i += 1;
        }
    }
    RawStr::Unterminated
}

/// `'c'` — same escape set as strings (single-char `\\ \" \' n t r`,
/// plus `\xHH` / `\uHHHH`, digit validity unchecked — see
/// `valid_escape_head`). Returns `None` when this position is not a char
/// literal at all: ORACLE-PORT `tokenFnAux`'s disambiguation guard
/// `curr == '\'' && next != '\''` — an unescaped `'` immediately after
/// the opening quote is NEVER char-literal content (that would need the
/// ambiguous bare `'''`), so it falls through to generic token handling
/// instead (the `f' x` / bare-`'`-symbol cases).
fn char_lit_len(rest: &str) -> Option<usize> {
    let mut it = rest.char_indices();
    it.next(); // the opening '
    let (_, c) = it.next()?;
    if c == '\'' {
        return None;
    }
    if c == '\\' {
        let (_, e) = it.next()?;
        let extra = match e {
            'x' => 2,
            'u' => 4,
            _ => 0,
        };
        for _ in 0..extra {
            it.next()?;
        }
    }
    match it.next() {
        Some((i, '\'')) => Some(i + 1),
        _ => None,
    }
}

/// `` `foo.bar `` — single backtick + hierarchical ident. ORACLE-PORT
/// `Basic.lean` `nameLitAux`/`tokenFnAux` (`curr == '`' &&
/// isIdFirstOrBeginEscape (next)`).
///
/// Divergence: an earlier draft of this port also special-cased a
/// double-backtick `` ``ident `` form as "macro-scope-free" name
/// literals. That is NOT part of `tokenFnAux`'s dispatch in the pinned
/// toolchain — verified absent from `Lean/Parser/Basic.lean` (a second
/// backtick is not `isIdFirstOrBeginEscape`, so `` ``foo `` never
/// reaches `nameLitAux`; it falls to plain symbol-table matching on the
/// first `` ` ``). Removed to match the oracle.
fn name_lit_len(rest: &str) -> Option<Result<usize, LexFail>> {
    let after = rest.strip_prefix('`')?;
    let c = after.chars().next()?;
    if !(is_id_first(c) || c == '«') {
        return None;
    }
    Some(match ident_len(after) {
        Ok(l) => Ok(l + 1),
        Err((elen, err)) => Err((elen + 1, err)),
    })
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

    // --- Task 3: idents & literals ----------------------------------

    fn kw_table() -> TokenTable {
        let mut t = TokenTable::default();
        for k in ["def", ":=", ".", "=>", "fun"] {
            t.insert(k);
        }
        t
    }

    #[test]
    fn ident_shaped_keywords_lex_as_atoms_longer_idents_win() {
        let t = kw_table();
        assert_eq!(lex_all("def", &t)[0], (TokenKind::Atom, "def"));
        // "define" is LONGER than table entry "def": ident wins.
        assert_eq!(lex_all("define", &t)[0], (TokenKind::Ident, "define"));
    }

    #[test]
    fn hierarchical_idents_are_one_token() {
        let t = kw_table();
        assert_eq!(
            lex_all("Foo.bar.baz", &t)[0],
            (TokenKind::Ident, "Foo.bar.baz")
        );
        // Trailing '.' NOT followed by an ident part stays a separate token.
        assert_eq!(
            lex_all("foo.", &t),
            vec![(TokenKind::Ident, "foo"), (TokenKind::Atom, ".")]
        );
    }

    #[test]
    fn french_quote_escapes_and_letterlike() {
        let t = kw_table();
        assert_eq!(
            lex_all("«weird id».x", &t)[0],
            (TokenKind::Ident, "«weird id».x")
        );
        assert_eq!(lex_all("α₁'", &t)[0], (TokenKind::Ident, "α₁'"));
        let (tok, err) = next_token("«never closed", 0, &t);
        assert_eq!(tok.kind, TokenKind::ErrorTok);
        assert_eq!(err.unwrap().code, "E0306");
    }

    #[test]
    fn number_literals() {
        let t = kw_table();
        assert_eq!(lex_all("0x1F", &t)[0], (TokenKind::Num, "0x1F"));
        assert_eq!(lex_all("0b101", &t)[0], (TokenKind::Num, "0b101"));
        assert_eq!(lex_all("0o77", &t)[0], (TokenKind::Num, "0o77"));
        assert_eq!(lex_all("42", &t)[0], (TokenKind::Num, "42"));
        assert_eq!(lex_all("2.5", &t)[0], (TokenKind::Scientific, "2.5"));
        assert_eq!(lex_all("1e-3", &t)[0], (TokenKind::Scientific, "1e-3"));
        // '.' not followed by a digit is NOT consumed by the number:
        // `1.foo` = Num, ".", Ident (field access on a literal).
        assert_eq!(
            lex_all("1.foo", &t),
            vec![
                (TokenKind::Num, "1"),
                (TokenKind::Atom, "."),
                (TokenKind::Ident, "foo")
            ]
        );
    }

    #[test]
    fn number_literals_allow_underscore_separators() {
        // ORACLE-PORT `takeDigitsFn`: `_` is a legal digit separator in
        // decimal/hex/octal/binary numerals (verified: `#check 1_000` on
        // the pinned toolchain elaborates to `1000 : Nat`).
        let t = kw_table();
        assert_eq!(lex_all("1_000_000", &t)[0], (TokenKind::Num, "1_000_000"));
        assert_eq!(lex_all("0xFF_FF", &t)[0], (TokenKind::Num, "0xFF_FF"));
    }

    #[test]
    fn string_char_and_name_literals() {
        let t = kw_table();
        assert_eq!(
            lex_all("\"a\\n\\\"b\"", &t)[0],
            (TokenKind::Str, "\"a\\n\\\"b\"")
        );
        assert_eq!(lex_all("'\\n'", &t)[0], (TokenKind::Char, "'\\n'"));
        assert_eq!(lex_all("'a'", &t)[0], (TokenKind::Char, "'a'"));
        assert_eq!(lex_all("`foo.bar", &t)[0], (TokenKind::NameLit, "`foo.bar"));
        let (tok, err) = next_token("\"never closed", 0, &t);
        assert_eq!(tok.kind, TokenKind::Str);
        assert_eq!(err.unwrap().code, "E0302");
    }

    #[test]
    fn char_literal_hex_and_unicode_escapes() {
        // ORACLE-PORT `quotedCharCoreFn`: `\xHH` / `\uHHHH` are valid
        // char-literal escapes, not just the single-char ones.
        let t = kw_table();
        assert_eq!(lex_all("'\\x41'", &t)[0], (TokenKind::Char, "'\\x41'"));
        assert_eq!(lex_all("'\\u0041'", &t)[0], (TokenKind::Char, "'\\u0041'"));
    }

    #[test]
    fn raw_strings() {
        let t = kw_table();
        assert_eq!(
            lex_all("r\"no \\escapes\"", &t)[0],
            (TokenKind::Str, "r\"no \\escapes\"")
        );
        assert_eq!(
            lex_all("r#\"has \" quote\"#", &t)[0],
            (TokenKind::Str, "r#\"has \" quote\"#")
        );
    }

    #[test]
    fn unterminated_raw_string_is_an_error_not_a_silent_ident_split() {
        let t = kw_table();
        let (tok, err) = next_token("r\"never closed", 0, &t);
        assert_eq!(tok.kind, TokenKind::Str);
        assert_eq!(tok.len as usize, "r\"never closed".len());
        assert_eq!(err.unwrap().code, "E0302");
    }

    #[test]
    fn char_lit_does_not_eat_apostrophe_idents() {
        let t = kw_table();
        // `f'` is an ident (apostrophe in isIdRest) — the ' after an
        // ident char is ident continuation, not a char literal opener.
        assert_eq!(lex_all("f' x", &t)[0], (TokenKind::Ident, "f'"));
    }

    #[test]
    fn doubled_quote_is_not_an_ambiguous_char_literal() {
        // ORACLE-PORT `tokenFnAux`'s `curr == '\'' && next != '\''`
        // guard: `''` never opens a char literal (that would require
        // the ambiguous bare `'''`), so with no matching table entry it
        // falls through to a single-byte ErrorTok, not a Char token.
        let t = kw_table();
        let (tok, _err) = next_token("''", 0, &t);
        assert_ne!(tok.kind, TokenKind::Char);
        assert_eq!(tok.len, 1);
    }
}
