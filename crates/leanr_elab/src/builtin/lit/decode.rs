//! The literal TOKEN decoders: raw source text -> value. Oracle:
//! `Init/Meta/Defs.lean`'s `decodeStrLit`/`decodeNatLitVal?` family.
//!
//! Split out of `builtin/lit.rs` by M4b-3 P3 task 6 so the elaborators
//! (`mod.rs`) and the pure string->value decoders live apart; every
//! function here is total on `&str` and returns `Option`/a value rather
//! than throwing, because the elaborator side is what turns a rejection
//! into a named `ElabError`.

/// oracle: `decodeNatLitVal?` (`Init/Meta/Defs.lean:964-979`).
///
/// A leading `0` is a radix prefix only when `x`/`X`, `b`/`B` or `o`/`O`
/// follows; `007` is decimal seven, and `0` alone is zero. `_` is a
/// digit separator in every radix. Returns `None` for anything the
/// oracle rejects — the caller turns that into `IllFormedLiteral`
/// rather than panicking, even though leanr's own lexer has already
/// validated the token.
///
/// **NAMED SEAM (`u64` width).** The oracle's result is an
/// arbitrary-precision `Nat`, and so is leanr's own `Nat`; this decoder
/// nonetheless folds into a `u64` and returns `None` on overflow rather
/// than wrapping. The value's only consumer is
/// [`super::mk_raw_nat_lit`], which needs it just to build one
/// `Store::expr_lit_nat` row, and a literal wider than `u64` is not
/// reachable from the committed corpus. `elab_num` turns the `None`
/// into `ElabError::IllFormedLiteral` naming this seam, so an overflow
/// is an attributable error rather than a silently wrapped value; the
/// fix, when a corpus record needs it, is to fold into `Nat` directly
/// here.
pub(crate) fn decode_nat_literal(s: &str) -> Option<u64> {
    let cs: Vec<char> = s.chars().collect();
    // Every index below is guarded: `cs[0]` only after the emptiness
    // test, `cs[1]` only after `cs.len() == 1` returned, and `cs[2..]`
    // only where `cs.len() >= 2` is already known (an empty digit run
    // is `Some(0)`, matching the oracle's own `atEnd` base case).
    if cs.is_empty() {
        return None;
    }
    if cs[0] == '0' {
        if cs.len() == 1 {
            return Some(0);
        }
        return match cs[1] {
            'x' | 'X' => digits(&cs[2..], 16),
            'b' | 'B' => digits(&cs[2..], 2),
            'o' | 'O' => digits(&cs[2..], 8),
            // oracle: `else if c.isDigit then decodeDecimalLitAux s 0 0`
            // — note the restart at index 0, NOT 1: the leading `0` is
            // part of the decimal run, so `007` is seven.
            c if c.is_ascii_digit() => digits(&cs, 10),
            _ => None,
        };
    }
    if cs[0].is_ascii_digit() {
        return digits(&cs, 10);
    }
    None
}

/// The shared body of `decodeDecimalLitAux`/`decodeBinLitAux`/
/// `decodeOctalLitAux`/`decodeHexLitAux` (`:923-962`): fold digits of
/// the given radix, skipping `_`, rejecting anything else. An empty
/// digit run is `Some(0)` — the oracle's own `atEnd -> some val` base
/// case with `val = 0`.
///
/// `char::to_digit` accepts exactly the character sets the four oracle
/// helpers do at radix 2/8/10/16 (ASCII digits, plus `a`-`f`/`A`-`F` at
/// 16), and nothing else — in particular no non-ASCII digit, matching
/// `Char.isDigit`. `checked_mul`/`checked_add` are the `u64` seam
/// documented on [`decode_nat_literal`].
fn digits(cs: &[char], radix: u32) -> Option<u64> {
    let mut val: u64 = 0;
    for c in cs {
        if *c == '_' {
            continue;
        }
        let d = c.to_digit(radix)?;
        val = val.checked_mul(radix as u64)?.checked_add(d as u64)?;
    }
    Some(val)
}

/// Decode a Lean string-literal TOKEN (raw source text of a `str`
/// syntax node, quotes included — exactly `elab_str`'s `raw`) to
/// its value. Transcribes `Init.Meta.Defs.decodeStrLit` /
/// `decodeStrLitAux` / `decodeQuotedChar` / `decodeRawStrLitAux` (read
/// directly from the pinned toolchain source,
/// `src/Init/Meta/Defs.lean:1089-1163`, not guessed):
///
/// - escapes: `\\`, `\"`, `\'`, `\r`, `\n`, `\t`, `\xHH` (exactly 2 hex
///   digits), `\uHHHH` (exactly 4 hex digits) — `Char.ofNat`'s own
///   fallback for a code point outside the valid Unicode-scalar range
///   is `'\0'` (`Init/Prelude.lean:2886`), not a panic or a
///   replacement character, so `char::from_u32(..).unwrap_or('\0')`
///   mirrors it exactly;
/// - a string GAP (`\` followed by whitespace) consumes that
///   whitespace and every further whitespace char, contributing
///   nothing to the value — Lean's line-continuation feature.
///   `decodeStringGap` matches Lean's own (unspecified-here) notion of
///   "whitespace"; this port uses `char::is_whitespace` as a
///   documented approximation — the committed corpus has no string
///   gaps (`dump_elab.lean`'s own doc comment excludes them), so this
///   path is exercised by neither side of the differential gate today;
/// - a RAW string literal `r"..."` / `r#"..."#` (leading `r`, N `#`s,
///   `"`, ..., `"`, N `#`s) copies its inner text verbatim, no escape
///   processing — `decodeRawStrLitAux`'s own behavior. Not in the
///   committed corpus either (a plain string literal is what the
///   corpus's `Elab0`/`dump_elab.lean` doc comment scopes this slice
///   to), included because the token shape is trivial to distinguish
///   correctly once already walking the raw text.
pub(crate) fn decode_string_literal(raw: &str) -> String {
    let chars: Vec<char> = raw.chars().collect();
    if chars.first() == Some(&'r') {
        let mut i = 1;
        let mut hashes = 0usize;
        while chars.get(i) == Some(&'#') {
            hashes += 1;
            i += 1;
        }
        // chars[i] is the opening '"'; the inner text runs to just
        // before the closing '"' + its matching N '#'s.
        let start = i + 1;
        let end = chars.len() - 1 - hashes;
        return chars[start..end].iter().collect();
    }

    let mut out = String::new();
    let end = chars.len() - 1; // index of the closing '"'
    let mut i = 1; // skip the opening '"'
    while i < end {
        let c = chars[i];
        if c != '\\' {
            out.push(c);
            i += 1;
            continue;
        }
        i += 1;
        let e = chars[i];
        match e {
            '\\' => {
                out.push('\\');
                i += 1;
            }
            '"' => {
                out.push('"');
                i += 1;
            }
            '\'' => {
                out.push('\'');
                i += 1;
            }
            'r' => {
                out.push('\r');
                i += 1;
            }
            'n' => {
                out.push('\n');
                i += 1;
            }
            't' => {
                out.push('\t');
                i += 1;
            }
            'x' => {
                let code = hex_digit(chars[i + 1]) * 16 + hex_digit(chars[i + 2]);
                out.push(char::from_u32(code).unwrap_or('\0'));
                i += 3;
            }
            'u' => {
                let code = ((hex_digit(chars[i + 1]) * 16 + hex_digit(chars[i + 2])) * 16
                    + hex_digit(chars[i + 3]))
                    * 16
                    + hex_digit(chars[i + 4]);
                out.push(char::from_u32(code).unwrap_or('\0'));
                i += 5;
            }
            gap if gap.is_whitespace() => {
                i += 1;
                while i < end && chars[i].is_whitespace() {
                    i += 1;
                }
            }
            // Parser-validated input (the token only reaches here
            // because leanr's own lexer already accepted it as a
            // well-formed string-literal token) never hits this arm;
            // never panic on it regardless — pass the character
            // through unchanged rather than drop it silently.
            other => {
                out.push(other);
                i += 1;
            }
        }
    }
    out
}

pub(crate) fn hex_digit(c: char) -> u32 {
    c.to_digit(16)
        .expect("well-formed \\x/\\u escape (parser-validated token)")
}

#[cfg(test)]
mod tests {
    use super::{decode_nat_literal, decode_string_literal};

    /// oracle: `decodeNatLitVal?` (`Init/Meta/Defs.lean:964-979`) and
    /// its four radix helpers (`:923-962`). Underscores are separators
    /// in every radix; a leading `0` is only a radix prefix when a
    /// radix letter follows.
    #[test]
    fn nat_literal_radixes_and_separators() {
        assert_eq!(decode_nat_literal("42"), Some(42));
        assert_eq!(decode_nat_literal("0"), Some(0));
        assert_eq!(decode_nat_literal("007"), Some(7));
        assert_eq!(decode_nat_literal("1_000_000"), Some(1_000_000));
        assert_eq!(decode_nat_literal("0x2A"), Some(42));
        assert_eq!(decode_nat_literal("0X2a"), Some(42));
        assert_eq!(decode_nat_literal("0b1010"), Some(10));
        assert_eq!(decode_nat_literal("0o52"), Some(42));
        assert_eq!(decode_nat_literal("0xff_ff"), Some(65535));
        assert_eq!(decode_nat_literal(""), None);
        assert_eq!(decode_nat_literal("0z1"), None);
        assert_eq!(decode_nat_literal("12a"), None);
    }

    #[test]
    fn plain() {
        assert_eq!(decode_string_literal("\"hello\""), "hello");
    }

    #[test]
    fn empty() {
        assert_eq!(decode_string_literal("\"\""), "");
    }

    #[test]
    fn simple_escapes() {
        assert_eq!(
            decode_string_literal("\"a\\nb\\tc\\\"d\\\\e\\'f\""),
            "a\nb\tc\"d\\e'f"
        );
    }

    #[test]
    fn hex_escape() {
        assert_eq!(decode_string_literal("\"\\x41\\x42\""), "AB");
    }

    #[test]
    fn unicode_escape() {
        assert_eq!(decode_string_literal("\"\\u00e9\""), "é");
    }

    #[test]
    fn raw_non_ascii_char() {
        assert_eq!(decode_string_literal("\"héllo\""), "héllo");
    }

    #[test]
    fn raw_string_literal() {
        assert_eq!(decode_string_literal("r\"a\\nb\""), "a\\nb");
        assert_eq!(decode_string_literal("r#\"a\"b\"#"), "a\"b");
    }
}
