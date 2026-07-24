//! The one literal that is a leaf (design spec § Scope): a string
//! literal elaborates straight to `Expr.lit (.strVal _)`, no instance
//! search, no `OfNat`/`Char.ofNat` machinery. `num`/`char` are NOT
//! leaves — both elaborate through an application (`OfNat.ofNat` /
//! `Char.ofNat`) requiring instance synthesis, so they land in M4b-3
//! and are never registered here.

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `Lean.Elab.Term.elabStrLit` (`Lean/Elab/BuiltinTerm.lean`) —
/// note the oracle itself never consults `expectedType?` for a string
/// literal (`fun stx _ => ...`); the value comes straight from the
/// syntax, independent of what the caller expects.
pub fn elab_str(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    _kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    // `node` is the `str` syntax node itself (a single atom child in
    // the oracle's own model, `Syntax.mkLit`); its `.text()` is exactly
    // that atom's raw source text — quotes and un-decoded escapes
    // included, no surrounding whitespace (confirmed empirically:
    // leanr's parser discovers trailing trivia lazily, only once the
    // Pratt loop peeks past the already-closed literal node, so it
    // never becomes a child of the literal node itself).
    let raw = node.text().to_string();
    let s = decode_string_literal(&raw);
    let id = elab
        .mctx
        .store_mut()
        .expr_lit_str(None, &s)
        .map_err(leanr_meta::MetaError::from)?;
    Ok(id)
}

/// Decode a Lean string-literal TOKEN (raw source text of a `str`
/// syntax node, quotes included — exactly `elab_str`'s `raw` above) to
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
fn decode_string_literal(raw: &str) -> String {
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

fn hex_digit(c: char) -> u32 {
    c.to_digit(16)
        .expect("well-formed \\x/\\u escape (parser-validated token)")
}

#[cfg(test)]
mod tests {
    use super::decode_string_literal;

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
