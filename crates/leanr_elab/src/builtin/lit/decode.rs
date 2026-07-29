//! The literal TOKEN decoders: raw source text -> value. Oracle:
//! `Init/Meta/Defs.lean`'s `decodeStrLit`/`decodeNatLitVal?` family.
//!
//! Split out of `builtin/lit.rs` by M4b-3 P3 task 6 so the elaborators
//! (`mod.rs`) and the pure string->value decoders live apart; every
//! function here is total on `&str` and returns `Option`/a value rather
//! than throwing, because the elaborator side is what turns a rejection
//! into a named `ElabError`.

use leanr_kernel::Nat;

/// oracle: `decodeNatLitVal?` (`Init/Meta/Defs.lean:964-979`).
///
/// A leading `0` is a radix prefix only when `x`/`X`, `b`/`B` or `o`/`O`
/// follows; `007` is decimal seven, and `0` alone is zero. `_` is a
/// digit separator in every radix. Returns `None` for anything the
/// oracle rejects — the caller turns that into `IllFormedLiteral`
/// rather than panicking, even though leanr's own lexer has already
/// validated the token.
///
/// ARBITRARY PRECISION, like the oracle's own `Nat`: there is no width
/// ceiling and no overflow path, so `None` means exactly one thing —
/// the token is not a Nat literal at all. (M4b-3 P3 task 6 review: this
/// folded into `u64` and reported a named seam on overflow, which
/// diverged from the oracle for any literal >= 2^64. `leanr_kernel`'s
/// `Nat` is `pub struct Nat(pub BigUint)` with `add`/`mul` on it, so
/// folding directly costs neither a dependency nor a seam.)
pub(crate) fn decode_nat_literal(s: &str) -> Option<Nat> {
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
            return Some(Nat::from(0));
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
/// `Char.isDigit`. The fold is `Nat::mul`/`Nat::add`, so it is exactly
/// the oracle's `radix*val + d` at arbitrary precision.
fn digits(cs: &[char], radix: u32) -> Option<Nat> {
    let base = Nat::from(radix as u64);
    let mut val = Nat::from(0);
    for c in cs {
        if *c == '_' {
            continue;
        }
        let d = c.to_digit(radix)?;
        val = val.mul(&base).add(&Nat::from(d as u64));
    }
    Some(val)
}

/// Decode a Lean string-literal TOKEN (raw source text of a `str`
/// syntax node, quotes included — exactly `elab_str`'s `raw`) to
/// its value. Transcribes `Init.Meta.Defs.decodeStrLit` /
/// `decodeStrLitAux` / `decodeQuotedChar` / `decodeRawStrLitAux` (read
/// directly from the pinned toolchain source,
/// `src/Init/Meta/Defs.lean:1089-1163`, not guessed). The escape set
/// itself moved to [`decode_quoted_char`] in task 7, shared verbatim
/// with the char-literal decoder exactly as the oracle shares it:
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
        // oracle: `decodeStrLitAux` (`:1121-1136`) tries
        // `decodeQuotedChar` FIRST and the string gap second; the two
        // are disjoint (no escape letter is whitespace), so the order
        // below reproduces the pre-extraction `match` exactly.
        if let Some((c, next)) = decode_quoted_char(&chars, i) {
            out.push(c);
            i = next;
            continue;
        }
        match chars.get(i) {
            Some(gap) if gap.is_whitespace() => {
                i += 1;
                while i < end && chars[i].is_whitespace() {
                    i += 1;
                }
            }
            // Parser-validated input (the token only reaches here
            // because leanr's own lexer already accepted it as a
            // well-formed string-literal token) never hits this arm;
            // never panic on it regardless — pass the character
            // through unchanged rather than drop it silently. A
            // TRUNCATED `\x`/`\u` escape now lands here too, since
            // `decode_quoted_char` rejects it instead of indexing past
            // the end of the buffer as this loop used to.
            Some(other) => {
                out.push(*other);
                i += 1;
            }
            // A trailing `\` with nothing after it at all: impossible
            // for a lexed token, and there is nothing to push.
            None => break,
        }
    }
    out
}

/// oracle: `decodeQuotedChar` (`Init/Meta/Defs.lean:1089-1113`) —
/// decode the escape sequence starting at `i`, the character AFTER the
/// backslash, returning the decoded character and the index just past
/// the sequence.
///
/// `None` for anything outside the escape set, exactly as the oracle
/// returns `none`. A string GAP (`\` + whitespace) is `decodeStringGap`'s
/// separate job (`:1117-1120`), tried second by `decodeStrLitAux`
/// (`:1129-1132`) — it is not an arm here, and a char literal cannot
/// contain one.
///
/// TOTAL by construction. The oracle reads through `String.Internal.get`,
/// which returns `(default : Char)` = `'A'` past the end of the buffer
/// (`Init/Data/String/Basic.lean:1869-1871`, `Init/Data/Char/Basic.lean:90`)
/// rather than faulting, so a token ending mid-escape decodes garbage
/// there rather than throwing. leanr instead bounds-checks every index
/// and returns `None`, which the caller reports as `IllFormedLiteral` —
/// a DOCUMENTED divergence on input leanr's lexer cannot produce (the
/// only tokens that reach here are ones it already accepted), taken
/// because this crate's never-panic rule for the literal decoders is
/// absolute and `'A'`-as-a-hex-digit is not a behaviour worth porting.
pub(crate) fn decode_quoted_char(cs: &[char], i: usize) -> Option<(char, usize)> {
    match *cs.get(i)? {
        '\\' => Some(('\\', i + 1)),
        '"' => Some(('"', i + 1)),
        '\'' => Some(('\'', i + 1)),
        'r' => Some(('\r', i + 1)),
        'n' => Some(('\n', i + 1)),
        't' => Some(('\t', i + 1)),
        // `\xHH` / `\uHHHH`: exactly 2 and exactly 4 hex digits.
        // `Char.ofNat`'s own fallback for a code point outside the valid
        // Unicode-scalar range is `'\0'` (`Init/Prelude.lean:2886-2889`),
        // not a panic and not a replacement character, so
        // `char::from_u32(..).unwrap_or('\0')` mirrors it exactly.
        'x' => hex_code(cs, i + 1, 2).map(|code| (char::from_u32(code).unwrap_or('\0'), i + 3)),
        'u' => hex_code(cs, i + 1, 4).map(|code| (char::from_u32(code).unwrap_or('\0'), i + 5)),
        _ => None,
    }
}

/// `n` consecutive hex digits from `at`, folded big-endian: the oracle's
/// chain of `decodeHexDigit` binds (`:1097-1105`), whose `none`
/// short-circuits the enclosing `do` block. `None` if the buffer is too
/// short or any character is not an ASCII hex digit — `char::to_digit(16)`
/// accepts exactly `decodeHexDigit`'s three ranges (`:940-946`) and
/// nothing else. `n <= 4`, so the fold cannot overflow `u32`.
fn hex_code(cs: &[char], at: usize, n: usize) -> Option<u32> {
    let mut code = 0u32;
    for k in 0..n {
        code = code * 16 + cs.get(at + k)?.to_digit(16)?;
    }
    Some(code)
}

/// oracle: `decodeCharLit` (`Init/Meta/Defs.lean:1177-1183`) — the
/// character at index 1 of the token, or, when that is a backslash,
/// `decodeQuotedChar` from index 2 (the rest of the token, including
/// the closing quote, is never inspected).
///
/// The shortest well-formed token is `'x'`, three characters. Anything
/// shorter is rejected rather than reading the oracle's out-of-range
/// `'A'` default (see [`decode_quoted_char`]'s note): unreachable from
/// leanr's lexer, and `None` becomes `IllFormedLiteral`, which is also
/// what `elabCharLit` does with the oracle's own `none`.
pub(crate) fn decode_char_literal(raw: &str) -> Option<char> {
    let cs: Vec<char> = raw.chars().collect();
    if cs.len() < 3 {
        return None;
    }
    if cs[1] == '\\' {
        decode_quoted_char(&cs, 2).map(|(c, _)| c)
    } else {
        Some(cs[1])
    }
}

/// oracle: `decodeScientificLitVal?` (`Init/Meta/Defs.lean:1008-1071`),
/// transcribed as a single pass over the token rather than the oracle's
/// four mutually-recursive `where` bindings. The states correspond
/// one-to-one: `decode` (the integer part, `:1058-1071`),
/// `decodeAfterDot` (`:1044-1056`), `decodeExp` (`:1034-1042`),
/// `decodeAfterExp` (`:1017-1032`).
///
/// Returns `(mantissa, exponentIsNegative, exponent)`, the oracle's
/// `(n, sign, e)` with value `n * 10^-e` if `sign` else `n * 10^e`.
///
/// Three subtleties, each transcribed rather than smoothed:
///
///  * The final combination (`:1018-1024`) with `e` = the number of
///    digits after the dot and `exp` = the written exponent: a negative
///    written exponent gives `(m, true, exp + e)`; a positive one gives
///    `(m, false, exp - e)` when `exp >= e` and `(m, true, e - exp)`
///    otherwise. All three arms are reachable; the third
///    (`1.25e1 -> (125, true, 1)`) is the only one no corpus record
///    covers, so it is measured in a unit test instead.
///  * `decodeExp` tests `atEnd` BEFORE it reads the sign (`:1035`), so a
///    token ending in a bare `e` is `none` — while `1e-`, which reaches
///    `decodeAfterExp`'s own `atEnd`, is `some (1, true, 0)`.
///  * `decode`'s `atEnd` is `none` (`:1059-1060`), which is what rejects
///    a plain `num` token here; `decodeAfterDot`'s `atEnd` is
///    `some (val, true, e)` (`:1045-1046`), which is what accepts `1.`.
///
/// ARBITRARY PRECISION in both components, like `decode_nat_literal`:
/// the oracle's `Nat`s have no width ceiling, so neither do these and
/// there is no overflow seam to diverge on. `None` means exactly one
/// thing — the token is not a scientific literal.
pub(crate) fn decode_scientific_literal(raw: &str) -> Option<(Nat, bool, Nat)> {
    let cs: Vec<char> = raw.chars().collect();
    let ten = Nat::from(10);
    // oracle: `:1009-1015` — an empty token, or one whose first
    // character is not a digit, before any state runs.
    if cs.first().is_none_or(|c| !c.is_ascii_digit()) {
        return None;
    }
    let mut i = 0usize;
    let mut mantissa = Nat::from(0);
    let mut dot_digits = Nat::from(0);
    let one = Nat::from(1);

    // `decode`: the integer part.
    while let Some(c) = cs.get(i) {
        if let Some(d) = ascii_digit(*c) {
            mantissa = mantissa.mul(&ten).add(&d);
        } else if *c != '_' {
            break;
        }
        i += 1;
    }
    if i < cs.len() && cs[i] == '.' {
        i += 1;
        // `decodeAfterDot`.
        while let Some(c) = cs.get(i) {
            if let Some(d) = ascii_digit(*c) {
                mantissa = mantissa.mul(&ten).add(&d);
                dot_digits = dot_digits.add(&one);
            } else if *c != '_' {
                break;
            }
            i += 1;
        }
        if i == cs.len() {
            // oracle: `decodeAfterDot`'s `atEnd` (`:1045-1046`).
            return Some((mantissa, true, dot_digits));
        }
    }
    // Both `decode` and `decodeAfterDot` reach here only via their
    // `e`/`E` arm; every other continuation (`atEnd` in `decode`, any
    // other character in either) is `none`. This is also what rejects a
    // plain `num` token such as `42`.
    if i >= cs.len() || (cs[i] != 'e' && cs[i] != 'E') {
        return None;
    }
    i += 1;
    // `decodeExp`: `atEnd` is `none` (`:1035`), checked BEFORE the sign.
    if i >= cs.len() {
        return None;
    }
    let written_negative = cs[i] == '-';
    if written_negative || cs[i] == '+' {
        i += 1;
    }
    // `decodeAfterExp`.
    let mut exp = Nat::from(0);
    while let Some(c) = cs.get(i) {
        if let Some(d) = ascii_digit(*c) {
            exp = exp.mul(&ten).add(&d);
        } else if *c != '_' {
            // oracle: `:1032` — any other character in the exponent.
            return None;
        }
        i += 1;
    }
    // oracle: `:1018-1024`.
    if written_negative {
        Some((mantissa, true, exp.add(&dot_digits)))
    } else if dot_digits.ble(&exp) {
        Some((mantissa, false, exp.sub(&dot_digits)))
    } else {
        Some((mantissa, true, dot_digits.sub(&exp)))
    }
}

/// The oracle's `'0' ≤ c && c ≤ '9'` guard plus its `c.toNat -
/// '0'.toNat` value, as one step. ASCII-only, so no non-ASCII digit
/// sneaks in — matching `Char.isDigit`.
fn ascii_digit(c: char) -> Option<Nat> {
    c.is_ascii_digit()
        .then(|| Nat::from(u64::from(c as u32 - '0' as u32)))
}

#[cfg(test)]
mod tests {
    use super::{
        decode_char_literal, decode_nat_literal, decode_scientific_literal, decode_string_literal,
    };
    use leanr_kernel::Nat;

    /// oracle: `decodeNatLitVal?` (`Init/Meta/Defs.lean:964-979`) and
    /// its four radix helpers (`:923-962`). Underscores are separators
    /// in every radix; a leading `0` is only a radix prefix when a
    /// radix letter follows.
    #[test]
    fn nat_literal_radixes_and_separators() {
        let n = |v: u64| Some(Nat::from(v));
        assert_eq!(decode_nat_literal("42"), n(42));
        assert_eq!(decode_nat_literal("0"), n(0));
        assert_eq!(decode_nat_literal("007"), n(7));
        assert_eq!(decode_nat_literal("1_000_000"), n(1_000_000));
        assert_eq!(decode_nat_literal("0x2A"), n(42));
        assert_eq!(decode_nat_literal("0X2a"), n(42));
        assert_eq!(decode_nat_literal("0b1010"), n(10));
        assert_eq!(decode_nat_literal("0o52"), n(42));
        assert_eq!(decode_nat_literal("0xff_ff"), n(65535));
        assert_eq!(decode_nat_literal(""), None);
        assert_eq!(decode_nat_literal("0z1"), None);
        assert_eq!(decode_nat_literal("12a"), None);
    }

    /// An EMPTY digit run after a radix prefix is `Some 0`, not `None`:
    /// `decodeHexLitAux s ⟨2⟩ 0` hits `String.Internal.atEnd`
    /// immediately and returns its accumulator (`:948-949`). leanr's
    /// lexer really can produce this token — `number_len` takes the
    /// maximal valid prefix, so bare `0x` lexes as `Num "0x"`
    /// (`lex.rs`'s own documented divergence note).
    #[test]
    fn radix_prefix_with_no_digits_is_zero() {
        assert_eq!(decode_nat_literal("0x"), Some(Nat::from(0)));
        assert_eq!(decode_nat_literal("0X"), Some(Nat::from(0)));
    }

    /// A `_` immediately after a leading `0` is NOT a decimal separator:
    /// `decodeNatLitVal?` reaches the `c.isDigit` test at index 1 with
    /// `c = '_'`, which is false, and falls to `else none` (`:976-977`).
    /// The separator rule only applies once a radix has been chosen.
    #[test]
    fn underscore_directly_after_a_leading_zero_is_rejected() {
        assert_eq!(decode_nat_literal("0_1"), None);
    }

    /// Arbitrary precision: a literal at and beyond the old `u64`
    /// ceiling decodes to its exact value rather than failing. `2^64` is
    /// the first value the previous `checked_mul`/`checked_add` fold
    /// rejected, in both the decimal and the hex path.
    #[test]
    fn literals_wider_than_u64_decode_exactly() {
        let two_pow_64 = Nat::from(u64::MAX).add(&Nat::from(1));
        assert_eq!(
            decode_nat_literal("18446744073709551616"),
            Some(two_pow_64.clone())
        );
        assert_eq!(
            decode_nat_literal("0x1_0000_0000_0000_0000"),
            Some(two_pow_64.clone())
        );
        // One well past it, to show the fold is not merely one digit
        // wider: 2^128.
        let two_pow_128 = two_pow_64.mul(&two_pow_64);
        assert_eq!(
            decode_nat_literal("340282366920938463463374607431768211456"),
            Some(two_pow_128)
        );
    }

    /// oracle: `decodeCharLit` (`Init/Meta/Defs.lean:1177-1183`) — the
    /// character at index 1; if it is `\`, `decodeQuotedChar`
    /// (`:1089-1113`) from index 2. Exactly the escape set
    /// `decode_string_literal` already handles, which is why task 7
    /// factors `decode_quoted_char` out of it rather than writing a
    /// second copy.
    #[test]
    fn char_literal_plain_and_escaped() {
        assert_eq!(decode_char_literal("'a'"), Some('a'));
        assert_eq!(decode_char_literal("'\\n'"), Some('\n'));
        assert_eq!(decode_char_literal("'\\\\'"), Some('\\'));
        assert_eq!(decode_char_literal("'\\''"), Some('\''));
        assert_eq!(decode_char_literal("'\\x41'"), Some('A'));
        assert_eq!(decode_char_literal("'\\u00e9'"), Some('é'));
        assert_eq!(decode_char_literal("'é'"), Some('é'));
    }

    /// Totality (Global Constraints: a literal decoder must never panic
    /// on an unexpected character). None of these tokens can come out of
    /// leanr's lexer, and a naive transcription of `decodeQuotedChar`
    /// indexes past the end of the buffer on most of them.
    ///
    /// The oracle is total here too, but only because
    /// `String.Internal.get` returns `(default : Char)` = `'A'` past the
    /// end of the string — and `'A'` is itself a hex digit. MEASURED
    /// against the pinned toolchain (`Lean.Syntax.decodeCharLit`,
    /// throwaway probe), the split is exactly:
    ///
    ///   agreements (`none` on both sides), because the oracle's own
    ///   `decodeHexDigit` sees a REAL non-hex character:
    ///     `'\`, `'\x4'`, `'\u00e'`, `'\q'`
    ///
    ///   divergences, all of them the out-of-range `'A'`:
    ///     `""` -> `some 'A'`, `"'"` -> `some 'A'`, `"''"` -> `some '\''`,
    ///     `'\x` -> `some 'ª'` (0xAA), `'\x4` -> `some 'J'` (0x4A),
    ///     `'\u00e` -> `some 'ê'` (0x00EA)
    ///
    /// leanr returns `None` for all six, which `elab_char` reports as
    /// `IllFormedLiteral`. See `decode_quoted_char`'s note for why that
    /// is the right trade on input leanr's lexer cannot produce.
    #[test]
    fn char_literal_truncated_never_panics() {
        assert_eq!(decode_char_literal(""), None);
        assert_eq!(decode_char_literal("'"), None);
        assert_eq!(decode_char_literal("''"), None);
        assert_eq!(decode_char_literal("'\\"), None);
        assert_eq!(decode_char_literal("'\\x"), None);
        assert_eq!(decode_char_literal("'\\x4"), None);
        assert_eq!(decode_char_literal("'\\x4'"), None);
        assert_eq!(decode_char_literal("'\\u00e"), None);
        assert_eq!(decode_char_literal("'\\u00e'"), None);
        assert_eq!(decode_char_literal("'\\q'"), None);
    }

    /// A truncated escape inside a STRING token must not panic either.
    /// Before the `decode_quoted_char` extraction each of these PANICKED
    /// (`hex_digit`'s `.expect`, reached through an unbounded
    /// `chars[i + 1]`); now the escape is simply rejected and falls to
    /// the pre-existing catch-all, which passes the character through
    /// unchanged.
    ///
    /// `decode_string_literal` is infallible BY SIGNATURE — a
    /// pre-existing simplification of `decodeStrLit : Option String`,
    /// which returns `none` for all three of these (measured). That
    /// divergence is older than this task and equally unreachable: the
    /// only tokens that get here are ones leanr's lexer accepted.
    #[test]
    fn string_literal_truncated_escape_never_panics() {
        assert_eq!(decode_string_literal("\"\\x4\""), "x4");
        assert_eq!(decode_string_literal("\"\\u00e\""), "u00e");
        assert_eq!(decode_string_literal("\"\\x\""), "x");
    }

    /// oracle: `decodeScientificLitVal?` (`Init/Meta/Defs.lean:1008-1071`).
    /// Returns `(mantissa, negativeExponent, exponent)`:
    ///   `1.5`     -> (15, true, 1)     -- one digit after the dot
    ///   `1.25`    -> (125, true, 2)
    ///   `121e100` -> (121, false, 100)
    ///   `1e-3`    -> (1, true, 3)
    ///   `1.5e2`   -> (15, false, 1)    -- exp 2 minus 1 dot digit
    ///   `1.5e-2`  -> (15, true, 3)     -- exp 2 plus 1 dot digit
    #[test]
    fn scientific_literal_mantissa_sign_and_exponent() {
        let s = |m: u64, neg: bool, e: u64| Some((Nat::from(m), neg, Nat::from(e)));
        assert_eq!(decode_scientific_literal("1.5"), s(15, true, 1));
        assert_eq!(decode_scientific_literal("1.25"), s(125, true, 2));
        assert_eq!(decode_scientific_literal("121e100"), s(121, false, 100));
        assert_eq!(decode_scientific_literal("1e-3"), s(1, true, 3));
        assert_eq!(decode_scientific_literal("1.5e2"), s(15, false, 1));
        assert_eq!(decode_scientific_literal("1.5e-2"), s(15, true, 3));
        assert_eq!(decode_scientific_literal("42"), None);
    }

    /// The THIRD arm of the exponent combination (`:1021-1024`): a
    /// positive written exponent SMALLER than the number of dot digits
    /// flips the sign back to negative. Neither the brief's examples nor
    /// any corpus record reaches it, so it gets its own test.
    #[test]
    fn scientific_literal_exponent_below_dot_digits() {
        assert_eq!(
            decode_scientific_literal("1.25e1"),
            Some((Nat::from(125), true, Nat::from(1)))
        );
        // exp == dot digits takes the `exp >= e` arm, exponent zero.
        assert_eq!(
            decode_scientific_literal("1.25e2"),
            Some((Nat::from(125), false, Nat::from(0)))
        );
    }

    /// `_` is a digit separator in the integer part, after the dot and in
    /// the exponent alike (`decode`/`decodeAfterDot`/`decodeAfterExp`
    /// each have their own `c == '_'` arm), and `E` is `e`.
    #[test]
    fn scientific_literal_separators_and_capital_e() {
        let s = |m: u64, neg: bool, e: u64| Some((Nat::from(m), neg, Nat::from(e)));
        assert_eq!(decode_scientific_literal("1_0.2_5"), s(1025, true, 2));
        assert_eq!(decode_scientific_literal("1.5E2"), s(15, false, 1));
        assert_eq!(decode_scientific_literal("1e1_0"), s(1, false, 10));
    }

    /// The oracle's edge cases around a trailing exponent marker, which a
    /// straight-line transcription gets wrong: `decodeExp` tests
    /// `atEnd` BEFORE reading the sign (`:1041`), so `1e` is `none`,
    /// while `1e-` reaches `decodeAfterExp`'s own `atEnd` and is
    /// `some (1, true, 0)`. A trailing bare `.` is `decodeAfterDot`'s
    /// `atEnd` case, `some (1, true, 0)`.
    ///
    /// All five MEASURED against the pinned toolchain
    /// (`Lean.Syntax.decodeScientificLitVal?`, throwaway probe), not
    /// derived from the source alone — the brief's own sketch got `1e`
    /// wrong by folding `decodeExp`'s `atEnd` into the sign test.
    #[test]
    fn scientific_literal_trailing_marker_edges() {
        assert_eq!(decode_scientific_literal("1e"), None);
        assert_eq!(decode_scientific_literal("1.5e"), None);
        assert_eq!(
            decode_scientific_literal("1e-"),
            Some((Nat::from(1), true, Nat::from(0)))
        );
        assert_eq!(
            decode_scientific_literal("1e+"),
            Some((Nat::from(1), false, Nat::from(0)))
        );
        assert_eq!(
            decode_scientific_literal("1."),
            Some((Nat::from(1), true, Nat::from(0)))
        );
    }

    /// Rejections and totality: an empty token, a token that does not
    /// start with a digit (`decodeScientificLitVal?`'s own `c.isDigit`
    /// guard, `:1013`), and trailing junk in each of the three states.
    #[test]
    fn scientific_literal_rejections_never_panic() {
        assert_eq!(decode_scientific_literal(""), None);
        assert_eq!(decode_scientific_literal(".5"), None);
        assert_eq!(decode_scientific_literal("e5"), None);
        assert_eq!(decode_scientific_literal("-1.5"), None);
        assert_eq!(decode_scientific_literal("1.5x"), None);
        assert_eq!(decode_scientific_literal("1x"), None);
        assert_eq!(decode_scientific_literal("1e5x"), None);
        assert_eq!(decode_scientific_literal("é"), None);
    }

    /// Arbitrary precision, like `decode_nat_literal`: neither the
    /// mantissa nor the exponent has a width ceiling, so there is no
    /// overflow seam to diverge on (M4b-3 P3 task 6 review folded the
    /// numeric decoders into `Nat` for exactly this reason).
    #[test]
    fn scientific_literal_wider_than_u64() {
        let two_pow_64 = Nat::from(u64::MAX).add(&Nat::from(1));
        // 2^64 written with one digit after the dot: the mantissa is
        // 10*2^64 + 5, an exact bignum, with exponent 1.
        let mantissa = two_pow_64.mul(&Nat::from(10)).add(&Nat::from(5));
        assert_eq!(
            decode_scientific_literal("18446744073709551616.5"),
            Some((mantissa, true, Nat::from(1)))
        );
        // The EXPONENT is arbitrary precision too: 10^20 - 1, three
        // decimal digits past `u64::MAX`.
        let huge_exp = Nat::from(10).pow(20).sub(&Nat::from(1));
        assert_eq!(
            decode_scientific_literal("1e99999999999999999999"),
            Some((Nat::from(1), false, huge_exp))
        );
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
