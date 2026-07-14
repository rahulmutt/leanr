//! Untrusted-input totality (docs/THREAT_MODEL.md): the lexer terminates
//! with progress on every input, and token texts concatenate back to
//! the source byte-for-byte.

use leanr_syntax::lex::{next_token, TokenKind, TokenTable};
use proptest::prelude::*;

proptest! {
    #[test]
    fn lexer_is_total_and_lossless(src in ".*", extra_tok in "[:=+*<>-]{1,3}") {
        let mut table = TokenTable::default();
        for k in ["def", ":=", ".", "fun", "=>"] { table.insert(k); }
        table.insert(&extra_tok);
        let mut pos = 0;
        let mut rebuilt = String::new();
        loop {
            let (tok, _err) = next_token(&src, pos, &table);
            if tok.kind == TokenKind::Eof { break; }
            prop_assert!(tok.len > 0, "no progress at {pos}");
            rebuilt.push_str(&src[pos..pos + tok.len as usize]);
            pos += tok.len as usize;
        }
        prop_assert_eq!(rebuilt, src);
    }
}
