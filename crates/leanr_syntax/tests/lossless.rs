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
            let (tok, _err) = next_token(&src, pos, &table, &TokenTable::default());
            if tok.kind == TokenKind::Eof { break; }
            prop_assert!(tok.len > 0, "no progress at {pos}");
            rebuilt.push_str(&src[pos..pos + tok.len as usize]);
            pos += tok.len as usize;
        }
        prop_assert_eq!(rebuilt, src);
    }
}

use leanr_syntax::grammar::GrammarSnapshot;
use leanr_syntax::{builtin, parse_module};
use std::sync::OnceLock;

fn snap() -> &'static GrammarSnapshot {
    static S: OnceLock<GrammarSnapshot> = OnceLock::new();
    S.get_or_init(builtin::snapshot)
}

proptest! {
    /// Spec §Acceptance 2 as a property: TOTAL losslessness.
    #[test]
    fn parse_round_trips_arbitrary_input(src in ".*") {
        let r = parse_module(&src, snap());
        prop_assert_eq!(r.tree.text(), src);
    }

    /// Keyword-dense soup stresses the interesting paths harder than
    /// uniform-random strings.
    #[test]
    fn parse_round_trips_lean_shaped_soup(
        parts in proptest::collection::vec(
            prop_oneof![
                Just("def".to_string()), Just("theorem".to_string()),
                Just(":=".to_string()), Just("fun".to_string()),
                Just("=>".to_string()), Just("(".to_string()),
                Just(")".to_string()), Just("{".to_string()),
                Just("match".to_string()), Just("with".to_string()),
                Just("|".to_string()), Just("do".to_string()),
                Just("\n".to_string()), Just(" ".to_string()),
                Just("«x»".to_string()), Just("/- c -/".to_string()),
                Just("\"s\"".to_string()), Just("42".to_string()),
                "[a-z]{1,4}".prop_map(|s| s),
            ],
            0..64,
        )
    ) {
        let src = parts.concat();
        let r = parse_module(&src, snap());
        prop_assert_eq!(r.tree.text(), src);
    }

    /// Reparse stability: parsing the (identical) text again yields the
    /// same canonical tree — determinism guard for the Pratt machinery.
    #[test]
    fn reparse_is_stable(src in ".*") {
        let r1 = parse_module(&src, snap());
        let r2 = parse_module(&src, snap());
        prop_assert_eq!(
            leanr_syntax::canon::canon_jsonl(&r1.tree),
            leanr_syntax::canon::canon_jsonl(&r2.tree)
        );
    }
}
