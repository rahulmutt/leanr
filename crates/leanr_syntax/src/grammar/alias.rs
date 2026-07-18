//! Lean parser-alias table (ORACLE-PORT of the `registerAlias` set in
//! Lean/Parser.lean:27-61 + Parser/Extra.lean:337-351). Deliberately
//! partial: aliases outside this table skip-and-record (M3b2a spec);
//! extend as the Mathlib ratchet demands. Arity is fixed by each
//! combinator's Lean type (Parser / Parser→Parser / Parser→Parser→Parser).
//! Shared by the olean descr interpreter (`leanr_grammar`) and the source-level `syntax`-command derivation (`grammar::surface`) — one pinned table, two consumers.

use std::sync::Arc;

use super::Prim;

pub enum AliasPrim {
    Const(Prim),
    Epsilon,
    Unary(fn(Prim) -> Prim),
    Transparent,
    Binary(fn(Prim, Prim) -> Prim),
}

fn seq2(a: Prim, b: Prim) -> Prim {
    // Flatten nested andthen chains like the builtin ports do.
    match a {
        Prim::Seq(mut v) => {
            v.push(b);
            Prim::Seq(v)
        }
        a => Prim::Seq(vec![a, b]),
    }
}
fn or2(a: Prim, b: Prim) -> Prim {
    match a {
        Prim::OrElse(mut v) => {
            v.push(b);
            Prim::OrElse(v)
        }
        a => Prim::OrElse(vec![a, b]),
    }
}

pub fn lookup(alias: &str) -> Option<AliasPrim> {
    use AliasPrim::*;
    Some(match alias {
        // binary combinators
        "andthen" => Binary(seq2),
        "orelse" => Binary(or2),
        // unary combinators
        "optional" => Unary(|p| Prim::Optional(Arc::new(p))),
        "many" => Unary(|p| Prim::Many(Arc::new(p))),
        "many1" => Unary(|p| Prim::Many1(Arc::new(p))),
        "many1Indent" => Unary(|p| Prim::Many1Indent(Arc::new(p))),
        "atomic" => Unary(|p| Prim::Atomic(Arc::new(p))),
        "lookahead" => Unary(|p| Prim::Lookahead(Arc::new(p))),
        "notFollowedBy" => Unary(|p| Prim::NotFollowedBy(Arc::new(p))),
        "group" => Unary(|p| Prim::Group(Arc::new(p))),
        "withPosition" => Unary(|p| Prim::WithPosition(Arc::new(p))),
        // M3b3 Task 9: `sepByIndent`/`sepBy1Indent` themselves (Extra.lean:
        // 202-208) are NOT `registerAlias`'d — confirmed both by reading
        // `Lean/Parser.lean:27-61` (this module's own citation) end to
        // end, and empirically: `lean` rejects `syntax .. sepByIndent(p,
        // sep) : cat` with "error: parser `sepByIndent` was not found".
        // Only the two Term/Basic.lean call sites that partially APPLY
        // them are registered (`register_parser_alias sepByIndentSemicolon
        // sepBy1IndentSemicolon`, `Term/Basic.lean:70-72`) — each fixes
        // `sep := "; "` and `allowTrailingSep := true`, leaving just the
        // item parser free, i.e. genuinely UNARY (`Parser → Parser`), not
        // the brief's draft `Binary(Prim, Prim)` shape (that shape would
        // accept a user-supplied separator the oracle itself can't reach
        // this way — a real divergence, not a simplification). Reuses the
        // ALREADY-`sep`-parameterized `Prim::SepByIndent` (`sep_by_indent`/
        // `sep_by1_indent`'s own doc comments) rather than adding a new
        // Prim variant.
        //
        // `sep` is stored here as the bare `";"`, NOT the oracle source's
        // `"; "` default argument: `Prim::SepByIndent.sep` is the ATOM
        // `sep_by_indent`'s interpreter actually `expect_atom`s against
        // (the trailing space is a PRETTY-PRINT-only decoration of the
        // oracle's own default parameter, never part of the matched
        // token) — the SAME convention every existing hand-written
        // `sep_by_indent`/`sep_by1_indent` call site already uses
        // (`builtin/tactic.rs`'s `tacticSeq1Indented`/`tacticSeqBracketed`,
        // `builtin/term.rs`'s `letRecDecl` sequence, both pass bare `";"`)
        // — confirmed the hard way: a first attempt at this alias with
        // `sep: "; ".to_string()` made `StxSepIndent.stx.jsonl`'s `#check`
        // line fail (leanr's atom spanned the space too, `"; "` at
        // `[106,108]`, where the oracle's own atom is bare `";"` at
        // `[106,107]`, the trailing space captured as ordinary trivia
        // instead).
        "sepByIndentSemicolon" => Unary(|p| Prim::SepByIndent {
            item: Arc::new(p),
            sep: ";".to_string(),
            min: 0,
        }),
        "sepBy1IndentSemicolon" => Unary(|p| Prim::SepByIndent {
            item: Arc::new(p),
            sep: ";".to_string(),
            min: 1,
        }),
        // literal leaves / token classes
        "num" => Const(Prim::NumLit),
        "str" => Const(Prim::StrLit),
        "char" => Const(Prim::CharLit),
        "name" => Const(Prim::NameLit),
        "scientific" => Const(Prim::ScientificLit),
        "ident" => Const(Prim::Ident),
        // position / whitespace checks
        "ws" => Const(Prim::CheckWsBefore),
        "noWs" => Const(Prim::CheckNoWsBefore),
        "colGt" => Const(Prim::CheckColGt),
        "colGe" => Const(Prim::CheckColGe),
        "colEq" => Const(Prim::CheckColEq),
        "lineEq" => Const(Prim::CheckLineEq),
        // pretty-printer hints: parse nothing / transparent
        "ppSpace" | "ppHardSpace" | "ppLine" | "ppAllowUngrouped" | "ppHardLineUnlessUngrouped" => {
            Epsilon
        }
        "ppGroup" | "ppRealGroup" | "ppRealFill" | "ppIndent" | "ppDedent"
        | "ppDedentIfGrouped" | "patternIgnore" => Transparent,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::Prim;
    use super::*;

    #[test]
    fn core_aliases_map() {
        assert!(matches!(lookup("andthen"), Some(AliasPrim::Binary(_))));
        assert!(matches!(lookup("orelse"), Some(AliasPrim::Binary(_))));
        assert!(matches!(lookup("optional"), Some(AliasPrim::Unary(_))));
        assert!(matches!(lookup("many"), Some(AliasPrim::Unary(_))));
        assert!(matches!(lookup("ppSpace"), Some(AliasPrim::Epsilon)));
        assert!(matches!(lookup("ppIndent"), Some(AliasPrim::Transparent)));
        assert!(matches!(
            lookup("num"),
            Some(AliasPrim::Const(Prim::NumLit))
        ));
        assert!(matches!(
            lookup("colGt"),
            Some(AliasPrim::Const(Prim::CheckColGt))
        ));
        assert!(lookup("declModifiers").is_none()); // deliberately absent → skip
        assert!(lookup("nonsense").is_none());
    }

    /// M3b3 Task 9: `sepByIndentSemicolon`/`sepBy1IndentSemicolon` are the
    /// only two `registerAlias`'d entries the oracle exposes in this
    /// family — bare `sepByIndent`/`sepBy1Indent` are deliberately absent
    /// (never registered by the pinned toolchain; a real `syntax ..
    /// sepByIndent(p, sep) : cat` command errors "parser `sepByIndent`
    /// was not found" against `lean` itself).
    #[test]
    fn sep_by_indent_semicolon_aliases_map() {
        assert!(lookup("sepByIndent").is_none());
        assert!(lookup("sepBy1Indent").is_none());
        let Some(AliasPrim::Unary(f)) = lookup("sepByIndentSemicolon") else {
            panic!("sepByIndentSemicolon must resolve to a Unary alias");
        };
        assert!(matches!(
            f(Prim::Ident),
            Prim::SepByIndent {
                sep,
                min: 0,
                ..
            } if sep == ";"
        ));
        let Some(AliasPrim::Unary(g)) = lookup("sepBy1IndentSemicolon") else {
            panic!("sepBy1IndentSemicolon must resolve to a Unary alias");
        };
        assert!(matches!(
            g(Prim::Ident),
            Prim::SepByIndent {
                sep,
                min: 1,
                ..
            } if sep == ";"
        ));
    }

    #[test]
    fn binary_builders_build() {
        let Some(AliasPrim::Binary(f)) = lookup("andthen") else {
            panic!()
        };
        let p = f(Prim::Ident, Prim::NumLit);
        assert!(matches!(p, Prim::Seq(ref v) if v.len() == 2));
        let Some(AliasPrim::Binary(g)) = lookup("orelse") else {
            panic!()
        };
        assert!(matches!(g(Prim::Ident, Prim::NumLit), Prim::OrElse(_)));
    }
}
