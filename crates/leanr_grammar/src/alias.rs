//! Lean parser-alias table (ORACLE-PORT of the `registerAlias` set in
//! Lean/Parser.lean:27-61 + Parser/Extra.lean:337-351). Deliberately
//! partial: aliases outside this table skip-and-record (M3b2a spec);
//! extend as the Mathlib ratchet demands. Arity is fixed by each
//! combinator's Lean type (Parser / Parser→Parser / Parser→Parser→Parser).

use std::sync::Arc;

use leanr_syntax::grammar::Prim;

pub(crate) enum AliasPrim {
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

pub(crate) fn lookup(alias: &str) -> Option<AliasPrim> {
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
    use super::*;
    use leanr_syntax::grammar::Prim;

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
