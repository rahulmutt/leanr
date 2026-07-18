//! Raw-`Parser` shim table (M3b3 Task 11) — the SECOND-CHANCE lookup
//! `alias::lookup` consults on its miss path (`_ => return
//! shim_lookup(alias)`). Same contract and `AliasPrim` arities as
//! `alias.rs`; kept in its own module so the deliberately-partial,
//! Mathlib-ratchet-driven `registerParserAlias` PORT (`alias.rs`, an
//! oracle-faithful transcription of `Lean/Parser.lean:27-61` +
//! `Extra.lean:337-351`) stays byte-for-byte a transcription, while the
//! data-RANKED additions this task justifies from a Mathlib corpus scan
//! live here with their own evidence trail.
//!
//! Both consumers of `alias::lookup` inherit these automatically: the
//! olean `ParserDescr` interpreter (`leanr_grammar::descr`, its
//! `ParserDescr.unary`/`const`/`binary` arms) and the source-level
//! `syntax`-command derivation (`grammar::surface`).
//!
//! # Ranking method (Task 11 Step 1)
//!
//! The M3b3 sweep had not been run when this table was authored (the
//! M3b2b `passlist:update` sweep was still in flight and the sweep does
//! NOT log alias-miss names anywhere), so candidates were ranked by a
//! STATIC CORPUS SCAN (brief method (a), the zero-conflict one): every
//! `.lean` under `.mathlib/Mathlib/**` + `.mathlib/.lake/packages/**`
//! was scanned for parser-alias CALLS inside `syntax`/`notation`
//! commands — a no-whitespace `funcName(` token (Lean's DSL requires no
//! space before the paren for a real combinator application; `foo (x)`
//! with a space is juxtaposition, not a call) — minus the names
//! `alias::lookup` already resolves and the `sepBy`/`sepBy1` forms
//! `surface.rs` handles in its own dedicated arm. Each surviving name
//! was counted by DISTINCT FILE. Registration was then confirmed against
//! the pinned toolchain source (`leanprover/lean4:v4.32.0-rc1`,
//! `.../src/lean/Lean/Parser.lean` + `Extra.lean`) — an unregistered
//! name cannot be shimmed (lean itself rejects it), and a name needing
//! more than one new `Prim` variant is DEFERRED (this is a table, not an
//! engine extension).
//!
//! ## Ranked table (name → files-blocked → decision)
//!
//! | name              | files | decision                                                                 |
//! |-------------------|-------|--------------------------------------------------------------------------|
//! | `withoutPosition` |   6   | CHOSEN — registered alias (`Parser.lean:51`); one new `Prim` variant     |
//! |                   |       | (`WithoutPosition`, pos-stack clear) — the position counterpart of the   |
//! |                   |       | existing `WithPosition`.                                                  |
//! | `withoutForbidden`|   1   | CHOSEN — registered alias (`Parser.lean:52`); maps to the ALREADY-        |
//! |                   |       | existing `Prim::WithoutForbidden` (zero new machinery).                   |
//! | `superscript`     |   3   | DEFERRED — NOT a core `registerParserAlias`; a Mathlib-defined parser     |
//! |                   |       | (`Mathlib/Tactic/Superscript`) needing a superscript-digit scanning       |
//! |                   |       | engine (multiple new `Prim` variants + lexer support).                    |
//! | `interpolatedStr` |   2   | DEFERRED — registered alias (`Parser.lean:53`) but needs the `s!"..."`    |
//! |                   |       | interpolation scanner (`StrInterpolation.lean`); >1 new `Prim` variant.   |
//! | `subscript`       |   1   | DEFERRED — same family as `superscript`; Mathlib-defined, engine-level.   |
//! | `rawIdent`        |   1   | DEFERRED — registered nullary alias (`Parser.lean:37`) but appears only   |
//! |                   |       | QUALIFIED (`Parser.rawIdent`) in 2 `#help` syntaxes in 1 file; a bare     |
//! |                   |       | unknown cat-name already soft-resolves to a `Category`, so it does not    |
//! |                   |       | HARD-block derivation the way a unary call does. Not worth an entry.      |
//! | `manyIndent`      |   0   | DEFERRED — registered alias (`Parser.lean:47`) but ZERO Mathlib call-     |
//! |                   |       | sites; no new `Prim::ManyIndent` earns its keep today.                    |
//!
//! Two entries CHOSEN, five deferred. The cap is 10; the data ranks far
//! fewer as impactful, and honesty over volume is the brief's rule — the
//! only two combinator-CALL names in the whole Mathlib+packages corpus
//! that (a) a `syntax` command actually applies, (b) the pinned
//! toolchain registers, and (c) fit within one new `Prim` variant are
//! `withoutPosition` and `withoutForbidden`.

use std::sync::Arc;

use super::alias::AliasPrim;
use super::Prim;

/// Second-chance alias resolution — see the module header for the
/// ranking method and the full chosen/deferred table. Same contract as
/// `alias::lookup`: `None` still means skip-and-record.
pub(crate) fn shim_lookup(name: &str) -> Option<AliasPrim> {
    use AliasPrim::*;
    Some(match name {
        "withoutPosition" => Unary(|p| Prim::WithoutPosition(Arc::new(p))),
        "withoutForbidden" => Unary(|p| Prim::WithoutForbidden(Arc::new(p))),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn chosen_shims_map_to_their_prims() {
        let Some(AliasPrim::Unary(f)) = shim_lookup("withoutPosition") else {
            panic!("withoutPosition must resolve to a Unary shim");
        };
        assert!(matches!(f(Prim::Ident), Prim::WithoutPosition(_)));

        let Some(AliasPrim::Unary(g)) = shim_lookup("withoutForbidden") else {
            panic!("withoutForbidden must resolve to a Unary shim");
        };
        assert!(matches!(g(Prim::Ident), Prim::WithoutForbidden(_)));
    }

    /// Deferred / unrelated names stay `None` (skip-and-record) — the
    /// table is capped and deliberately partial, and the miss path
    /// through `alias::lookup` must remain a true miss for everything
    /// not explicitly shimmed.
    #[test]
    fn deferred_and_unknown_names_stay_none() {
        for n in [
            "superscript",
            "subscript",
            "interpolatedStr",
            "rawIdent",
            "manyIndent",
            "nonsense",
        ] {
            assert!(shim_lookup(n).is_none(), "{n} must stay a miss");
        }
    }
}
