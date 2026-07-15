//! The `level` category (universe levels: `Sort u`, `Type (max u v)`,
//! …) — ORACLE-PORT `Lean/Parser/Level.lean` in full (7 declarations,
//! all `port` per docs/superpowers/specs/2026-07-13-m3a-builtin-surface.md's
//! level table). Small and self-contained; every shape below was
//! cross-checked against fresh oracle dumps (`Sort (max u v)`,
//! `Sort (imax u v)`, `Sort (u + 1)`, `Sort (u)`, `Sort max`, `Sort _`,
//! `Sort 1` — see task-8 report for the exact probes), not just read
//! off the source.
//!
//! ## The `NonReservedSymbol` dispatch fix this category needed
//!
//! `max`/`imax` (`Level.max`/`Level.imax`) are `nonReservedSymbol "max"
//! true`/`nonReservedSymbol "imax" true` — the `true` is `includeIdent`
//! (ORACLE-PORT `nonReservedSymbolInfo`, Basic.lean): because `max`'s
//! text is deliberately NEVER harvested into the token table (so it
//! keeps lexing as a plain `Ident` everywhere outside `level` position
//! — the whole point of `nonReservedSymbol`, see grammar.rs's
//! `walk_symbols` doc comment), `max`/`imax` could never be DISPATCHED
//! to at all: `parse.rs`'s `dispatch` only matched a `FirstTok::Sym`
//! entry against an `Atom`-kind token, and `max`'s token always lexes
//! as `Ident`. Fixed at the root (`parse.rs::dispatch`, not here): a
//! `FirstTok::Sym(s)` entry now ALSO matches an `Ident`-kind token whose
//! text equals `s` — exactly the oracle's dual `firstTokens := .tokens
//! [sym, "ident"]` registration, collapsed into one dispatch arm since
//! `first_tok` already maps both `Symbol` and `NonReservedSymbol` to the
//! same `FirstTok::Sym`. See parse.rs's `dispatch` fn doc comment for
//! the full citation.
//!
//! Once dispatch could even try the `max`/`imax` candidates, ordinary
//! longest-match does the rest: `max`/`imax` alone (no level following,
//! e.g. `Sort max`) makes `many1(levelParser maxPrec)` fail — that
//! candidate loses to the plain `Level.ident` candidate, which wins by
//! successfully consuming the bare ident "max" (confirmed against a
//! fresh dump: `Sort max`'s level slot is a bare `ident "max"`, NOT a
//! `Level.max` node). And in "term" position (a completely separate
//! category/dispatch table), plain `max` is unaffected — it dispatches
//! only against `term`'s `FirstTok::Ident` entry (`Term.ident`), never
//! sees `level`'s `Sym("max")` entry at all. Both directions are
//! covered by this file's tests.

use crate::grammar::*;

pub fn register(b: &mut SnapshotBuilder) {
    // paren  "(" level ")"  (bare `leading_parser`, no `:prec` — MAX_PREC)
    b.leading2(
        "level",
        "Lean.Parser.Level.paren",
        MAX_PREC,
        seq([sym("("), cat("level", 0), sym(")")]),
    );
    // max/imax: nonReservedSymbol(sym, includeIdent := true) >>
    // many1(levelParser maxPrec) — bare `leading_parser`, MAX_PREC.
    b.leading2(
        "level",
        "Lean.Parser.Level.max",
        MAX_PREC,
        seq([
            Prim::NonReservedSymbol("max".into()),
            many1(cat("level", MAX_PREC)),
        ]),
    );
    b.leading2(
        "level",
        "Lean.Parser.Level.imax",
        MAX_PREC,
        seq([
            Prim::NonReservedSymbol("imax".into()),
            many1(cat("level", MAX_PREC)),
        ]),
    );
    // hole: "_" (bare `leading_parser`, MAX_PREC).
    b.leading2("level", "Lean.Parser.Level.hole", MAX_PREC, sym("_"));
    // num := checkPrec maxPrec >> numLit — NOT a `leading_parser` (no
    // node wrap of its own: `NumLit` already self-wraps in a "num"
    // node, `leading2` would double-wrap it). `checkPrec maxPrec` is a
    // no-op here (MAX_PREC is the highest declared prec in the whole
    // system, so `self.prec <= MAX_PREC` always holds) — same reasoning
    // `command.rs`'s micro term set already relies on for `Term.ident`.
    b.leading_raw("level", Prim::NumLit);
    // ident := checkPrec maxPrec >> Parser.ident — likewise no node wrap.
    b.leading_raw("level", Prim::Ident);
    // addLit: trailing_parser:65 " + " >> numLit — the single `:65`
    // annotation supplies ONLY `prec`; `lhsPrec` is omitted and defaults
    // to `0`, NOT to 65 — ORACLE-PORT `BuiltinNotation.lean:194-197`
    // (`elabTParserMacroAux`: `lhsPrec?.getD <| quote 0`). So 65/0, not
    // 65/65 (a mistake this port previously made here and at several
    // `term` sites — see `term.rs`'s `completion`/`proj`/`explicitUniv`
    // and `term_app.rs`'s `namedPattern`/`pipeProj`/`pipeCompletion`/
    // `subst`, all fixed for the same reason).
    b.trailing2(
        "level",
        "Lean.Parser.Level.addLit",
        65,
        0,
        seq([sym("+"), Prim::NumLit]),
    );
}

// Integration tests exercising `max`/`imax` dispatch (incl. the
// NonReservedSymbol fix) live in `term.rs`'s test module: `level` is
// only reachable through `Term.sort`/`Term.type` (`Sort u`, `Type u`),
// so a standalone test here would need to duplicate that wiring.
// See `term::tests::{level_max_and_imax_..., bare_max_falls_back_...,
// plain_ident_max_in_term_position_...}`.
