//! The 19 "app/proj extras" from the term category's App/projection/
//! structural machinery section (docs/superpowers/specs/
//! 2026-07-13-m3a-builtin-surface.md) that Task 8 wave 1 left unported:
//! `dotIdent`, `namedPattern`, `pipeProj`, `pipeCompletion`, `subst`,
//! `panic`, `unreachable`, `dbgTrace`, `borrowed`, `noindex`, `binrel`,
//! `binrel_no_prop`, `binop`, `binop_lazy`, `leftact`, `rightact`,
//! `unop`, `forInMacro`, `forInMacro'`. ORACLE-PORT `Lean/Parser/
//! Term.lean` — every shape below was cross-checked against a fresh
//! oracle dump (`probe1.lean`/`probe2.lean`, task-8-wave2 report) as
//! well as read off the source.
//!
//! `super::*` pulls in `term.rs`'s private helpers (`nd`, `argument`,
//! `explicit_univ_suffix`) and the `crate::grammar::*`/`Prim` glob it
//! already imports — private `use`s are visible to descendant modules
//! in Rust, so nothing needs re-exporting.

use super::*;

/// `dotIdent := leading_parser "." >> checkNoWsBefore >> rawIdent`
/// (bare, MAX_PREC). `rawIdent` and `Prim::Ident` produce the same
/// syntax tree (ORACLE-PORT Extra.lean's own comment on `rawIdent`:
/// "`ident` and `rawIdent` produce the same syntax tree, so we reuse
/// the antiquotation kind name") — same substitution `proj`'s `fieldIdx
/// <|> rawIdent` alternative already relies on (Task 8 wave 1).
/// Confirmed against a fresh dump of `.mk`: `{"a":".","i":"mk"}` under
/// `Lean.Parser.Term.dotIdent`, two children, no further wrap.
fn register_dot_ident(b: &mut SnapshotBuilder) {
    b.leading2(
        "term",
        "Lean.Parser.Term.dotIdent",
        MAX_PREC,
        seq([sym("."), Prim::CheckNoWsBefore, Prim::Ident]),
    );
}

/// `namedPattern : TrailingParser := trailing_parser checkStackTop
/// isIdent .. >> checkNoWsBefore "no space before '@'" >> "@" >>
/// optional (atomic (ident >> ":")) >> termParser maxPrec` (bare
/// `trailing_parser`, so MAX_PREC/MAX_PREC like `proj`/`completion`).
/// `checkStackTop` (verifying the already-parsed lhs is a plain ident)
/// has no `Prim` counterpart — same documented skip `explicitUniv`
/// already uses (Task 8 wave 1) for its own `checkStackTop`. Confirmed
/// against a fresh dump of `y@Foo.mk`: `Lean.Parser.Term.namedPattern{
/// "@", null(empty), ident "Foo.mk" }` (note: `Foo.mk` lexes as ONE
/// dotted ident token, not app/proj — ordinary Lean qualified-name
/// lexing, unrelated to this port).
fn register_named_pattern(b: &mut SnapshotBuilder) {
    b.trailing2(
        "term",
        "Lean.Parser.Term.namedPattern",
        MAX_PREC,
        MAX_PREC,
        seq([
            Prim::CheckNoWsBefore,
            sym("@"),
            opt(atomic(seq([Prim::Ident, sym(":")]))),
            cat("term", MAX_PREC),
        ]),
    );
}

/// `pipeProj := trailing_parser:minPrec " |>." >> checkNoWsBefore >>
/// (fieldIdx <|> rawIdent) >> optional explicitUnivSuffix >> many
/// argument` — `:minPrec` sets BOTH prec and lhsPrec to `minPrec` (the
/// same single-number convention `level.rs`'s `addLit:65` and `subst`
/// below use). Shares `explicit_univ_suffix`/`argument` verbatim with
/// `explicitUniv`/`app` (`term.rs`, hoisted this wave for exactly this
/// reuse). Confirmed against a fresh dump of `x |>.foo`: atom `"|>."`
/// (NOT three separate tokens), then ident "foo", then two empty
/// `null`s (the unexercised `optional explicitUnivSuffix`/`many
/// argument` slots).
fn register_pipe_proj(b: &mut SnapshotBuilder) {
    b.trailing2(
        "term",
        "Lean.Parser.Term.pipeProj",
        MIN_PREC,
        MIN_PREC,
        seq([
            sym("|>."),
            Prim::CheckNoWsBefore,
            or_else([Prim::FieldIdx, Prim::Ident]),
            opt(explicit_univ_suffix()),
            many(argument()),
        ]),
    );
    // pipeCompletion := trailing_parser:minPrec " |>." (bare symbol,
    // same token as `pipeProj`'s prefix — ordinary longest-match tells
    // them apart, same mechanism as `cdot`/`dotIdent`'s shared "." lead:
    // `x |>.foo` lets `pipeProj` consume further and win; `x |>.` alone
    // leaves `pipeCompletion` the longest match). Confirmed against a
    // fresh dump of `x |>.`.
    b.trailing2(
        "term",
        "Lean.Parser.Term.pipeCompletion",
        MIN_PREC,
        MIN_PREC,
        sym("|>."),
    );
}

/// `subst := trailing_parser:75 " ▸ " >> sepBy1 (termParser 75) " ▸ "`
/// — `:75` sets both prec/lhsPrec to 75 (same convention as `addLit`).
/// Confirmed against a fresh dump of `h ▸ x`: `Lean.Parser.Term.subst{
/// "▸", null(sepBy1 [ident x]) }`.
fn register_subst(b: &mut SnapshotBuilder) {
    b.trailing2(
        "term",
        "Lean.Parser.Term.subst",
        75,
        75,
        seq([sym("▸"), sep_by1(cat("term", 75), "▸")]),
    );
}

/// `panic := leading_parser:leadPrec "panic! " >> termParser`;
/// `unreachable := leading_parser:leadPrec "unreachable!"` (no
/// argument). Both confirmed against fresh dumps (`panic! "boom"`,
/// `unreachable!`).
fn register_panic_unreachable(b: &mut SnapshotBuilder) {
    b.leading2(
        "term",
        "Lean.Parser.Term.panic",
        LEAD_PREC,
        seq([sym("panic!"), cat("term", 0)]),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.unreachable",
        LEAD_PREC,
        sym("unreachable!"),
    );
}

/// `dbgTrace := leading_parser:leadPrec withPosition ("dbg_trace" >>
/// (interpolatedStr termParser <|> termParser)) >> optSemicolon
/// termParser`. **Divergence**: only the plain `termParser` alternative
/// is ported — `interpolatedStr` (string-interpolation lexing/parsing,
/// `StrInterpolation.lean`) is real, non-trivial machinery with no
/// `@[builtin_..._parser]` attribute of its own (not itself a surface-
/// table row) and no fixture needs it; same treatment `optSemicolon`
/// already gets throughout this file (only the explicit `";"` form of
/// `semicolonOrLinebreak`/`optSemicolon`'s two alternatives is ported).
/// Confirmed shape against a fresh dump of `dbg_trace x; y`.
fn register_dbg_trace(b: &mut SnapshotBuilder) {
    b.leading2(
        "term",
        "Lean.Parser.Term.dbgTrace",
        LEAD_PREC,
        seq([
            Prim::WithPosition(Arc::new(seq([sym("dbg_trace"), cat("term", 0)]))),
            sym(";"),
            cat("term", 0),
        ]),
    );
}

/// `borrowed := leading_parser "@& " >> termParser leadPrec` (bare,
/// MAX_PREC). Confirmed against a fresh dump of `f (@& x)`.
fn register_borrowed(b: &mut SnapshotBuilder) {
    b.leading2(
        "term",
        "Lean.Parser.Term.borrowed",
        MAX_PREC,
        seq([sym("@&"), cat("term", LEAD_PREC)]),
    );
}

/// `noindex := leading_parser "no_index " >> termParser maxPrec` (bare,
/// MAX_PREC). Confirmed against a fresh dump of `no_index x`.
fn register_noindex(b: &mut SnapshotBuilder) {
    b.leading2(
        "term",
        "Lean.Parser.Term.noindex",
        MAX_PREC,
        seq([sym("no_index"), cat("term", MAX_PREC)]),
    );
}

/// The `binrel%`/`binop%`/`leftact%`/`rightact%`/`unop%` family
/// (Term.lean:761-786) — all bare `leading_parser`s (MAX_PREC), the
/// two-term-argument ones (`binrel[_no_prop]`/`binop[_lazy]`/
/// `leftact`/`rightact`) sharing one shape (`"kw% " >> ident >> ppSpace
/// >> termParser maxPrec >> ppSpace >> termParser maxPrec`), `unop%`
/// taking only ONE term argument. Confirmed against fresh dumps of
/// `binrel% Eq a b` / `binop% f a b` / `unop% f a`.
fn register_binop_family(b: &mut SnapshotBuilder) {
    let two_arg = |kw: &'static str| {
        seq([
            sym(kw),
            Prim::Ident,
            cat("term", MAX_PREC),
            cat("term", MAX_PREC),
        ])
    };
    b.leading2(
        "term",
        "Lean.Parser.Term.binrel",
        MAX_PREC,
        two_arg("binrel%"),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.binrel_no_prop",
        MAX_PREC,
        two_arg("binrel_no_prop%"),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.binop",
        MAX_PREC,
        two_arg("binop%"),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.binop_lazy",
        MAX_PREC,
        two_arg("binop_lazy%"),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.leftact",
        MAX_PREC,
        two_arg("leftact%"),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.rightact",
        MAX_PREC,
        two_arg("rightact%"),
    );
    // unop% := "unop% " >> ident >> ppSpace >> termParser maxPrec — ONE
    // term argument, not two.
    b.leading2(
        "term",
        "Lean.Parser.Term.unop",
        MAX_PREC,
        seq([sym("unop%"), Prim::Ident, cat("term", MAX_PREC)]),
    );
}

/// `forInMacro := leading_parser "for_in% " >> termParser maxPrec >>
/// termParser maxPrec >> ppSpace >> termParser maxPrec` (bare,
/// MAX_PREC, THREE term arguments, no `ident`); `forInMacro'` is the
/// same shape with the `for_in'%` keyword. Confirmed against a fresh
/// dump of `for_in% x y z`.
fn register_for_in_macro(b: &mut SnapshotBuilder) {
    let three_arg = |kw: &'static str| {
        seq([
            sym(kw),
            cat("term", MAX_PREC),
            cat("term", MAX_PREC),
            cat("term", MAX_PREC),
        ])
    };
    b.leading2(
        "term",
        "Lean.Parser.Term.forInMacro",
        MAX_PREC,
        three_arg("for_in%"),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.forInMacro'",
        MAX_PREC,
        three_arg("for_in'%"),
    );
}

pub(super) fn register(b: &mut SnapshotBuilder) {
    register_dot_ident(b);
    register_named_pattern(b);
    register_pipe_proj(b);
    register_subst(b);
    register_panic_unreachable(b);
    register_dbg_trace(b);
    register_borrowed(b);
    register_noindex(b);
    register_binop_family(b);
    register_for_in_macro(b);
}
