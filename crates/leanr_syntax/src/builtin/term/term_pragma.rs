//! The elaborator-internal "pragma" terms (30 rows — the surface
//! table's own characterization: "obscure, syntactically trivial, no
//! M3b dependency... same 'obscure but trivial' logic as `#exit`") plus
//! the 2-row parser-authoring meta-DSL (`leading_parser`/
//! `trailing_parser`). ORACLE-PORT `Lean/Parser/Term.lean` (`stateRefT`
//! through `debugAssert`, `«leading_parser»`/`«trailing_parser»`) plus
//! one row outside `Lean/Parser/`: `elabToSyntax`
//! (`Lean/Elab/Term/TermElabM.lean:815`). Every shape below was
//! cross-checked against fresh oracle dumps (`probe1.lean`/
//! `probe2.lean`, task-8-wave2 report), not just read off the source.
//!
//! `super::*` pulls in `term.rs`'s private helpers (`nd`, `binder_ident`,
//! `term_hole`) and the `crate::grammar::*`/`Prim` glob it already
//! imports.
//!
//! **Divergence, all six `throwNamedError[At]Macro`/
//! `logNamedError[At]Macro`/`logNamedWarning[At]Macro`**: each real
//! shape is `.. >> (interpolatedStr termParser <|> termParser maxPrec)`
//! — only the plain `termParser maxPrec` alternative is ported.
//! `interpolatedStr` (`StrInterpolation.lean`) is real string-
//! interpolation lexing/parsing machinery with no `@[builtin_..._parser]`
//! attribute of its own (not itself a surface-table row) and no fixture
//! needs it — same treatment `dbgTrace` (`term_app.rs`) already
//! documents for its own `interpolatedStr` alternative.

use super::*;

/// `macroArg := termParser maxPrec` — a plain alias, NOT itself a
/// `leading_parser` (no node wrap; confirmed against a fresh dump of
/// `StateRefT Foo Bar`, whose first argument is a bare ident, no extra
/// wrapper).
fn macro_arg() -> Prim {
    cat("term", MAX_PREC)
}
/// `macroDollarArg := leading_parser "$" >> termParser 10` — unlike
/// `macroArg`, this ONE IS a real `leading_parser` (own node).
/// Confirmed against a fresh dump of `StateRefT Foo $ Baz`: the `$ Baz`
/// argument wraps in its own `Lean.Parser.Term.macroDollarArg{ "$",
/// ident }` node.
fn macro_dollar_arg(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.macroDollarArg");
    nd(k, seq([sym("$"), cat("term", 10)]))
}
/// `macroLastArg := macroDollarArg <|> macroArg`.
fn macro_last_arg(b: &mut SnapshotBuilder) -> Prim {
    let dollar = macro_dollar_arg(b);
    or_else([dollar, macro_arg()])
}

/// `identWithPartialTrailingDot`, ORACLE-PORT Extra.lean: `ident`
/// followed by an optional, no-surrounding-whitespace `"." ident` tail
/// — a plain `Parser` sequence (no `leading_parser`), so it contributes
/// a bare ident leaf plus a null, not a node of its own. `command.rs`'s
/// module-header `import` already inlines this same shape (Task 7);
/// duplicated here as a named fn rather than shared across the
/// `command`/`term` module boundary, since that boundary predates this
/// task.
fn ident_with_partial_trailing_dot() -> Prim {
    seq([
        Prim::Ident,
        opt(seq([
            Prim::CheckNoWsBefore,
            sym("."),
            Prim::CheckNoWsBefore,
            Prim::Ident,
        ])),
    ])
}

/// `optExprPrecedence := optional (atomic ":" >> termParser maxPrec)`
/// (`Term.lean:388`) — `atomic` scopes over the `":"` token ALONE (the
/// oracle's `>>` binds tighter than the outer `optional`'s argument, so
/// it parses as `optional ((atomic ":") >> termParser maxPrec)`, NOT
/// `optional (atomic (":" >> termParser maxPrec))`). This matters:
/// scoping `atomic` over both would let backtracking swallow a partial
/// `":" >> termParser maxPrec` failure silently past the `":"` itself;
/// scoping it over `":"` alone means only the bare colon token is tried
/// atomically, and once a `":"` is committed the following
/// `termParser maxPrec` is required (a real parse failure there is NOT
/// backtracked over). Used by `«leading_parser»`/`«trailing_parser»`
/// below.
fn opt_expr_precedence() -> Prim {
    opt(seq([atomic(sym(":")), cat("term", MAX_PREC)]))
}

/// `matchExprPat := leading_parser optional (atomic (ident >> "@")) >>
/// ident >> many binderIdent` — shared by `matchExpr` (via
/// `matchExprAlt`) AND `letExpr` directly. Confirmed against a fresh
/// dump of `match_expr` / `let_expr` (task-8-wave2 report probes):
/// `Lean.Parser.Term.matchExprPat{ null(optional empty), ident "Foo",
/// null(many [a, b]) }`.
pub(in crate::builtin) fn match_expr_pat(b: &mut SnapshotBuilder) -> Prim {
    let bi = binder_ident(b);
    let k = b.kind("Lean.Parser.Term.matchExprPat");
    nd(
        k,
        seq([
            opt(atomic(seq([Prim::Ident, sym("@")]))),
            Prim::Ident,
            many(bi),
        ]),
    )
}
/// `matchExprAlt (rhsParser) := leading_parser "| " >> ppIndent
/// (matchExprPat >> " => " >> rhsParser)` — `rhs` is a REAL parameter
/// (Task 9 — was hardcoded to `termParser` until `do_notation.rs`'s
/// `doMatchExpr` needed its own `rhsParser := doSeq`; the real
/// declaration's `matchExprAltExpr` generic instantiation is a
/// quotation-only convenience, M3b, not another call site this port
/// needs).
pub(super) fn match_expr_alt(b: &mut SnapshotBuilder, rhs: Prim) -> Prim {
    let pat = match_expr_pat(b);
    let k = b.kind("Lean.Parser.Term.matchExprAlt");
    nd(k, seq([sym("|"), pat, sym("=>"), rhs]))
}
/// `matchExprElseAlt (rhsParser) := leading_parser "| " >> ppIndent
/// (hole >> " => " >> rhsParser)`.
pub(super) fn match_expr_else_alt(b: &mut SnapshotBuilder, rhs: Prim) -> Prim {
    let hole = term_hole(b);
    let k = b.kind("Lean.Parser.Term.matchExprElseAlt");
    nd(k, seq([sym("|"), hole, sym("=>"), rhs]))
}
/// `matchExprAlts (rhsParser) := leading_parser withPosition $ many
/// (ppLine >> checkColGe "irrelevant" >> notFollowedBy (symbol "| " >>
/// " _ ") "irrelevant" >> matchExprAlt rhsParser) >> (ppLine >>
/// checkColGe .. >> matchExprElseAlt rhsParser)`. Confirmed against a
/// fresh dump of `match_expr e with | Foo a b => a | _ => e`:
/// `Lean.Parser.Term.matchExprAlts{ null([matchExprAlt]),
/// matchExprElseAlt }`. `rhs` is cloned once per alt-kind (`matchExprAlt`
/// / `matchExprElseAlt`), matching each's own independent `rhsParser`
/// instantiation in the oracle.
pub(in crate::builtin) fn match_expr_alts(b: &mut SnapshotBuilder, rhs: Prim) -> Prim {
    let alt = match_expr_alt(b, rhs.clone());
    let else_alt = match_expr_else_alt(b, rhs);
    let k = b.kind("Lean.Parser.Term.matchExprAlts");
    nd(
        k,
        Prim::WithPosition(Arc::new(seq([
            many(seq([
                Prim::CheckColGe,
                Prim::NotFollowedBy(Arc::new(seq([sym("|"), sym("_")]))),
                alt,
            ])),
            Prim::CheckColGe,
            else_alt,
        ]))),
    )
}

fn register_match_expr_let_expr(b: &mut SnapshotBuilder) {
    // matchExpr := leading_parser:leadPrec "match_expr " >> termParser
    // >> " with" >> ppDedent (matchExprAlts termParser).
    let alts = match_expr_alts(b, cat("term", 0));
    b.leading2(
        "term",
        "Lean.Parser.Term.matchExpr",
        LEAD_PREC,
        seq([sym("match_expr"), cat("term", 0), sym("with"), alts]),
    );
    // letExpr := leading_parser:leadPrec withPosition ("let_expr " >>
    // matchExprPat >> " := " >> termParser >> checkColGt >> " | " >>
    // termParser) >> optSemicolon termParser. Only the explicit ";"
    // form of `optSemicolon` is ported (this file's established
    // convention throughout `term.rs`/`term_app.rs`).
    let pat = match_expr_pat(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.letExpr",
        LEAD_PREC,
        seq([
            Prim::WithPosition(Arc::new(seq([
                sym("let_expr"),
                pat,
                sym(":="),
                cat("term", 0),
                Prim::CheckColGt,
                sym("|"),
                cat("term", 0),
            ]))),
            sym(";"),
            cat("term", 0),
        ]),
    );
}

fn register_state_ref_t_and_show_term_elab(b: &mut SnapshotBuilder) {
    // stateRefT := leading_parser (bare, MAX_PREC) "StateRefT " >>
    // macroArg >> ppSpace >> macroLastArg.
    let last = macro_last_arg(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.stateRefT",
        MAX_PREC,
        seq([sym("StateRefT"), macro_arg(), last]),
    );
    // showTermElabImpl := leading_parser:leadPrec "show_term_elab " >>
    // termParser.
    b.leading2(
        "term",
        "Lean.Parser.Term.showTermElabImpl",
        LEAD_PREC,
        seq([sym("show_term_elab"), cat("term", 0)]),
    );
}

/// The six `throwNamedError[At]Macro`/`logNamedError[At]Macro`/
/// `logNamedWarning[At]Macro` productions — all bare `leading_parser`s
/// (MAX_PREC), two shapes: the non-`At` four take `identWithPartial
/// TrailingDot >> termParser maxPrec` (skipping the `interpolatedStr`
/// alternative, see module doc); the `At` two additionally take a
/// leading `termParser maxPrec` (the `Syntax` to attribute the
/// error/log to) before the ident.
fn register_named_error_log_macros(b: &mut SnapshotBuilder) {
    let plain = |kw: &'static str| {
        seq([
            sym(kw),
            ident_with_partial_trailing_dot(),
            cat("term", MAX_PREC),
        ])
    };
    let at = |kw: &'static str| {
        seq([
            sym(kw),
            cat("term", MAX_PREC),
            ident_with_partial_trailing_dot(),
            cat("term", MAX_PREC),
        ])
    };
    b.leading2(
        "term",
        "Lean.Parser.Term.throwNamedErrorMacro",
        MAX_PREC,
        plain("throwNamedError"),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.throwNamedErrorAtMacro",
        MAX_PREC,
        at("throwNamedErrorAt"),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.logNamedErrorMacro",
        MAX_PREC,
        plain("logNamedError"),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.logNamedErrorAtMacro",
        MAX_PREC,
        at("logNamedErrorAt"),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.logNamedWarningMacro",
        MAX_PREC,
        plain("logNamedWarning"),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.logNamedWarningAtMacro",
        MAX_PREC,
        at("logNamedWarningAt"),
    );
}

/// The elaborator-context "meta pragma" family (`declName` through
/// `noErrorIfUnused`): fixed-shape, mostly `ident`/`termParser`
/// sequences, no shared structure worth a helper beyond `macro_arg`-
/// style directness. All bare `leading_parser`s (MAX_PREC) except where
/// noted. Confirmed shapes against fresh dumps of every one of these in
/// `probe2.lean` (task-8-wave2 report).
fn register_meta_pragmas(b: &mut SnapshotBuilder) {
    // declName := leading_parser "decl_name%" (no further tokens).
    b.leading2(
        "term",
        "Lean.Parser.Term.declName",
        MAX_PREC,
        sym("decl_name%"),
    );
    // «privateDecl» := leading_parser "private_decl% " >> termParser
    // maxPrec.
    b.leading2(
        "term",
        "Lean.Parser.Term.privateDecl",
        MAX_PREC,
        seq([sym("private_decl%"), cat("term", MAX_PREC)]),
    );
    // withDeclName := leading_parser "with_decl_name% " >> optional "?"
    // >> ident >> ppSpace >> termParser.
    b.leading2(
        "term",
        "Lean.Parser.Term.withDeclName",
        MAX_PREC,
        seq([
            sym("with_decl_name%"),
            opt(sym("?")),
            Prim::Ident,
            cat("term", 0),
        ]),
    );
    // typeOf := leading_parser "type_of% " >> termParser maxPrec.
    b.leading2(
        "term",
        "Lean.Parser.Term.typeOf",
        MAX_PREC,
        seq([sym("type_of%"), cat("term", MAX_PREC)]),
    );
    // ensureTypeOf := leading_parser "ensure_type_of% " >> termParser
    // maxPrec >> strLit >> ppSpace >> termParser.
    b.leading2(
        "term",
        "Lean.Parser.Term.ensureTypeOf",
        MAX_PREC,
        seq([
            sym("ensure_type_of%"),
            cat("term", MAX_PREC),
            Prim::StrLit,
            cat("term", 0),
        ]),
    );
    // ensureExpectedType := leading_parser "ensure_expected_type% " >>
    // strLit >> ppSpace >> termParser maxPrec.
    b.leading2(
        "term",
        "Lean.Parser.Term.ensureExpectedType",
        MAX_PREC,
        seq([
            sym("ensure_expected_type%"),
            Prim::StrLit,
            cat("term", MAX_PREC),
        ]),
    );
    // noImplicitLambda := leading_parser "no_implicit_lambda% " >>
    // termParser maxPrec.
    b.leading2(
        "term",
        "Lean.Parser.Term.noImplicitLambda",
        MAX_PREC,
        seq([sym("no_implicit_lambda%"), cat("term", MAX_PREC)]),
    );
    // «inferInstanceAs» := leading_parser "inferInstanceAs" >>
    // (((" $ " <|> " <| ") >> termParser minPrec) <|> (ppSpace >>
    // termParser argPrec)).
    b.leading2(
        "term",
        "Lean.Parser.Term.inferInstanceAs",
        MAX_PREC,
        seq([
            sym("inferInstanceAs"),
            or_else([
                seq([or_else([sym("$"), sym("<|")]), cat("term", MIN_PREC)]),
                cat("term", ARG_PREC),
            ]),
        ]),
    );
    // valueOf := leading_parser "value_of% " >> ident.
    b.leading2(
        "term",
        "Lean.Parser.Term.valueOf",
        MAX_PREC,
        seq([sym("value_of%"), Prim::Ident]),
    );
    // clear := leading_parser "clear% " >> ident >> semicolonOrLinebreak
    // >> ppDedent ppLine >> termParser. Only the explicit ";" form of
    // `semicolonOrLinebreak` is ported (same convention as
    // `optSemicolon` elsewhere).
    b.leading2(
        "term",
        "Lean.Parser.Term.clear",
        MAX_PREC,
        seq([sym("clear%"), Prim::Ident, sym(";"), cat("term", 0)]),
    );
    // letMVar := leading_parser "let_mvar% " >> "?" >> ident >> " := "
    // >> termParser >> "; " >> termParser.
    b.leading2(
        "term",
        "Lean.Parser.Term.letMVar",
        MAX_PREC,
        seq([
            sym("let_mvar%"),
            sym("?"),
            Prim::Ident,
            sym(":="),
            cat("term", 0),
            sym(";"),
            cat("term", 0),
        ]),
    );
    // waitIfTypeMVar / waitIfTypeContainsMVar / waitIfContainsMVar :=
    // leading_parser "wait_if_..._mvar% " >> "?" >> ident >> "; " >>
    // termParser.
    for (kind, kw) in [
        ("Lean.Parser.Term.waitIfTypeMVar", "wait_if_type_mvar%"),
        (
            "Lean.Parser.Term.waitIfTypeContainsMVar",
            "wait_if_type_contains_mvar%",
        ),
        (
            "Lean.Parser.Term.waitIfContainsMVar",
            "wait_if_contains_mvar%",
        ),
    ] {
        b.leading2(
            "term",
            kind,
            MAX_PREC,
            seq([sym(kw), sym("?"), Prim::Ident, sym(";"), cat("term", 0)]),
        );
    }
    // defaultOrOfNonempty := leading_parser "default_or_ofNonempty% " >>
    // optional "unsafe".
    b.leading2(
        "term",
        "Lean.Parser.Term.defaultOrOfNonempty",
        MAX_PREC,
        seq([sym("default_or_ofNonempty%"), opt(sym("unsafe"))]),
    );
    // noErrorIfUnused := leading_parser "no_error_if_unused% " >>
    // termParser.
    b.leading2(
        "term",
        "Lean.Parser.Term.noErrorIfUnused",
        MAX_PREC,
        seq([sym("no_error_if_unused%"), cat("term", 0)]),
    );
    // elabToSyntax := leading_parser "elabToSyntax% " >> Parser.numLit
    // (bare, MAX_PREC; `Lean/Elab/Term/TermElabM.lean:815`, the ONE
    // term-category row outside `Lean/Parser/`).
    b.leading2(
        "term",
        "Lean.Parser.Term.elabToSyntax",
        MAX_PREC,
        seq([sym("elabToSyntax%"), Prim::NumLit]),
    );
}

/// `«idbg»`/`assert`/`debugAssert` — all `leading_parser:leadPrec
/// withPosition (kw >> [checkColGt >>] termParser) >> optSemicolon
/// termParser` (only `«idbg»` has the extra `checkColGt`, a zero-width
/// no-op either way). Confirmed against fresh dumps of `idbg x; y` /
/// `assert! x; y` / `debug_assert! x; y`.
fn register_idbg_assert_family(b: &mut SnapshotBuilder) {
    b.leading2(
        "term",
        "Lean.Parser.Term.idbg",
        LEAD_PREC,
        seq([
            Prim::WithPosition(Arc::new(seq([
                sym("idbg"),
                Prim::CheckColGt,
                cat("term", 0),
            ]))),
            sym(";"),
            cat("term", 0),
        ]),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.assert",
        LEAD_PREC,
        seq([
            Prim::WithPosition(Arc::new(seq([sym("assert!"), cat("term", 0)]))),
            sym(";"),
            cat("term", 0),
        ]),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.debugAssert",
        LEAD_PREC,
        seq([
            Prim::WithPosition(Arc::new(seq([sym("debug_assert!"), cat("term", 0)]))),
            sym(";"),
            cat("term", 0),
        ]),
    );
}

/// `«leading_parser»  := leading_parser:leadPrec "leading_parser" >>
/// optExprPrecedence >> optional withAnonymousAntiquot >> ppSpace >>
/// termParser`; `«trailing_parser» := leading_parser:leadPrec
/// "trailing_parser" >> optExprPrecedence >> optExprPrecedence >>
/// ppSpace >> termParser`. `withAnonymousAntiquot`'s inner
/// `trueVal <|> falseVal` detail isn't transcribed (no fixture forces
/// `leading_parser (withAnonymousAntiquot := true/false) ..`) — left as
/// a real, always-empty optional slot (the `opt(never())` idiom used
/// throughout this file for un-exercised optional sub-grammars).
/// Confirmed against fresh dumps of `leading_parser "foo"` /
/// `trailing_parser "foo"`: both show 4 flat children (keyword, two
/// empty `null`s, then the embedded term) — see module doc for why the
/// fixture avoids a `>>`-composed body (that needs `Init`'s `>>`
/// notation, unavailable under M3a's builtin-only grammar).
fn register_parser_meta_dsl(b: &mut SnapshotBuilder) {
    b.leading2(
        "term",
        "Lean.Parser.Term.leading_parser",
        LEAD_PREC,
        seq([
            sym("leading_parser"),
            opt_expr_precedence(),
            opt(never()),
            cat("term", 0),
        ]),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.trailing_parser",
        LEAD_PREC,
        seq([
            sym("trailing_parser"),
            opt_expr_precedence(),
            opt_expr_precedence(),
            cat("term", 0),
        ]),
    );
}

pub(super) fn register(b: &mut SnapshotBuilder) {
    register_state_ref_t_and_show_term_elab(b);
    register_match_expr_let_expr(b);
    register_named_error_log_macros(b);
    register_meta_pragmas(b);
    register_idbg_assert_family(b);
    register_parser_meta_dsl(b);
}
