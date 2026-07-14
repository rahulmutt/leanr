//! The `term` category's `port`-status rows (docs/superpowers/specs/
//! 2026-07-13-m3a-builtin-surface.md's term table) — ORACLE-PORT
//! `Lean/Parser/Term.lean` + `Lean/Parser/Term/Basic.lean`. Every shape
//! below was cross-checked against fresh oracle dumps (see task-8
//! report for the probe transcripts), not just read off the source —
//! several sub-parsers here (`hygienicLParen`/`hygieneInfo`,
//! `structInstLVal`, `matchAlt`, `letId`/`letIdDecl`/`letDecl`, …)
//! aren't themselves `@[builtin_term_parser]`-attributed (so they're
//! not separate rows in the surface table) but DO wrap in their own
//! named node (`leading_parser`), which only a real oracle dump makes
//! legible.
//!
//! This task ports the brief's "must-have set" for the M3a corpus, not
//! literally all 106 `port`-status term rows — every row NOT ported
//! here is listed with a reason in the task-8 report (mostly: needs
//! Task 9's `do`/tactic machinery, or is an obscure elaborator-internal
//! pragma with zero fixture value and no bearing on the M3a acceptance
//! bar). One `fn` per parser; `register` wires them into the category
//! in roughly source order.

use crate::grammar::*;
use crate::kind::{SyntaxKind, KIND_NULL};
use std::sync::Arc;

// This wave (M3a Task 8, second pass): the remaining `port`-status term
// rows the brief's "must-have set" left for a follow-up — pragma terms
// and the app/proj "extras" are large, self-contained groups, split
// into their own submodules per the plan's module-size discipline
// (term.rs was already ~960 lines). `cdot` and the `let`-family
// siblings stay here, colocated with the `paren`/`let`/`have` code they
// share helpers with.
mod term_app;
mod term_pragma;

// ================================================================
// Shared helpers (not their own surface-table rows; oracle-named
// sub-parsers used by several of the productions below).
// ================================================================

fn nd(kind: SyntaxKind, body: Prim) -> Prim {
    Prim::Node {
        kind,
        prec: None,
        body: Arc::new(body),
    }
}

/// `hygieneInfo` (Extra.lean): always succeeds, wraps a zero-width
/// empty `ident` in its own (unqualified — NOT `Lean.Parser.Term.*`;
/// confirmed against a fresh dump) `hygieneInfo` node.
fn hygiene_info(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("hygieneInfo");
    nd(k, Prim::EmitEmptyIdent)
}

/// `hygienicLParen := leading_parser (withAnonymousAntiquot := false)
/// "(" >> hygieneInfo` — the common `"(" >> hygieneInfo` prefix shared
/// by `paren`/`tuple`/`typeAscription`/`anonymousCtor`... (anonymousCtor
/// actually uses `⟨`, not this — see `anonymous_ctor`). Bare
/// `leading_parser`, so MAX_PREC; confirmed node-wraps in its own
/// `Lean.Parser.Term.hygienicLParen` kind (fresh dump: `(x)`'s first
/// child).
fn hygienic_lparen(b: &mut SnapshotBuilder) -> Prim {
    let hi = hygiene_info(b);
    let k = b.kind("Lean.Parser.Term.hygienicLParen");
    nd(k, seq([sym("("), hi]))
}

/// `Term/Basic.lean` `binderIdent := ident <|> hole` — `hole` here is
/// the real `Term.hole` parser (self-wraps in its own node when it's
/// the winning alternative; confirmed against `match n with | _ => ..`
/// dumps, whose pattern-position `_` is a `Lean.Parser.Term.hole` node
/// same as term-position `_`). `term_hole()` below is the SAME body
/// `Term.hole`'s own `leading2` registration uses (kept as one fn so
/// both call sites can't drift).
fn term_hole(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.hole");
    nd(k, sym("_"))
}
fn binder_ident(b: &mut SnapshotBuilder) -> Prim {
    let hole = term_hole(b);
    or_else([Prim::Ident, hole])
}

/// `binderType (requireType := false) := optional (" : " >> termParser)`;
/// `binderType (requireType := true) := node nullKind (" : " >>
/// termParser)` — a MANDATORY (never-empty) `null`-kind wrapper, used
/// by `depArrow`'s `bracketedBinder true`. `Prim::Optional` always
/// wraps in `KIND_NULL` too, so the ONLY difference is optionality;
/// building the `require_type` case directly out of `KIND_NULL` (a
/// fixed kind, no interning needed) reproduces `node nullKind (..)`
/// exactly.
fn binder_type(require_type: bool) -> Prim {
    let inner = seq([sym(":"), cat("term", 0)]);
    if require_type {
        Prim::Node {
            kind: KIND_NULL,
            prec: None,
            body: Arc::new(inner),
        }
    } else {
        opt(inner)
    }
}
/// `typeSpec := leading_parser " : " >> termParser`; `optType := optional
/// typeSpec` (Basic.lean:262,265). `typeSpec` IS its own `leading_parser`,
/// so a PRESENT `optType` wraps in a `Lean.Parser.Term.typeSpec` node
/// (inside `optional`'s own `null` wrapper): `null{ typeSpec{":", term} }`.
/// An ABSENT `optType` is the ordinary empty `null{}` `Prim::Optional`
/// produces. Confirmed by regenerated fixture dumps of `let x : T := v`
/// and `fun x : A => e` (both exercise a present `optType`), which show
/// exactly this shape — no fixture previously exercised a present
/// `optType`, which is why this was missed before.
fn opt_type(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.typeSpec");
    opt(nd(k, seq([sym(":"), cat("term", 0)])))
}

fn explicit_binder(b: &mut SnapshotBuilder, require_type: bool) -> Prim {
    let bi = binder_ident(b);
    let k = b.kind("Lean.Parser.Term.explicitBinder");
    nd(
        k,
        seq([
            sym("("),
            many1(bi),
            binder_type(require_type),
            // `optional (binderTactic <|> binderDefault)` — neither
            // sub-parser is transcribed (no fixture uses `(x : A := v)`
            // or `(x : A := by tac)`); left as a real, always-empty
            // optional slot (Task 7's `empty_opt()` idiom one level up).
            opt(never()),
            sym(")"),
        ]),
    )
}
fn implicit_binder(b: &mut SnapshotBuilder, require_type: bool) -> Prim {
    let bi = binder_ident(b);
    let k = b.kind("Lean.Parser.Term.implicitBinder");
    nd(
        k,
        seq([sym("{"), many1(bi), binder_type(require_type), sym("}")]),
    )
}
fn strict_implicit_binder(b: &mut SnapshotBuilder, require_type: bool) -> Prim {
    let bi = binder_ident(b);
    let k = b.kind("Lean.Parser.Term.strictImplicitBinder");
    // `strictImplicitLeftBracket := atomic (group (symbol "{" >> "{"))
    // <|> "⦃"`; ASCII `{{ }}` alt included for fidelity even though no
    // fixture exercises it.
    nd(
        k,
        seq([
            or_else([
                atomic(Prim::Group(Arc::new(seq([sym("{"), sym("{")])))),
                sym("⦃"),
            ]),
            many1(bi),
            binder_type(require_type),
            or_else([
                atomic(Prim::Group(Arc::new(seq([sym("}"), sym("}")])))),
                sym("⦄"),
            ]),
        ]),
    )
}
fn inst_binder(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.instBinder");
    // `optIdent := optional (atomic (ident >> " : "))`.
    let opt_ident = opt(atomic(seq([Prim::Ident, sym(":")])));
    nd(k, seq([sym("["), opt_ident, cat("term", 0), sym("]")]))
}
/// `bracketedBinder (requireType) := explicitBinder <|>
/// strictImplicitBinder <|> implicitBinder <|> instBinder` (source
/// order — `<|>` is plain PEG orelse here, not a Pratt longest-match,
/// so order matters, though in practice each alternative's own leading
/// bracket makes them mutually exclusive anyway).
fn bracketed_binder(b: &mut SnapshotBuilder, require_type: bool) -> Prim {
    let e = explicit_binder(b, require_type);
    let si = strict_implicit_binder(b, require_type);
    let i = implicit_binder(b, require_type);
    let inst = inst_binder(b);
    or_else([e, si, i, inst])
}

// ================================================================
// Core literals/atoms.
// ================================================================

fn register_literals(b: &mut SnapshotBuilder) {
    // ident/num/scientific/str/char := checkPrec maxPrec >> <lexer
    // leaf> — NOT `leading_parser` (no node wrap of their own; the
    // literal `Prim`s already self-wrap where the oracle does —
    // `NumLit`/`ScientificLit`/`StrLit`/`CharLit` each wrap in their own
    // "num"/"scientific"/"str"/"char" node, `Ident` doesn't wrap at
    // all). `leading2` would double-wrap; `leading_raw` matches the
    // Task-7 micro set's existing `Term.ident`/`Term.num` precedent
    // exactly (moved here per the brief's Step 2).
    b.leading_raw("term", Prim::Ident);
    b.leading_raw("term", Prim::NumLit);
    b.leading_raw("term", Prim::ScientificLit);
    b.leading_raw("term", Prim::StrLit);
    b.leading_raw("term", Prim::CharLit);
    // «sorry» := leading_parser "sorry" (bare leading_parser, MAX_PREC).
    b.leading2("term", "Lean.Parser.Term.sorry", MAX_PREC, sym("sorry"));
    // omission := leading_parser "⋯".
    b.leading2("term", "Lean.Parser.Term.omission", MAX_PREC, sym("⋯"));
    // quotedName := leading_parser nameLit — IS `leading_parser` (node
    // wrap), unlike ident/num/etc: confirmed a fresh dump of `` `foo.bar
    // `` shows `Lean.Parser.Term.quotedName` wrapping `NameLit`'s own
    // self-wrapped "name" node (double-wrap, not a `leading_raw`).
    b.leading2(
        "term",
        "Lean.Parser.Term.quotedName",
        MAX_PREC,
        Prim::NameLit,
    );
    // doubleQuotedName := leading_parser "`" >> checkNoWsBefore >>
    // rawCh '`' >> ident — see `Prim::RawChar`'s doc comment for why
    // the second backtick can't go through the ordinary lexer.
    b.leading2(
        "term",
        "Lean.Parser.Term.doubleQuotedName",
        MAX_PREC,
        seq([sym("`"), Prim::CheckNoWsBefore, raw_char('`'), Prim::Ident]),
    );
}

fn register_holes_and_sorts(b: &mut SnapshotBuilder) {
    // hole := leading_parser "_".
    b.leading2("term", "Lean.Parser.Term.hole", MAX_PREC, sym("_"));
    // syntheticHole := leading_parser "?" >> (ident <|> "_").
    b.leading2(
        "term",
        "Lean.Parser.Term.syntheticHole",
        MAX_PREC,
        seq([sym("?"), or_else([Prim::Ident, sym("_")])]),
    );
    // `Sort`/`Type`/`Prop` share the same optional-level-argument shape:
    // "Kw" >> optional (checkWsBefore "" >> checkPrec leadPrec >>
    // checkColGt >> levelParser maxPrec). `checkWsBefore`/`checkPrec`/
    // `checkColGt` are all zero-width guards (no tree contribution);
    // only the `optional(..)`'s presence/absence of a level shows up.
    let level_arg = || {
        opt(seq([
            Prim::CheckWsBefore,
            Prim::CheckPrec(LEAD_PREC),
            Prim::CheckColGt,
            cat("level", MAX_PREC),
        ]))
    };
    b.leading2(
        "term",
        "Lean.Parser.Term.sort",
        MAX_PREC,
        seq([sym("Sort"), level_arg()]),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.type",
        MAX_PREC,
        seq([sym("Type"), level_arg()]),
    );
    b.leading2("term", "Lean.Parser.Term.prop", MAX_PREC, sym("Prop"));
}

/// `cdot := leading_parser unicodeSymbol "·" "." >> hygieneInfo` (bare,
/// MAX_PREC; Task 8 wave 1 deferred this — "zero fixture value" — but it
/// costs nothing now that `hygiene_info` exists). ORACLE-PORT confirmed
/// against a fresh dump of `(· )`/`(. )`: `Term.paren`'s inner term is a
/// bare `Lean.Parser.Term.cdot{ "·"|".", hygieneInfo{} }`, two children,
/// no further wrap. Shares its leading `Sym(".")` slot with `dotIdent`
/// (`term_pragma`... no — `term_app`'s `dotIdent`, `Term.lean:924`) —
/// resolved by ordinary longest-match, same mechanism as `level`'s
/// `max`/`imax` vs plain `ident`: `.foo` (no ws, ident follows) wins for
/// `dotIdent` (longer match), bare `.` (nothing ident-shaped follows
/// with no ws) wins for `cdot`.
fn register_cdot(b: &mut SnapshotBuilder) {
    let hi = hygiene_info(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.cdot",
        MAX_PREC,
        seq([or_else([sym("·"), sym(".")]), hi]),
    );
}

fn register_paren_family(b: &mut SnapshotBuilder) {
    // paren := hygienicLParen >> withoutPosition (withoutForbidden
    // (ppDedentIfGrouped termParser)) >> ")" — the pp/position/
    // forbidden combinators are all parsing no-ops.
    let lp = hygienic_lparen(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.paren",
        MAX_PREC,
        seq([lp, cat("term", 0), sym(")")]),
    );
    // tuple := hygienicLParen >> optional (termParser >> ", " >>
    // sepBy1 termParser ", " (allowTrailingSep := true)) >> ")".
    let lp = hygienic_lparen(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.tuple",
        MAX_PREC,
        seq([
            lp,
            opt(seq([
                cat("term", 0),
                sym(","),
                sep_by1_trailing(cat("term", 0), ","),
            ])),
            sym(")"),
        ]),
    );
    // typeAscription := hygienicLParen >> (termParser >> " :" >>
    // optional (ppSpace >> termParser)) >> ")".
    let lp = hygienic_lparen(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.typeAscription",
        MAX_PREC,
        seq([lp, cat("term", 0), sym(":"), opt(cat("term", 0)), sym(")")]),
    );
    // anonymousCtor := "⟨" >> sepBy termParser ", " (allowTrailingSep :=
    // true) >> "⟩".
    b.leading2(
        "term",
        "Lean.Parser.Term.anonymousCtor",
        MAX_PREC,
        seq([sym("⟨"), sep_by_trailing(cat("term", 0), ","), sym("⟩")]),
    );
    // inaccessible := ".(" >> termParser >> ")".
    b.leading2(
        "term",
        "Lean.Parser.Term.inaccessible",
        MAX_PREC,
        seq([sym(".("), cat("term", 0), sym(")")]),
    );
    // explicit := "@" >> termParser maxPrec.
    b.leading2(
        "term",
        "Lean.Parser.Term.explicit",
        MAX_PREC,
        seq([sym("@"), cat("term", MAX_PREC)]),
    );
    // «unsafe» := leading_parser:leadPrec "unsafe " >> termParser.
    b.leading2(
        "term",
        "Lean.Parser.Term.unsafe",
        LEAD_PREC,
        seq([sym("unsafe"), cat("term", 0)]),
    );
}

// ================================================================
// Binders/forall/fun/match/structInst.
// ================================================================

fn register_forall(b: &mut SnapshotBuilder) {
    // «forall» := leading_parser:leadPrec unicodeSymbol "∀" "forall" >>
    // many1 (binderIdent <|> bracketedBinder) >> optType >> ", " >>
    // termParser.
    let bi = binder_ident(b);
    let bb = bracketed_binder(b, false);
    let ot = opt_type(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.forall",
        LEAD_PREC,
        seq([
            or_else([sym("∀"), sym("forall")]),
            many1(or_else([bi, bb])),
            ot,
            sym(","),
            cat("term", 0),
        ]),
    );
}

fn fun_binder(b: &mut SnapshotBuilder) -> Prim {
    // funStrictImplicitBinder/funImplicitBinder gate their own binder
    // alt behind a `lookahead` (disambiguating a `{`-led struct-instance
    // TERM from a `{`-led implicit BINDER — both are legal in argument
    // position); `instBinder` and the `termParser maxPrec` fallback need
    // no lookahead (each has its own leading bracket / is the catch-all).
    let strict_lookahead = seq([
        sym("⦃"),
        many1(binder_ident(b)),
        or_else([sym(":"), sym("⦄")]),
    ]);
    let strict = strict_implicit_binder(b, false);
    let implicit_lookahead = seq([
        sym("{"),
        many1(binder_ident(b)),
        or_else([sym(":"), sym("}")]),
    ]);
    let implicit = implicit_binder(b, false);
    let inst = inst_binder(b);
    or_else([
        atomic(seq([Prim::Lookahead(Arc::new(strict_lookahead)), strict])),
        atomic(seq([
            Prim::Lookahead(Arc::new(implicit_lookahead)),
            implicit,
        ])),
        inst,
        cat("term", MAX_PREC),
    ])
}

fn basic_fun(b: &mut SnapshotBuilder) -> Prim {
    // basicFun := leading_parser (many1 (funBinder) >> optType >>
    // unicodeSymbol " ↦" " =>") >> termParser.
    let fb = fun_binder(b);
    let ot = opt_type(b);
    let k = b.kind("Lean.Parser.Term.basicFun");
    nd(
        k,
        seq([
            many1(fb),
            ot,
            or_else([sym("↦"), sym("=>")]),
            cat("term", 0),
        ]),
    )
}

/// `matchDiscr := leading_parser optional (atomic (binderIdent >> " :
/// ")) >> termParser` — not attributed, but IS `leading_parser` (own
/// node, confirmed by dump).
fn match_discr(b: &mut SnapshotBuilder) -> Prim {
    let bi = binder_ident(b);
    let k = b.kind("Lean.Parser.Term.matchDiscr");
    nd(k, seq([opt(atomic(seq([bi, sym(":")]))), cat("term", 0)]))
}
/// `matchAlt (rhsParser) := leading_parser "| " >> sepBy1 (sepBy1
/// termParser ", ") " | " >> darrow >> checkColGe(..) >> rhsParser`
/// (Term.lean:265-269). The INNER `sepBy1 termParser ", "` has NO
/// `allowTrailingSep` — plain `sep_by1`, not `sep_by1_trailing` (a prior
/// version of this port wrongly used the trailing variant here).
/// `rhs` lets `structInstFieldEqns` reuse this for its own rhs shape
/// (still `termParser` in every call site this task ports).
fn match_alt(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.matchAlt");
    nd(
        k,
        seq([
            sym("|"),
            sep_by1(sep_by1(cat("term", 0), ","), "|"),
            sym("=>"),
            Prim::CheckColGe,
            cat("term", 0),
        ]),
    )
}
/// `matchAlts (rhsParser) := leading_parser withPosition $ many1Indent
/// (ppLine >> matchAlt rhsParser)` — the outer `withPosition` is
/// redundant with `Many1Indent`'s own internal one (same position, no
/// input consumed between them); skipped, see task-8 report.
fn match_alts(b: &mut SnapshotBuilder) -> Prim {
    let alt = match_alt(b);
    let k = b.kind("Lean.Parser.Term.matchAlts");
    nd(k, Prim::Many1Indent(Arc::new(alt)))
}

fn register_fun(b: &mut SnapshotBuilder) {
    // «fun» := leading_parser:maxPrec unicodeSymbol "λ" "fun" >>
    // (basicFun <|> matchAlts).
    let bf = basic_fun(b);
    let ma = match_alts(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.fun",
        MAX_PREC,
        seq([or_else([sym("λ"), sym("fun")]), or_else([bf, ma])]),
    );
}

fn register_match(b: &mut SnapshotBuilder) {
    // «match» := leading_parser:leadPrec "match " >> optional
    // generalizingParam >> optional motive >> sepBy1 matchDiscr ", " >>
    // " with" >> matchAlts. `generalizingParam`/`motive` aren't
    // transcribed (no fixture uses `match (generalizing := ..)`/`match
    // (motive := ..)`) — left as real, always-empty optional slots
    // (same idiom as `explicitBinder`'s `binderTactic`/`binderDefault`
    // slot above).
    let discr = match_discr(b);
    let alts = match_alts(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.match",
        LEAD_PREC,
        seq([
            sym("match"),
            opt(never()),
            opt(never()),
            sep_by1(discr, ","),
            sym("with"),
            alts,
        ]),
    );
    // «nomatch» := leading_parser:leadPrec "nomatch " >> sepBy1
    // termParser ", ".
    b.leading2(
        "term",
        "Lean.Parser.Term.nomatch",
        LEAD_PREC,
        seq([sym("nomatch"), sep_by1(cat("term", 0), ",")]),
    );
    // «nofun» := leading_parser "nofun" (bare, MAX_PREC).
    b.leading2("term", "Lean.Parser.Term.nofun", MAX_PREC, sym("nofun"));
}

/// `structInstLVal := leading_parser (ident <|> fieldIdx <|>
/// structInstArrayRef) >> many (group ("." >> (ident <|> fieldIdx)) <|>
/// structInstArrayRef)`. `structInstArrayRef` (`"[" >> termParser >>
/// "]"`) isn't ported (no fixture uses `{ arr[i] := .. }`) — the `many`
/// loop only tries the `group(".">>..)` alt here.
fn struct_inst_lval(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.structInstLVal");
    nd(
        k,
        seq([
            or_else([Prim::Ident, Prim::FieldIdx]),
            many(Prim::Group(Arc::new(seq([
                sym("."),
                or_else([Prim::Ident, Prim::FieldIdx]),
            ])))),
        ]),
    )
}
/// `structInstFieldDef := leading_parser " := " >> optional "private"
/// >> termParser` — registered into the `structInstFieldDecl` category
/// (surface table's own 2-row category, not `term`).
fn struct_inst_field_def(b: &mut SnapshotBuilder) {
    b.leading2(
        "structInstFieldDecl",
        "Lean.Parser.Term.structInstFieldDef",
        MAX_PREC,
        seq([sym(":="), opt(sym("private")), cat("term", 0)]),
    );
}
/// `structInstFieldEqns := leading_parser optional "private" >>
/// matchAlts`.
fn struct_inst_field_eqns(b: &mut SnapshotBuilder) {
    let alts = match_alts(b);
    b.leading2(
        "structInstFieldDecl",
        "Lean.Parser.Term.structInstFieldEqns",
        MAX_PREC,
        seq([opt(sym("private")), alts]),
    );
}
/// `structInstField := ppGroup <| leading_parser structInstLVal >>
/// optional (many (checkColGt >> structInstFieldBinder) >>
/// optTypeForStructInst >> structInstFieldDeclParser)`.
/// `structInstFieldBinder`/`optTypeForStructInst` (`{ f (x) := e }`
/// abbreviation-with-binders / `{ f := e : T }` inline type override)
/// aren't transcribed — no fixture uses either; left as real, always-
/// empty slots inside the SAME optional as the (fixture-exercised)
/// field-decl parse, matching how the oracle's own `optional(a >> b >>
/// c)` fails/succeeds as ONE unit (if `structInstFieldDeclParser`
/// itself succeeds — the part we DO port — the whole `optional` must
/// succeed too, so those slots can't be dropped from the `Seq`).
fn struct_inst_field(b: &mut SnapshotBuilder) -> Prim {
    let lval = struct_inst_lval(b);
    let k = b.kind("Lean.Parser.Term.structInstField");
    nd(
        k,
        seq([
            lval,
            opt(seq([
                many(never()),
                opt(never()),
                cat("structInstFieldDecl", 0),
            ])),
        ]),
    )
}
fn struct_inst_fields(b: &mut SnapshotBuilder) -> Prim {
    let field = struct_inst_field(b);
    let k = b.kind("Lean.Parser.Term.structInstFields");
    // KNOWN DIVERGENCE (M3a): oracle is `sepByIndent structInstField ", "
    // (allowTrailingSep := true)` — column/newline-sensitive (a same-
    // column-newline is an implicit separator alternative to a literal
    // `,`, per `checkColGe` gating each item). Approximated here as a
    // plain, non-indentation-aware `SepBy`. This is a REAL divergence on
    // MULTI-LINE struct instance literals (a newline-separated, no-comma
    // field list will not parse the way the oracle does); every
    // committed fixture's struct instance is single-line, where the two
    // are unobservable from each other, so the gap doesn't show up in
    // the golden gate. Needs the `sepByIndent` machinery (see
    // `SepByIndentSemicolon` in `grammar.rs`, generalized to a comma
    // separator) to close for real — tracked, not fixed, in this task.
    // Also recorded in the task-8 report's Fix wave 1 section.
    nd(k, sep_by_trailing(field, ","))
}
fn opt_ellipsis(b: &mut SnapshotBuilder) -> Prim {
    // optEllipsis := leading_parser optional " ..".
    let k = b.kind("Lean.Parser.Term.optEllipsis");
    nd(k, opt(sym("..")))
}

fn register_struct_inst(b: &mut SnapshotBuilder) {
    struct_inst_field_def(b);
    struct_inst_field_eqns(b);
    // structInst := leading_parser "{ " >> optional (atomic (sepBy1
    // termParser ", " >> " with ")) >> structInstFields (..) >>
    // optEllipsis >> optional (" : " >> termParser) >> " }".
    let with_terms = opt(atomic(seq([sep_by1(cat("term", 0), ","), sym("with")])));
    let fields = struct_inst_fields(b);
    let ellipsis = opt_ellipsis(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.structInst",
        MAX_PREC,
        seq([
            sym("{"),
            with_terms,
            fields,
            ellipsis,
            opt(seq([sym(":"), cat("term", 0)])),
            sym("}"),
        ]),
    );
    // structInstDefault := leading_parser "struct_inst_default%" (bare,
    // MAX_PREC).
    b.leading2(
        "term",
        "Lean.Parser.Term.structInstDefault",
        MAX_PREC,
        sym("struct_inst_default%"),
    );
}

// ================================================================
// let / have / show / suffices.
// ================================================================

/// `letConfig := leading_parser many letConfigItem` — `letConfigItem`
/// (`+nondep`/`-nondep`/`(eq := h)`/…) isn't transcribed (no fixture
/// uses any `let` option); always-empty `many(never())`.
fn let_config(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.letConfig");
    nd(k, many(never()))
}
/// `letId := leading_parser (ppSpace >> binderIdent >> notFollowedBy
/// (checkNoWsBefore >> "[") ..) <|> hygieneInfo`.
fn let_id(b: &mut SnapshotBuilder) -> Prim {
    let bi = binder_ident(b);
    let hi = hygiene_info(b);
    let k = b.kind("Lean.Parser.Term.letId");
    nd(
        k,
        or_else([
            seq([
                bi,
                Prim::NotFollowedBy(Arc::new(seq([Prim::CheckNoWsBefore, sym("[")]))),
            ]),
            hi,
        ]),
    )
}
/// `letIdBinder := binderIdent <|> bracketedBinder`.
fn let_id_binder(b: &mut SnapshotBuilder) -> Prim {
    let bi = binder_ident(b);
    let bb = bracketed_binder(b, false);
    or_else([bi, bb])
}
/// `letIdLhs := letId >> many (letIdBinder) >> optType`.
fn let_id_lhs(b: &mut SnapshotBuilder) -> Prim {
    let id = let_id(b);
    let binder = let_id_binder(b);
    let ot = opt_type(b);
    seq([id, many(binder), ot])
}
/// `letIdDecl := leading_parser atomic (letIdLhs >> " := ") >>
/// termParser`.
fn let_id_decl(b: &mut SnapshotBuilder) -> Prim {
    let lhs = let_id_lhs(b);
    let k = b.kind("Lean.Parser.Term.letIdDecl");
    nd(k, seq([atomic(lhs), sym(":="), cat("term", 0)]))
    // NOTE: `atomic` here only needs to cover `letIdLhs >> " := "` per
    // source; wrapping the trailing `":="` inside it too is harmless
    // (still atomic, no observable difference) and keeps this a single
    // `atomic(..)` call instead of two `Seq` fragments.
}
/// `letDecl := leading_parser notFollowedBy (nonReservedSymbol "rec")
/// >> (letPatDecl true <|> letIdDecl <|> letPatDecl <|> letEqnsDecl)` —
/// only the `letIdDecl` alternative is ported (no fixture uses
/// pattern-`let`/`let f | pat => ..` equational form).
fn let_decl(b: &mut SnapshotBuilder) -> Prim {
    let id_decl = let_id_decl(b);
    let k = b.kind("Lean.Parser.Term.letDecl");
    nd(
        k,
        seq([
            Prim::NotFollowedBy(Arc::new(Prim::NonReservedSymbol("rec".into()))),
            id_decl,
        ]),
    )
}
/// Shared shape of `let`/`have` (and, structurally, `haveI`/`letI`/
/// `let_fun`/`let_delayed`/`let_tmp`/`letrec` — NOT ported here, see
/// task-8 report): `withPosition (kw >> letConfig >> letDecl) >>
/// optSemicolon termParser`. `optSemicolon`'s `checkLinebreakBefore`
/// alternative (a `;`-free, newline-separated body) isn't ported — only
/// the explicit `";"` form is (every fixture uses it).
fn let_like(b: &mut SnapshotBuilder, kind_name: &str, keyword: &str, prec: u32) {
    let cfg = let_config(b);
    let decl = let_decl(b);
    b.leading2(
        "term",
        kind_name,
        prec,
        seq([
            Prim::WithPosition(Arc::new(seq([sym(keyword), cfg, decl]))),
            sym(";"),
            cat("term", 0),
        ]),
    );
}

/// `fromTerm := leading_parser "from " >> termParser` (bare, MAX_PREC).
fn from_term(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.fromTerm");
    nd(k, seq([sym("from"), cat("term", 0)]))
}

fn register_let_have_show_suffices(b: &mut SnapshotBuilder) {
    let_like(b, "Lean.Parser.Term.let", "let", LEAD_PREC);
    let_like(b, "Lean.Parser.Term.have", "have", LEAD_PREC);

    // «show» := leading_parser:leadPrec "show " >> termParser >>
    // showRhs. `showRhs := fromTerm <|> byTactic'` — only `fromTerm` is
    // ported (byTactic' needs Task 9's `tacticSeq`; deferred with it).
    let rhs = from_term(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.show",
        LEAD_PREC,
        seq([sym("show"), cat("term", 0), rhs]),
    );

    // «suffices» := leading_parser:leadPrec withPosition ("suffices " >>
    // sufficesDecl) >> optSemicolon termParser. `sufficesDecl :=
    // leading_parser (atomic (group (binderIdent >> " : ")) <|>
    // hygieneInfo) >> termParser >> showRhs`.
    let bi = binder_ident(b);
    let hi = hygiene_info(b);
    let rhs = from_term(b);
    let decl_k = b.kind("Lean.Parser.Term.sufficesDecl");
    let decl = nd(
        decl_k,
        seq([
            or_else([atomic(Prim::Group(Arc::new(seq([bi, sym(":")])))), hi]),
            cat("term", 0),
            rhs,
        ]),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.suffices",
        LEAD_PREC,
        seq([
            Prim::WithPosition(Arc::new(seq([sym("suffices"), decl]))),
            sym(";"),
            cat("term", 0),
        ]),
    );
}

/// `let`'s siblings (Task 8 wave 2 — deferred by wave 1 as "cheap to
/// add later" once `let_like`/`let_decl`/`let_config` existed): oracle
/// shapes cross-checked against a fresh dump of `let_fun x := 1; x` /
/// `let_delayed x := 1; x` / `let_tmp x := 1; x` / `haveI x := 1; x` /
/// `letI x := 1; x` (each shows the expected `letDecl{letIdDecl{letId,
/// null, null, ":=", num}}` body, `haveI`/`letI` additionally showing a
/// `letConfig{null}` sibling — see task-8-wave2 report for the probe
/// transcript).
fn register_let_family_siblings(b: &mut SnapshotBuilder) {
    // «let_fun» := leading_parser:leadPrec withPosition ((symbol
    // "let_fun " <|> "let_λ ") >> letDecl) >> optSemicolon termParser —
    // NO `letConfig` (unlike `let`/`have`/`haveI`/`letI`).
    let decl = let_decl(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.let_fun",
        LEAD_PREC,
        seq([
            Prim::WithPosition(Arc::new(seq([
                or_else([sym("let_fun"), sym("let_λ")]),
                decl,
            ]))),
            sym(";"),
            cat("term", 0),
        ]),
    );
    // «let_delayed» := leading_parser:leadPrec withPosition
    // ("let_delayed " >> letDecl) >> optSemicolon termParser.
    let decl = let_decl(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.let_delayed",
        LEAD_PREC,
        seq([
            Prim::WithPosition(Arc::new(seq([sym("let_delayed"), decl]))),
            sym(";"),
            cat("term", 0),
        ]),
    );
    // «let_tmp» := leading_parser:leadPrec withPosition ("let_tmp " >>
    // letDecl) >> optSemicolon termParser.
    let decl = let_decl(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.let_tmp",
        LEAD_PREC,
        seq([
            Prim::WithPosition(Arc::new(seq([sym("let_tmp"), decl]))),
            sym(";"),
            cat("term", 0),
        ]),
    );
    // «haveI» := leading_parser (BARE — no `:leadPrec` annotation, so
    // MAX_PREC per this file's established bare-`leading_parser`
    // convention) withPosition ("haveI " >> letConfig >> letDecl) >>
    // optSemicolon termParser.
    let cfg = let_config(b);
    let decl = let_decl(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.haveI",
        MAX_PREC,
        seq([
            Prim::WithPosition(Arc::new(seq([sym("haveI"), cfg, decl]))),
            sym(";"),
            cat("term", 0),
        ]),
    );
    // «letI» := leading_parser (bare, MAX_PREC) withPosition ("letI " >>
    // letConfig >> letDecl) >> optSemicolon termParser.
    let cfg = let_config(b);
    let decl = let_decl(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.letI",
        MAX_PREC,
        seq([
            Prim::WithPosition(Arc::new(seq([sym("letI"), cfg, decl]))),
            sym(";"),
            cat("term", 0),
        ]),
    );
    register_letrec(b);
}

/// `letRecDecl := leading_parser optional Command.docComment >>
/// optional «attributes» >> letDecl >> Termination.suffix` —
/// `docComment`/`attributes` aren't transcribed (no fixture uses either
/// on a `let rec`); real, always-empty optional slots (same idiom as
/// `explicitBinder`'s `binderTactic`/`binderDefault`). `Termination.
/// suffix` reuses the SAME kind name `command.rs`'s micro
/// `optDeclSig`/`declValSimple` placeholder already interns (harmless —
/// `KindInterner::intern` is idempotent) with the identical two-empty-
/// optional shape (`terminationBy?`/`decreasingBy` aren't transcribed
/// either — no fixture uses `let rec ... termination_by ...`).
fn let_rec_decl(b: &mut SnapshotBuilder) -> Prim {
    let decl = let_decl(b);
    let suffix_k = b.kind("Lean.Parser.Termination.suffix");
    let suffix = nd(suffix_k, seq([opt(never()), opt(never())]));
    let k = b.kind("Lean.Parser.Term.letRecDecl");
    nd(k, seq([opt(never()), opt(never()), decl, suffix]))
}
/// `letRecDecls := leading_parser sepBy1 letRecDecl ", "`.
fn let_rec_decls(b: &mut SnapshotBuilder) -> Prim {
    let decl = let_rec_decl(b);
    let k = b.kind("Lean.Parser.Term.letRecDecls");
    nd(k, sep_by1(decl, ","))
}
/// `«letrec» := leading_parser:leadPrec withPosition (group ("let " >>
/// nonReservedSymbol "rec ") >> letRecDecls) >> optSemicolon termParser`
/// — `nonReservedSymbol "rec"` reuses the SAME dispatch fix `level`'s
/// `max`/`imax` needed (Task 8 wave 1, `parse.rs::dispatch`'s
/// `FirstTok::Sym` arm matching an `Ident`-kind token too); no further
/// interpreter change needed here, confirmed by a fresh dump of `let rec
/// x := 1; x` parsing as `Lean.Parser.Term.letrec` (not falling back to
/// plain `Term.let` — the oracle's own longest-match: `let` alone
/// matches `Term.let`, `let` immediately followed by `rec` matches the
/// longer `letrec`, exactly like `Sort max` vs `Sort (max u v)`).
fn register_letrec(b: &mut SnapshotBuilder) {
    let decls = let_rec_decls(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.letrec",
        LEAD_PREC,
        seq([
            Prim::WithPosition(Arc::new(seq([
                Prim::Group(Arc::new(seq([
                    sym("let"),
                    Prim::NonReservedSymbol("rec".into()),
                ]))),
                decls,
            ]))),
            sym(";"),
            cat("term", 0),
        ]),
    );
}

// ================================================================
// depArrow / forall's sibling, arrow, app/proj/completion/explicitUniv.
// ================================================================

fn register_dep_arrow(b: &mut SnapshotBuilder) {
    // depArrow := leading_parser:25 depArrowPrefix >> termParser.
    // `depArrowPrefix := depArrowShortPrefix <|> depArrowLongPrefix`;
    // `depArrowShortPrefix` (`{α} → ..` shorthand) isn't ported (no
    // fixture uses it — the source itself calls it "cryptic" and the
    // real toolchain nearly never uses it either); only
    // `depArrowLongPrefix := bracketedBinder true >> unicodeSymbol " →
    // " " -> "` is.
    let bb = bracketed_binder(b, true);
    b.leading2(
        "term",
        "Lean.Parser.Term.depArrow",
        25,
        seq([bb, or_else([sym("→"), sym("->")]), cat("term", 0)]),
    );
}

fn register_arrow_app_proj(b: &mut SnapshotBuilder) {
    // arrow := trailing_parser checkPrec 25 >> unicodeSymbol " → " " ->
    // " >> termParser 25. The manual inline `checkPrec 25` (rather than
    // the `trailing_parser:P:L` sugar) means this does NOT also gate on
    // `lhsPrec` — real usage (`f x → g y`) needs an unrestricted lhs,
    // confirmed by the existing `pow` test precedent (`trailing2(...,
    // 75, 76, ..)` — SAME prec on both sides recurses right-assoc); rhs
    // recurses at the operator's OWN prec (25, not 24 — ORACLE-PORT:
    // the pinned source says `termParser 25`, not `24` as the task
    // brief's inline sketch states; the source wins, see task-8
    // report's divergence list).
    b.trailing2(
        "term",
        "Lean.Parser.Term.arrow",
        25,
        0,
        seq([or_else([sym("→"), sym("->")]), cat("term", 25)]),
    );
    // completion := trailing_parser checkNoWsBefore >> "." (editor-
    // completion marker; bare `trailing_parser` with BOTH annotations
    // omitted — ORACLE-PORT `BuiltinNotation.lean:194-197`
    // (`elabTParserMacroAux`): an omitted `prec` defaults to
    // `Parser.maxPrec`, but an omitted `lhsPrec` defaults to `0`, NOT to
    // `prec` — so this is MAX_PREC/0, not MAX_PREC/MAX_PREC. Same for
    // `proj`/`explicitUniv` immediately below.
    b.trailing2(
        "term",
        "Lean.Parser.Term.completion",
        MAX_PREC,
        0,
        seq([Prim::CheckNoWsBefore, sym(".")]),
    );
    // proj := trailing_parser checkNoWsBefore >> "." >> checkNoWsBefore
    // >> (fieldIdx <|> rawIdent). Bare `trailing_parser`: MAX_PREC/0 (see
    // `completion`'s comment above for the oracle citation).
    b.trailing2(
        "term",
        "Lean.Parser.Term.proj",
        MAX_PREC,
        0,
        seq([
            Prim::CheckNoWsBefore,
            sym("."),
            Prim::CheckNoWsBefore,
            or_else([Prim::FieldIdx, Prim::Ident]),
        ]),
    );
    // explicitUniv := trailing_parser checkStackTop .. >>
    // explicitUnivSuffix. Bare `trailing_parser`: MAX_PREC/0 (see
    // `completion`'s comment above for the oracle citation).
    // `checkStackTop` (verifying the already-parsed lhs LOOKS like an
    // identifier/dotIdent/proj) has no `Prim` counterpart and is a
    // semantic-only guard (never mis-shapes the tree either way — worst
    // case this fires where the oracle wouldn't, which no fixture
    // exercises) — skipped.
    b.trailing2(
        "term",
        "Lean.Parser.Term.explicitUniv",
        MAX_PREC,
        0,
        explicit_univ_suffix(),
    );
    // app := trailing_parser:leadPrec:maxPrec many1 argument. `argument
    // := checkWsBefore .. >> checkColGt .. >> (namedArgument <|>
    // ellipsis <|> termParser argPrec)`.
    b.trailing2(
        "term",
        "Lean.Parser.Term.app",
        LEAD_PREC,
        MAX_PREC,
        many1(argument()),
    );
}
/// `namedArgument := leading_parser atomic ("(" >> ident >> " := ") >>
/// termParser >> ")"`.
fn named_argument() -> Prim {
    seq([
        atomic(seq([sym("("), Prim::Ident, sym(":=")])),
        cat("term", 0),
        sym(")"),
    ])
}
/// `ellipsis := leading_parser ".." >> notFollowedBy (checkNoWsBefore
/// >> ".") ".`. immediately after `..`"`.
fn ellipsis_arg() -> Prim {
    seq([
        sym(".."),
        Prim::NotFollowedBy(Arc::new(seq([Prim::CheckNoWsBefore, sym(".")]))),
    ])
}
/// `argument := checkWsBefore .. >> checkColGt .. >> (namedArgument <|>
/// ellipsis <|> termParser argPrec)` (Term.lean:900-904) — hoisted from
/// a `register_arrow_app_proj`-local closure (Task 8 wave 1) to a
/// module fn so `term_app`'s `pipeProj` (`many argument`, Term.lean:958)
/// can share it verbatim instead of drifting a second copy.
pub(super) fn argument() -> Prim {
    seq([
        Prim::CheckWsBefore,
        Prim::CheckColGt,
        or_else([named_argument(), ellipsis_arg(), cat("term", ARG_PREC)]),
    ])
}
/// `explicitUnivSuffix := checkNoWsBefore >> ".{" >> sepBy1 levelParser
/// ", " >> "}"` (Term.lean:944-945) — hoisted to a module fn (Task 8
/// wave 2) so `term_app`'s `pipeProj` (`optional explicitUnivSuffix`,
/// Term.lean:958) can reuse the exact same shape `explicitUniv` already
/// uses, rather than a second hand-copied definition.
pub(super) fn explicit_univ_suffix() -> Prim {
    seq([
        Prim::CheckNoWsBefore,
        sym(".{"),
        sep_by1(cat("level", 0), ","),
        sym("}"),
    ])
}

pub fn register(b: &mut SnapshotBuilder) {
    register_literals(b);
    register_holes_and_sorts(b);
    register_cdot(b);
    register_paren_family(b);
    register_forall(b);
    register_fun(b);
    register_match(b);
    register_struct_inst(b);
    register_let_have_show_suffices(b);
    register_let_family_siblings(b);
    register_dep_arrow(b);
    register_arrow_app_proj(b);
    term_app::register(b);
    term_pragma::register(b);
}

#[cfg(test)]
mod tests {
    use crate::builtin;
    use crate::parse_module;

    /// Parse `prelude\n\n<src>`, asserting a CLEAN parse (matches the
    /// oracle-comparison gate's own requirement: only clean parses are
    /// oracle-compared), and return the canonical JSON dump for
    /// substring assertions.
    fn parse_ok(src: &str) -> String {
        let snap = builtin::snapshot();
        let full = format!("prelude\n\n{src}");
        let result = parse_module(&full, &snap);
        assert!(
            result.errors.is_empty(),
            "expected clean parse of {src:?}, got {:?}",
            result.errors
        );
        assert_eq!(result.tree.text(), full, "round-trip failed for {src:?}");
        crate::canon::canon_jsonl(&result.tree)
    }

    // ---- level's NonReservedSymbol dispatch fix (Task 8) --------------

    #[test]
    fn level_max_and_imax_with_args_parse_as_level_nodes() {
        let out = parse_ok("def a := fun (x : Sort (max u v)) => x");
        assert!(out.contains("Lean.Parser.Level.max"), "{out}");
        let out = parse_ok("def a := fun (x : Sort (imax u v)) => x");
        assert!(out.contains("Lean.Parser.Level.imax"), "{out}");
    }

    #[test]
    fn bare_max_with_no_following_level_falls_back_to_ident_in_level_position() {
        // `Sort max` (no args): `Level.max`'s `many1` has nothing to
        // consume, so it loses the longest-match to plain `Level.ident`
        // — the level slot is a bare ident, not a `Level.max` node.
        let out = parse_ok("def a := fun (x : Sort max) => x");
        assert!(!out.contains("Lean.Parser.Level.max"), "{out}");
        assert!(out.contains("\"i\":\"max\""), "{out}");
    }

    #[test]
    fn plain_ident_max_in_term_position_is_unaffected() {
        // A completely separate category/dispatch table — `level`'s
        // `NonReservedSymbol("max")` entry must not leak into `term`.
        let out = parse_ok("def a := max");
        assert!(!out.contains("Lean.Parser.Level."), "{out}");
        assert!(out.contains("\"i\":\"max\""), "{out}");
    }

    // ---- interpreter fixes this task needed (regression coverage) ----

    #[test]
    fn term_app_juxtaposition_applies_a_bare_ident_head() {
        // Regression for the `category()` leading-dispatch lhs_prec
        // pre-seed fix: without it, a bare `leading_raw` ident head
        // never counts as MAX_PREC-strength, and `app`'s `lhs_prec >=
        // MAX_PREC` trailing gate never qualifies.
        let out = parse_ok("def x := f a b c");
        assert!(out.contains("Lean.Parser.Term.app"), "{out}");
    }

    #[test]
    fn fun_multiple_binders_including_an_implicit_one() {
        // Regression for the `category()` total-leading-failure
        // phantom-consumption fix: `many1(funBinder)`'s fallback
        // `cat("term", maxPrec)` alternative used to leak a permanently-
        // consumed whitespace token on failure, making `many1` abort
        // with a hard error instead of cleanly stopping after the
        // binders it already had.
        let out = parse_ok("def x := fun (a : A) {b : B} => a");
        assert!(out.contains("Lean.Parser.Term.typeAscription"), "{out}");
        assert!(out.contains("Lean.Parser.Term.implicitBinder"), "{out}");
    }

    #[test]
    fn had_ws_before_current_sees_through_a_wrapping_node() {
        // Regression for `had_ws_before_current`'s Task 8 review fix:
        // `Term.app`'s `many1(checkWsBefore >> ..)` pushes `Start(null)`
        // (the `many1` node) BEFORE its body's first `CheckWsBefore`
        // runs — the old "check `events.last()`" heuristic always saw
        // that `Start`, never the whitespace token before it, so
        // `checkWsBefore` failed for EVERY argument.
        let out = parse_ok("def x := f a");
        assert!(out.contains("Lean.Parser.Term.app"), "{out}");
    }
}
