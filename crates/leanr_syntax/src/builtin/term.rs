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
mod term_quot;
// Re-exported (Task 9) so `do_notation.rs` (a SIBLING of `term`, not a
// descendant) can reuse `matchExprPat`/`matchExprAlt(s)` for
// `doLetExpr`/`doLetMetaExpr`/`doMatchExpr` without a second, drifting
// copy — `term_pragma` itself stays a private submodule (unchanged),
// only these three names are threaded through.
pub(super) use term_pragma::{match_expr_alts, match_expr_pat};

// ================================================================
// Shared helpers (not their own surface-table rows; oracle-named
// sub-parsers used by several of the productions below).
// ================================================================

pub(super) fn nd(kind: SyntaxKind, body: Prim) -> Prim {
    Prim::Node {
        kind,
        prec: None,
        body: Arc::new(body),
    }
}

/// `hygieneInfo` (Extra.lean): always succeeds, wraps a zero-width
/// empty `ident` in its own (unqualified — NOT `Lean.Parser.Term.*`;
/// confirmed against a fresh dump) `hygieneInfo` node.
pub(super) fn hygiene_info(b: &mut SnapshotBuilder) -> Prim {
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
pub(super) fn term_hole(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.hole");
    nd(k, sym("_"))
}
pub(super) fn binder_ident(b: &mut SnapshotBuilder) -> Prim {
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
/// `typeSpec` itself, unwrapped in `optional` — hoisted (Task 10) so
/// `Term/Basic.lean`'s `optTypeForStructInst := optional (atomic
/// (typeSpec >> notFollowedBy "}" "}"))` (`struct_inst_field`, below) can
/// reuse the exact same node shape `opt_type` wraps, rather than a
/// second hand-copied `":" >> term` definition.
pub(super) fn type_spec(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.typeSpec");
    nd(k, seq([sym(":"), cat("term", 0)]))
}
pub(super) fn opt_type(b: &mut SnapshotBuilder) -> Prim {
    opt(type_spec(b))
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
            // optional slot (`never()`'s own doc comment, grammar.rs).
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
pub(super) fn inst_binder(b: &mut SnapshotBuilder) -> Prim {
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
pub(super) fn bracketed_binder(b: &mut SnapshotBuilder, require_type: bool) -> Prim {
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

/// `syntheticHole := leading_parser "?" >> (ident <|> "_")` — the SAME
/// body `syntheticHole`'s own `leading2` registration below uses,
/// FULLY NODE-WRAPPED (like `term_hole`'s own doc comment: "kept as one
/// fn so both call sites can't drift") — hoisted (Task 9) so
/// `tactic.rs`'s `matchRhs` (`Term.hole <|> Term.syntheticHole <|>
/// tacticSeq`) can embed the already-wrapped node directly, the same
/// way `binder_ident` embeds `term_hole(b)`.
pub(super) fn synthetic_hole(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.syntheticHole");
    nd(k, seq([sym("?"), or_else([Prim::Ident, sym("_")])]))
}

fn register_holes_and_sorts(b: &mut SnapshotBuilder) {
    // hole := leading_parser "_".
    b.leading2("term", "Lean.Parser.Term.hole", MAX_PREC, sym("_"));
    // syntheticHole := leading_parser "?" >> (ident <|> "_") — BARE body
    // here (not `synthetic_hole(b)`, which is already node-wrapped —
    // `leading2` would double-wrap it, same reasoning as `term_hole`
    // vs. this file's plain `hole` registration just above).
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
    // (ppDedentIfGrouped termParser)) >> ")" — `withoutPosition`/
    // `ppDedentIfGrouped` are parsing no-ops (position-marker/pretty-
    // print only), but `withoutForbidden` is REAL as of Task 9 (see
    // `Prim::WithForbidden`'s doc comment): once `do_notation.rs`
    // registers `withForbidden "do" ..` scopes (`doFor`'s iterable,
    // `doUnless`'s condition, …), a parenthesized sub-term must clear
    // that scope — "there is no parsing ambiguity inside these nested
    // constructs" (Basic.lean's own doc comment) — so `(foo do bar)`
    // used AS a `for`-loop iterable, e.g., can still contain its own
    // nested `do`.
    let lp = hygienic_lparen(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.paren",
        MAX_PREC,
        seq([lp, without_forbidden(cat("term", 0)), sym(")")]),
    );
    // tuple := hygienicLParen >> optional (withoutPosition
    // (withoutForbidden (termParser >> ", " >> sepBy1 termParser ", "
    // (allowTrailingSep := true)))) >> ")" — `withoutForbidden` scopes
    // the WHOLE inner sequence (both the first term and the trailing
    // list), same reasoning as `paren` above.
    let lp = hygienic_lparen(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.tuple",
        MAX_PREC,
        seq([
            lp,
            opt(without_forbidden(seq([
                cat("term", 0),
                sym(","),
                sep_by1_trailing(cat("term", 0), ","),
            ]))),
            sym(")"),
        ]),
    );
    // typeAscription := hygienicLParen >> (withoutPosition
    // (withoutForbidden (termParser >> " :" >> optional (ppSpace >>
    // termParser)))) >> ")".
    let lp = hygienic_lparen(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.typeAscription",
        MAX_PREC,
        seq([
            lp,
            without_forbidden(seq([cat("term", 0), sym(":"), opt(cat("term", 0))])),
            sym(")"),
        ]),
    );
    // anonymousCtor := "⟨" >> withoutPosition (withoutForbidden (sepBy
    // termParser ", " (allowTrailingSep := true))) >> "⟩".
    b.leading2(
        "term",
        "Lean.Parser.Term.anonymousCtor",
        MAX_PREC,
        seq([
            sym("⟨"),
            without_forbidden(sep_by_trailing(cat("term", 0), ",")),
            sym("⟩"),
        ]),
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
pub(super) fn match_discr(b: &mut SnapshotBuilder) -> Prim {
    let bi = binder_ident(b);
    let k = b.kind("Lean.Parser.Term.matchDiscr");
    nd(k, seq([opt(atomic(seq([bi, sym(":")]))), cat("term", 0)]))
}
/// `matchAlt (rhsParser) := leading_parser "| " >> sepBy1 (sepBy1
/// termParser ", ") " | " >> darrow >> checkColGe(..) >> rhsParser`
/// (Term.lean:265-269). The INNER `sepBy1 termParser ", "` has NO
/// `allowTrailingSep` — plain `sep_by1`, not `sep_by1_trailing` (a prior
/// version of this port wrongly used the trailing variant here).
/// `rhs` is a REAL parameter (Task 9 — was hardcoded to `termParser`
/// until `do_notation.rs`/`tactic.rs` needed their own `rhsParser`s:
/// `doMatch`'s `doSeq`, `Tactic.«match»`'s `matchRhs` = `hole <|>
/// syntheticHole <|> tacticSeq`); `structInstFieldEqns`'s own call
/// passes `cat("term", 0)`, same as `register_fun`/`register_match`.
pub(super) fn match_alt(b: &mut SnapshotBuilder, rhs: Prim) -> Prim {
    let k = b.kind("Lean.Parser.Term.matchAlt");
    nd(
        k,
        seq([
            sym("|"),
            sep_by1(sep_by1(cat("term", 0), ","), "|"),
            sym("=>"),
            Prim::CheckColGe,
            rhs,
        ]),
    )
}
/// `matchAlts (rhsParser) := leading_parser withPosition $ many1Indent
/// (ppLine >> matchAlt rhsParser)` — the outer `withPosition` is
/// redundant with `Many1Indent`'s own internal one (same position, no
/// input consumed between them); skipped, see task-8 report.
pub(super) fn match_alts(b: &mut SnapshotBuilder, rhs: Prim) -> Prim {
    let alt = match_alt(b, rhs);
    let k = b.kind("Lean.Parser.Term.matchAlts");
    nd(k, Prim::Many1Indent(Arc::new(alt)))
}

fn register_fun(b: &mut SnapshotBuilder) {
    // «fun» := leading_parser:maxPrec unicodeSymbol "λ" "fun" >>
    // (basicFun <|> matchAlts).
    let bf = basic_fun(b);
    let ma = match_alts(b, cat("term", 0));
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
    let alts = match_alts(b, cat("term", 0));
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
    let alts = match_alts(b, cat("term", 0));
    b.leading2(
        "structInstFieldDecl",
        "Lean.Parser.Term.structInstFieldEqns",
        MAX_PREC,
        seq([opt(sym("private")), alts]),
    );
}
/// `structInstFieldBinder := binderIdent <|> bracketedBinder`
/// (`Term/Basic.lean:286-288`; `withAntiquot` wraps ONLY the
/// antiquotation alternative, so the real path is a bare `or_else`, no
/// extra node — same shape as `openDecl`/`funBinder`'s own antiquot
/// wrapper).
fn struct_inst_field_binder(b: &mut SnapshotBuilder) -> Prim {
    let bi = binder_ident(b);
    let bb = bracketed_binder(b, false);
    or_else([bi, bb])
}
/// `optTypeForStructInst := optional (atomic (typeSpec >> notFollowedBy
/// "}" "}"))` (`Term/Basic.lean:290`) — the `notFollowedBy` guard stops
/// a trailing `: T` from being swallowed here when it's actually the
/// STRUCT INSTANCE's own closing `: T }` (`Term.structInst`'s last
/// optional slot), not a per-field type override.
fn opt_type_for_struct_inst(b: &mut SnapshotBuilder) -> Prim {
    let ts = type_spec(b);
    opt(atomic(seq([ts, Prim::NotFollowedBy(Arc::new(sym("}")))])))
}
/// `structInstField := ppGroup <| leading_parser structInstLVal >>
/// optional (many (checkColGt >> ppSpace >> structInstFieldBinder) >>
/// optTypeForStructInst >> ppDedent structInstFieldDeclParser)`
/// (`Term/Basic.lean:293-294`) — Task 10: `structInstFieldBinder`/
/// `optTypeForStructInst` are now real (a prior version left both
/// always-empty, "no fixture uses either"; `Types.lean`'s `instance ...
/// where mark u := u` now does — the field-decl-with-binder
/// abbreviation form). Confirmed against a fresh oracle dump (task-10
/// report): `mark u := u`'s field is `structInstField{structInstLVal{
/// mark} null{ null{u} null{} structInstFieldDef{":=", null{}, u} }}` —
/// exactly `many(binder)`'s null wrapping ONE bare-ident binder, then
/// `optTypeForStructInst`'s empty null, then the field-decl recursion.
fn struct_inst_field(b: &mut SnapshotBuilder) -> Prim {
    let lval = struct_inst_lval(b);
    let binder = struct_inst_field_binder(b);
    let opt_ty = opt_type_for_struct_inst(b);
    let k = b.kind("Lean.Parser.Term.structInstField");
    nd(
        k,
        seq([
            lval,
            opt(seq([many(binder), opt_ty, cat("structInstFieldDecl", 0)])),
        ]),
    )
}
/// `Term.structInstFields (p : Parser) := node structInstFields p` —
/// parameterized by BOTH the item's own separator (Task 9: `Term.
/// structInst`'s literal `{ a := x, b := y }` uses `sepByIndent
/// structInstField ", " ..`) AND, since Task 10, the CALLER's separator
/// (`Command.whereStructInst`'s `where a := x; b := y` uses `sepByIndent
/// structInstField "; " ..` instead) — the same underlying `node`
/// wrapper, only the separator differs per call site.
pub(super) fn struct_inst_fields(b: &mut SnapshotBuilder, sep: &str) -> Prim {
    let field = struct_inst_field(b);
    let k = b.kind("Lean.Parser.Term.structInstFields");
    // FIXED (M3a Task 9, was a KNOWN DIVERGENCE per the task-8 report's
    // Fix wave 1 section): oracle is `sepByIndent structInstField ", "
    // (allowTrailingSep := true)` — column/newline-sensitive (a same-
    // column-newline is an implicit separator alternative to a literal
    // `,`, per `checkColGe` gating each item, with the accepted implicit
    // separator itself contributing a real empty `null` node —
    // `pushNone`). Task 9's do-notation/tactic work made the general
    // `sep_by_indent` primitive available (generalized from the
    // semicolon-only `SepByIndentSemicolon` placeholder to a
    // `sep`-parameterized `Prim::SepByIndent`, see grammar.rs), so the
    // plain non-indentation-aware `SepBy` approximation is replaced here.
    // Confirmed against a fresh oracle dump of a MULTI-LINE, no-comma
    // struct instance (`{ a := x\n  b := y }`, task-9 report): children
    // interleave `structInstField, null{}, structInstField` — exactly
    // what `sep_by_indent` now produces (see its regression test in
    // parse.rs). Covered by `StructMultiLine.lean` (this task's fixture).
    nd(k, sep_by_indent(field, sep))
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
    let fields = struct_inst_fields(b, ",");
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
pub(super) fn let_config(b: &mut SnapshotBuilder) -> Prim {
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
pub(super) fn let_decl(b: &mut SnapshotBuilder) -> Prim {
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

/// `byTactic' := leading_parser "by " >> Tactic.tacticSeqIndentGt` —
/// NOT itself `@[builtin_term_parser]`-attributed (so not its own
/// surface-table row — same "named but unattributed" treatment as
/// `matchDiscr`/`hygienicLParen`), but IS `leading_parser`, so it
/// node-wraps in its own `Lean.Parser.Term.byTactic'` kind. `showRhs :=
/// fromTerm <|> byTactic'`'s second alternative (Task 9 — was deferred
/// pending `tacticSeq`, now that `tactic.rs` exists).
fn by_tactic_prime(b: &mut SnapshotBuilder) -> Prim {
    let seq_gt = super::tactic::tactic_seq_indent_gt(b);
    let k = b.kind("Lean.Parser.Term.byTactic'");
    nd(k, seq([sym("by"), seq_gt]))
}
/// `showRhs := fromTerm <|> byTactic'` — shared by `«show»` and
/// `sufficesDecl` (both call sites this port needs).
fn show_rhs(b: &mut SnapshotBuilder) -> Prim {
    let from = from_term(b);
    let by_tac = by_tactic_prime(b);
    or_else([from, by_tac])
}

/// `byTactic := leading_parser:leadPrec ppAllowUngrouped >> "by " >>
/// Tactic.tacticSeqIndentGt` (Term.lean:107-108) — fixture-critical:
/// `by` blocks.
fn register_by_tactic(b: &mut SnapshotBuilder) {
    let seq_gt = super::tactic::tactic_seq_indent_gt(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.byTactic",
        LEAD_PREC,
        seq([sym("by"), seq_gt]),
    );
}

fn register_let_have_show_suffices(b: &mut SnapshotBuilder) {
    let_like(b, "Lean.Parser.Term.let", "let", LEAD_PREC);
    let_like(b, "Lean.Parser.Term.have", "have", LEAD_PREC);

    // «show» := leading_parser:leadPrec "show " >> termParser >>
    // showRhs.
    let rhs = show_rhs(b);
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
    let rhs = show_rhs(b);
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
pub(super) fn let_rec_decl(b: &mut SnapshotBuilder) -> Prim {
    let decl = let_decl(b);
    let suffix = super::command::termination_suffix(b);
    let k = b.kind("Lean.Parser.Term.letRecDecl");
    // Task 10: `optional Command.docComment >> optional «attributes»`
    // are now real (`command::doc_comment`/`attr::attributes` didn't
    // exist yet when this was first ported — see those fns' own doc
    // comments) — no fixture needs either on a `let rec`/`where`
    // binding, but wiring the real productions costs nothing once they
    // exist, and is more faithful than an unconditionally-empty slot.
    let doc = super::command::doc_comment(b);
    let attrs = super::attr::attributes(b);
    nd(k, seq([opt(doc), opt(attrs), decl, suffix]))
}
/// `letRecDecls := leading_parser sepBy1 letRecDecl ", "`.
pub(super) fn let_rec_decls(b: &mut SnapshotBuilder) -> Prim {
    let decl = let_rec_decl(b);
    let k = b.kind("Lean.Parser.Term.letRecDecls");
    nd(k, sep_by1(decl, ","))
}

/// `whereDecls := ppDedent ppLine >> "where" >> sepByIndent (ppGroup
/// letRecDecl) "; " (allowTrailingSep := true) >> optional whereFinally`
/// (`Term.lean:740-741`) — M3a Task 10 (`command_decl.rs`'s
/// `declValSimple`/`declValEqns` and this file's own `let_rec_decl`'s
/// `whereFinally` slot? no — `letRecDecl` has no `whereDecls` of its
/// own; this is `declValSimple`'s trailing `optional Term.whereDecls`
/// and `matchAltsWhereDecls`' own `optional whereDecls`, below).
/// `ppGroup` is pretty-print-only (confirmed no extra node, same as
/// `Term.attrInstance`'s own `ppGroup`). `whereFinally` (the `finally |
/// name => tacticSeq` subsection) isn't transcribed — no fixture uses
/// it; a real, always-empty optional slot.
pub(super) fn where_decls(b: &mut SnapshotBuilder) -> Prim {
    let decl = let_rec_decl(b);
    let k = b.kind("Lean.Parser.Term.whereDecls");
    nd(
        k,
        seq([sym("where"), sep_by_indent(decl, ";"), opt(never())]),
    )
}
/// `matchAltsWhereDecls := matchAlts >> Termination.suffix >> optional
/// whereDecls` (`Term.lean:744-745`) — `declValEqns`'s whole body
/// (`command_decl.rs`).
pub(super) fn match_alts_where_decls(b: &mut SnapshotBuilder) -> Prim {
    let alts = match_alts(b, cat("term", 0));
    let suffix = super::command::termination_suffix(b);
    let wd = where_decls(b);
    let k = b.kind("Lean.Parser.Term.matchAltsWhereDecls");
    nd(k, seq([alts, suffix, opt(wd)]))
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

/// `Term.«open» := leading_parser:leadPrec "open" >> Command.openDecl >>
/// withOpenDecl (" in " >> termParser)` (`Command.lean:1018-1019`) —
/// term-scoped `open Foo in <term>`. One of the M3a Task 9-review's 4
/// "wrapper rows owned by nobody in writing" (task-10 brief) — DISTINCT
/// kind from the command-category `«open»` (`command_open.rs`) despite
/// sharing a name and the same `Command.openDecl` sub-grammar (re-
/// exported from `command.rs` for exactly this reuse). `withOpenDecl`
/// threads scope-resolution state through elaboration only — zero tree
/// contribution (same as the command-category `«open»`'s own
/// `withPosition`, which also isn't a real tree node).
fn register_open_in_term(b: &mut SnapshotBuilder) {
    let decl = super::command::open_decl(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.open",
        LEAD_PREC,
        seq([sym("open"), decl, sym("in"), cat("term", 0)]),
    );
}
/// `Term.«set_option» := leading_parser:leadPrec "set_option " >>
/// identWithPartialTrailingDot >> ppSpace >> Command.optionValue >> "
/// in " >> termParser` (`Command.lean:1025-1026`) — term-scoped
/// `set_option opt val in <term>`; the other Task 9-review wrapper row.
fn register_set_option_in_term(b: &mut SnapshotBuilder) {
    b.leading2(
        "term",
        "Lean.Parser.Term.set_option",
        LEAD_PREC,
        seq([
            sym("set_option"),
            super::command::ident_with_partial_trailing_dot(),
            super::command::option_value(),
            sym("in"),
            cat("term", 0),
        ]),
    );
}

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
    register_by_tactic(b);
    register_open_in_term(b);
    register_set_option_in_term(b);
    term_app::register(b);
    term_pragma::register(b);
    term_quot::register(b);
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
