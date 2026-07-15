//! `doElem` category (27 rows, all `port` per the surface table) +
//! the term-category `do`-block wrappers — ORACLE-PORT `Lean/Parser/
//! Do.lean` (every declaration in that file sits in ITS OWN `namespace
//! Term`, nested under `namespace Lean.Parser` — `Do.lean` never opens
//! a `namespace Do` — so every kind name below is `Lean.Parser.Term.*`,
//! matching the surface table's own note on this). One `fn` per
//! production; oracle-checked against fresh dumps (see task-9 report
//! for the probe transcripts), not just read off the source.
//!
//! Shares `term.rs`'s `letConfig`/`letDecl`/`letRecDecls`/`matchDiscr`/
//! `matchAlt(s)`/`binderIdent`/`optType`/`nd` (now `pub(super)`, i.e.
//! visible throughout `builtin`) and `term_pragma`'s `matchExprPat`/
//! `matchExprAlts` (re-exported through `term.rs`), rather than a
//! second, drifting copy of any of them.

use super::term::{
    binder_ident, let_config, let_decl, let_rec_decls, match_alts, match_discr, match_expr_alts,
    match_expr_pat, nd, opt_type,
};
use crate::grammar::*;
use std::sync::Arc;

// ================================================================
// Shared helpers (not their own surface-table rows).
// ================================================================

/// `leftArrow := unicodeSymbol "← " "<- "` (Do.lean:23).
pub(super) fn left_arrow() -> Prim {
    or_else([sym("←"), sym("<-")])
}

/// `notFollowedByRedefinedTermToken` (Do.lean:60-67) — the set of
/// keywords `doReassign`/`doReassignArrow`/`doExpr` must NOT be
/// immediately followed by (each is itself a `doElem`/term keyword that
/// would otherwise ambiguously overlap). Zero-width; no tree
/// contribution, matches only guard against.
fn not_followed_by_redefined_term_token() -> Prim {
    Prim::NotFollowedBy(Arc::new(or_else([
        sym("set_option"),
        sym("open"),
        sym("if"),
        sym("match"),
        sym("match_expr"),
        sym("let"),
        sym("let_expr"),
        sym("have"),
        sym("do"),
        sym("dbg_trace"),
        sym("idbg"),
        sym("assert!"),
        sym("debug_assert!"),
        sym("for"),
        sym("unless"),
        sym("return"),
        sym("try"),
    ])))
}

/// `doSeqItem := leading_parser ppLine >> doElemParser >> optional "; "`
/// (`ppLine` is a pretty-print-only no-op).
fn do_seq_item(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.doSeqItem");
    nd(k, seq([cat("doElem", 0), opt(sym(";"))]))
}
/// `doSeqIndent := leading_parser many1Indent doSeqItem`.
fn do_seq_indent(b: &mut SnapshotBuilder) -> Prim {
    let item = do_seq_item(b);
    let k = b.kind("Lean.Parser.Term.doSeqIndent");
    nd(k, Prim::Many1Indent(Arc::new(item)))
}
/// `doSeqBracketed := leading_parser "{" >> withoutPosition (many1
/// doSeqItem) >> ppLine >> "}"` — plain `many1`, NOT `many1Indent`: a
/// bracketed do-block is NOT indentation-scoped (items are separated
/// only by an optional `;`, relying on each `doElemParser`'s own
/// natural termination). `withoutPosition`/`ppLine` are treated as
/// no-ops (same blanket simplification `term.rs`'s `paren` etc. already
/// document — this port doesn't model `withoutPosition`'s marker-
/// clearing effect; low-impact here since a `doIf`'s own else-chain
/// `checkColGe` guards are the only realistic construct that could
/// observe an inherited outer marker inside `{ }`, and no fixture nests
/// one there).
fn do_seq_bracketed(b: &mut SnapshotBuilder) -> Prim {
    let item = do_seq_item(b);
    let k = b.kind("Lean.Parser.Term.doSeqBracketed");
    nd(k, seq([sym("{"), many1(item), sym("}")]))
}
/// `doSeq := withAntiquot (..) <| doSeqBracketed <|> doSeqIndent` — the
/// `withAntiquot` bypass means `doSeq` itself does NOT `leading_parser`-
/// wrap (no extra node) — confirmed against a fresh dump of a `do`
/// block: `Term.do{"do", doSeqIndent{...}}`, no intervening `doSeq`
/// layer (task-9 report).
pub(super) fn do_seq(b: &mut SnapshotBuilder) -> Prim {
    let bracketed = do_seq_bracketed(b);
    let indent = do_seq_indent(b);
    or_else([bracketed, indent])
}
/// `doMatchAlts := ppDedent <| matchAlts (rhsParser := doSeq)` — same
/// shape `doCatchMatch` reuses (its `doMatchAlts` call, Do.lean:206) and
/// `doMatchExpr`'s own `matchExprAlts (rhsParser := doSeq)`, so this is
/// the ONE place `doSeq`-as-rhs is threaded through `matchAlts`.
fn do_match_alts(b: &mut SnapshotBuilder) -> Prim {
    let seq_p = do_seq(b);
    match_alts(b, seq_p)
}

// ---- doIf's condition family (Do.lean:156-166) --------------------

fn do_if_let_pure(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.doIfLetPure");
    nd(k, seq([sym(":="), cat("term", 0)]))
}
fn do_if_let_bind(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.doIfLetBind");
    nd(k, seq([left_arrow(), cat("term", 0)]))
}
fn do_if_let(b: &mut SnapshotBuilder) -> Prim {
    let pure_alt = do_if_let_pure(b);
    let bind_alt = do_if_let_bind(b);
    let k = b.kind("Lean.Parser.Term.doIfLet");
    nd(
        k,
        seq([sym("let"), cat("term", 0), or_else([pure_alt, bind_alt])]),
    )
}
fn do_if_prop(b: &mut SnapshotBuilder) -> Prim {
    let bi = binder_ident(b);
    let k = b.kind("Lean.Parser.Term.doIfProp");
    nd(k, seq([opt(atomic(seq([bi, sym(":")]))), cat("term", 0)]))
}
/// `doIfCond := withAntiquot (..) <| doIfLet <|> doIfProp` — bypass, no
/// extra node (same `doSeq` pattern above).
fn do_if_cond(b: &mut SnapshotBuilder) -> Prim {
    let let_alt = do_if_let(b);
    let prop_alt = do_if_prop(b);
    or_else([let_alt, prop_alt])
}
/// `elseIf := atomic (group (withPosition ("else " >> checkLineEq >>
/// " if ")))` — the inner `withPosition` establishes ITS OWN marker (at
/// "else"'s position) so `checkLineEq` checks "if" against "else"'s
/// OWN line, not whatever outer marker `doIf` itself established.
fn else_if() -> Prim {
    atomic(Prim::Group(Arc::new(Prim::WithPosition(Arc::new(seq([
        sym("else"),
        Prim::CheckLineEq,
        sym("if"),
    ]))))))
}

// ---- doTry's catch/finally family (Do.lean:203-208) ---------------

fn do_catch(b: &mut SnapshotBuilder) -> Prim {
    let bi = binder_ident(b);
    let k = b.kind("Lean.Parser.Term.doCatch");
    let seq_p = do_seq(b);
    nd(
        k,
        seq([
            atomic(seq([sym("catch"), bi])),
            opt(seq([sym(":"), cat("term", 0)])),
            sym("=>"),
            seq_p,
        ]),
    )
}
fn do_catch_match(b: &mut SnapshotBuilder) -> Prim {
    let alts = do_match_alts(b);
    let k = b.kind("Lean.Parser.Term.doCatchMatch");
    nd(k, seq([sym("catch"), alts]))
}
fn do_finally(b: &mut SnapshotBuilder) -> Prim {
    let seq_p = do_seq(b);
    let k = b.kind("Lean.Parser.Term.doFinally");
    nd(k, seq([sym("finally"), seq_p]))
}

// ---- doFor's declaration list (Do.lean:177-178) --------------------

/// `doForDecl := leading_parser optional (atomic (ident >> " : ")) >>
/// termParser >> " in " >> withForbidden "do" termParser` — NOT itself
/// `leading_parser`-wrapped? It IS: bare `def x := leading_parser ..`
/// self-wraps (confirmed by a fresh dump: `doFor`'s `sepBy1` items are
/// each a `Lean.Parser.Term.doForDecl` node).
fn do_for_decl(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Term.doForDecl");
    nd(
        k,
        seq([
            opt(atomic(seq([Prim::Ident, sym(":")]))),
            cat("term", 0),
            sym("in"),
            with_forbidden("do", cat("term", 0)),
        ]),
    )
}

// ---- doLetArrow/doReassignArrow's doIdDecl/doPatDecl (Do.lean:93-98) ----

/// `doIdDecl := leading_parser atomic (ident >> optType >> ppSpace >>
/// leftArrow) >> doElemParser`.
fn do_id_decl(b: &mut SnapshotBuilder) -> Prim {
    let ot = opt_type(b);
    let k = b.kind("Lean.Parser.Term.doIdDecl");
    nd(
        k,
        seq([
            atomic(seq([Prim::Ident, ot, left_arrow()])),
            cat("doElem", 0),
        ]),
    )
}
/// `doPatDecl := leading_parser atomic (termParser >> optType >>
/// ppSpace >> leftArrow) >> doElemParser >> optional ((checkColGe >>
/// " | " >> doSeqIndent) >> optional (checkColGe >> doSeqIndent))`.
fn do_pat_decl(b: &mut SnapshotBuilder) -> Prim {
    let ot = opt_type(b);
    let seq_indent1 = do_seq_indent(b);
    let seq_indent2 = do_seq_indent(b);
    let k = b.kind("Lean.Parser.Term.doPatDecl");
    nd(
        k,
        seq([
            atomic(seq([cat("term", 0), ot, left_arrow()])),
            cat("doElem", 0),
            opt(seq([
                Prim::CheckColGe,
                sym("|"),
                seq_indent1,
                opt(seq([Prim::CheckColGe, seq_indent2])),
            ])),
        ]),
    )
}

/// `letIdDeclNoBinders := leading_parser atomic (node ``letId ident >>
/// pushNone >> optType >> " := ") >> termParser` (Do.lean:109-110) —
/// `node \`\`letId ident` wraps a BARE ident directly in the SAME
/// `Lean.Parser.Term.letId` kind `term.rs`'s `let_id` uses (interning is
/// idempotent — no drift risk); `pushNone` = `opt(never())`'s own
/// always-empty-`null` idiom.
fn let_id_decl_no_binders(b: &mut SnapshotBuilder) -> Prim {
    let let_id_k = b.kind("Lean.Parser.Term.letId");
    let ot = opt_type(b);
    let k = b.kind("Lean.Parser.Term.letIdDeclNoBinders");
    nd(
        k,
        seq([
            atomic(seq([
                nd(let_id_k, Prim::Ident),
                opt(never()),
                ot,
                sym(":="),
            ])),
            cat("term", 0),
        ]),
    )
}

/// `optMetaFalse := optional (atomic ("(" >> nonReservedSymbol "meta" >>
/// " := " >> nonReservedSymbol "false" >> ") "))` (Do.lean:198).
fn opt_meta_false() -> Prim {
    opt(atomic(seq([
        sym("("),
        Prim::NonReservedSymbol("meta".into()),
        sym(":="),
        Prim::NonReservedSymbol("false".into()),
        sym(")"),
    ])))
}

// ================================================================
// The 27 `doElem` rows.
// ================================================================

fn register_do_let_family(b: &mut SnapshotBuilder) {
    // doLet := leading_parser "let " >> optional "mut " >> letConfig >>
    // letDecl.
    let cfg = let_config(b);
    let decl = let_decl(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doLet",
        MAX_PREC,
        seq([sym("let"), opt(sym("mut")), cfg, decl]),
    );
    // doLetElse := leading_parser withPosition <| "let " >> optional
    // "mut " >> letConfig >> termParser >> " := " >> termParser >>
    // (checkColGe >> " | " >> doSeqIndent) >> optional (checkColGe >>
    // doSeqIndent).
    let cfg = let_config(b);
    let seq_indent1 = do_seq_indent(b);
    let seq_indent2 = do_seq_indent(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doLetElse",
        MAX_PREC,
        Prim::WithPosition(Arc::new(seq([
            sym("let"),
            opt(sym("mut")),
            cfg,
            cat("term", 0),
            sym(":="),
            cat("term", 0),
            Prim::CheckColGe,
            sym("|"),
            seq_indent1,
            opt(seq([Prim::CheckColGe, seq_indent2])),
        ]))),
    );
    // doLetExpr := leading_parser withPosition <| "let_expr " >>
    // matchExprPat >> " := " >> termParser >> (checkColGe >> " | " >>
    // doSeqIndent) >> optional (checkColGe >> doSeqIndent).
    let pat = match_expr_pat(b);
    let seq_indent1 = do_seq_indent(b);
    let seq_indent2 = do_seq_indent(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doLetExpr",
        MAX_PREC,
        Prim::WithPosition(Arc::new(seq([
            sym("let_expr"),
            pat,
            sym(":="),
            cat("term", 0),
            Prim::CheckColGe,
            sym("|"),
            seq_indent1,
            opt(seq([Prim::CheckColGe, seq_indent2])),
        ]))),
    );
    // doLetMetaExpr — same shape, "←" instead of ":=".
    let pat = match_expr_pat(b);
    let seq_indent1 = do_seq_indent(b);
    let seq_indent2 = do_seq_indent(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doLetMetaExpr",
        MAX_PREC,
        Prim::WithPosition(Arc::new(seq([
            sym("let_expr"),
            pat,
            left_arrow(),
            cat("term", 0),
            Prim::CheckColGe,
            sym("|"),
            seq_indent1,
            opt(seq([Prim::CheckColGe, seq_indent2])),
        ]))),
    );
    // doLetRec := leading_parser group ("let " >> nonReservedSymbol
    // "rec ") >> letRecDecls.
    let decls = let_rec_decls(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doLetRec",
        MAX_PREC,
        seq([
            Prim::Group(Arc::new(seq([
                sym("let"),
                Prim::NonReservedSymbol("rec".into()),
            ]))),
            decls,
        ]),
    );
    // doLetArrow := leading_parser withPosition <| "let " >> optional
    // "mut " >> letConfig >> (doIdDecl <|> doPatDecl).
    let cfg = let_config(b);
    let id_decl = do_id_decl(b);
    let pat_decl = do_pat_decl(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doLetArrow",
        MAX_PREC,
        Prim::WithPosition(Arc::new(seq([
            sym("let"),
            opt(sym("mut")),
            cfg,
            or_else([id_decl, pat_decl]),
        ]))),
    );
    // doReassign := leading_parser notFollowedByRedefinedTermToken >>
    // (letIdDeclNoBinders <|> letPatDecl) — `letPatDecl` is NOT ported
    // (no fixture uses pattern-reassignment; same "one alternative
    // deferred" convention `term.rs`'s `let_decl` already established).
    let no_binders = let_id_decl_no_binders(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doReassign",
        MAX_PREC,
        seq([not_followed_by_redefined_term_token(), no_binders]),
    );
    // doReassignArrow := leading_parser notFollowedByRedefinedTermToken
    // >> (doIdDecl <|> doPatDecl) — both alternatives ARE ported here.
    let id_decl = do_id_decl(b);
    let pat_decl = do_pat_decl(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doReassignArrow",
        MAX_PREC,
        seq([
            not_followed_by_redefined_term_token(),
            or_else([id_decl, pat_decl]),
        ]),
    );
    // doHave := leading_parser "have" >> Term.letConfig >> Term.letDecl.
    let cfg = let_config(b);
    let decl = let_decl(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doHave",
        MAX_PREC,
        seq([sym("have"), cfg, decl]),
    );
}

fn register_do_control_flow(b: &mut SnapshotBuilder) {
    // doIf — see the `withResetCache <| withPositionAfterLinebreak <|
    // ..` doc comment above `else_if`: simplified to an unconditional
    // `WithPosition` (real Lean only refreshes the marker when the
    // PREVIOUS token had a trailing linebreak; every do-block `if` this
    // port's fixtures exercise is itself the first token of a fresh
    // `doSeqItem`, where that's always true, so this is unobservable in
    // practice — flagged as a documented, bounded divergence).
    let cond1 = do_if_cond(b);
    let seq1 = do_seq(b);
    let cond2 = do_if_cond(b);
    let seq2 = do_seq(b);
    let seq3 = do_seq(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doIf",
        MAX_PREC,
        Prim::WithPosition(Arc::new(seq([
            sym("if"),
            cond1,
            sym("then"),
            seq1,
            many(seq([
                Prim::CheckColGe,
                Prim::Group(Arc::new(seq([else_if(), cond2, sym("then"), seq2]))),
            ])),
            opt(seq([Prim::CheckColGe, sym("else"), seq3])),
        ]))),
    );
    // doUnless := leading_parser "unless " >> withForbidden "do"
    // termParser >> " do " >> doSeq.
    let seq_p = do_seq(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doUnless",
        MAX_PREC,
        seq([
            sym("unless"),
            with_forbidden("do", cat("term", 0)),
            sym("do"),
            seq_p,
        ]),
    );
    // doFor := leading_parser "for " >> sepBy1 doForDecl ", " >> "do "
    // >> doSeq.
    let decl = do_for_decl(b);
    let seq_p = do_seq(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doFor",
        MAX_PREC,
        seq([sym("for"), sep_by1(decl, ","), sym("do"), seq_p]),
    );
    // doMatch := leading_parser:leadPrec "match " >> optional
    // dependentParam >> optional generalizingParam >> optional motive >>
    // sepBy1 matchDiscr ", " >> " with" >> doMatchAlts. `dependentParam`/
    // `generalizingParam`/`motive` aren't transcribed (no fixture uses
    // any of `match (dependent := ..)`/`(generalizing := ..)`/`(motive
    // := ..)`) — real, always-empty optional slots (same idiom `term.rs`'s
    // `register_match` already established for the plain term `match`).
    let discr = match_discr(b);
    let alts = do_match_alts(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doMatch",
        LEAD_PREC,
        seq([
            sym("match"),
            opt(never()),
            opt(never()),
            opt(never()),
            sep_by1(discr, ","),
            sym("with"),
            alts,
        ]),
    );
    // doMatchExpr := leading_parser:leadPrec "match_expr " >>
    // optMetaFalse >> termParser >> " with" >> doMatchExprAlts.
    let seq_p = do_seq(b);
    let alts = match_expr_alts(b, seq_p);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doMatchExpr",
        LEAD_PREC,
        seq([
            sym("match_expr"),
            opt_meta_false(),
            cat("term", 0),
            sym("with"),
            alts,
        ]),
    );
    // doTry := leading_parser "try " >> doSeq >> many (doCatch <|>
    // doCatchMatch) >> optional doFinally.
    let seq_p = do_seq(b);
    let catch1 = do_catch(b);
    let catch_match1 = do_catch_match(b);
    let finally1 = do_finally(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doTry",
        MAX_PREC,
        seq([
            sym("try"),
            seq_p,
            many(or_else([catch1, catch_match1])),
            opt(finally1),
        ]),
    );
    // doRepeat := leading_parser "repeat " >> doSeq.
    let seq_p = do_seq(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doRepeat",
        MAX_PREC,
        seq([sym("repeat"), seq_p]),
    );
    // doWhile := leading_parser "while " >> withForbidden "do" doIfCond
    // >> " do " >> doSeq.
    let cond = do_if_cond(b);
    let seq_p = do_seq(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doWhile",
        MAX_PREC,
        seq([sym("while"), with_forbidden("do", cond), sym("do"), seq_p]),
    );
    // doRepeatUntil := leading_parser "repeat " >> doSeq >> ppDedent
    // ppLine >> "until " >> termParser.
    let seq_p = do_seq(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doRepeatUntil",
        MAX_PREC,
        seq([sym("repeat"), seq_p, sym("until"), cat("term", 0)]),
    );
}

fn register_do_misc(b: &mut SnapshotBuilder) {
    // doBreak/doContinue := leading_parser "break"/"continue" (bare).
    b.leading2("doElem", "Lean.Parser.Term.doBreak", MAX_PREC, sym("break"));
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doContinue",
        MAX_PREC,
        sym("continue"),
    );
    // doReturn := leading_parser:leadPrec withPosition ("return" >>
    // optional (ppSpace >> checkLineEq >> termParser)).
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doReturn",
        LEAD_PREC,
        Prim::WithPosition(Arc::new(seq([
            sym("return"),
            opt(seq([Prim::CheckLineEq, cat("term", 0)])),
        ]))),
    );
    // doDbgTrace := leading_parser:leadPrec "dbg_trace " >>
    // ((interpolatedStr termParser) <|> termParser) — `interpolatedStr`
    // not ported (same divergence `term_app.rs`'s `dbgTrace` already
    // documents: no fixture needs string-interpolation lexing).
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doDbgTrace",
        LEAD_PREC,
        seq([sym("dbg_trace"), cat("term", 0)]),
    );
    // doIdbg := leading_parser:leadPrec withPosition ("idbg " >>
    // termParser).
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doIdbg",
        LEAD_PREC,
        Prim::WithPosition(Arc::new(seq([sym("idbg"), cat("term", 0)]))),
    );
    // doAssert := leading_parser:leadPrec "assert! " >> termParser.
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doAssert",
        LEAD_PREC,
        seq([sym("assert!"), cat("term", 0)]),
    );
    // doDebugAssert := leading_parser:leadPrec "debug_assert! " >>
    // termParser.
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doDebugAssert",
        LEAD_PREC,
        seq([sym("debug_assert!"), cat("term", 0)]),
    );
    // doExpr := leading_parser notFollowedByRedefinedTermToken >>
    // termParser >> notFollowedBy (symbol ":=" <|> leftArrow) "..".
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doExpr",
        MAX_PREC,
        seq([
            not_followed_by_redefined_term_token(),
            cat("term", 0),
            Prim::NotFollowedBy(Arc::new(or_else([sym(":="), left_arrow()]))),
        ]),
    );
    // doNested := leading_parser "do " >> doSeq.
    let seq_p = do_seq(b);
    b.leading2(
        "doElem",
        "Lean.Parser.Term.doNested",
        MAX_PREC,
        seq([sym("do"), seq_p]),
    );
}

// ================================================================
// The term-category `do`-block wrappers (7 rows).
// ================================================================

fn register_term_wrappers(b: &mut SnapshotBuilder) {
    // nestedAction := leading_parser:minPrec leftArrow >> doElemParser.
    b.leading2(
        "term",
        "Lean.Parser.Term.nestedAction",
        MIN_PREC,
        seq([left_arrow(), cat("doElem", 0)]),
    );
    // doForward := leading_parser (default+1 — a registration-order
    // tie-break, doesn't change `prec`; bare `leading_parser` still
    // means MAX_PREC, this file's established convention) atomic ("do"
    // >> checkNoWsBefore >> leftArrow) >> doSeq.
    let seq_p = do_seq(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.doForward",
        MAX_PREC,
        seq([
            atomic(seq([sym("do"), Prim::CheckNoWsBefore, left_arrow()])),
            seq_p,
        ]),
    );
    // «do» := leading_parser:argPrec ppAllowUngrouped >> "do " >> doSeq.
    let seq_p = do_seq(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.do",
        ARG_PREC,
        seq([sym("do"), seq_p]),
    );
    // termUnless := leading_parser "unless " >> withForbidden "do"
    // termParser >> " do " >> doSeq.
    let seq_p = do_seq(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.termUnless",
        MAX_PREC,
        seq([
            sym("unless"),
            with_forbidden("do", cat("term", 0)),
            sym("do"),
            seq_p,
        ]),
    );
    // termFor := leading_parser "for " >> sepBy1 doForDecl ", " >> " do
    // " >> doSeq.
    let decl = do_for_decl(b);
    let seq_p = do_seq(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.termFor",
        MAX_PREC,
        seq([sym("for"), sep_by1(decl, ","), sym("do"), seq_p]),
    );
    // termTry := leading_parser "try " >> doSeq >> many (doCatch <|>
    // doCatchMatch) >> optional doFinally.
    let seq_p = do_seq(b);
    let catch1 = do_catch(b);
    let catch_match1 = do_catch_match(b);
    let finally1 = do_finally(b);
    b.leading2(
        "term",
        "Lean.Parser.Term.termTry",
        MAX_PREC,
        seq([
            sym("try"),
            seq_p,
            many(or_else([catch1, catch_match1])),
            opt(finally1),
        ]),
    );
    // termReturn := leading_parser:leadPrec withPosition ("return" >>
    // optional (ppSpace >> checkLineEq >> termParser)) — same shape as
    // `doReturn` above (a distinct kind name, so a distinct `leading2`
    // registration; no fn-sharing risk since each call interns its own
    // `Prim::WithPosition` tree fresh).
    b.leading2(
        "term",
        "Lean.Parser.Term.termReturn",
        LEAD_PREC,
        Prim::WithPosition(Arc::new(seq([
            sym("return"),
            opt(seq([Prim::CheckLineEq, cat("term", 0)])),
        ]))),
    );
}

pub fn register(b: &mut SnapshotBuilder) {
    register_do_let_family(b);
    register_do_control_flow(b);
    register_do_misc(b);
    register_term_wrappers(b);
}

#[cfg(test)]
mod tests {
    use crate::builtin;
    use crate::parse_module;

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

    #[test]
    fn smoke_do_try_catch_finally() {
        let out =
            parse_ok("def doTryEx := do\n  try\n    x\n  catch e =>\n    y\n  finally\n    z");
        assert!(out.contains("Lean.Parser.Term.doTry"), "{out}");
        assert!(out.contains("Lean.Parser.Term.doCatch"), "{out}");
        assert!(out.contains("Lean.Parser.Term.doFinally"), "{out}");
    }

    #[test]
    fn smoke_do_for_multi_decl() {
        let out = parse_ok("def doForMulti := do\n  for a in xs, b in ys do\n    f a b");
        assert!(out.contains("Lean.Parser.Term.doFor"), "{out}");
        assert!(out.contains("Lean.Parser.Term.doForDecl"), "{out}");
    }

    #[test]
    fn smoke_do_while() {
        let out = parse_ok("def doWhileEx := do\n  while cond do\n    x");
        assert!(out.contains("Lean.Parser.Term.doWhile"), "{out}");
    }

    #[test]
    fn smoke_do_repeat_until() {
        let out = parse_ok("def doRepeatUntilEx := do\n  repeat\n    x\n  until cond");
        assert!(out.contains("Lean.Parser.Term.doRepeatUntil"), "{out}");
    }

    #[test]
    fn smoke_do_unless() {
        let out = parse_ok("def doUnlessEx := do\n  unless cond do\n    x");
        assert!(out.contains("Lean.Parser.Term.doUnless"), "{out}");
    }

    #[test]
    fn smoke_do_have() {
        let out = parse_ok("def doHaveEx := do\n  have h := a\n  h");
        assert!(out.contains("Lean.Parser.Term.doHave"), "{out}");
    }

    #[test]
    fn smoke_do_let_rec() {
        let out = parse_ok("def doLetRecEx := do\n  let rec f := fun x => x\n  f a");
        assert!(out.contains("Lean.Parser.Term.doLetRec"), "{out}");
    }

    #[test]
    fn smoke_do_break_continue() {
        let out = parse_ok(
            "def doBreakContinueEx := do\n  for x in xs do\n    if p then\n      break\n    continue",
        );
        assert!(out.contains("Lean.Parser.Term.doBreak"), "{out}");
        assert!(out.contains("Lean.Parser.Term.doContinue"), "{out}");
    }

    #[test]
    fn smoke_do_dbg_trace_and_assert() {
        let out = parse_ok("def doDbgTraceEx := do\n  dbg_trace x\n  pure x");
        assert!(out.contains("Lean.Parser.Term.doDbgTrace"), "{out}");
        let out = parse_ok("def doAssertEx := do\n  assert! x\n  pure x");
        assert!(out.contains("Lean.Parser.Term.doAssert"), "{out}");
    }

    #[test]
    fn smoke_nested_action_and_do_forward() {
        let out = parse_ok("def doNestedActionEx := f (← g)");
        assert!(out.contains("Lean.Parser.Term.nestedAction"), "{out}");
        let out = parse_ok("def doForwardEx := f (do← g)");
        assert!(out.contains("Lean.Parser.Term.doForward"), "{out}");
    }

    #[test]
    fn smoke_term_unless_for_try_return() {
        let out = parse_ok("def termUnlessEx := unless cond do\n  x");
        assert!(out.contains("Lean.Parser.Term.termUnless"), "{out}");
        let out = parse_ok("def termForEx := for a in xs do\n  f a");
        assert!(out.contains("Lean.Parser.Term.termFor"), "{out}");
        let out = parse_ok("def termTryEx := try\n  x\ncatch e =>\n  y");
        assert!(out.contains("Lean.Parser.Term.termTry"), "{out}");
        let out = parse_ok("def termReturnEx := return x");
        assert!(out.contains("Lean.Parser.Term.termReturn"), "{out}");
    }

    #[test]
    fn smoke_do_if_else_if_else() {
        let out =
            parse_ok("def foo := do\n  if a then\n    x\n  else if b then\n    y\n  else\n    w");
        assert!(out.contains("Lean.Parser.Term.doIf"), "{out}");
    }

    #[test]
    fn smoke_do_if_let() {
        // `doIfLet`/`doIfLetPure` — a pattern-`let` condition (`if let x
        // := e then ..`), ported per source but not exercised by any
        // committed fixture (every `MatchDo.lean`/`ByTac.lean` `if` uses
        // a plain `doIfProp` condition instead).
        let out = parse_ok("def doIfLetEx := do\n  if let x := e then\n    a\n  else\n    b");
        assert!(out.contains("Lean.Parser.Term.doIfLet"), "{out}");
        assert!(out.contains("Lean.Parser.Term.doIfLetPure"), "{out}");
    }

    #[test]
    fn smoke_do_if_let_bind() {
        // `doIfLetBind` — the `←` variant (`if let x ← e then ..`).
        let out = parse_ok("def doIfLetBindEx := do\n  if let x ← e then\n    a\n  else\n    b");
        assert!(out.contains("Lean.Parser.Term.doIfLetBind"), "{out}");
    }

    #[test]
    fn smoke_do_pat_decl() {
        // `doPatDecl` — a PATTERN (not bare ident) `let`-arrow LHS
        // (`let (a, b) ← pair`), ported per source but not exercised by
        // any committed fixture (every `MatchDo.lean` `let .. ←` uses a
        // bare ident LHS, which resolves to `doIdDecl` instead).
        let out = parse_ok("def doPatDeclEx := do\n  let (a, b) ← pair\n  pure a");
        assert!(out.contains("Lean.Parser.Term.doPatDecl"), "{out}");
    }

    #[test]
    fn smoke_do_reassign() {
        let out = parse_ok("def r := do\n  let mut x := a\n  x := b\n  pure x");
        assert!(out.contains("Lean.Parser.Term.doReassign"), "{out}");
        assert!(out.contains("Lean.Parser.Term.letIdDeclNoBinders"), "{out}");
    }

    #[test]
    fn smoke_do_match_expr_and_let_expr() {
        let out =
            parse_ok("def m := do\n  match_expr e with\n  | Foo a b => pure a\n  | _ => pure e");
        assert!(out.contains("Lean.Parser.Term.doMatchExpr"), "{out}");
        let out = parse_ok("def le := do\n  let_expr Foo a b := e | pure a\n  pure e");
        assert!(out.contains("Lean.Parser.Term.doLetExpr"), "{out}");
    }
}
