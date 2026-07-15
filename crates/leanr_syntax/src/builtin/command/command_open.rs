//! Scoping/namespacing commands: `namespace`/`section`/`end`/
//! `withWeakNamespace`, `open` (all 5 sub-forms) + the generic `«in»`
//! command-continuation wrapper, `mutual`, `initialize`, `variable`/
//! `universe`, `set_option`, `attribute`, `export`, `import` (the
//! error-message-only placeholder), `include`/`omit`. ORACLE-PORT
//! `Lean/Parser/Command.lean:288-864,968-977` — cross-checked against
//! fresh dumps of `Cmds.lean` (task-10 report).

use crate::builtin::command::{ident_with_partial_trailing_dot, nd};
use crate::builtin::do_notation::{do_seq, left_arrow};
use crate::builtin::term::{bracketed_binder, inst_binder, type_spec};
use crate::grammar::*;
use std::sync::Arc;

// ================================================================
// namespace / section / end / with_weak_namespace.
// ================================================================

fn namespace_cmd(b: &mut SnapshotBuilder) {
    b.leading2(
        "command",
        "Lean.Parser.Command.namespace",
        MAX_PREC,
        seq([sym("namespace"), Prim::CheckColGt, Prim::Ident]),
    );
}
fn with_weak_namespace(b: &mut SnapshotBuilder) {
    b.leading2(
        "command",
        "Lean.Parser.Command.withWeakNamespace",
        MAX_PREC,
        seq([
            sym("with_weak_namespace"),
            Prim::CheckColGt,
            Prim::Ident,
            Prim::CheckColGt,
            cat("command", 0),
        ]),
    );
}
/// `sectionHeader := optional ("@[" >> nonReservedSymbol "expose" >>
/// "] ") >> optional "public " >> optional "noncomputable " >> optional
/// "meta "` — none of these 4 slots are exercised by any fixture, but
/// each is a plain keyword/attribute-bracket, cheap to port for real
/// (confirmed against a fresh dump of `section MySection`: all 4 empty
/// `null`s, same shape `section`'s own children show).
fn section_header(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.sectionHeader");
    nd(
        k,
        seq([
            opt(seq([
                sym("@["),
                Prim::NonReservedSymbol("expose".into()),
                sym("]"),
            ])),
            opt(sym("public")),
            opt(sym("noncomputable")),
            opt(sym("meta")),
        ]),
    )
}
fn section_cmd(b: &mut SnapshotBuilder) {
    let header = section_header(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.section",
        MAX_PREC,
        seq([
            header,
            sym("section"),
            opt(seq([Prim::CheckColGt, Prim::Ident])),
        ]),
    );
}
fn end_cmd(b: &mut SnapshotBuilder) {
    b.leading2(
        "command",
        "Lean.Parser.Command.end",
        MAX_PREC,
        seq([
            sym("end"),
            opt(seq([Prim::CheckColGt, ident_with_partial_trailing_dot()])),
        ]),
    );
}

// ================================================================
// variable / universe.
// ================================================================

fn variable_cmd(b: &mut SnapshotBuilder) {
    let binder = bracketed_binder(b, false);
    b.leading2(
        "command",
        "Lean.Parser.Command.variable",
        MAX_PREC,
        seq([sym("variable"), many1(seq([Prim::CheckColGt, binder]))]),
    );
}
fn universe_cmd(b: &mut SnapshotBuilder) {
    b.leading2(
        "command",
        "Lean.Parser.Command.universe",
        MAX_PREC,
        seq([sym("universe"), many1(seq([Prim::CheckColGt, Prim::Ident]))]),
    );
}

// ================================================================
// open (all 5 sub-forms) + the generic `«in»` wrapper.
// ================================================================

fn open_hiding(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.openHiding");
    nd(
        k,
        seq([
            atomic(seq([Prim::Ident, sym("hiding")])),
            many1(seq([Prim::CheckColGt, Prim::Ident])),
        ]),
    )
}
fn open_renaming_item(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.openRenamingItem");
    nd(
        k,
        seq([
            Prim::Ident,
            or_else([sym("→"), sym("->")]),
            Prim::CheckColGt,
            Prim::Ident,
        ]),
    )
}
fn open_renaming(b: &mut SnapshotBuilder) -> Prim {
    let item = open_renaming_item(b);
    let k = b.kind("Lean.Parser.Command.openRenaming");
    nd(
        k,
        seq([
            atomic(seq([Prim::Ident, sym("renaming")])),
            sep_by1(item, ","),
        ]),
    )
}
fn open_only(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.openOnly");
    nd(
        k,
        seq([
            atomic(seq([Prim::Ident, sym("(")])),
            many1(Prim::Ident),
            sym(")"),
        ]),
    )
}
fn open_simple(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.openSimple");
    nd(k, many1(seq([Prim::CheckColGt, Prim::Ident])))
}
fn open_scoped(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.openScoped");
    nd(
        k,
        seq([sym("scoped"), many1(seq([Prim::CheckColGt, Prim::Ident]))]),
    )
}
/// `openDecl := withAntiquot (..) <| openHiding <|> openRenaming <|>
/// openOnly <|> openSimple <|> openScoped` — the antiquot wrapper is a
/// no-op on the real (non-antiquotation) path, so this is a bare
/// `or_else`, matching `declVal`'s identical shape; shared by
/// `Command.«open»` (this file), `Term.«open»` (`term.rs`), and
/// `Tactic.«open»` (`tactic.rs`).
pub(crate) fn open_decl(b: &mut SnapshotBuilder) -> Prim {
    let hiding = open_hiding(b);
    let renaming = open_renaming(b);
    let only = open_only(b);
    let simple = open_simple(b);
    let scoped = open_scoped(b);
    or_else([hiding, renaming, only, simple, scoped])
}
fn open_cmd(b: &mut SnapshotBuilder) {
    let decl = open_decl(b);
    let body = Prim::WithPosition(Arc::new(seq([sym("open"), decl])));
    b.leading2("command", "Lean.Parser.Command.open", MAX_PREC, body);
}
/// `«in» := trailing_parser withOpen (ppDedent (" in" >> ppLine >>
/// commandParser))` (`Command.lean:864-865`) — a TRAILING command-
/// category production: the already-parsed command becomes the Pratt
/// lhs, then `"in"`, then another whole command recursion. Bare
/// `trailing_parser` (no `:P:L` annotation) — per `BuiltinNotation.
/// lean:194-197` (already the load-bearing citation for `term.rs`'s
/// `arrow`/`completion`/`proj`), an omitted `prec` defaults to
/// `maxPrec` but an omitted `lhsPrec` defaults to 0, NOT to `prec`.
/// `withOpen` threads scope-resolution state through ELABORATION only —
/// confirmed zero tree contribution against a fresh dump of `open Outer.
/// Inner in def opened := deep`: `Lean.Parser.Command.in`'s 3 children
/// are exactly `open`, `"in"`, the recursed `declaration` — no extra
/// node for `withOpen`.
fn in_cmd(b: &mut SnapshotBuilder) {
    b.trailing2(
        "command",
        "Lean.Parser.Command.in",
        MAX_PREC,
        0,
        seq([sym("in"), cat("command", 0)]),
    );
}

// ================================================================
// mutual.
// ================================================================

fn mutual_cmd(b: &mut SnapshotBuilder) {
    b.leading2(
        "command",
        "Lean.Parser.Command.mutual",
        MAX_PREC,
        seq([
            sym("mutual"),
            many1(seq([
                Prim::NotFollowedBy(Arc::new(sym("end"))),
                cat("command", 0),
            ])),
            sym("end"),
        ]),
    );
}

// ================================================================
// initialize / builtin_initialize.
// ================================================================

/// `«initialize» := declModifiers false >> initializeKeyword >> optional
/// (atomic (ident >> Term.typeSpec >> ppSpace >> Term.leftArrow)) >>
/// Term.doSeq` (`Command.lean:858-862`) — obscure bootstrapping command
/// (no fixture uses it), still ported in full: `do_notation.rs` already
/// exports `do_seq`/`left_arrow` for exactly this kind of reuse.
/// `initializeKeyword := leading_parser "initialize " <|>
/// "builtin_initialize "` — IS `leading_parser` (self-wraps; a prior
/// version of this port missed that, dropping the wrap — confirmed
/// against a fresh dump of `initialize foo : Nat ← pure z`, task-10
/// report).
fn initialize_keyword(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.initializeKeyword");
    nd(k, or_else([sym("initialize"), sym("builtin_initialize")]))
}
fn initialize_cmd(b: &mut SnapshotBuilder) {
    let modifiers = crate::builtin::command::decl_modifiers(b);
    let keyword = initialize_keyword(b);
    let ts = type_spec(b);
    let seq_p = do_seq(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.initialize",
        MAX_PREC,
        seq([
            modifiers,
            keyword,
            opt(atomic(seq([Prim::Ident, ts, left_arrow()]))),
            seq_p,
        ]),
    );
}

// ================================================================
// set_option (+ its own `... in` continuation shares `«in»`, above).
// ================================================================

/// `optionValue := nonReservedSymbol "true" <|> nonReservedSymbol
/// "false" <|> strLit <|> numLit` (`Command.lean:666`).
pub(crate) fn option_value() -> Prim {
    or_else([
        Prim::NonReservedSymbol("true".into()),
        Prim::NonReservedSymbol("false".into()),
        Prim::StrLit,
        Prim::NumLit,
    ])
}
fn set_option_cmd(b: &mut SnapshotBuilder) {
    b.leading2(
        "command",
        "Lean.Parser.Command.set_option",
        MAX_PREC,
        seq([
            sym("set_option"),
            ident_with_partial_trailing_dot(),
            option_value(),
        ]),
    );
}

// ================================================================
// attribute / export / import (placeholder) / include / omit.
// ================================================================

/// `eraseAttr := "-" >> rawIdent` — `rawIdent` (bypasses reserved-word
/// restrictions) approximated with plain `ident`; no fixture erases a
/// reserved-word-named attribute. Documented divergence (same as
/// `command_decl.rs`'s `ctor` row).
fn erase_attr(b: &mut SnapshotBuilder) -> Prim {
    // IS `leading_parser` (self-wraps) — a prior version of this port
    // missed that, dropping the wrap; confirmed against a fresh dump of
    // `attribute [-simp] foo`: the `sepBy1`'s item is
    // `Lean.Parser.Command.eraseAttr{"-", "simp"}`, not a bare pair.
    let k = b.kind("Lean.Parser.Command.eraseAttr");
    nd(k, seq([sym("-"), Prim::Ident]))
}
fn attribute_cmd(b: &mut SnapshotBuilder) {
    let inst = crate::builtin::attr::attr_instance(b);
    let erase = erase_attr(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.attribute",
        MAX_PREC,
        seq([
            sym("attribute"),
            sym("["),
            sep_by1(or_else([erase, inst]), ","),
            sym("]"),
            many1(Prim::Ident),
        ]),
    );
}
fn export_cmd(b: &mut SnapshotBuilder) {
    b.leading2(
        "command",
        "Lean.Parser.Command.export",
        MAX_PREC,
        seq([
            sym("export"),
            Prim::Ident,
            sym("("),
            many1(Prim::Ident),
            sym(")"),
        ]),
    );
}
/// `«import» := leading_parser "import"` — "not a real command, only
/// for error messages" (source's own comment): bare `MAX_PREC` node, no
/// further children, so a stray mid-file `import` at least gets a
/// dedicated, nameable node instead of falling straight to recovery.
fn import_placeholder(b: &mut SnapshotBuilder) {
    b.leading2(
        "command",
        "Lean.Parser.Command.import",
        MAX_PREC,
        sym("import"),
    );
}
fn include_cmd(b: &mut SnapshotBuilder) {
    b.leading2(
        "command",
        "Lean.Parser.Command.include",
        MAX_PREC,
        seq([sym("include"), many1(seq([Prim::CheckColGt, Prim::Ident]))]),
    );
}
fn omit_cmd(b: &mut SnapshotBuilder) {
    let inst = inst_binder(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.omit",
        MAX_PREC,
        seq([
            sym("omit"),
            many1(seq([Prim::CheckColGt, or_else([Prim::Ident, inst])])),
        ]),
    );
}

pub fn register(b: &mut SnapshotBuilder) {
    namespace_cmd(b);
    with_weak_namespace(b);
    section_cmd(b);
    end_cmd(b);
    variable_cmd(b);
    universe_cmd(b);
    open_cmd(b);
    in_cmd(b);
    mutual_cmd(b);
    initialize_cmd(b);
    set_option_cmd(b);
    attribute_cmd(b);
    export_cmd(b);
    import_placeholder(b);
    include_cmd(b);
    omit_cmd(b);
}
