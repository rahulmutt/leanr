//! The `attr` category (`Lean/Parser/Attr.lean`, surface table's own
//! 12-row category) + `Priority.numPrio` (the table's `prio` misc
//! singleton) + `Term.attributes`/`attrInstance`/`attrKind`/`«scoped»`/
//! `«local»` (`Lean/Parser/Term.lean:583-590` — Term-namespaced helper
//! productions, not their own surface-table rows, but colocated here
//! since they exist ONLY to feed `declModifiers`' `@[attr1, attr2]`
//! slot and `attribute`'s `[...]` list).
//!
//! Not itself one of Task 10's named rows (the brief's table assigns
//! this category to nobody) — ported here because `Lean.Parser.
//! Command.declModifiers`' attribute slot and the `attribute` command
//! are fixture-critical (`@[someAttr] def attributed := x`, `attribute
//! [someAttr] opened`) and structurally depend on it. ORACLE-PORT
//! `Lean/Parser/Attr.lean` (12 declarations, confirmed "trivial
//! fixed-shape" by the surface table's own annotation) + `Term.lean`
//! lines 583-590.
//!
//! `Attr.simple`/`«instance»`/`default_instance`'s own optional priority
//! slot (`priorityParser`) recurses into the `prio` category exactly
//! like `term`'s `cat("term", ..)` — `Priority.numPrio` (`checkPrec
//! maxPrec >> numLit`) is registered there via `leading_raw` (bare, no
//! extra node — same "not `leading_parser`, self-wraps via `NumLit`'s
//! own `num` node" shape as `Term.num`, `term.rs`'s `register_literals`).

use crate::grammar::*;
use std::sync::Arc;

fn nd(kind: crate::kind::SyntaxKind, body: Prim) -> Prim {
    Prim::Node {
        kind,
        prec: None,
        body: Arc::new(body),
    }
}

// ================================================================
// `attr` category (Attr.lean).
// ================================================================

/// `externEntry := leading_parser optional (ident >> ppSpace) >>
/// optional (nonReservedSymbol "inline ") >> strLit` — NOT its own
/// surface-table row (not `@[builtin_attr_parser]`-attributed, plain
/// helper), but IS `leading_parser` (self-wraps) — a prior version of
/// this port missed that, dropping the wrap; confirmed against a fresh
/// dump of `@[extern "foo"]`/`@[extern foo inline "bar"]` (task-10
/// report): the item inside `extern`'s own `many` is `Lean.Parser.Attr.
/// externEntry{..}`, not a bare tuple.
fn extern_entry(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Attr.externEntry");
    nd(
        k,
        seq([
            opt(Prim::Ident),
            opt(Prim::NonReservedSymbol("inline".into())),
            Prim::StrLit,
        ]),
    )
}

fn register_attr_category(b: &mut SnapshotBuilder) {
    // ORDERING NOTE (M3a Task 10 review finding): every
    // `nonReservedSymbol`-keyed row (`recursor`/`default_instance`/
    // `specialize`/`extern`) is registered BEFORE `simple` —
    // DELIBERATELY, not source order (the oracle declares `simple`
    // first). Each is `nonReservedSymbol`-keyed, so its leading token
    // is `Ident`-kind text, dispatched ALONGSIDE `simple`'s own generic
    // `Ident`-kind candidate (`dispatch`'s dual `FirstTok::Sym` arm,
    // parse.rs). Whenever the row's OWN tail can consume the exact same
    // span `simple`'s `optional (priorityParser <|> ident)` tail would
    // (a bare numeral via the shared `prio` category recursion, e.g.
    // `@[recursor 0]`/`@[default_instance 50]`; or simply NOTHING,
    // since `specialize`/`extern`'s own tails are `many`-based and admit
    // zero items too, e.g. bare `@[specialize]`/`@[extern]`) — this is
    // an EXACT tie in total consumed length. This engine's
    // `longest_match` (parse.rs) keeps the FIRST candidate on a tie
    // (`self.pos > w.end`, strict), so registration order is genuinely
    // load-bearing here: fresh dumps of `@[recursor 0]`/`@[default_
    // instance 50]`/bare `@[specialize]` all confirmed the specific row
    // must win, not `simple` (task-10 report — this fixes real bugs an
    // early version of this file had, since `simple` was registered
    // first throughout). `class`/`instance`/`«macro»`/`«export»`/
    // `tactic_alt`/`tactic_tag`/`tactic_name` are all REAL `Symbol`s
    // (not `nonReservedSymbol`), so they always lex as `Atom`, never
    // `Ident` — no collision with `simple`'s `Ident`-keyed dispatch,
    // hence no ordering sensitivity for them.
    //
    // recursor := leading_parser nonReservedSymbol "recursor " >> numLit.
    b.leading2(
        "attr",
        "Lean.Parser.Attr.recursor",
        MAX_PREC,
        seq([Prim::NonReservedSymbol("recursor".into()), Prim::NumLit]),
    );
    // default_instance := leading_parser nonReservedSymbol
    // "default_instance" >> optional (ppSpace >> priorityParser).
    b.leading2(
        "attr",
        "Lean.Parser.Attr.default_instance",
        MAX_PREC,
        seq([
            Prim::NonReservedSymbol("default_instance".into()),
            opt(cat("prio", 0)),
        ]),
    );
    // «specialize» := leading_parser (nonReservedSymbol "specialize") >>
    // many (ppSpace >> (ident <|> numLit)).
    b.leading2(
        "attr",
        "Lean.Parser.Attr.specialize",
        MAX_PREC,
        seq([
            Prim::NonReservedSymbol("specialize".into()),
            many(or_else([Prim::Ident, Prim::NumLit])),
        ]),
    );
    // extern := leading_parser nonReservedSymbol "extern" >> many
    // (ppSpace >> externEntry).
    let entry = extern_entry(b);
    b.leading2(
        "attr",
        "Lean.Parser.Attr.extern",
        MAX_PREC,
        seq([Prim::NonReservedSymbol("extern".into()), many(entry)]),
    );
    // simple := leading_parser ident >> optional (ppSpace >>
    // (priorityParser <|> ident)).
    b.leading2(
        "attr",
        "Lean.Parser.Attr.simple",
        MAX_PREC,
        seq([Prim::Ident, opt(or_else([cat("prio", 0), Prim::Ident]))]),
    );
    // «macro» := leading_parser "macro " >> ident.
    b.leading2(
        "attr",
        "Lean.Parser.Attr.macro",
        MAX_PREC,
        seq([sym("macro"), Prim::Ident]),
    );
    // «export» := leading_parser "export " >> ident.
    b.leading2(
        "attr",
        "Lean.Parser.Attr.export",
        MAX_PREC,
        seq([sym("export"), Prim::Ident]),
    );
    // «class» := leading_parser "class".
    b.leading2("attr", "Lean.Parser.Attr.class", MAX_PREC, sym("class"));
    // «instance» := leading_parser "instance" >> optional (ppSpace >>
    // priorityParser).
    b.leading2(
        "attr",
        "Lean.Parser.Attr.instance",
        MAX_PREC,
        seq([sym("instance"), opt(cat("prio", 0))]),
    );
    // «tactic_alt» := leading_parser "tactic_alt" >> ppSpace >> ident.
    b.leading2(
        "attr",
        "Lean.Parser.Attr.tactic_alt",
        MAX_PREC,
        seq([sym("tactic_alt"), Prim::Ident]),
    );
    // «tactic_tag» := leading_parser "tactic_tag" >> many1 (ppSpace >>
    // ident).
    b.leading2(
        "attr",
        "Lean.Parser.Attr.tactic_tag",
        MAX_PREC,
        seq([sym("tactic_tag"), many1(Prim::Ident)]),
    );
    // «tactic_name» := leading_parser "tactic_name" >> ppSpace >> (ident
    // <|> strLit).
    b.leading2(
        "attr",
        "Lean.Parser.Attr.tactic_name",
        MAX_PREC,
        seq([sym("tactic_name"), or_else([Prim::Ident, Prim::StrLit])]),
    );
}

/// `Priority.numPrio := checkPrec maxPrec >> numLit` — the `prio`
/// misc-singleton category; NOT `leading_parser` (self-wraps only via
/// `NumLit`'s own "num" node, same `leading_raw` shape as `Term.num`).
fn register_prio_category(b: &mut SnapshotBuilder) {
    b.leading_raw("prio", Prim::NumLit);
}

// ================================================================
// `Term.attributes`/`attrInstance`/`attrKind`/`«scoped»`/`«local»`
// (Term.lean:583-590) — feed `declModifiers`/`attribute`'s `@[...]`.
// ================================================================

/// `«scoped» := leading_parser "scoped "`; `«local» := leading_parser
/// "local "` — each IS its own `leading_parser` (self-wraps), even
/// though neither is `@[builtin_term_parser]`-attributed (same "named,
/// unattributed, but node-wrapping" shape as `matchDiscr`/
/// `hygienicLParen`).
fn scoped_or_local(b: &mut SnapshotBuilder) -> Prim {
    let scoped_k = b.kind("Lean.Parser.Term.scoped");
    let local_k = b.kind("Lean.Parser.Term.local");
    or_else([nd(scoped_k, sym("scoped")), nd(local_k, sym("local"))])
}

/// `attrKind := leading_parser optional («scoped» <|> «local»)`.
pub(super) fn attr_kind(b: &mut SnapshotBuilder) -> Prim {
    let alt = scoped_or_local(b);
    let k = b.kind("Lean.Parser.Term.attrKind");
    nd(k, opt(alt))
}

/// `attrInstance := ppGroup $ leading_parser attrKind >> attrParser` —
/// `ppGroup` is a pretty-print-only no-op (confirmed against a fresh
/// oracle dump of `@[someAttr]`: `attrInstance`'s node has exactly 2
/// children, `attrKind` then the `attr`-category result — no extra
/// "group" wrapper). `attrParser := categoryParser \`attr rbp`. `pub(
/// super)`: `command_open.rs`'s `attribute` command (`attribute [foo]
/// bar`) needs a bare `attrInstance` too, distinct from `attributes`'
/// `@[...]`-bracketed list below.
pub(super) fn attr_instance(b: &mut SnapshotBuilder) -> Prim {
    let kind = attr_kind(b);
    let k = b.kind("Lean.Parser.Term.attrInstance");
    nd(k, seq([kind, cat("attr", 0)]))
}

/// `attributes := leading_parser "@[" >> withoutPosition (sepBy1
/// attrInstance ", ") >> "] "` — `withoutPosition` is position-marker-
/// only (no tree contribution); `sepBy1`'s own `null` wrap is what shows
/// up around the (possibly single) `attrInstance` in a fresh dump.
pub(super) fn attributes(b: &mut SnapshotBuilder) -> Prim {
    let inst = attr_instance(b);
    let k = b.kind("Lean.Parser.Term.attributes");
    nd(k, seq([sym("@["), sep_by1(inst, ","), sym("]")]))
}

pub fn register(b: &mut SnapshotBuilder) {
    register_prio_category(b);
    register_attr_category(b);
}
