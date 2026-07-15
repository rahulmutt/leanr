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
    // DISPATCH NOTE (M3a Task 10 review Finding 1 — corrected; the
    // previous version of this comment claimed a registration-order
    // tie-break that real Lean does not have). `attr`'s category
    // behavior is `LeadingIdentBehavior::Symbol` (`Attr.lean:20`:
    // `registerBuiltinParserAttribute \`builtin_attr_parser
    // ``Category.attr .symbol`). ORACLE-PORT `Basic.lean`'s `indexed`:
    // under `.symbol`, when the leading token is an ident whose text
    // equals a registered literal key (`recursor`/`default_instance`/
    // `specialize`/`extern`, each `nonReservedSymbol`-keyed), ONLY that
    // key's parser runs — `simple`'s generic `ident`-keyed candidate is
    // never even tried, full stop, no tie to break. `parse.rs::dispatch`
    // now implements this directly (`suppress_plain_ident`), so e.g.
    // `@[extern foo]` is REJECTED (`externEntry` needs a `strLit`,
    // `simple` is never a candidate to fall back to) and `@[recursor 0]`/
    // `@[default_instance 50]`/bare `@[specialize]` all resolve to their
    // own row without any longest-match contest against `simple`.
    // Registration order below is therefore no longer semantically
    // load-bearing for this tie — kept as-is (rather than reverting to
    // the oracle's own source order, which declares `simple` first) only
    // to avoid gratuitous dump churn (`AttrWide.lean`'s committed dump
    // already reflects this order). `class`/`instance`/`«macro»`/
    // `«export»`/`tactic_alt`/`tactic_tag`/`tactic_name` are all REAL
    // `Symbol`s (not `nonReservedSymbol`), so they always lex as `Atom`,
    // never `Ident` — never in the running for this dispatch at all.
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

#[cfg(test)]
mod tests {
    use crate::builtin;
    use crate::parse_module;

    /// M3a Task 10 review Finding 1 — `attr`'s category behavior is
    /// `LeadingIdentBehavior::Symbol` (`Attr.lean:20`), so a literal-key
    /// ident match (`recursor`/`default_instance`/`specialize`/`extern`)
    /// must suppress `Attr.simple`'s generic `ident` candidate entirely,
    /// not merely out-consume or out-order it. These four MUST be
    /// rejected: `externEntry` needs a `strLit` (`@[extern foo]` has a
    /// bare ident instead), `recursor` needs a mandatory `numLit`
    /// (`@[recursor]` has none), and `default_instance`'s optional tail
    /// is `priorityParser` (a numeral), not an arbitrary `ident`
    /// (`@[default_instance foo]`).
    fn expect_rejected(attr_src: &str) {
        let snap = builtin::snapshot();
        let src = format!("prelude\n\n{attr_src} def x := y\n");
        let result = parse_module(&src, &snap);
        assert!(
            !result.errors.is_empty(),
            "expected {attr_src:?} to be REJECTED (oracle divergence \
             otherwise), but it parsed clean"
        );
    }

    fn expect_accepted(attr_src: &str) {
        let snap = builtin::snapshot();
        let src = format!("prelude\n\n{attr_src} def x := y\n");
        let result = parse_module(&src, &snap);
        assert!(
            result.errors.is_empty(),
            "expected {attr_src:?} to parse clean, got {:?}",
            result.errors
        );
    }

    #[test]
    fn extern_foo_is_rejected_not_misparsed_as_simple() {
        expect_rejected("@[extern foo]");
    }

    #[test]
    fn bare_recursor_is_rejected_not_misparsed_as_simple() {
        expect_rejected("@[recursor]");
    }

    #[test]
    fn default_instance_foo_is_rejected_not_misparsed_as_simple() {
        expect_rejected("@[default_instance foo]");
    }

    #[test]
    fn recursor_with_numeral_still_parses_as_recursor() {
        let snap = builtin::snapshot();
        let src = "prelude\n\n@[recursor 0] def x := y\n";
        let result = parse_module(src, &snap);
        assert!(
            result.errors.is_empty(),
            "expected clean parse, got {:?}",
            result.errors
        );
        let out = crate::canon::canon_jsonl(&result.tree);
        assert!(out.contains(r#""k":"Lean.Parser.Attr.recursor""#), "{out}");
    }

    #[test]
    fn specialize_with_ident_still_parses_as_specialize() {
        let snap = builtin::snapshot();
        let src = "prelude\n\n@[specialize foo] def x := y\n";
        let result = parse_module(src, &snap);
        assert!(
            result.errors.is_empty(),
            "expected clean parse, got {:?}",
            result.errors
        );
        let out = crate::canon::canon_jsonl(&result.tree);
        assert!(
            out.contains(r#""k":"Lean.Parser.Attr.specialize""#),
            "{out}"
        );
    }

    #[test]
    fn extern_with_strlit_still_parses_as_extern() {
        let snap = builtin::snapshot();
        let src = "prelude\n\n@[extern \"f\"] def x := y\n";
        let result = parse_module(src, &snap);
        assert!(
            result.errors.is_empty(),
            "expected clean parse, got {:?}",
            result.errors
        );
        let out = crate::canon::canon_jsonl(&result.tree);
        assert!(out.contains(r#""k":"Lean.Parser.Attr.extern""#), "{out}");
    }

    #[test]
    fn plain_simp_still_parses_as_simple() {
        expect_accepted("@[simp]");
        let snap = builtin::snapshot();
        let src = "prelude\n\n@[simp] def x := y\n";
        let result = parse_module(src, &snap);
        let out = crate::canon::canon_jsonl(&result.tree);
        assert!(out.contains(r#""k":"Lean.Parser.Attr.simple""#), "{out}");
    }
}
