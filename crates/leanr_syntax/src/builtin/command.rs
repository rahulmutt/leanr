//! The micro command set + module header (Task 7's vertical slice).
//! ORACLE-PORT `Lean/Parser/Module/Syntax.lean` (header) and
//! `Lean/Parser/Command.lean` (`declaration`/`definition`/…) — every
//! shape below was cross-checked against a FRESH oracle dump of
//! `tests/fixtures/syntax/Micro.lean` (`mise run fixtures:regen`),
//! not just read off the source: the pinned v4.32.0-rc1 toolchain has
//! the module-system rewrite (`module`/`public import`/`meta import`),
//! which the task brief's inline sketch (citing an older `Module.lean`
//! shape) didn't anticipate — this file mirrors the ACTUAL pin.
//! Task 10 replaces the micro command set with the real `declaration`
//! dispatcher (`abbrev`/`theorem`/`instance`/…); every "not implemented
//! yet" slot below is a real, oracle-confirmed empty `null` node in the
//! meantime (never a guess), so Task 10 can extend rather than redo it.

use crate::grammar::*;
use crate::kind::SyntaxKind;
use std::sync::Arc;

/// `Prim::Node` with no prec gate — the sub-node shape every compound
/// production uses.
fn node_named(kind: SyntaxKind, body: Prim) -> Prim {
    Prim::Node {
        kind,
        prec: None,
        body: Arc::new(body),
    }
}

/// Placeholder for a grammar slot this micro set doesn't implement yet
/// (termination hints, universe binders, deriving clauses, doc
/// comments, attributes, …). Every M3a fixture that reaches one of
/// these slots leaves it absent, and an always-empty `optional`
/// reproduces the oracle's empty `null` node exactly: `Prim::Optional`
/// always wraps in a `null` node (parse.rs), and an empty `Seq` pushes
/// no events, so the `null` ends up with zero children either way —
/// bit-for-bit what a real oracle dump shows for these slots (Task 7's
/// Micro.lean dump: `declModifiers`'s 7 children, `optDeclSig`'s 2,
/// `Termination.suffix`'s 2, are all empty `null`s exactly like this).
fn empty_opt() -> Prim {
    Prim::Optional(Arc::new(Prim::Seq(vec![])))
}

pub fn register(b: &mut SnapshotBuilder) {
    // --- module header (ORACLE-PORT `Lean/Parser/Module/Syntax.lean`
    // `header`) ---------------------------------------------------
    // v4.32.0-rc1's `header` = optional module marker, optional
    // prelude, many imports (each with optional public/meta/all
    // modifiers then an identifier). `ppLine` calls throughout the
    // oracle's definition are formatter-only no-ops (`Lean/Parser/
    // Extra.lean`: `ppLine := skip`, arity 0) — they push no syntax,
    // so they're simply absent here. Confirmed shape (3 children:
    // null(module?), null(prelude?), null(imports*)) against a fresh
    // dump of `prelude\n\ndef x := 42\n`.
    let header_kind = b.kind("Lean.Parser.Module.header");
    let module_tk_kind = b.kind("Lean.Parser.Module.moduleTk");
    let prelude_kind = b.kind("Lean.Parser.Module.prelude");
    let public_kind = b.kind("Lean.Parser.Module.public");
    let meta_kind = b.kind("Lean.Parser.Module.meta");
    let all_kind = b.kind("Lean.Parser.Module.all");
    let import_kind = b.kind("Lean.Parser.Module.import");
    b.set_header(node_named(
        header_kind,
        seq([
            opt(node_named(module_tk_kind, sym("module"))),
            opt(node_named(prelude_kind, sym("prelude"))),
            many(node_named(
                import_kind,
                seq([
                    // ORACLE-PORT: the oracle wraps
                    // `optional public >> optional meta >> "import"` in
                    // `atomic` (so a partial match backtracks cleanly);
                    // doesn't affect the success-path shape below.
                    atomic(seq([
                        opt(node_named(public_kind, sym("public"))),
                        opt(node_named(meta_kind, sym("meta"))),
                        sym("import"),
                    ])),
                    opt(node_named(all_kind, sym("all"))),
                    // ORACLE-PORT `identWithPartialTrailingDot`
                    // (Extra.lean): `ident >> optional (checkNoWsBefore
                    // >> "." >> checkNoWsBefore >> ident)` — a plain
                    // `Parser` sequence (no `leading_parser`), so it
                    // contributes a bare ident leaf plus a null, not a
                    // node of its own.
                    Prim::Ident,
                    opt(seq([
                        Prim::CheckNoWsBefore,
                        sym("."),
                        Prim::CheckNoWsBefore,
                        Prim::Ident,
                    ])),
                ]),
            )),
        ]),
    ));

    // --- micro command set -------------------------------------------
    // Just enough for the vertical slice: `def x := <term>`.
    let modifiers = b.kind("Lean.Parser.Command.declModifiers");
    let def_k = b.kind("Lean.Parser.Command.definition");
    let decl_id = b.kind("Lean.Parser.Command.declId");
    let decl_sig = b.kind("Lean.Parser.Command.optDeclSig");
    let decl_val = b.kind("Lean.Parser.Command.declValSimple");
    let termination_suffix = b.kind("Lean.Parser.Termination.suffix");
    b.leading2(
        "command",
        "Lean.Parser.Command.declaration",
        MAX_PREC,
        seq([
            // `declModifiers false` (Command.lean): 7 optional slots —
            // doc comment, attributes, visibility, protected,
            // meta|noncomputable, unsafe, partial|nonrec — none
            // implemented yet.
            node_named(
                modifiers,
                seq((0..7).map(|_| empty_opt()).collect::<Vec<_>>()),
            ),
            node_named(
                def_k,
                seq([
                    sym("def"),
                    node_named(decl_id, seq([Prim::Ident, empty_opt()])),
                    node_named(decl_sig, seq([empty_opt(), empty_opt()])),
                    node_named(
                        decl_val,
                        seq([
                            sym(":="),
                            cat("term", 0),
                            node_named(termination_suffix, seq([empty_opt(), empty_opt()])),
                            empty_opt(),
                        ]),
                    ),
                    empty_opt(), // optDefDeriving
                ]),
            ),
        ]),
    );
    // The term category's own literal/atom registrations (idents,
    // numerals, …) now live in `term.rs` (M3a Task 8) — this file keeps
    // only the command-category micro set.
}
