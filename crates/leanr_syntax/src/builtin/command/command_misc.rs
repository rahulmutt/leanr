//! Every remaining `command`-category `port` row: `moduleDoc` + the
//! `#`-prefixed introspection commands + the small bootstrapping/
//! registration commands. All structurally trivial fixed-shape
//! productions (symbols, idents, optional string/attribute arguments) —
//! ORACLE-PORT `Lean/Parser/Command.lean:59-61,533-664,889-1009` +
//! `Lean/Meta/Tactic/Grind/Parser.lean:140-144`.

use crate::builtin::attr::attr_kind;
use crate::builtin::command::doc_comment;
use crate::grammar::*;

fn module_doc(b: &mut SnapshotBuilder) {
    // moduleDoc := leading_parser ppDedent <| "/-!" >> ifVersoModuleDocs
    // versoCommentBody commentBody >> ppLine — `doc.verso` defaults
    // false, same `commentBody`/`Prim::DocCommentBody` raw scan
    // `Command.docComment` uses (see that fn's own citation).
    b.leading2(
        "command",
        "Lean.Parser.Command.moduleDoc",
        MAX_PREC,
        seq([sym("/-!"), Prim::DocCommentBody]),
    );
}

fn check_family(b: &mut SnapshotBuilder) {
    b.leading2(
        "command",
        "Lean.Parser.Command.check",
        MAX_PREC,
        seq([sym("#check"), cat("term", 0)]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.check_failure",
        MAX_PREC,
        seq([sym("#check_failure"), cat("term", 0)]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.importPath",
        MAX_PREC,
        seq([sym("#import_path"), Prim::Ident]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.assertNotExists",
        MAX_PREC,
        seq([sym("assert_not_exists"), many1(Prim::Ident)]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.assertNotImported",
        MAX_PREC,
        seq([sym("assert_not_imported"), many1(Prim::Ident)]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.checkAssertions",
        MAX_PREC,
        seq([sym("#check_assertions"), opt(sym("!"))]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.eval",
        MAX_PREC,
        seq([sym("#eval"), cat("term", 0)]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.evalBang",
        MAX_PREC,
        seq([sym("#eval!"), cat("term", 0)]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.synth",
        MAX_PREC,
        seq([sym("#synth"), cat("term", 0)]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.exit",
        MAX_PREC,
        sym("#exit"),
    );
}

fn print_family(b: &mut SnapshotBuilder) {
    b.leading2(
        "command",
        "Lean.Parser.Command.print",
        MAX_PREC,
        seq([sym("#print"), or_else([Prim::Ident, Prim::StrLit])]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.printSig",
        MAX_PREC,
        seq([
            sym("#print"),
            Prim::NonReservedSymbol("sig".into()),
            Prim::Ident,
        ]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.printAxioms",
        MAX_PREC,
        seq([
            sym("#print"),
            Prim::NonReservedSymbol("axioms".into()),
            Prim::Ident,
        ]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.printEqns",
        MAX_PREC,
        seq([
            sym("#print"),
            or_else([
                Prim::NonReservedSymbol("equations".into()),
                Prim::NonReservedSymbol("eqns".into()),
            ]),
            Prim::Ident,
        ]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.printTacTags",
        MAX_PREC,
        seq([
            sym("#print"),
            Prim::NonReservedSymbol("tactic".into()),
            Prim::NonReservedSymbol("tags".into()),
        ]),
    );
}

fn misc_hash_commands(b: &mut SnapshotBuilder) {
    b.leading2(
        "command",
        "Lean.Parser.Command.where",
        MAX_PREC,
        sym("#where"),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.version",
        MAX_PREC,
        sym("#version"),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.withExporting",
        MAX_PREC,
        seq([sym("#with_exporting"), cat("command", 0)]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.dumpAsyncEnvState",
        MAX_PREC,
        sym("#dump_async_env_state"),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.showDeprecatedModules",
        MAX_PREC,
        sym("#show_deprecated_modules"),
    );
}

/// The `optional (ppSpace >> strLit) >> optional (" (" >> nonReservedSymbol
/// "since" >> " := " >> strLit >> ")")` tail shared by `deprecatedSyntax`
/// and `«deprecated_module»`.
fn since_clause_tail() -> Prim {
    seq([
        opt(Prim::StrLit),
        opt(seq([
            sym("("),
            Prim::NonReservedSymbol("since".into()),
            sym(":="),
            Prim::StrLit,
            sym(")"),
        ])),
    ])
}

fn bootstrapping_and_registration(b: &mut SnapshotBuilder) {
    b.leading2(
        "command",
        "Lean.Parser.Command.deprecatedSyntax",
        MAX_PREC,
        seq([sym("deprecated_syntax"), Prim::Ident, since_clause_tail()]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.init_quot",
        MAX_PREC,
        sym("init_quot"),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.docs_to_verso",
        MAX_PREC,
        seq([sym("docs_to_verso"), sep_by1(Prim::Ident, ",")]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.deprecated_module",
        MAX_PREC,
        seq([sym("deprecated_module"), since_clause_tail()]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.unlock_limits",
        MAX_PREC,
        sym("unlock_limits"),
    );
    // addDocString := docComment >> "add_decl_doc " >> ident.
    let doc = doc_comment(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.addDocString",
        MAX_PREC,
        seq([doc, sym("add_decl_doc"), Prim::Ident]),
    );
    // «register_tactic_tag» := optional (docComment >> ppLine) >>
    // "register_tactic_tag " >> ident >> strLit.
    let doc = doc_comment(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.register_tactic_tag",
        MAX_PREC,
        seq([
            opt(doc),
            sym("register_tactic_tag"),
            Prim::Ident,
            Prim::StrLit,
        ]),
    );
    // «tactic_extension» := optional (docComment >> ppLine) >>
    // "tactic_extension " >> ident.
    let doc = doc_comment(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.tactic_extension",
        MAX_PREC,
        seq([opt(doc), sym("tactic_extension"), Prim::Ident]),
    );
    // «recommended_spelling» := optional (docComment >> ppLine) >>
    // "recommended_spelling " >> strLit >> " for " >> strLit >> " in " >>
    // "[" >> sepBy1 ident ", " >> "]".
    let doc = doc_comment(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.recommended_spelling",
        MAX_PREC,
        seq([
            opt(doc),
            sym("recommended_spelling"),
            Prim::StrLit,
            Prim::NonReservedSymbol("for".into()),
            Prim::StrLit,
            Prim::NonReservedSymbol("in".into()),
            sym("["),
            sep_by1(Prim::Ident, ","),
            sym("]"),
        ]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.genInjectiveTheorems",
        MAX_PREC,
        seq([sym("gen_injective_theorems%"), Prim::Ident]),
    );
    // registerErrorExplanationStx := optional docComment >>
    // "register_error_explanation " >> ident >> termParser.
    let doc = doc_comment(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.registerErrorExplanationStx",
        MAX_PREC,
        seq([
            opt(doc),
            sym("register_error_explanation"),
            Prim::Ident,
            cat("term", 0),
        ]),
    );
}

/// `grindPattern` (`Grind/Parser.lean:140-141`) is `Term.attrKind`, then
/// the `"grind_pattern "` keyword, then an optional bracketed ident,
/// then an ident, then `darrow`, then a comma-separated term list, then
/// an optional `grindPatternCnstrs` tail. `grindPatternCnstrs`'s own
/// inner `guard`/`check`/`notDefEq`/`defEq` sub-grammar is NOT
/// transcribed (grind-tactic-specific, zero fixture value, needs its
/// own `where`-clause `many1Indent` recursion into a bespoke constraint
/// syntax); real, always-empty optional slot.
fn grind_commands(b: &mut SnapshotBuilder) {
    let ak = attr_kind(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.grindPattern",
        MAX_PREC,
        seq([
            ak,
            sym("grind_pattern"),
            opt(seq([sym("["), Prim::Ident, sym("]")])),
            Prim::Ident,
            sym("=>"),
            sep_by1(cat("term", 0), ","),
            opt(never()),
        ]),
    );
    b.leading2(
        "command",
        "Lean.Parser.Command.initGrindNorm",
        MAX_PREC,
        seq([
            sym("init_grind_norm"),
            many(Prim::Ident),
            sym("|"),
            many(Prim::Ident),
        ]),
    );
}

pub fn register(b: &mut SnapshotBuilder) {
    module_doc(b);
    check_family(b);
    print_family(b);
    misc_hash_commands(b);
    bootstrapping_and_registration(b);
    grind_commands(b);
}
