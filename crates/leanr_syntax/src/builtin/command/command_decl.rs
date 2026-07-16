//! The `declaration` dispatcher (`Lean/Parser/Command.lean:100-285`) —
//! ONE surface-table row (`declaration`, the single most fixture-
//! critical row in the whole plan), whose body is an `or_else` over 11
//! plain (unattributed) `def`s: `«abbrev»`/`definition`/`«theorem»`/
//! `«opaque»`/`«instance»`/`«axiom»`/`«example»`/`«inductive»`/
//! `«coinductive»`/`classInductive`/`«structure»`. ORACLE-PORT the whole
//! file cross-checked against fresh dumps of `Decls.lean`/`Types.lean`
//! (task-10 report has the probe transcripts).
//!
//! Documented divergence shared by EVERY alternative below: the oracle
//! wraps each declaration's identifier in `recover declId
//! skipUntilWsOrDelim` (best-effort resync if the identifier itself is
//! malformed) — this port calls `decl_id` directly, with no inner
//! recovery. A malformed identifier here fails the whole `declaration`
//! candidate, and `recover_command` (Task 7/11) takes over at the
//! command level instead — Task 11 owns recovery hardening generally,
//! consistent with Tasks 8/9's own `recover ... skip` precedent
//! (`term.rs`'s `«deriving»`-style `sepBy1 (recover termParser skip)`
//! sites use the same "just run the inner parser" simplification).

use crate::builtin::attr::attr_kind;
use crate::builtin::command::{decl_modifiers, doc_comment, named_prio, nd, termination_suffix};
use crate::builtin::term::{
    binder_ident, bracketed_binder, match_alts_where_decls, opt_type, struct_inst_fields,
    type_spec, where_decls,
};
use crate::grammar::*;
use std::sync::Arc;

/// `declId := ident >> optional (checkNoWsBefore ".{" >> sepBy1 (recover
/// ident ..) ", " >> "}")` — no fixture uses the `.{u,v}` universe-param
/// suffix, but it costs nothing to port for real (`recover ident ..`
/// simplified to plain `ident`, same divergence as the module doc
/// comment).
fn decl_id(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.declId");
    nd(
        k,
        seq([
            Prim::Ident,
            opt(seq([
                Prim::CheckNoWsBefore,
                sym(".{"),
                sep_by1(Prim::Ident, ","),
                sym("}"),
            ])),
        ]),
    )
}

fn decl_binder(b: &mut SnapshotBuilder) -> Prim {
    let bi = binder_ident(b);
    let bb = bracketed_binder(b, false);
    or_else([bi, bb])
}
/// `declSig := many (ppSpace >> (Term.binderIdent <|> Term.bracketedBinder))
/// >> Term.typeSpec` — mandatory type (bare `typeSpec` node, not wrapped
/// in a further `optional`).
fn decl_sig(b: &mut SnapshotBuilder) -> Prim {
    let binder = decl_binder(b);
    let ts = type_spec(b);
    let k = b.kind("Lean.Parser.Command.declSig");
    nd(k, seq([many(binder), ts]))
}
/// `optDeclSig := many (..) >> Term.optType` — optional type.
fn opt_decl_sig(b: &mut SnapshotBuilder) -> Prim {
    let binder = decl_binder(b);
    let ot = opt_type(b);
    let k = b.kind("Lean.Parser.Command.optDeclSig");
    nd(k, seq([many(binder), ot]))
}

/// `declValSimple := " :=" >> ppHardLineUnlessUngrouped >> declBody >>
/// Termination.suffix >> optional Term.whereDecls`. `declBody`'s
/// `lookahead (setExpected [] "by") >> termParser leadPrec <|>
/// termParser` is a pretty-printer/error-quality nicety over "parse a
/// term" — both branches parse identically (the term category's own
/// `byTactic` production is fixed-shape regardless of the surrounding
/// rbp), so a plain `cat("term", 0)` produces the identical tree either
/// way (matches every prior task's own convention here, e.g. `ByTac.
/// lean`'s existing golden fixture already exercises `:= by ..`
/// bodies through this exact path).
fn decl_val_simple(b: &mut SnapshotBuilder) -> Prim {
    let suffix = termination_suffix(b);
    let wd = where_decls(b);
    let k = b.kind("Lean.Parser.Command.declValSimple");
    nd(k, seq([sym(":="), cat("term", 0), suffix, opt(wd)]))
}
/// `declValEqns := leading_parser Term.matchAltsWhereDecls`.
fn decl_val_eqns(b: &mut SnapshotBuilder) -> Prim {
    let mawd = match_alts_where_decls(b);
    let k = b.kind("Lean.Parser.Command.declValEqns");
    nd(k, mawd)
}
/// `whereStructInst := ppIndent ppSpace >> "where" >> Term.
/// structInstFields (sepByIndent Term.structInstField "; "
/// (allowTrailingSep := true)) >> optional Term.whereDecls` — NOTE the
/// `"; "` separator (semicolon), distinct from `Term.structInst`'s own
/// literal `{ .. }` use of `Term.structInstFields`, which separates
/// fields with `", "` (comma) — the same underlying `structInstFields
/// (p : Parser) := node structInstFields p` wrapper, parameterized
/// differently per call site (`term.rs`'s `struct_inst_fields` takes the
/// separator as a parameter for exactly this reason).
fn where_struct_inst(b: &mut SnapshotBuilder) -> Prim {
    let fields = struct_inst_fields(b, ";");
    let wd = where_decls(b);
    let k = b.kind("Lean.Parser.Command.whereStructInst");
    nd(k, seq([sym("where"), fields, opt(wd)]))
}
/// `declVal := withAntiquot (..) <| declValSimple <|> declValEqns <|>
/// whereStructInst` — the antiquot wrapper only matters for the
/// (unsupported, M3b) antiquotation path; the real path is a bare
/// `or_else`, no extra node (same shape as `openDecl`).
fn decl_val(b: &mut SnapshotBuilder) -> Prim {
    let simple = decl_val_simple(b);
    let eqns = decl_val_eqns(b);
    let wsi = where_struct_inst(b);
    or_else([simple, eqns, wsi])
}

// ================================================================
// `deriving` clauses (shared by `definition`, `inductive`/
// `coinductive`/`classInductive`, `structure`, and the top-level
// `«deriving»` command in `command_misc.rs`).
// ================================================================

/// `derivingClass := leading_parser optional ("@[" >> nonReservedSymbol
/// "expose" >> "]") >> withForbidden "for" termParser` — IS
/// `leading_parser` (self-wraps; a prior version of this port missed
/// that, dropping the wrap — confirmed against a fresh dump of `deriving
/// instance Repr for Foo`, task-10 report: the item inside `derivingClasses`'
/// own `sepBy1` wrap is `Lean.Parser.Command.derivingClass{null{},
/// id:"Repr"}`, not a bare `id:"Repr"`). `withForbidden` is the SAME
/// primitive Task 9's `do`-notation needed (`Command.lean:190`'s own
/// citation for this exact row in the task brief); needed so the
/// deriving list's own trailing `" for "` keyword can't be swallowed as
/// a term application argument.
fn deriving_class(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.derivingClass");
    nd(
        k,
        seq([
            opt(seq([
                sym("@["),
                Prim::NonReservedSymbol("expose".into()),
                sym("]"),
            ])),
            with_forbidden("for", cat("term", 0)),
        ]),
    )
}
fn deriving_classes(b: &mut SnapshotBuilder) -> Prim {
    let dc = deriving_class(b);
    sep_by1(dc, ",")
}
/// The `"deriving " >> notSymbol "instance" >> notSymbol "noncomputable"`
/// prefix shared by `optDeriving`/`optDefDeriving`/the top-level
/// `«deriving»` command — `notSymbol` ORACLE-PORT is a `NotFollowedBy`
/// guard (zero-width, same as `Term.letDecl`'s `notFollowedBy
/// (nonReservedSymbol "rec")`).
pub(super) fn deriving_clause_prefix() -> Prim {
    atomic(seq([
        sym("deriving"),
        Prim::NotFollowedBy(Arc::new(sym("instance"))),
        Prim::NotFollowedBy(Arc::new(sym("noncomputable"))),
    ]))
}
/// `optDeriving := leading_parser optional (.. >> derivingClasses)` — IS
/// `leading_parser` (self-wraps; used by `inductive`/`coinductive`/
/// `classInductive`/`structure`).
fn opt_deriving(b: &mut SnapshotBuilder) -> Prim {
    let classes = deriving_classes(b);
    let k = b.kind("Lean.Parser.Command.optDeriving");
    nd(k, opt(seq([deriving_clause_prefix(), classes])))
}
/// `optDefDeriving := optional (.. >> derivingClasses)` — NOT
/// `leading_parser` (a plain `def` bound to an `optional(..)` VALUE), so
/// unlike `optDeriving` it does NOT self-wrap: confirmed against a fresh
/// dump of `def documented .. := a` (no deriving clause): `definition`'s
/// LAST child is a bare `null{}`, no `optDefDeriving`-named node.
fn opt_def_deriving(b: &mut SnapshotBuilder) -> Prim {
    let classes = deriving_classes(b);
    opt(seq([deriving_clause_prefix(), classes]))
}

// ================================================================
// The 11 `declaration` alternatives.
// ================================================================

fn abbrev(b: &mut SnapshotBuilder) -> Prim {
    let id = decl_id(b);
    let sig = opt_decl_sig(b);
    let val = decl_val(b);
    let k = b.kind("Lean.Parser.Command.abbrev");
    nd(k, seq([sym("abbrev"), id, sig, val]))
}
fn definition(b: &mut SnapshotBuilder) -> Prim {
    let id = decl_id(b);
    let sig = opt_decl_sig(b);
    let val = decl_val(b);
    let deriv = opt_def_deriving(b);
    let k = b.kind("Lean.Parser.Command.definition");
    nd(k, seq([sym("def"), id, sig, val, deriv]))
}
fn theorem(b: &mut SnapshotBuilder) -> Prim {
    let id = decl_id(b);
    let sig = decl_sig(b);
    let val = decl_val(b);
    let k = b.kind("Lean.Parser.Command.theorem");
    nd(k, seq([sym("theorem"), id, sig, val]))
}
fn opaque(b: &mut SnapshotBuilder) -> Prim {
    let id = decl_id(b);
    let sig = decl_sig(b);
    let val = decl_val_simple(b);
    let k = b.kind("Lean.Parser.Command.opaque");
    nd(k, seq([sym("opaque"), id, sig, opt(val)]))
}
fn instance_decl(b: &mut SnapshotBuilder) -> Prim {
    let ak = attr_kind(b);
    let prio = opt(named_prio(b));
    let id = decl_id(b);
    let sig = decl_sig(b);
    let val = decl_val(b);
    let k = b.kind("Lean.Parser.Command.instance");
    nd(k, seq([ak, sym("instance"), prio, opt(id), sig, val]))
}
fn axiom_decl(b: &mut SnapshotBuilder) -> Prim {
    let id = decl_id(b);
    let sig = decl_sig(b);
    let k = b.kind("Lean.Parser.Command.axiom");
    nd(k, seq([sym("axiom"), id, sig]))
}
fn example_decl(b: &mut SnapshotBuilder) -> Prim {
    let sig = opt_decl_sig(b);
    let val = decl_val(b);
    let k = b.kind("Lean.Parser.Command.example");
    nd(k, seq([sym("example"), sig, val]))
}

/// `ctor := atomic (optional docComment >> "\n| ") >> ppGroup
/// (declModifiers true >> rawIdent >> optDeclSig)` — the `"\n| "`
/// literal strips to a bare `"|"` token (the leading newline is
/// whitespace-formatting convention, not a distinct check — confirmed
/// against a fresh dump: the atom is `{"a":"|",...}`, never `"\n|"`).
/// `rawIdent` (a ctor name bypassing reserved-word restrictions)
/// approximated with plain `ident` — no fixture needs a
/// reserved-word-named constructor; documented divergence.
fn ctor(b: &mut SnapshotBuilder) -> Prim {
    let doc = doc_comment(b);
    let modifiers = decl_modifiers(b);
    let sig = opt_decl_sig(b);
    let k = b.kind("Lean.Parser.Command.ctor");
    nd(
        k,
        seq([
            atomic(seq([opt(doc), sym("|")])),
            modifiers,
            Prim::Ident,
            sig,
        ]),
    )
}

fn inductive_like(b: &mut SnapshotBuilder, kind_name: &str, keyword: &str) -> Prim {
    let id = decl_id(b);
    let sig = opt_decl_sig(b);
    let ctor_p = ctor(b);
    let deriv = opt_deriving(b);
    let k = b.kind(kind_name);
    nd(
        k,
        seq([
            sym(keyword),
            id,
            sig,
            opt(or_else([sym(":="), sym("where")])),
            many(ctor_p),
            // `optional (ppDedent ppLine >> computedFields)` — no call
            // site in this port's scope exercises `with`-computed
            // fields on an inductive (needs a fresh `manyIndent`
            // recursion into `Term.matchAlts`, zero fixture value);
            // real, always-empty optional slot.
            opt(never()),
            deriv,
        ]),
    )
}
fn class_inductive(b: &mut SnapshotBuilder) -> Prim {
    let id = decl_id(b);
    let sig = opt_decl_sig(b);
    let ctor_p = ctor(b);
    let deriv = opt_deriving(b);
    let k = b.kind("Lean.Parser.Command.classInductive");
    nd(
        k,
        seq([
            atomic(Prim::Group(Arc::new(seq([sym("class"), sym("inductive")])))),
            id,
            sig,
            opt(or_else([sym(":="), sym("where")])),
            many(ctor_p),
            deriv,
        ]),
    )
}

// ================================================================
// `structure`/`class` (both dispatch through `«structure»`).
// ================================================================

fn struct_parent(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.structParent");
    nd(
        k,
        seq([opt(atomic(seq([Prim::Ident, sym(":")]))), cat("term", 0)]),
    )
}
fn extends_clause(b: &mut SnapshotBuilder) -> Prim {
    let parent = struct_parent(b);
    let ot = opt_type(b);
    let k = b.kind("Lean.Parser.Command.extends");
    nd(k, seq([sym("extends"), sep_by1(parent, ","), ot]))
}
/// `structCtor := leading_parser atomic (ppIndent (declModifiers true >>
/// ident >> many (ppSpace >> Term.bracketedBinder) >> " :: "))` — no
/// fixture names a custom struct constructor; still ported (cheap,
/// reuses machinery already needed elsewhere).
fn struct_ctor(b: &mut SnapshotBuilder) -> Prim {
    let modifiers = decl_modifiers(b);
    let binder = bracketed_binder(b, false);
    let k = b.kind("Lean.Parser.Command.structCtor");
    nd(
        k,
        atomic(seq([modifiers, Prim::Ident, many(binder), sym("::")])),
    )
}
/// `Term.binderTactic`/`Term.binderDefault`'s slot — not transcribed
/// anywhere in this port (same always-empty idiom `term.rs`'s
/// `explicit_binder` already established for the identical
/// `optional (binderTactic <|> binderDefault)` shape).
fn opt_binder_tactic_or_default() -> Prim {
    opt(never())
}
fn struct_explicit_binder(b: &mut SnapshotBuilder) -> Prim {
    let modifiers = decl_modifiers(b);
    let sig = opt_decl_sig(b);
    let k = b.kind("Lean.Parser.Command.structExplicitBinder");
    nd(
        k,
        seq([
            atomic(seq([modifiers, sym("(")])),
            many1(Prim::Ident),
            sig,
            opt_binder_tactic_or_default(),
            sym(")"),
        ]),
    )
}
fn struct_implicit_binder(b: &mut SnapshotBuilder) -> Prim {
    let modifiers = decl_modifiers(b);
    let sig = decl_sig(b);
    let k = b.kind("Lean.Parser.Command.structImplicitBinder");
    nd(
        k,
        seq([
            atomic(seq([modifiers, sym("{")])),
            many1(Prim::Ident),
            sig,
            sym("}"),
        ]),
    )
}
fn struct_inst_binder(b: &mut SnapshotBuilder) -> Prim {
    let modifiers = decl_modifiers(b);
    let sig = decl_sig(b);
    let k = b.kind("Lean.Parser.Command.structInstBinder");
    nd(
        k,
        seq([
            atomic(seq([modifiers, sym("[")])),
            many1(Prim::Ident),
            sig,
            sym("]"),
        ]),
    )
}
fn struct_simple_binder(b: &mut SnapshotBuilder) -> Prim {
    let modifiers = decl_modifiers(b);
    let sig = opt_decl_sig(b);
    let k = b.kind("Lean.Parser.Command.structSimpleBinder");
    nd(
        k,
        seq([
            atomic(seq([modifiers, Prim::Ident])),
            sig,
            opt_binder_tactic_or_default(),
        ]),
    )
}
/// `manyIndent p := withPosition ((colGe p)*)` (`Extra.lean:193-199`) —
/// the 0-or-more sibling of `Prim::Many1Indent`'s own expansion; no new
/// `Prim` variant needed, it's the SAME `WithPosition(Many(Seq([
/// CheckColGe, p])))` shape with `Many` instead of `Many1` (see `parse.
/// rs`'s `Many1Indent` interpreter arm for the citation this mirrors).
fn many_indent(p: Prim) -> Prim {
    Prim::WithPosition(Arc::new(Prim::Many(Arc::new(seq([Prim::CheckColGe, p])))))
}
fn struct_fields(b: &mut SnapshotBuilder) -> Prim {
    let explicit = struct_explicit_binder(b);
    let implicit = struct_implicit_binder(b);
    let inst = struct_inst_binder(b);
    let simple = struct_simple_binder(b);
    let k = b.kind("Lean.Parser.Command.structFields");
    nd(k, many_indent(or_else([explicit, implicit, inst, simple])))
}
fn structure_like(b: &mut SnapshotBuilder) -> Prim {
    let structure_tk_k = b.kind("Lean.Parser.Command.structureTk");
    let class_tk_k = b.kind("Lean.Parser.Command.classTk");
    let tk = or_else([
        nd(structure_tk_k, sym("structure")),
        nd(class_tk_k, sym("class")),
    ]);
    let id = decl_id(b);
    let sig = opt_decl_sig(b);
    let ext = extends_clause(b);
    let ctor_p = struct_ctor(b);
    let fields = struct_fields(b);
    let deriv = opt_deriving(b);
    let k = b.kind("Lean.Parser.Command.structure");
    nd(
        k,
        seq([
            tk,
            id,
            sig,
            opt(ext),
            opt(seq([
                or_else([sym(":="), sym("where")]),
                opt(ctor_p),
                fields,
            ])),
            deriv,
        ]),
    )
}

/// The standalone `«deriving»` command (`Command.lean:286-287`) is the
/// keyword `"deriving "`, then an optional `"noncomputable "`, then
/// `"instance "`, then `derivingClasses`, then `" for "`, then a comma-
/// separated term list (`sepBy1 (recover termParser skip) ", "`) — the
/// STANDALONE command form (`deriving instance Foo for Bar`), distinct
/// from `optDeriving`/`optDefDeriving`'s trailing-clause use of the
/// same `derivingClasses` sub-grammar. `recover termParser skip`
/// simplified to plain `termParser` (same divergence as every other
/// `recover ..` site in this port).
fn deriving_cmd(b: &mut SnapshotBuilder) {
    let classes = deriving_classes(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.deriving",
        MAX_PREC,
        seq([
            sym("deriving"),
            opt(sym("noncomputable")),
            sym("instance"),
            classes,
            sym("for"),
            sep_by1(cat("term", 0), ","),
        ]),
    );
}

/// `declaration := leading_parser declModifiers false >> («abbrev» <|>
/// definition <|> «theorem» <|> «opaque» <|> «instance» <|> «axiom» <|>
/// «example» <|> «inductive» <|> «coinductive» <|> classInductive <|>
/// «structure»)` (`Command.lean:282-285`) — THE fixture-critical row;
/// every alternative below is a plain, unattributed `def` combined
/// via `<|>` inside this ONE `@[builtin_command_parser]` row's body
/// (only `declaration` itself needs registering into the category —
/// same "one row, many internal alternatives" shape the surface table
/// documents).
pub fn register(b: &mut SnapshotBuilder) {
    let modifiers = decl_modifiers(b);
    let alts = or_else([
        abbrev(b),
        definition(b),
        theorem(b),
        opaque(b),
        instance_decl(b),
        axiom_decl(b),
        example_decl(b),
        inductive_like(b, "Lean.Parser.Command.inductive", "inductive"),
        inductive_like(b, "Lean.Parser.Command.coinductive", "coinductive"),
        class_inductive(b),
        structure_like(b),
    ]);
    b.leading2(
        "command",
        "Lean.Parser.Command.declaration",
        MAX_PREC,
        seq([modifiers, alts]),
    );
    deriving_cmd(b);
}
