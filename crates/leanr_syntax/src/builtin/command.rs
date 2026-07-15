//! The `command` category (M3a Task 10 — surface table's largest
//! category, 52 `port`-status rows + the module header). ORACLE-PORT
//! `Lean/Parser/Command.lean` (authority over the task brief's inline
//! sketch — see the module-doc comments of the split-out files below
//! for the per-area citations) + `Lean/Parser/Module/Syntax.lean`
//! (header, unchanged since Task 7).
//!
//! Split by grammar area (module-size discipline — this category alone
//! is 52 rows, the plan's largest porting surface):
//! - `command.rs` (this file): module header (Task 7, untouched),
//!   `docComment`/`declModifiers` (shared by every other file here),
//!   and the top-level `register` dispatcher.
//! - `command_decl.rs`: the `declaration` dispatcher and its whole
//!   `definition`/`theorem`/`instance`/…/`structure` family.
//! - `command_open.rs`: `namespace`/`section`/`end`/`open` (all 5
//!   sub-forms)/`«in»`/`mutual`/`variable`/`universe`/`set_option`/
//!   `attribute`/`export`/`import`/`include`/`omit`.
//! - `command_misc.rs`: `moduleDoc` + every `#`-prefixed
//!   introspection command + the small bootstrapping/registration
//!   commands (`init_quot`, `grindPattern`, …).
//!
//! Kind names are byte-for-byte from the surface table's "kind name"
//! column with escaping guillemets STRIPPED — confirmed against every
//! fresh oracle dump this task ran (e.g. source declares `def
//! «private»`, but a live dump's node kind is the bare
//! `"Lean.Parser.Command.private"`, matching every prior task's own
//! established convention (`term.rs`'s `Lean.Parser.Term.sorry`, not
//! `«sorry»`)).

mod command_decl;
mod command_misc;
mod command_notation;
mod command_open;

// Re-exported (Task 10) so `term.rs`'s `Term.«open»`/`Term.«set_option»`
// and `tactic.rs`'s `Tactic.«open»`/`Tactic.«set_option»` (the 4
// `... in <term|tactic>` wrapper rows — a DIFFERENT production per
// category, but sharing the identical `Command.openDecl`/
// `Command.optionValue` sub-grammar the command-category `«open»`/
// `«set_option»` also use) can reuse the exact same shapes without a
// second, drifting copy — same "hoist, re-export" idiom `term.rs`
// already established for `term_pragma::{match_expr_alts,
// match_expr_pat}`. `command_open` itself stays a private submodule;
// only these two names are threaded through.
pub(super) use command_open::{open_decl, option_value};

use crate::grammar::*;
use crate::kind::SyntaxKind;
use std::sync::Arc;

/// `Prim::Node` with no prec gate — the sub-node shape every compound
/// production uses (shared by every file in this module).
pub(super) fn nd(kind: SyntaxKind, body: Prim) -> Prim {
    Prim::Node {
        kind,
        prec: None,
        body: Arc::new(body),
    }
}

/// `identWithPartialTrailingDot` (`Extra.lean`): `ident >> optional
/// (checkNoWsBefore >> "." >> checkNoWsBefore >> ident)` — a plain
/// `Parser` sequence (no `leading_parser` of its own), so it contributes
/// a bare ident leaf plus a null, never a node. Shared by the module
/// header's own `import` (Task 7), `«end»`'s optional trailing label,
/// and `«set_option»`'s option name.
pub(super) fn ident_with_partial_trailing_dot() -> Prim {
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

/// `Termination.suffix := optional (ppDedent ppLine >> (terminationBy?
/// <|> terminationBy <|> partialFixpoint <|> coinductiveFixpoint <|>
/// inductiveFixpoint)) >> optional decreasingBy` (`Term.lean:707-708` —
/// despite the name, lives in the `Termination` namespace, needed
/// wherever a declaration body can end, hence `let rec`'s own use in
/// `term.rs`). None of the 5 `terminationBy`-family alternatives or
/// `decreasingBy` are transcribed (no fixture uses `termination_by`/
/// `decreasing_by`) — both slots are real, always-empty optionals,
/// confirmed byte-for-byte against every fixture's own
/// `Lean.Parser.Termination.suffix{null{} null{}}` (task-10 report).
/// Shared by `command_decl.rs`'s `declValSimple` AND `term.rs`'s
/// `letRecDecl` (a single definition so both call sites can't drift —
/// this was Task 8/9's own precedent for `term_hole`/`synthetic_hole`).
pub(super) fn termination_suffix(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Termination.suffix");
    nd(k, seq([opt(never()), opt(never())]))
}

/// `Command.docComment := leading_parser ppDedent $ "/--" >> ppSpace >>
/// ifVerso versoCommentBody commentBody >> ppLine` (`Term.lean:91-92`,
/// despite the name living in the `Command` namespace) — `doc.verso`
/// defaults false, so every fixture takes the `commentBody` branch;
/// `ppDedent`/`ppSpace`/`ppLine` are pretty-print-only no-ops. See
/// `Prim::DocCommentBody`'s own doc comment for the fresh-dump citation
/// pinning the exact 2-child shape (`"/--"` atom, then the raw body
/// atom running through the closing `-/`).
pub(super) fn doc_comment(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.docComment");
    nd(k, seq([sym("/--"), Prim::DocCommentBody]))
}

/// `declModifiers (inline : Bool) := optional docComment >> optional
/// (Term.«attributes» >> ..) >> optional visibility >> optional
/// «protected» >> optional («meta» <|> «noncomputable») >> optional
/// «unsafe» >> optional («partial» <|> «nonrec»)` (Command.lean:114-121).
/// The `inline` parameter only toggles a `ppDedent ppLine` PRETTY-PRINT
/// hint after the attributes slot (whether `@[attr]` prints on its own
/// line) — no tree-shape difference between `declModifiers false`
/// (top-level declarations) and `nestedDeclModifiers`/`declModifiers
/// true` (ctors, structure binders, `computedField`) — confirmed
/// against fresh dumps of both call shapes (`Decls.lean`'s top-level
/// modifiers vs. `Types.lean`'s `structSimpleBinder`/`ctor` modifiers,
/// task-10 report): both are the identical 7-child
/// `Lean.Parser.Command.declModifiers` node. One shared fn, no `inline`
/// parameter, is therefore faithful, not a shortcut.
pub(super) fn decl_modifiers(b: &mut SnapshotBuilder) -> Prim {
    let doc = doc_comment(b);
    let attrs = super::attr::attributes(b);
    let private_k = b.kind("Lean.Parser.Command.private");
    let public_k = b.kind("Lean.Parser.Command.public");
    let visibility = or_else([nd(private_k, sym("private")), nd(public_k, sym("public"))]);
    let protected_k = b.kind("Lean.Parser.Command.protected");
    let meta_k = b.kind("Lean.Parser.Command.meta");
    let noncomputable_k = b.kind("Lean.Parser.Command.noncomputable");
    let unsafe_k = b.kind("Lean.Parser.Command.unsafe");
    let partial_k = b.kind("Lean.Parser.Command.partial");
    let nonrec_k = b.kind("Lean.Parser.Command.nonrec");
    let k = b.kind("Lean.Parser.Command.declModifiers");
    nd(
        k,
        seq([
            opt(doc),
            opt(attrs),
            opt(visibility),
            opt(nd(protected_k, sym("protected"))),
            opt(or_else([
                nd(meta_k, sym("meta")),
                nd(noncomputable_k, sym("noncomputable")),
            ])),
            opt(nd(unsafe_k, sym("unsafe"))),
            opt(or_else([
                nd(partial_k, sym("partial")),
                nd(nonrec_k, sym("nonrec")),
            ])),
        ]),
    )
}

/// `namedPrio := leading_parser atomic (" (" >> nonReservedSymbol
/// "priority") >> " := " >> withoutPosition priorityParser >> ")"` —
/// unattributed but `leading_parser` (self-wraps, same "named helper"
/// shape as `matchDiscr`); recurses into the `prio` category (`attr.rs`'s
/// `Priority.numPrio`). Hoisted here (M3b1 Task 2) from `command_decl.rs`
/// (its original sole consumer, `instance`'s `(priority := ..)` slot) so
/// `command_notation.rs`'s `notation`/mixfix-family `namedPrio` optional
/// can share the identical definition instead of a second, drifting copy
/// — same "hoist, re-export" idiom this file's own module doc already
/// uses for `command_open`'s `open_decl`/`option_value`. Confirmed
/// byte-identical shape at both call sites against a fresh oracle dump
/// of `instance (priority := 200) : ..` (task-10 report) and
/// `infixl:65 (name := .. ) (priority := 10) " ⊕⊕⊕ " => Sum3` (task-2
/// report).
pub(super) fn named_prio(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.namedPrio");
    nd(
        k,
        seq([
            atomic(seq([sym("("), Prim::NonReservedSymbol("priority".into())])),
            sym(":="),
            cat("prio", 0),
            sym(")"),
        ]),
    )
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
    b.set_header(nd(
        header_kind,
        seq([
            opt(nd(module_tk_kind, sym("module"))),
            opt(nd(prelude_kind, sym("prelude"))),
            many(nd(
                import_kind,
                seq([
                    // ORACLE-PORT: the oracle wraps
                    // `optional public >> optional meta >> "import"` in
                    // `atomic` (so a partial match backtracks cleanly);
                    // doesn't affect the success-path shape below.
                    atomic(seq([
                        opt(nd(public_kind, sym("public"))),
                        opt(nd(meta_kind, sym("meta"))),
                        sym("import"),
                    ])),
                    opt(nd(all_kind, sym("all"))),
                    // ORACLE-PORT `identWithPartialTrailingDot`
                    // (Extra.lean): a plain `Parser` sequence (no
                    // `leading_parser`), so it contributes a bare ident
                    // leaf plus a null, not a node of its own.
                    ident_with_partial_trailing_dot(),
                ]),
            )),
        ]),
    ));

    command_decl::register(b);
    command_open::register(b);
    command_misc::register(b);
    command_notation::register(b);
}

#[cfg(test)]
mod tests {
    use crate::builtin;
    use crate::parse_module;

    /// `recover_command`/`starts_command` regression (task-10 brief:
    /// "if your work makes `starts_command` correct/meaningful, verify
    /// it"). Before this task, `declaration` (`FirstTok::Any`, an
    /// all-optional `declModifiers` lead) was the ONLY leading command,
    /// so `starts_command` (which only matches `FirstTok::Sym` entries)
    /// was permanently inert — a bad command swept clean to EOF. Now
    /// that keyword-keyed commands (`namespace`, `#check`, …) are
    /// registered, an unrecognized token run must resync at the very
    /// next one instead of consuming the rest of the file.
    #[test]
    fn recover_command_resyncs_at_the_next_keyword_command_not_eof() {
        let snap = builtin::snapshot();
        // `%%%` isn't a command-category leading token at all (nor a
        // valid term/binder/etc. — a "just garbage" run), followed by a
        // real, keyword-led command (`namespace`) that recovery should
        // resync on rather than swallow.
        let src = "prelude\n\n%%%\nnamespace Foo\nend Foo\n";
        let result = parse_module(src, &snap);

        // Total: never panics/hangs, always round-trips byte-exact,
        // errors included.
        assert_eq!(result.tree.text(), src, "round-trip failed");
        assert_eq!(
            result.errors.len(),
            1,
            "expected exactly one recovery diagnostic, got {:?}",
            result.errors
        );
        assert_eq!(result.errors[0].code, "E0301");

        let out = crate::canon::canon_jsonl(&result.tree);
        // The recovered `namespace Foo`/`end Foo` commands must show up
        // as REAL, correctly-kinded nodes — not swallowed into the
        // error-recovery sweep (which the pre-Task-10 `FirstTok::Any`-
        // only dispatch table would have done, sweeping straight to
        // EOF instead of stopping at `namespace`).
        assert!(
            out.contains(r#""k":"Lean.Parser.Command.namespace""#),
            "{out}"
        );
        assert!(out.contains(r#""k":"Lean.Parser.Command.end""#), "{out}");
        assert!(out.contains(r#""k":"<error>""#), "{out}");
    }

    /// The standalone `«deriving»` command (`Lean.Parser.Command.
    /// deriving`) + a NON-empty `optDeriving`/`derivingClass` slot — no
    /// committed fixture exercises either (`Types.lean`'s `optDeriving`
    /// is always the empty-`null` case); coverage lives here instead.
    /// Shape confirmed against a fresh oracle dump of `structure Foo
    /// where x : Nat` followed by `deriving instance Repr for Foo`
    /// (task-10 report).
    #[test]
    fn deriving_command_and_a_populated_deriving_clause_parse_clean() {
        let snap = builtin::snapshot();
        let src = "prelude\n\nstructure Foo where\n  x : Nat\n  deriving Repr\n\nderiving instance Repr for Foo\n";
        let result = parse_module(src, &snap);
        assert!(
            result.errors.is_empty(),
            "expected clean parse, got {:?}",
            result.errors
        );
        assert_eq!(result.tree.text(), src, "round-trip failed");

        let out = crate::canon::canon_jsonl(&result.tree);
        assert!(
            out.contains(r#""k":"Lean.Parser.Command.derivingClass""#),
            "{out}"
        );
        assert!(
            out.contains(r#""k":"Lean.Parser.Command.deriving""#),
            "{out}"
        );
    }

    /// `initialize`/`builtin_initialize` + `attribute [-simp] ..`'s
    /// `eraseAttr` + `instance (priority := ..)`'s `namedPrio` — none
    /// exercised by a committed fixture. Also the two self-wrap bugs a
    /// fresh oracle dump caught this task (`eraseAttr`/
    /// `initializeKeyword` ARE `leading_parser`, a prior version of
    /// this file's own code missed both wraps — task-10 report has the
    /// probe transcripts).
    #[test]
    fn initialize_builtin_initialize_erase_attr_and_named_prio_parse_clean() {
        let snap = builtin::snapshot();
        let src = "prelude\n\ninitialize foo : Nat ← pure z\n\nbuiltin_initialize\n  pure z\n\nattribute [-simp] bar\n\ninstance (priority := 200) : Inhabited Nat where\n  default := z\n";
        let result = parse_module(src, &snap);
        assert!(
            result.errors.is_empty(),
            "expected clean parse, got {:?}",
            result.errors
        );
        assert_eq!(result.tree.text(), src, "round-trip failed");

        let out = crate::canon::canon_jsonl(&result.tree);
        assert!(
            out.contains(r#""k":"Lean.Parser.Command.initialize""#),
            "{out}"
        );
        assert!(
            out.contains(r#""k":"Lean.Parser.Command.initializeKeyword""#),
            "{out}"
        );
        assert!(out.contains(r#""a":"builtin_initialize""#), "{out}");
        assert!(
            out.contains(r#""k":"Lean.Parser.Command.eraseAttr""#),
            "{out}"
        );
        assert!(
            out.contains(r#""k":"Lean.Parser.Command.namedPrio""#),
            "{out}"
        );
    }
}
