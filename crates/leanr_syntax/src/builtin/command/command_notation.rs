//! `notation`/`infixl`/`infixr`/`infix`/`prefix`/`postfix` command
//! SHAPES only (M3b1 Task 2 — pure M3a-style grammar-production
//! porting; no registration/overlay logic, no derivation, those are
//! M3b1 Tasks 3-7). ORACLE-PORT `Lean/Parser/Syntax.lean` (task brief's
//! `:92-105` citation for the surface these six commands live at in the
//! pinned toolchain).
//!
//! ORACLE DUMP (Step 1 — authority for every kind name/child order
//! below; scratch probe `_probe_notation.lean`/`_probe_notation{2,3,4}.
//! lean`, deleted before commit per Step 6, dumped via `tests/fixtures/
//! syntax/dump_syntax.lean` against the pinned `lean` at
//! `/home/dev/.elan/bin/lean`, toolchain v4.32.0-rc1):
//!
//! `infixl:65 " ⊕ " => Sum` →
//! ```text
//! {"k":"Lean.Parser.Command.mixfix","c":[
//!   {"k":"null","c":[]},                          // optional docComment
//!   {"k":"null","c":[]},                          // optional Term.attributes
//!   {"k":"Lean.Parser.Term.attrKind","c":[{"k":"null","c":[]}]},
//!   {"k":"Lean.Parser.Command.infixl","c":[{"a":"infixl"}]},  // mixfixKind
//!   {"k":"Lean.Parser.precedence","c":[{"a":":"},{"k":"num","c":[{"a":"65"}]}]},
//!   {"k":"null","c":[]},                          // optional namedName
//!   {"k":"null","c":[]},                          // optional namedPrio
//!   {"k":"str","c":[{"a":"\" ⊕ \""}]},
//!   {"a":"=>"},
//!   {"i":"Sum"}
//! ]}
//! ```
//! `infixr`/`infix`/`prefix`/`postfix` are BYTE-IDENTICAL in shape,
//! differing only in the `mixfixKind` alternative that matched
//! (`Lean.Parser.Command.infixr`/`.infix`/`.prefix`/`.postfix` — each
//! its own self-node-wrapping kind, confirmed against a fresh dump of
//! all five) — ALL FIVE share the ONE outer command kind
//! `Lean.Parser.Command.mixfix`, never a per-fixity outer kind (the
//! brief's sketch's "or the mixfix kind from dump" placeholder resolves
//! to this ONE shared kind). `infixl:65 (name := fooName) (priority :=
//! 10) " ⊕⊕⊕ " => Sum3` confirms `mixfix`'s own `namedName`/`namedPrio`
//! slots (untested by the 5-line probe above, which omits them) are
//! populated exactly like `instance (priority := ..)`'s own
//! `Lean.Parser.Command.namedPrio` (`command_decl.rs`, hoisted to
//! `command.rs` this task so both share ONE definition). Precedence is
//! MANDATORY for `mixfix` (not `optional`-wrapped): a fresh dump of
//! `infixl " ⊕ " => Sum` (no `:65`) truncates the whole `mixfix` node to
//! just 5 children, `[null, null, attrKind, infixl-node,
//! {"k":"Lean.Parser.precedence","c":[{"k":"<missing>"}]}]` — the parse
//! error aborts the rest of the production, confirming `precedence`
//! itself (not `optional precedence`) sits at that slot. A bare `"max"`/
//! `"min"` keyword in the precedence slot (`infixl:max ..`) is REJECTED
//! (dump shows `{"a":":"},{"k":"<missing>"}]` — the num literal itself
//! is mandatory, no `prec`-category keyword fallback at this call site)
//! — `precedence := ":" >> NumLit` is the whole shape, matching the
//! brief's `Prim::NumLit` sketch exactly, no `cat("prec", ..)` category
//! needed.
//!
//! `notation:70 a:71 " ⊗ " b:71 => Prod a b` →
//! ```text
//! {"k":"Lean.Parser.Command.notation","c":[
//!   {"k":"null","c":[]},                          // optional docComment
//!   {"k":"null","c":[]},                          // optional Term.attributes
//!   {"k":"Lean.Parser.Term.attrKind","c":[{"k":"null","c":[]}]},
//!   {"a":"notation"},                              // BARE atom (not node-wrapped
//!                                                   // — only one keyword, unlike mixfixKind)
//!   {"k":"null","c":[{"k":"Lean.Parser.precedence","c":[..]}]},  // optional precedence
//!   {"k":"null","c":[]},                          // optional namedName
//!   {"k":"null","c":[]},                          // optional namedPrio
//!   {"k":"null","c":[                             // many notationItem
//!     {"k":"Lean.Parser.Command.identPrec","c":[{"i":"a"},{"k":"null","c":[{prec}]}]},
//!     {"k":"str","c":[{"a":"\" ⊗ \""}]},
//!     {"k":"Lean.Parser.Command.identPrec","c":[{"i":"b"},{"k":"null","c":[{prec}]}]}
//!   ]},
//!   {"a":"=>"},
//!   {"k":"Lean.Parser.Term.app","c":[{"i":"Prod"},{"k":"null","c":[{"i":"a"},{"i":"b"}]}]}
//! ]}
//! ```
//! `notation "foo" => Foo` confirms `precedence` here IS `optional`
//! (bare `{"k":"null","c":[]}` when omitted — unlike `mixfix`'s
//! mandatory slot) and a bare string-literal `notationItem` is just a
//! `str` node directly, no `identPrec` wrap (`notationItem := strLit
//! <|> identPrec`). `notation (name := foo) (priority := 10) a " ⊗ " b
//! => ..` confirms `notation`'s own `namedName`/`namedPrio` optionals
//! sit at the SAME position as `mixfix`'s (same shared `Command.
//! namedName`/`Command.namedPrio` kinds). `identPrec := ident >>
//! optional precedence` (`Command.identPrec`, 2 children, the inner
//! `precedence` optional-wrapped exactly like the top-level slot).
//!
//! Malformed/edge cases (bare `notation:max ..`, missing `mixfix`
//! precedence) are NOT hardened here — Task 9 owns recovery, Task 2's
//! only job is the clean-parse shape for well-formed source (this
//! file's brief: "malformed source yields error nodes, never a panic";
//! the interpreter's existing `Optional`/`OrElse`/mandatory-child
//! failure handling already satisfies that with zero extra code here).

use crate::builtin::attr::{attr_kind, attributes};
use crate::builtin::command::{doc_comment, named_name, named_prio, nd, precedence};
use crate::grammar::*;

/// `optional docComment >> optional Term.«attributes» >> Term.attrKind`
/// — the 3-child prefix shared BYTE-FOR-BYTE by `mixfix` and `notation`
/// (confirmed identical in both oracle dumps above); NOT `declModifiers`
/// (that's a DIFFERENT, 7-child shape used by `declaration` — see
/// `command.rs`'s own `decl_modifiers`) despite the superficial
/// resemblance, so this gets its own small helper rather than reusing
/// that one.
fn notation_prefix(b: &mut SnapshotBuilder) -> Prim {
    let doc = doc_comment(b);
    let attrs = attributes(b);
    let ak = attr_kind(b);
    seq([opt(doc), opt(attrs), ak])
}

/// `Lean.Parser.Command.identPrec := ident >> optional precedence` —
/// `notation`'s per-binder item (`a:71`, `x`, …).
fn ident_prec(b: &mut SnapshotBuilder) -> Prim {
    let prec = precedence(b);
    let k = b.kind("Lean.Parser.Command.identPrec");
    nd(k, seq([Prim::Ident, opt(prec)]))
}

/// `notationItem := strLit <|> identPrec` — a bare notation symbol
/// (`" ⊗ "`) is a plain `str` leaf (`Prim::StrLit` self-wraps, same
/// "leaf, not `leading_parser`" shape as `Term.num`/`attr.rs`'s
/// `Priority.numPrio`), a bound argument (`a`, `a:71`) is `identPrec`.
fn notation_item(b: &mut SnapshotBuilder) -> Prim {
    let ip = ident_prec(b);
    or_else([Prim::StrLit, ip])
}

/// `mixfixKind := «infixl» <|> «infixr» <|> «infix» <|> «prefix» <|>
/// «postfix»` — each alternative is its own unattributed, self-
/// node-wrapping `leading_parser` (same shape as `command.rs`'s
/// `visibility`/`protected`/… `declModifiers` alternatives), letting
/// the ONE shared outer `Lean.Parser.Command.mixfix` kind record which
/// fixity keyword actually matched via this child's own kind name.
fn mixfix_kind(b: &mut SnapshotBuilder) -> Prim {
    let infixl_k = b.kind("Lean.Parser.Command.infixl");
    let infixr_k = b.kind("Lean.Parser.Command.infixr");
    let infix_k = b.kind("Lean.Parser.Command.infix");
    let prefix_k = b.kind("Lean.Parser.Command.prefix");
    let postfix_k = b.kind("Lean.Parser.Command.postfix");
    or_else([
        nd(infixl_k, sym("infixl")),
        nd(infixr_k, sym("infixr")),
        nd(infix_k, sym("infix")),
        nd(prefix_k, sym("prefix")),
        nd(postfix_k, sym("postfix")),
    ])
}

pub fn register(b: &mut SnapshotBuilder) {
    // `mixfix` (infixl/infixr/infix/prefix/postfix — ONE shared oracle
    // kind, see module doc): prefix, mixfixKind, MANDATORY precedence,
    // optional namedName/namedPrio, the single symbol string, `=>`,
    // term.
    let prefix = notation_prefix(b);
    let mk = mixfix_kind(b);
    let prec = precedence(b);
    let nn = opt(named_name(b));
    let np = opt(named_prio(b));
    b.leading2(
        "command",
        "Lean.Parser.Command.mixfix",
        MAX_PREC,
        seq([
            prefix,
            mk,
            prec,
            nn,
            np,
            Prim::StrLit,
            sym("=>"),
            cat("term", 0),
        ]),
    );

    // `notation`: prefix, bare `"notation"` keyword atom, OPTIONAL
    // precedence, optional namedName/namedPrio, many notationItem,
    // `=>`, term.
    let prefix = notation_prefix(b);
    let prec = opt(precedence(b));
    let nn = opt(named_name(b));
    let np = opt(named_prio(b));
    let item = notation_item(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.notation",
        MAX_PREC,
        seq([
            prefix,
            sym("notation"),
            prec,
            nn,
            np,
            many(item),
            sym("=>"),
            cat("term", 0),
        ]),
    );
}

#[cfg(test)]
mod tests {
    /// Step 2/3/5 of the task brief — RED before `register` wired the
    /// six commands into the `command` category (they landed in
    /// `recover_command`'s error-node sweep, `errors` non-empty), GREEN
    /// after (byte-exact round-trip, no diagnostics).
    #[test]
    fn notation_and_mixfix_round_trip_clean() {
        let snap = crate::builtin::snapshot();
        for src in [
            "prelude\ninfixl:65 \" ⊕ \" => Sum\n",
            "prelude\ninfixr:65 \" ⇒ \" => Arrow\n",
            "prelude\ninfix:65 \" ⊙ \" => Foo\n",
            "prelude\nprefix:100 \"~\" => Not\n",
            "prelude\npostfix:100 \"!\" => Fact\n",
            "prelude\nnotation:70 a \" ⊗ \" b => Prod a b\n",
        ] {
            let r = crate::parse_module(src, &snap);
            assert_eq!(r.tree.text(), src, "round-trip: {src:?}");
            assert!(
                r.errors.is_empty(),
                "should parse clean: {src:?} errs={:?}",
                r.errors
            );
        }
    }

    /// Regression guard for the `namedName`/`namedPrio` optional-slot
    /// ORDER (module doc's oracle dump: `namedName` — `(name := ..)` —
    /// sits BEFORE `namedPrio` — `(priority := ..)` — in both `mixfix`
    /// and `notation`'s child sequence). Both slots are `opt(...)`, so a
    /// swapped-order bug in `register` (line up `nn`/`np` after `np`/
    /// `nn`) would still round-trip byte-for-byte and parse clean on
    /// sources that only ever set ONE of the two — only a source setting
    /// BOTH, with a structural order assertion, would catch a swap. The
    /// two sources below are the module doc's own oracle-confirmed
    /// `(name := ..) (priority := ..)` probes (lines 36-38, 79-81 above),
    /// with the doc's `..`/`Sum3` term placeholders filled in with real
    /// terms so they're complete, parseable sources.
    #[test]
    fn notation_named_args_parse_clean_and_ordered() {
        let snap = crate::builtin::snapshot();
        for src in [
            "prelude\ninfixl:65 (name := fooName) (priority := 10) \" ⊕⊕⊕ \" => Sum3\n",
            "prelude\nnotation (name := foo) (priority := 10) a \" ⊗ \" b => Prod a b\n",
        ] {
            let r = crate::parse_module(src, &snap);
            assert_eq!(r.tree.text(), src, "round-trip: {src:?}");
            assert!(
                r.errors.is_empty(),
                "should parse clean: {src:?} errs={:?}",
                r.errors
            );

            let mut named_name_pos = None;
            let mut named_prio_pos = None;
            for (i, node) in r.tree.root().descendants().enumerate() {
                match r.tree.kinds.name(node.kind()) {
                    "Lean.Parser.Command.namedName" => named_name_pos = Some(i),
                    "Lean.Parser.Command.namedPrio" => named_prio_pos = Some(i),
                    _ => {}
                }
            }
            let named_name_pos =
                named_name_pos.unwrap_or_else(|| panic!("no namedName node in {src:?}"));
            let named_prio_pos =
                named_prio_pos.unwrap_or_else(|| panic!("no namedPrio node in {src:?}"));
            assert!(
                named_name_pos < named_prio_pos,
                "namedName ({named_name_pos}) should precede namedPrio ({named_prio_pos}) in {src:?}"
            );
        }
    }
}
