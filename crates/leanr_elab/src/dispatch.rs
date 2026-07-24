//! The dispatch table: syntax-kind name -> leaf elaborator.
//!
//! `elaborator_name_for` is the single source of truth for "is this a
//! leaf we elaborate" — Tasks 4-6 grow it one arm per leaf kind.
//! `dispatch` is the actual entry point `TermElabM::elab_term` calls;
//! an unregistered kind is `ElabError::UnsupportedSyntax`, never a
//! panic and never a wrong `ExprId` (named-seam discipline).
//!
//! **`SynElem`, not `SyntaxNode`** (Task 5 reconciliation): a leaf term
//! is not always a rowan NODE. `leanr_syntax`'s own grammar
//! (`builtin/term.rs`) registers a bare identifier as
//! `b.leading_raw("term", Prim::Ident)` — `Prim::Ident`'s own run arm
//! (`parse.rs`) is a plain `self.bump(t, KIND_IDENT)`, an unwrapped
//! leaf token with NO enclosing `start`/`finish` node pair (unlike
//! `str`/`num`/`char`, whose `Prim::StrLit`/etc go through `self.lit`,
//! which DOES wrap). Empirically confirmed (a throwaway probe test,
//! `cargo test -p leanr_elab --test zzscratch_probe -- --nocapture`,
//! never landed): parsing the term `"Nat"` produces a `KIND_NULL` root
//! whose ONLY child is a rowan TOKEN of kind `KIND_IDENT` (interned
//! name `"<ident>"`, not `"ident"` — `KindInterner::new`'s fixed-slot
//! list) — `root.first_child()` (node-only) finds nothing, so a term
//! position genuinely needs `SyntaxNode` OR `SyntaxToken` depending on
//! which leaf kind landed there. `SynElem` (`rowan::NodeOrToken`,
//! `leanr_syntax::tree`'s own re-export) is the minimal type that
//! covers both without forcing every existing Node-shaped leaf (`str`,
//! and Task 6's `sort`/hole) through a token-shaped API.

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::{is_trivia, KindInterner};
use leanr_syntax::tree::{NodeOrToken, SyntaxNode, SyntaxToken};

use crate::elab::TermElabM;
use crate::error::ElabError;

/// A term-syntax leaf position: a rowan NODE (`str`, and Task 6's
/// `sort`/`hole`/ascription — every kind that goes through `self.lit`
/// or a `leading2`/`nd`-style node wrap) or a rowan TOKEN (`ident` —
/// the one bare-leaf-token kind so far; see this module's doc comment).
pub type SynElem = NodeOrToken<SyntaxNode, SyntaxToken>;

/// Every syntactically-meaningful (non-trivia) child of `node`, in
/// source order. Task 6's multi-child leaves (`sort`/`type`'s optional
/// level argument, `paren`/`typeAscription`'s inner term(s)) all need
/// to navigate by POSITION, which the raw `children_with_tokens()`
/// stream doesn't support directly — it interleaves real syntax with
/// whitespace/comment trivia tokens (`is_trivia`, `leanr_syntax::kind`).
/// This is the leanr-tree equivalent of Lean's own `Syntax.getArg`/
/// `stx[i]`, which indexes into an ALREADY-trivia-stripped `Array
/// Syntax` (a `Syntax.node`'s `args` field never carries whitespace —
/// that lives only in each leaf's own `SourceInfo`), not a new
/// convention invented here.
pub(crate) fn non_trivia_children(node: &SyntaxNode) -> Vec<SynElem> {
    node.children_with_tokens()
        .filter(|el| !is_trivia(el.kind()))
        .collect()
}

/// The registered leaf kinds. Returns a stable label for a registered
/// kind, `None` otherwise. Grown by Tasks 4-6, now complete for M4b-1
/// slice 1. Keyed on the kind's INTERNED name — `"<ident>"` for a bare
/// identifier (`KindInterner`'s fixed-slot name, not the string
/// `"ident"` a dynamically-interned node kind would have; see this
/// module's doc comment), `"str"` for a string literal (a real
/// `leading2`/`self.lit`-wrapped node kind), and Task 6's five
/// `Lean.Parser.Term.*` kinds (all real `leading2`-wrapped nodes,
/// confirmed against a fresh parse dump — see `builtin::ascription`'s
/// module doc for the `paren`/`typeAscription` shape correction).
pub fn elaborator_name_for(kind: &str) -> Option<&'static str> {
    match kind {
        "str" => Some("str"),
        "<ident>" => Some("ident"),
        "Lean.Parser.Term.prop" => Some("prop"),
        "Lean.Parser.Term.type" => Some("type"),
        "Lean.Parser.Term.sort" => Some("sort"),
        "Lean.Parser.Term.paren" => Some("paren"),
        "Lean.Parser.Term.typeAscription" => Some("typeAscription"),
        "Lean.Parser.Term.hole" => Some("hole"),
        "Lean.Parser.Term.arrow" => Some("arrow"),
        "Lean.Parser.Term.forall" => Some("forall"),
        "Lean.Parser.Term.depArrow" => Some("depArrow"),
        _ => None,
    }
}

/// Dispatch a term position to its leaf elaborator. Unregistered kind ->
/// UnsupportedSyntax (never a panic, never a wrong ExprId). A kind
/// registered above but arriving as the "wrong" `SynElem` variant (e.g.
/// `"str"`'s name matching on a bare TOKEN) is unreachable in practice —
/// `leanr_syntax`'s own grammar wraps `str/num/char` as nodes and
/// `ident` as a token, always the same way — but is still routed to
/// `UnsupportedSyntax` rather than panicking, per this crate's
/// never-panic-on-a-named-seam discipline.
///
/// Named-seam audit (Task 7): both `match` blocks that read a kind name
/// in this crate — this one, and `builtin::sort::elab_level`'s nested
/// dispatch over `Lean.Parser.Level.*` kinds — end in a catch-all `(other,
/// _) => Err(ElabError::UnsupportedSyntax(other.to_string()))` arm. There
/// is no third place in `leanr_elab` that pattern-matches on a kind name
/// (`resolve.rs`'s `resolve_global` never inspects syntax at all), so
/// every non-leaf term/level kind that reaches either dispatch point is
/// named, never silently skipped or defaulted.
///
/// Deferred (each hits `UnsupportedSyntax` until its slice lands):
/// ```text
///   binders (fun/forall/let/have/show) ......... M4b-2 (in progress; arrow landed)
///   application, @, named/optional args ........ M4b-3
///   num / char literals (OfNat / Char.ofNat) ... M4b-3
///   coercions (mkCoe) .......................... M4b-3
///   elabAsElim, dot-notation, binop%, ⟨⟩ ....... M4b-4
///   macro expansion in dispatch ................ first macro-form slice
///   open / alias / export / _root_ resolution .. later slice
/// ```
/// (`Lean.Parser.Level.max`/`.imax`/`.paren`/`.addLit`, the level-scope
/// analogue of the above, are named seams inside `elab_level` itself —
/// see `builtin::sort`'s own module doc — rather than this table, since
/// they are not term-position kinds `dispatch` ever sees directly.)
pub fn dispatch(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let name = kinds.name(elem.kind());
    match (name, elem) {
        ("str", NodeOrToken::Node(node)) => crate::builtin::lit::elab_str(elab, node, kinds),
        ("<ident>", NodeOrToken::Token(tok)) => crate::builtin::ident::elab_ident(elab, tok, kinds),
        ("Lean.Parser.Term.prop", NodeOrToken::Node(node)) => {
            crate::builtin::sort::elab_prop(elab, node, kinds)
        }
        ("Lean.Parser.Term.type", NodeOrToken::Node(node)) => {
            crate::builtin::sort::elab_type(elab, node, kinds)
        }
        ("Lean.Parser.Term.sort", NodeOrToken::Node(node)) => {
            crate::builtin::sort::elab_sort(elab, node, kinds)
        }
        ("Lean.Parser.Term.paren", NodeOrToken::Node(node)) => {
            crate::builtin::ascription::elab_paren(elab, node, kinds, expected)
        }
        ("Lean.Parser.Term.typeAscription", NodeOrToken::Node(node)) => {
            crate::builtin::ascription::elab_ascription(elab, node, kinds, expected)
        }
        ("Lean.Parser.Term.hole", NodeOrToken::Node(node)) => {
            crate::builtin::hole::elab_hole(elab, node, kinds, expected)
        }
        ("Lean.Parser.Term.arrow", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_arrow(elab, node, kinds)
        }
        ("Lean.Parser.Term.forall", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_forall(elab, node, kinds)
        }
        ("Lean.Parser.Term.depArrow", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_dep_arrow(elab, node, kinds)
        }
        (other, _) => Err(ElabError::UnsupportedSyntax(other.to_string())),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn unregistered_kind_is_unsupported() {
        // A synthetic node of an unknown kind must dispatch to
        // UnsupportedSyntax carrying the kind name — never a panic,
        // never a wrong ExprId.
        let name = crate::dispatch::elaborator_name_for("Lean.Parser.Term.match");
        assert!(
            name.is_none(),
            "match is not a leaf and must not be registered"
        );
    }
}
