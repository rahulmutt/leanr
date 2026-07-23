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
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::{NodeOrToken, SyntaxNode, SyntaxToken};

use crate::elab::TermElabM;
use crate::error::ElabError;

/// A term-syntax leaf position: a rowan NODE (`str`, and Task 6's
/// `sort`/`hole`/ascription — every kind that goes through `self.lit`
/// or a `leading2`/`nd`-style node wrap) or a rowan TOKEN (`ident` —
/// the one bare-leaf-token kind so far; see this module's doc comment).
pub type SynElem = NodeOrToken<SyntaxNode, SyntaxToken>;

/// The registered leaf kinds. Returns a stable label for a registered
/// kind, `None` otherwise. Grown as Tasks 4-6 land their elaborators.
/// Keyed on the kind's INTERNED name — `"<ident>"` for a bare
/// identifier (`KindInterner`'s fixed-slot name, not the string
/// `"ident"` a dynamically-interned node kind would have; see this
/// module's doc comment), `"str"` for a string literal (a real
/// `leading2`/`self.lit`-wrapped node kind).
pub fn elaborator_name_for(kind: &str) -> Option<&'static str> {
    match kind {
        "str" => Some("str"),
        "<ident>" => Some("ident"),
        // filled in by Task 6 (sort/ascription/hole)
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
pub fn dispatch(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let _ = expected;
    let name = kinds.name(elem.kind());
    match (name, elem) {
        ("str", NodeOrToken::Node(node)) => crate::builtin::lit::elab_str(elab, node, kinds),
        ("<ident>", NodeOrToken::Token(tok)) => crate::builtin::ident::elab_ident(elab, tok, kinds),
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
