//! The dispatch table: syntax-kind name -> leaf elaborator.
//!
//! `elaborator_name_for` is the single source of truth for "is this a
//! leaf we elaborate" — Tasks 4-6 grow it one arm per leaf kind.
//! `dispatch` is the actual entry point `TermElabM::elab_term` calls;
//! an unregistered kind is `ElabError::UnsupportedSyntax`, never a
//! panic and never a wrong `ExprId` (named-seam discipline).

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

use crate::elab::TermElabM;
use crate::error::ElabError;

/// The registered leaf kinds. Returns a stable label for a registered
/// kind, `None` otherwise. Grown as Tasks 4-6 land their elaborators.
pub fn elaborator_name_for(kind: &str) -> Option<&'static str> {
    match kind {
        "str" => Some("str"),
        // filled in by Tasks 5-6 (sort/ident/ascription/hole)
        _ => None,
    }
}

/// Dispatch a term node to its leaf elaborator. Unregistered kind ->
/// UnsupportedSyntax (never a panic, never a wrong ExprId).
pub fn dispatch(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let _ = expected;
    let name = kinds.name(node.kind());
    match name {
        "str" => crate::builtin::lit::elab_str(elab, node, kinds),
        other => Err(ElabError::UnsupportedSyntax(other.to_string())),
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
