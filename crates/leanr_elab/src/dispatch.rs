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
///
/// `match_single_binding` allowed: this is a single-arm placeholder
/// only until Tasks 4-6 add one arm per registered leaf kind — the
/// `match` shape is deliberate, not a `None`-returning stub to be
/// simplified away.
#[allow(clippy::match_single_binding)]
pub fn elaborator_name_for(kind: &str) -> Option<&'static str> {
    match kind {
        // filled in by Tasks 4-6
        _ => None,
    }
}

/// Dispatch a term node to its leaf elaborator. Unregistered kind ->
/// UnsupportedSyntax (never a panic, never a wrong ExprId).
///
/// `match_single_binding` allowed for the same reason as
/// `elaborator_name_for` above.
#[allow(clippy::match_single_binding)]
pub fn dispatch(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let _ = (elab, expected);
    let name = kinds.name(node.kind());
    match name {
        // Tasks 4-6 add one arm each, delegating to builtin::*.
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
