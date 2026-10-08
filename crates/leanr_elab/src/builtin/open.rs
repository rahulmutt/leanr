//! Term-level `open … in` (oracle `elabOpen`, `BuiltinTerm.lean:400-408`).
//!
//! The opened declarations scope the body only: they are installed in
//! `TermElabM::resolve` for the body's elaboration and the previous list
//! comes back on both paths (the oracle's `withTheReader Core.Context`).
//! A term the body postpones resumes with them, because `save_context`
//! records `resolve.open_decls` (oracle `SavedContext.openDecls`,
//! `TermElabM.lean:49`). `pushScope`/`popScope` only touch scoped
//! environment extensions, which leanr does not model: inert.

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

use crate::command::scope::{elab_open_decl, node, OpenState};
use crate::dispatch::non_trivia_children;
use crate::elab::TermElabM;
use crate::error::ElabError;

/// `[<atom> "open", openDecl, <atom> "in", term]`. `elabOpenDecl` starts
/// from the current namespace and open declarations, so command-level
/// `open`s and enclosing `open … in`s stay visible.
pub(crate) fn elab_open(
    elab: &mut TermElabM,
    stx: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let ch = non_trivia_children(stx);
    let decl = node(ch.get(1), "openDecl")?;
    let body = ch
        .get(3)
        .ok_or_else(|| ElabError::Internal("`open … in` without a body".into()))?;
    let open_decls = {
        let tables = elab.resolve.tables;
        let view = elab.view;
        let mut s = OpenState {
            st: elab.mctx.store_mut(),
            view,
            tables,
            ns: elab.resolve.ns,
            open_decls: elab.resolve.open_decls.to_vec(),
            main_module: elab.resolve.main_module,
        };
        elab_open_decl(&mut s, &decl, kinds)?;
        s.open_decls
    };
    let prev = std::mem::replace(&mut elab.resolve.open_decls, open_decls.into());
    let out = elab.elab_term(body, kinds, expected);
    elab.resolve.open_decls = prev;
    out
}
