//! `TermElabM`: the leaf-term elaborator's own state, layered directly
//! over `leanr_meta::MetaCtx`. Independent of any single parse — the
//! `KindInterner` is passed to `elab_term`, never stored, so one
//! `TermElabM` can elaborate nodes drawn from different snapshots.

use leanr_kernel::bank::{ExprId, NameId};
use leanr_meta::MetaCtx;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

use crate::dispatch;
use crate::error::ElabError;

pub struct TermElabM<'e> {
    pub mctx: MetaCtx<'e>,
    /// Universe parameters in scope, for `Sort u`. Empty for closed leaf
    /// terms; the field exists because `sort` reads it.
    pub level_names: Vec<NameId>,
}

impl<'e> TermElabM<'e> {
    pub fn new(mctx: MetaCtx<'e>) -> Self {
        TermElabM {
            mctx,
            level_names: Vec::new(),
        }
    }

    pub fn elab_term(
        &mut self,
        node: &SyntaxNode,
        kinds: &KindInterner,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        dispatch::dispatch(self, node, kinds, expected)
    }

    pub fn elab_term_ensuring_type(
        &mut self,
        node: &SyntaxNode,
        kinds: &KindInterner,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        let e = self.elab_term(node, kinds, expected)?;
        if let Some(t) = expected {
            let inferred = self.mctx.infer_type(e)?;
            if !self.mctx.is_def_eq(inferred, t)? {
                return Err(ElabError::TypeMismatch {
                    expected: t,
                    got: inferred,
                });
            }
        }
        Ok(e)
    }
}
