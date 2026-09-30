//! Term-level postponement, the PRODUCER side. Oracle:
//! `Lean/Elab/Term/TermElabM.lean`'s `tryPostpone` family
//! (`:1369-1387`) and `postponeElabTermCore` (`:1449-1453`).
//!
//! The three places postponement lives:
//! - here: the producers, and `postpone_elab_term`, which turns a term
//!   into a `.postponed` synthetic mvar;
//! - `elab.rs`'s `elab_using_elab_fns`: the catch
//!   (`elabUsingElabFnsAux`, `:1615-1661`);
//! - `synthetic/ladder.rs`'s `resume_postponed`: the resume
//!   (`resumePostponed`, `SyntheticMVars.lean:32-73`).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_meta::MVarKind;

use crate::dispatch::SynElem;
use crate::elab::{TermElabM, TermTarget};
use crate::error::ElabError;
use crate::synthetic::SyntheticMVarKind;

impl<'e> TermElabM<'e> {
    /// oracle: `tryPostpone` (`TermElabM.lean:1370-1372`).
    pub fn try_postpone(&self) -> Result<(), ElabError> {
        if self.may_postpone {
            Err(ElabError::Postpone)
        } else {
            Ok(())
        }
    }

    /// oracle: `isMVarApp` (`TermElabM.lean:1375-1376`) —
    /// `(← whnfR e).getAppFn.isMVar`. `whnf_r` both unfolds reducible
    /// heads (`outParam ?m` is `?m`) and instantiates an assigned head
    /// mvar, so this is exact, not the instantiate-then-spine-walk
    /// approximation P1 carried.
    pub fn is_mvar_app(&mut self, e: ExprId) -> Result<bool, ElabError> {
        let r = self.mctx.whnf_r(e)?;
        let base = self.view.store;
        let mut cur = r;
        while let Node::App { f, .. } = self.mctx.store().expr_node(Some(base), cur) {
            cur = f;
        }
        Ok(matches!(
            self.mctx.store().expr_node(Some(base), cur),
            Node::MVar { .. }
        ))
    }

    /// oracle: `tryPostponeIfMVar` (`TermElabM.lean:1379-1381`).
    pub fn try_postpone_if_mvar(&mut self, e: ExprId) -> Result<(), ElabError> {
        if self.is_mvar_app(e)? {
            self.try_postpone()?;
        }
        Ok(())
    }

    /// oracle: `tryPostponeIfNoneOrMVar` (`TermElabM.lean:1384-1387`).
    /// The spec's P2 surface; its first production caller is P4's
    /// `resolveDottedIdentFn` (`App.lean:1988`).
    pub fn try_postpone_if_none_or_mvar(&mut self, e: Option<ExprId>) -> Result<(), ElabError> {
        match e {
            Some(e) => self.try_postpone_if_mvar(e),
            None => self.try_postpone(),
        }
    }

    /// oracle: `postponeElabTermCore` (`TermElabM.lean:1449-1453`), also
    /// `postponeElabTerm` (`:1608-1610`), whose only addition is the
    /// info-tree context (UI-only, not ported).
    ///
    /// `mkFreshExprMVar expectedType? .syntheticOpaque`: opaque, so no
    /// `is_def_eq` can assign it — only `resume_postponed` does, through
    /// a direct `assign`. With no expected type the mvar's type is a
    /// fresh type mvar (`mkFreshExprMVarImpl`'s `none` arm,
    /// `Meta/Basic.lean:872-875`).
    pub fn postpone_elab_term(
        &mut self,
        stx: &SynElem,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        self.postpone_elab_target(&TermTarget::Stx(stx.clone()), expected)
    }

    /// `postpone_elab_term` over a [`TermTarget`]: a postponed flatten
    /// tail records its start in `tail_from`, so the resume re-enters the
    /// tail and not the whole `⟨…⟩` (`synthetic/ladder.rs`'s
    /// `resume_postponed`).
    pub(crate) fn postpone_elab_target(
        &mut self,
        target: &TermTarget,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        let ty = match expected {
            Some(t) => t,
            None => self.mk_fresh_type_mvar()?,
        };
        let (mvar, mvar_id) = self.mk_fresh_expr_mvar_of_kind(ty, MVarKind::SyntheticOpaque)?;
        let ctx = self.save_context();
        self.register_synthetic_mvar(
            target.ref_elem(),
            mvar_id,
            SyntheticMVarKind::Postponed {
                ctx,
                tail_from: target.tail_from(),
            },
        );
        Ok(mvar)
    }
}
