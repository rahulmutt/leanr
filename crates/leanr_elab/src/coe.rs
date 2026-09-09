//! oracle: `mkCoe` (`Lean/Elab/Term/TermElabM.lean:1294-1322`),
//! `ensureHasType` (`:1334-1340`), `ensureType` (`:1935-1949`, task 9)
//! and the `.coe` arm of `synthesizeSyntheticMVar`
//! (`Lean/Elab/SyntheticMVars.lean:545-560`) — the elaborator half of
//! M4b-3 P4. The Meta half is `leanr_meta::coe` (`Lean/Meta/Coe.lean`).
//!
//! Dropped, with no term impact: `withTraceNode`, `pushInfoLeaf`'s
//! `CoeExpansionTrace`, `withoutMacroStackAtErr`, and the
//! `errorMsgHeader?`/`mkErrorMsg?`/`mkImmedErrorMsg?`/`f?` message
//! payloads (leanr defers the prose layer, design spec § Amendment item 2).

use leanr_kernel::bank::ExprId;
use leanr_meta::{LOption, MVarId, MVarKind, MetaError, TransparencyMode};

use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::synthetic::state::SyntheticMVarKind;

impl<'e> TermElabM<'e> {
    /// oracle: `mkCoe` (`TermElabM.lean:1294-1322`) — `coerceCollectingNames?`;
    /// `.some eNew` is the answer (`:1301-1306`); `.none` is `failure`,
    /// caught into `throwTypeMismatchError` (`:1307`, `:1322`); `.undef`
    /// mints a `syntheticOpaque` mvar of the expected type and registers
    /// it as `.coe` (`:1308-1311`). A `MetaM` error inside the coercion
    /// (`Coe.lean`'s post-expansion throws, `MetaError::CoeExpansionMismatch`)
    /// is caught into the same `throwTypeMismatchError` (`:1313-1317`),
    /// so it lands as `TypeMismatch` here too. The monad-lift guard's
    /// `MetaError::Unsupported` is NOT caught: it is a named seam and
    /// surfaces as `UnsupportedSyntax` (design spec § Amendment 5 item 6).
    pub fn mk_coe(
        &mut self,
        stx: &SynElem,
        expected: ExprId,
        e: ExprId,
    ) -> Result<ExprId, ElabError> {
        match self.mctx.coerce(e, expected) {
            Ok(LOption::Some(new_e)) => Ok(new_e),
            Ok(LOption::None) | Err(MetaError::CoeExpansionMismatch(_)) => {
                let got = self.mctx.infer_type(e)?;
                Err(ElabError::TypeMismatch { expected, got })
            }
            Ok(LOption::Undef) => {
                let (mvar, id) =
                    self.mk_fresh_expr_mvar_of_kind(expected, MVarKind::SyntheticOpaque)?;
                self.register_synthetic_mvar(
                    stx.clone(),
                    id,
                    SyntheticMVarKind::Coe {
                        expected_type: expected,
                        e,
                    },
                );
                Ok(mvar)
            }
            Err(MetaError::Unsupported(m)) => Err(ElabError::UnsupportedSyntax(m)),
            Err(err) => Err(ElabError::from(err)),
        }
    }

    /// oracle: `ensureHasType` (`TermElabM.lean:1334-1340`) — `none`
    /// expected type returns `e`; otherwise `isDefEq (← inferType e)
    /// expectedType` or `mkCoe`. Replaces the M4b-1 posture (error on a
    /// defeq mismatch) at every site that used to open-code it:
    /// `elab_term_ensuring_type`, the `($e :)` ascription arm, and
    /// `elab_and_add_new_arg` (`ensureArgType`, `App.lean:54-62`).
    pub fn ensure_has_type(
        &mut self,
        stx: &SynElem,
        expected: Option<ExprId>,
        e: ExprId,
    ) -> Result<ExprId, ElabError> {
        let Some(expected) = expected else {
            return Ok(e);
        };
        let e_type = self.mctx.infer_type(e)?;
        if self.mctx.is_def_eq(e_type, expected)? {
            return Ok(e);
        }
        self.mk_coe(stx, expected, e)
    }

    /// oracle: the `.coe` arm of `synthesizeSyntheticMVar`
    /// (`SyntheticMVars.lean:545-560`). First, under `withDefault`,
    /// `isDefEq (← inferType e) expectedType` — "types may be defeq now
    /// due to mvar assignments, type class defaulting, etc." — and, if
    /// the occurs check passes, assign `e` ITSELF (`:546-551`; no
    /// search, no expansion). Otherwise `coerceCollectingNames?`; on
    /// `.some coerced` with a passing occurs check, assign it (`:552-558`).
    /// Else `false`: not ready yet (`:559`). `check_occurs` answers `true`
    /// when the mvar does NOT occur — the oracle's `occursCheck` polarity
    /// (see its doc at `leanr_meta::MetaCtx::check_occurs`).
    ///
    /// The `inferType` is INSIDE the `withDefault` scope, as `:546`
    /// writes it (`withDefault do isDefEq (← inferType e) expectedType`);
    /// `infer_type` reduces, so the scope is not decorative. The oracle's
    /// own `mvarId.withContext` (`:545`) is the ladder's wrapper around
    /// every arm (`ladder.rs::with_mvar_local_context`), not this
    /// function's job.
    ///
    /// Unlike `mk_coe`, this arm does NOT re-label a post-expansion
    /// throw: `:552` calls `coerceCollectingNames?` bare, with no `try`
    /// around it, so `MetaError::CoeExpansionMismatch` propagates as
    /// itself through `ElabError::Meta`. `mkCoe`'s `try` (`:1313-1317`)
    /// is what makes `TypeMismatch` the answer THERE, and nowhere else.
    pub(crate) fn synthesize_coe_mvar(
        &mut self,
        mvar_id: MVarId,
        expected: ExprId,
        e: ExprId,
    ) -> Result<bool, ElabError> {
        let defeq = self
            .mctx
            .with_transparency(TransparencyMode::Default, |m| {
                let e_type = m.infer_type(e)?;
                m.is_def_eq(e_type, expected)
            })?;
        if defeq && self.mctx.check_occurs(mvar_id, e)? {
            self.mctx.mctx_mut().assign(mvar_id, e)?;
            return Ok(true);
        }
        match self.mctx.coerce(e, expected) {
            Ok(LOption::Some(coerced)) => {
                if self.mctx.check_occurs(mvar_id, coerced)? {
                    self.mctx.mctx_mut().assign(mvar_id, coerced)?;
                    return Ok(true);
                }
                Ok(false)
            }
            Ok(LOption::None) | Ok(LOption::Undef) => Ok(false),
            // The oracle has no `try` here (`:552`, unlike `mkCoe`'s
            // `:1313`): a post-expansion throw propagates as the
            // elaboration error it is, NOT as a `TypeMismatch`.
            Err(err @ MetaError::CoeExpansionMismatch(_)) => Err(ElabError::from(err)),
            Err(MetaError::Unsupported(m)) => Err(ElabError::UnsupportedSyntax(m)),
            Err(err) => Err(ElabError::from(err)),
        }
    }
}
