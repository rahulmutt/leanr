//! oracle: `mkCoe` (`Lean/Elab/Term/TermElabM.lean:1294-1322`),
//! `ensureHasType` (`:1334-1340`), `ensureType` (`:1935-1949`, task 9)
//! and the `.coe` arm of `synthesizeSyntheticMVar`
//! (`Lean/Elab/SyntheticMVars.lean:545-560`) — the elaborator half of
//! M4b-3 P4. The Meta half is `leanr_meta::coe` (`Lean/Meta/Coe.lean`).
//!
//! **Where the rest of the slice lives, and the rule that puts it
//! there.** This module is organised TOPIC-BY-ORACLE-FUNCTION: a
//! standalone `TermElabM` function of the oracle's gets its body here.
//! An ARM of a `match` lives with its DISPATCH instead, next to the
//! sibling arms it is chosen among — so P4's two `.coe` arms are not
//! both here:
//!
//! - the SCHEDULING arm, `synthesizeSyntheticMVar`'s `.coe`
//!   (`SyntheticMVars.lean:545-560`), is big enough to be its own
//!   function, so its body IS here as
//!   [`TermElabM::synthesize_coe_mvar`] and `synthetic/ladder.rs`'s arm
//!   just calls it;
//! - the REPORTER arm, `reportStuckSyntheticMVar`'s `.coe`
//!   (`SyntheticMVars.lean:304-310`), is small enough to stay inline,
//!   so its body is in `synthetic/report.rs:104` beside the
//!   `.typeClass` and `.tactic` arms it is dispatched against. It is
//!   elaborator-tier P4 all the same — named here so a reader after the
//!   slice's full extent does not have to hunt for it.
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
    ///
    /// **KNOWN DIVERGENCE — the oracle's `catch` is BLANKET, this
    /// `match` is not.** `:1312-1322` has two arms, `| .error _ msg`
    /// and `| _`, and BOTH end in `throwTypeMismatchError`: every
    /// exception raised anywhere inside the `try` — an `inferType`
    /// failure, an instance-synthesis failure, any other `MetaM` error
    /// on the way into or out of `coerceCollectingNames?` — comes back
    /// out as "type mismatch". leanr folds only the two cases named
    /// above; any other `MetaError` falls through the final
    /// `Err(err) => ElabError::from(err)` and surfaces as
    /// `ElabError::Meta(..)` where the oracle would have said "type
    /// mismatch". No corpus record can reach it — a record exists only
    /// where BOTH sides elaborate, so an error-vs-error disagreement is
    /// never one — and keeping the underlying error is arguably the
    /// better report. It is a divergence all the same, recorded here
    /// rather than left to be rediscovered.
    pub(crate) fn mk_coe(
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
    pub(crate) fn ensure_has_type(
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
    /// writes it (`withDefault do isDefEq (← inferType e) expectedType`),
    /// and the transcription keeps it there: correct BY TRANSCRIPTION,
    /// at a cost of one line.
    ///
    /// It is, today, UNOBSERVABLE. `Config::default().transparency` is
    /// already `TransparencyMode::Default`
    /// (`leanr_meta/src/config.rs:185`) and nothing on the path in
    /// lowers it, so the scope re-sets what is already ambient.
    /// Measured, not assumed: replacing this whole `with_transparency`
    /// block with a bare `infer_type` + `is_def_eq` leaves the entire
    /// `leanr_elab` suite — corpus gate included — green (whole-branch
    /// fix wave, recorded in its report). It starts biting the moment a
    /// caller runs the synthetic-mvar fixpoint under a LOWER
    /// transparency (`Instances`/`Reducible`), which is what the
    /// oracle's `withDefault` is there to defend against and why the
    /// line stays.
    ///
    /// The oracle's own `mvarId.withContext` (`:545`) is the ladder's
    /// wrapper around every arm (`ladder.rs::with_mvar_local_context`),
    /// not this function's job.
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

    /// oracle: `ensureType` (`TermElabM.lean:1935-1949`) — `isType e`
    /// (`InferType.lean:502-508`: the type `whnfD`s to a `Sort`); else
    /// `isDefEq eType (Sort ?u)` with a fresh level mvar; else
    /// `coerceToSort?`; else "type expected" (`:1946-1949`) — but only on
    /// `coerceToSort?`'s `none` answer (no `CoeSort` instance at all).
    /// `coerceToSort?` (`Coe.lean:114-126`) can also THROW, when the
    /// post-expansion result still isn't a `Sort` (`:122-124`); the call
    /// site at `:1943` has no `try` around it, so that throw propagates
    /// as itself, exactly like `synthesize_coe_mvar`'s bare
    /// `coerceCollectingNames?` call (this file, `:552`) — NOT folded
    /// into "type expected", which is a distinct oracle error class. The
    /// `hasSyntheticSorry` `throwAbortTerm` branch (`:1947`) has no
    /// producer here (leanr has no `sorry` recovery).
    ///
    /// **`_stx` is unused on purpose, and kept on purpose.** The
    /// oracle's `ensureType` takes no syntax; its sole caller `elabType`
    /// supplies the reference around it, as `withRef stx <| ensureType
    /// type` (`:1954`). `withRef` sets the position errors and info
    /// nodes are reported AT, and leanr defers that whole prose layer
    /// (module doc above; design spec § Amendment item 2), so the
    /// parameter is inert until it lands. Keeping it — same `&SynElem`
    /// in the same position as [`Self::mk_coe`] and
    /// [`Self::ensure_has_type`], which do use theirs — makes landing
    /// the prose layer a body change here rather than a signature
    /// change at every call site.
    ///
    /// Visibility, settled for all four functions in this module: every
    /// caller is in-crate (`builtin/binder.rs`, `builtin/ascription.rs`,
    /// `app/args.rs`, `elab.rs`, `synthetic/ladder.rs`), so all four are
    /// `pub(crate)`. Three were `pub` until the whole-branch fix wave —
    /// an external-API claim nothing was making use of.
    pub(crate) fn ensure_type(&mut self, _stx: &SynElem, e: ExprId) -> Result<ExprId, ElabError> {
        let ty = self.mctx.infer_type(e)?;
        let w = self
            .mctx
            .with_transparency(TransparencyMode::Default, |m| m.whnf(ty))?;
        let base = self.view.store;
        if matches!(
            self.mctx.store().expr_node(Some(base), w),
            leanr_kernel::bank::terms::Node::Sort { .. }
        ) {
            return Ok(e);
        }
        let u = self.mk_fresh_level_mvar()?;
        let sort_u = self
            .mctx
            .store_mut()
            .expr_sort(None, u)
            .map_err(MetaError::from)?;
        if self.mctx.is_def_eq(ty, sort_u)? {
            return Ok(e);
        }
        match self.mctx.coerce_to_sort(e) {
            Ok(Some(coerced)) => Ok(coerced),
            Ok(None) => Err(ElabError::TypeExpected { e, ty }),
            // No `try` here either (`TermElabM.lean:1943`, unlike
            // `mkCoe`'s `:1313`): a post-expansion throw is the
            // elaboration error it is, NOT "type expected".
            Err(err @ MetaError::CoeExpansionMismatch(_)) => Err(ElabError::from(err)),
            Err(MetaError::Unsupported(m)) => Err(ElabError::UnsupportedSyntax(m)),
            Err(err) => Err(ElabError::from(err)),
        }
    }
}
