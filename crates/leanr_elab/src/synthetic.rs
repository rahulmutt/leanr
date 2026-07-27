//! `synthesizeSyntheticMVars` — the elaborator's scheduler. Oracle:
//! `Lean/Elab/SyntheticMVars.lean`, plus the state and registration
//! helpers from `Lean/Elab/Term/TermElabM.lean`.
//!
//! M4b-2 deliberately shipped no scheduler because no closed term in its
//! grammar created a synthetic mvar. M4b-3 P1 created the first ones
//! (implicit-argument mvars) but drained none. This module is where
//! every synthetic mvar leanr creates is finally either solved, resumed,
//! or reported stuck.
//!
//! The state lives on `TermElabM` (see `elab.rs`), mirroring the
//! oracle's `Term.State`/`Term.Context` one-to-one; only the `impl`
//! block is here. A nested sub-struct was rejected: every step touching
//! both the table and `&mut self` would need a `mem::take`/restore dance
//! for no structural gain (design spec § P2a).

use leanr_kernel::bank::{ExprId, NameId};
use leanr_meta::MVarId;
use leanr_syntax::kind::KindInterner;

use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `inductive PostponeBehavior` (`SyntheticMVars.lean:423-441`).
///
/// Three-valued, not a `bool`: `Partial` means "typeclass problems may
/// be postponed, everything else may not" and is what `let`'s type
/// elaboration uses (`Binders.lean:775`). The ladder gates rungs 2-5 on
/// `!= Yes` and the stuck report on `== No` — two different tests that a
/// boolean would collapse.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PostponeBehavior {
    Yes,
    No,
    Partial,
}

/// oracle: `structure SavedContext` (`TermElabM.lean:45-53`).
///
/// The oracle saves exactly seven fields: `declName?`, `options`,
/// `openDecls`, `macroStack`, `errToSorry`, `levelNames`,
/// `fixedTermElabs`. leanr models `levelNames` alone — `declName?`,
/// `options`, `openDecls`, `macroStack`, `errToSorry` and
/// `fixedTermElabs` have no leanr counterpart yet: there is no command
/// layer, no options plumbing, no `open` resolution (`resolve.rs`'s own
/// deferral), no macro stack (`dispatch.rs` never expands a macro), and
/// no `errToSorry` recovery or fixed-elabs registry. Each arrives with
/// the slice that adds the concept; adding empty placeholders now would
/// be speculative surface.
///
/// `mayPostpone` is NOT one of the seven — it is a `Context` reader
/// field (`Context.mayPostpone : Bool := true`, `TermElabM.lean:303`)
/// scoped only by `withoutPostponing` (`:1049-1050`), and
/// `withSavedContext` (`:1434-1442`) never touches it. Modeling it here
/// too would make `with_saved_context` clobber whatever
/// `without_postponing` (or the ladder's own postponement scoping) had
/// in effect — leanr's `may_postpone` field is scoped exclusively by
/// `TermElabM::without_postponing`.
#[derive(Debug, Clone)]
pub struct SavedContext {
    pub level_names: Vec<NameId>,
}

/// oracle: `inductive SyntheticMVarKind` (`TermElabM.lean:65-92`).
///
/// **All four variants exist from P2a**, even though P2a produces only
/// `TypeClass` and `Postponed`: the oracle's control flow branches on
/// the kind in places far from where it is set, and a missing variant is
/// a silent fidelity hole where a missing *arm* is a named seam. P4
/// produces `Coe`; P5 registers `Tactic`.
///
/// The oracle's message-carrying payloads (`extraErrorMsg?`,
/// `mkErrorMsg?`, `header?`) are omitted: leanr defers the prose layer
/// (design spec § Amendment, item 2). `Coe` keeps the two payloads that
/// are `Expr`s rather than messages, because P4's arm computes with
/// them.
#[derive(Debug, Clone)]
pub enum SyntheticMVarKind {
    TypeClass,
    Coe { expected_type: ExprId, e: ExprId },
    Tactic,
    Postponed { ctx: SavedContext },
}

/// oracle: `structure SyntheticMVarDecl` (`TermElabM.lean:105-108`).
///
/// `stx` is a `SynElem` — an OWNED rowan handle (`rowan::SyntaxNode` is
/// Rc-backed), so the table needs no lifetime parameter. The matching
/// `KindInterner` is NOT stored: `TermElabM`'s module doc pins that it
/// is passed per call, so every fixpoint entry point takes `kinds`
/// instead. One elaboration uses one tree, so one interner is always the
/// right one.
#[derive(Debug, Clone)]
pub struct SyntheticMVarDecl {
    pub stx: SynElem,
    pub kind: SyntheticMVarKind,
}

/// oracle: `inductive MVarErrorKind` (`TermElabM.lean:116-124`).
#[derive(Debug, Clone)]
pub enum MVarErrorKind {
    /// oracle: `.implicitArg (lctx) (ctx)` — the parent application.
    /// leanr stores only the application: the oracle's `lctx` exists for
    /// the named-argument eta feature's error rendering, which is prose.
    ImplicitArg {
        app: ExprId,
    },
    Hole,
}

/// oracle: `structure MVarErrorInfo` (`TermElabM.lean:135-139`).
/// Registered here, rendered by whichever slice grows a diagnostics
/// layer (design spec § Amendment, item 2).
#[derive(Debug, Clone)]
pub struct MVarErrorInfo {
    pub mvar_id: MVarId,
    pub stx: SynElem,
    pub kind: MVarErrorKind,
}

impl<'e> TermElabM<'e> {
    /// oracle: `registerSyntheticMVar` (`TermElabM.lean:864-865`).
    /// `pending_mvars` is a list whose **head is the most recent** — the
    /// oracle conses, so leanr inserts at 0. Every ordering in this
    /// module depends on that invariant.
    pub fn register_synthetic_mvar(
        &mut self,
        stx: SynElem,
        mvar_id: MVarId,
        kind: SyntheticMVarKind,
    ) {
        self.synthetic_mvars
            .insert(mvar_id, SyntheticMVarDecl { stx, kind });
        self.pending_mvars.insert(0, mvar_id);
    }

    /// oracle: `getSyntheticMVarDecl?` (`TermElabM.lean:1455-1456`).
    pub fn synthetic_mvar_decl(&self, mvar_id: MVarId) -> Option<&SyntheticMVarDecl> {
        self.synthetic_mvars.get(&mvar_id)
    }

    /// oracle: `markAsResolved` (`SyntheticMVars.lean:417-418`) — erases
    /// from `syntheticMVars` ONLY. `pending_mvars` is managed by the
    /// step's own filter; removing it here too would double-remove and
    /// break the step's progress count.
    pub fn mark_as_resolved(&mut self, mvar_id: MVarId) {
        self.synthetic_mvars.remove(&mvar_id);
    }

    /// oracle: `registerMVarErrorImplicitArgInfo` (`TermElabM.lean:876-877`).
    pub fn register_mvar_error_implicit_arg_info(
        &mut self,
        mvar_id: MVarId,
        stx: SynElem,
        app: ExprId,
    ) {
        self.mvar_error_infos.push(MVarErrorInfo {
            mvar_id,
            stx,
            kind: MVarErrorKind::ImplicitArg { app },
        });
    }

    /// oracle: `registerMVarErrorHoleInfo` (`TermElabM.lean:873-874`).
    pub fn register_mvar_error_hole_info(&mut self, mvar_id: MVarId, stx: SynElem) {
        self.mvar_error_infos.push(MVarErrorInfo {
            mvar_id,
            stx,
            kind: MVarErrorKind::Hole,
        });
    }

    /// oracle: `saveContext` (`TermElabM.lean:1420-1428`), restricted to
    /// the field leanr has (see `SavedContext`).
    pub fn save_context(&self) -> SavedContext {
        SavedContext {
            level_names: self.level_names.clone(),
        }
    }

    /// oracle: `withSavedContext` (`TermElabM.lean:1434-1442`).
    /// Restores on BOTH paths — the oracle gets that from `withReader`'s
    /// scoping; leanr's is a field, so the restore is explicit.
    ///
    /// Does NOT touch `may_postpone`: the oracle's `withSavedContext`
    /// never does either (`mayPostpone` is not one of `SavedContext`'s
    /// seven fields — see that struct's own doc). `may_postpone` is
    /// scoped exclusively by `without_postponing`.
    pub fn with_saved_context<R>(
        &mut self,
        saved: &SavedContext,
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let prev_levels = std::mem::replace(&mut self.level_names, saved.level_names.clone());
        let out = k(self);
        self.level_names = prev_levels;
        out
    }

    /// oracle: `withoutPostponing` (`TermElabM.lean:1049-1050`).
    pub fn without_postponing<R>(
        &mut self,
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let prev = std::mem::replace(&mut self.may_postpone, false);
        let out = k(self);
        self.may_postpone = prev;
        out
    }

    /// The ordering core of `synthesizeSyntheticMVarsStep`
    /// (`SyntheticMVars.lean:573-594`), with the per-mvar outcome
    /// supplied by the caller.
    ///
    /// Split out so the two fidelity-critical orderings can be tested
    /// without a class fixture (see `tests/synthetic_smoke.rs`): the real
    /// step passes `synthesize_synthetic_mvar`, tests pass a stub.
    pub fn step_with(
        &mut self,
        mut f: impl FnMut(&mut Self, MVarId) -> Result<bool, ElabError>,
    ) -> Result<bool, ElabError> {
        // oracle: `let pendingMVars := (← get).pendingMVars` then
        // `modify fun s => { s with pendingMVars := [] }` (:577-580) —
        // snapshot AND clear, so mvars created during the walk
        // accumulate in a fresh list.
        let pending = std::mem::take(&mut self.pending_mvars);
        let num_synthetic = pending.len();

        // oracle: `pendingMVars.filterRevM ..` (:584). `filterRevM` is
        // `filterAuxM p as.reverse []`
        // (`Init/Data/List/Control.lean:180-181`): it visits
        // RIGHT-TO-LEFT and, because `filterAuxM` prepends, returns the
        // survivors in the ORIGINAL list order. `pending_mvars` is
        // head-is-most-recent, so right-to-left is OLDEST-FIRST, i.e.
        // creation order — the oracle's own stated reason for using
        // `filterRevM` rather than `filterM`.
        let mut remaining = Vec::new();
        for mvar_id in pending.iter().rev().copied() {
            let succeeded = f(self, mvar_id)?;
            if succeeded {
                self.mark_as_resolved(mvar_id);
            } else {
                remaining.push(mvar_id);
            }
        }
        // Collected oldest-first; restore head-is-most-recent.
        remaining.reverse();

        // oracle: `pendingMVars := s.pendingMVars ++ remainingPendingMVars`
        // (:593) — `s.pendingMVars` here is what the walk CREATED, so
        // new-pending comes FIRST and still-unsolved after.
        let mut merged = std::mem::take(&mut self.pending_mvars);
        merged.extend(remaining.iter().copied());
        self.pending_mvars = merged;

        // oracle: `return numSyntheticMVars != remainingPendingMVars.length`
        // (:594) — against the SNAPSHOT length, not the merged list, so
        // newly created mvars can never mask progress.
        Ok(num_synthetic != remaining.len())
    }

    /// oracle: `synthesizeSyntheticMVarsStep` (`SyntheticMVars.lean:573-594`).
    pub fn synthesize_synthetic_mvars_step(
        &mut self,
        postpone_on_error: bool,
        run_tactics: bool,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        self.step_with(|elab, mvar_id| {
            elab.synthesize_synthetic_mvar(mvar_id, postpone_on_error, run_tactics, kinds)
        })
    }

    /// oracle: `synthesizeSyntheticMVar` (`SyntheticMVars.lean:539-569`).
    ///
    /// Returns `true` when the mvar was synthesized, `false` for "not
    /// ready yet". An mvar with no decl returns `true` — the oracle's
    /// `| return true -- The metavariable has already been synthesized`.
    pub fn synthesize_synthetic_mvar(
        &mut self,
        mvar_id: MVarId,
        postpone_on_error: bool,
        run_tactics: bool,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        let Some(decl) = self.synthetic_mvar_decl(mvar_id).cloned() else {
            return Ok(true);
        };
        match decl.kind {
            SyntheticMVarKind::TypeClass => self.synthesize_pending_inst_mvar(mvar_id),
            SyntheticMVarKind::Postponed { ref ctx } => {
                self.resume_postponed(ctx, &decl.stx, mvar_id, postpone_on_error, kinds)
            }
            SyntheticMVarKind::Coe { .. } => Err(ElabError::UnsupportedSyntax(
                "coercion synthetic mvars require coercion insertion — M4b-3 P4".to_string(),
            )),
            SyntheticMVarKind::Tactic => {
                // oracle: the `.tactic` arm runs the tactic only when
                // `runTactics` (`SyntheticMVars.lean:563-569`), and
                // returns `false` otherwise. Rung 5 is the only caller
                // that passes `run_tactics: true`, so this seam is
                // reachable ONLY there — a silent `false` here would make
                // the ladder report "stuck" for a reason the user cannot
                // see.
                if run_tactics {
                    Err(ElabError::UnsupportedSyntax(
                        "autoParam tactic execution requires the `by` elaborator — later M4"
                            .to_string(),
                    ))
                } else {
                    Ok(false)
                }
            }
        }
    }

    /// Task 4: real typeclass instance synthesis. Stub returns `false`
    /// ("not ready yet") so the ladder never mistakes an unimplemented
    /// rung for success.
    // Task 4
    pub fn synthesize_pending_inst_mvar(&mut self, mvar_id: MVarId) -> Result<bool, ElabError> {
        let _ = mvar_id;
        Ok(false)
    }

    /// Task 5: resuming a postponed elaboration. Stub returns `false`
    /// ("not ready yet") so the ladder never mistakes an unimplemented
    /// rung for success.
    // Task 5
    pub fn resume_postponed(
        &mut self,
        ctx: &SavedContext,
        stx: &SynElem,
        mvar_id: MVarId,
        postpone_on_error: bool,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        let _ = (ctx, stx, mvar_id, postpone_on_error, kinds);
        Ok(false)
    }
}
