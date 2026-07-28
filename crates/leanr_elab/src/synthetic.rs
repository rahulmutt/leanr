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

use leanr_kernel::bank::terms::Node;
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

    /// oracle: `synthesizeInstMVarCore` (`TermElabM.lean:1232-1288`).
    ///
    /// Returns `true` when the instance was synthesized, `false` when it
    /// is blocked by unassigned mvars ("try again later"), and errors
    /// when resolution or assignment irrevocably fails.
    pub fn synthesize_inst_mvar_core(&mut self, inst_mvar: MVarId) -> Result<bool, ElabError> {
        let ty = self
            .mctx
            .mctx()
            .decl(inst_mvar)
            .expect("instance mvar is declared")
            .ty;
        let ty = self.mctx.instantiate_mvars(ty)?;
        // The trichotomy: `Ok(Some)` = `.some`, `Err(IsDefEqStuck)` =
        // `.undef`, `Ok(None)` = `.none`. Preserving `undef` as "not
        // ready yet" rather than failure is the whole reason
        // postponement works.
        let val = match self.mctx.synth_instance(ty) {
            Ok(Some(val)) => val,
            Ok(None) => return Err(ElabError::InstanceSynthesisFailed { goal: ty }),
            Err(leanr_meta::MetaError::IsDefEqStuck(_)) => return Ok(false),
            Err(e) => return Err(ElabError::from(e)),
        };
        if self.mctx.mctx().is_assigned(inst_mvar) {
            // oracle: :1240-1272 — the mvar may already carry a value
            // inferred by typing. Reconcile rather than overwrite.
            let old_val = self
                .mctx
                .mctx()
                .assignment(inst_mvar)
                .expect("just checked assigned");
            let old_val = self.mctx.instantiate_mvars(old_val)?;
            if !self.mctx.is_def_eq(old_val, val)? {
                // oracle: :1243-1262 — if EITHER side still mentions a
                // pending mvar, the mismatch is not yet grounded: return
                // `false` and retry later rather than throwing. Dropping
                // this branch turns a resolvable dependency between
                // postponed mvars into a hard error.
                if self.contains_pending_mvar(old_val)? || self.contains_pending_mvar(val)? {
                    return Ok(false);
                }
                // oracle: :1263-1269 — the oracle infers BOTH `old_val`
                // and `val`'s types here and runs a second `isDefEq` on
                // them, but only to pick which of two error MESSAGES to
                // throw ("type not defeq" vs. "instance not defeq");
                // both still throw. Since leanr's prose layer is
                // deferred plan-wide (design spec § Amendment, item 2),
                // there is nothing for that second check to select
                // between — it throws on the same condition either way,
                // so it is not reproduced here.
                let inferred = self.mctx.infer_type(old_val)?;
                return Err(ElabError::InstanceMismatch {
                    synthesized: val,
                    inferred,
                });
            }
        } else {
            // oracle: :1271-1272 — assign via `isDefEq`, not a raw
            // assign: the mvar's type may still need unification.
            //
            // `is_def_eq_mvar_value` is not a `MetaCtx` method (and one
            // must not be added — Task 1's three accessors are the
            // entire `leanr_meta` allowance for this plan): build the
            // `Expr.mvar` node for `inst_mvar` exactly as
            // `mk_fresh_expr_mvar_of_kind` builds its own
            // (`elab.rs`, `store.expr_mvar(None, Some(name))`), then call
            // the existing `is_def_eq` on it.
            let mvar_expr = self
                .mctx
                .store_mut()
                .expr_mvar(None, Some(inst_mvar.0))
                .map_err(leanr_meta::MetaError::from)?;
            if !self.mctx.is_def_eq(mvar_expr, val)? {
                return Err(ElabError::InstanceMismatch {
                    synthesized: val,
                    inferred: ty,
                });
            }
        }
        Ok(true)
    }

    /// oracle: `synthesizePendingInstMVar` (`SyntheticMVars.lean:79-85`)
    /// — `synthesizeInstMVarCore` with errors LOGGED rather than
    /// propagated, returning `true` so the mvar leaves the pending list.
    ///
    /// leanr has no message log, so a synthesis failure propagates as an
    /// `ElabError` instead of being logged and swallowed. That is the
    /// deliberate difference: the oracle keeps elaborating to collect
    /// more errors, leanr stops at the first. Recorded rather than
    /// hidden — the slice that adds a diagnostics layer revisits it.
    pub fn synthesize_pending_inst_mvar(&mut self, inst_mvar: MVarId) -> Result<bool, ElabError> {
        self.synthesize_inst_mvar_core(inst_mvar)
    }

    /// oracle: `containsPendingMVar` — does `e` mention an mvar that is
    /// still on the pending list?
    ///
    /// Walks `e` collecting mvar ids and testing membership in
    /// `pending_mvars`, using the same traversal idiom `app/finalize.rs`'s
    /// `update_binder_names` uses (`Store::expr_node` over `Node`) rather
    /// than a new visitor abstraction.
    fn contains_pending_mvar(&mut self, e: ExprId) -> Result<bool, ElabError> {
        let base = self.view.store;
        match self.mctx.store().expr_node(Some(base), e) {
            Node::MVar { id: Some(name) } => Ok(self.pending_mvars.contains(&MVarId(name))),
            Node::MVar { id: None } => Ok(false),
            Node::App { f, arg } => {
                Ok(self.contains_pending_mvar(f)? || self.contains_pending_mvar(arg)?)
            }
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => Ok(self.contains_pending_mvar(binder_type)? || self.contains_pending_mvar(body)?),
            Node::LetE {
                ty, value, body, ..
            } => Ok(self.contains_pending_mvar(ty)?
                || self.contains_pending_mvar(value)?
                || self.contains_pending_mvar(body)?),
            Node::MData { expr, .. } => self.contains_pending_mvar(expr),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                self.contains_pending_mvar(structure)
            }
            Node::BVar { .. }
            | Node::BVarBig { .. }
            | Node::FVar { .. }
            | Node::Sort { .. }
            | Node::Const { .. }
            | Node::LitNat { .. }
            | Node::LitStr { .. } => Ok(false),
        }
    }

    /// oracle: `synthesizeSyntheticMVars` (`SyntheticMVars.lean:611-646`).
    ///
    /// Transliterated structurally, including two things easy to get
    /// subtly wrong: the stuck report is the LAST `else if` INSIDE the
    /// loop body (not a step after it), and only
    /// `processPostponedUniverseConstraints` runs after the loop.
    ///
    /// leanr drops the oracle's `ignoreStuckTC` parameter: its only
    /// caller is `simp` argument elaboration, which no leanr slice has.
    pub fn synthesize_synthetic_mvars(
        &mut self,
        postpone: PostponeBehavior,
        kinds: &KindInterner,
    ) -> Result<(), ElabError> {
        loop {
            if self.pending_mvars.is_empty() {
                break;
            }
            if self.synthesize_synthetic_mvars_step(false, false, kinds)? {
                continue;
            }
            if postpone == PostponeBehavior::Yes {
                break;
            }
            // Rung 2: postponement disabled, elaboration errors
            // postponed. The oracle's own worked example
            // (:618-635) is why `postponeOnError` and `mayPostpone` are
            // separate knobs.
            if self.without_postponing(|e| e.synthesize_synthetic_mvars_step(true, false, kinds))? {
                continue;
            }
            // Rung 3: default instances (P3; shape-guarded seam here).
            if self.synthesize_using_default()? {
                continue;
            }
            // Rung 4: postponement disabled, errors NOT postponed —
            // force a commitment.
            if self
                .without_postponing(|e| e.synthesize_synthetic_mvars_step(false, false, kinds))?
            {
                continue;
            }
            // Rung 5: run tactics.
            if self.synthesize_synthetic_mvars_step(false, true, kinds)? {
                continue;
            }
            if postpone == PostponeBehavior::No {
                self.report_stuck_synthetic_mvars()?;
            }
            break;
        }
        if postpone == PostponeBehavior::No {
            self.process_postponed_universe_constraints()?;
        }
        Ok(())
    }

    /// oracle: `synthesizeSyntheticMVarsNoPostponing`
    /// (`SyntheticMVars.lean:649-650`).
    pub fn synthesize_synthetic_mvars_no_postponing(
        &mut self,
        kinds: &KindInterner,
    ) -> Result<(), ElabError> {
        self.synthesize_synthetic_mvars(PostponeBehavior::No, kinds)
    }

    /// oracle: `resumePostponed` (`SyntheticMVars.lean:32-74`) —
    /// re-elaborate the postponed syntax under its saved context, ensure
    /// it has the mvar's type, and assign.
    ///
    /// The oracle's `occursCheck` guard before assigning is preserved:
    /// a resumed result may mention `mvarId` itself when it contains
    /// synthetic `sorry`s.
    fn resume_postponed(
        &mut self,
        ctx: &SavedContext,
        stx: &SynElem,
        mvar_id: MVarId,
        postpone_on_error: bool,
        kinds: &KindInterner,
    ) -> Result<bool, ElabError> {
        let expected = self
            .mctx
            .mctx()
            .decl(mvar_id)
            .expect("postponed mvar is declared")
            .ty;
        let expected = self.mctx.instantiate_mvars(expected)?;
        let stx = stx.clone();
        let result = self.with_saved_context(ctx, |elab| {
            elab.elab_term_ensuring_type(&stx, kinds, Some(expected))
        });
        match result {
            Ok(e) => {
                // oracle: :56-58 — `occursCheck` guards the assignment:
                // a resumed result may mention `mvarId` itself when it
                // contains synthetic `sorry`s, and assigning through
                // that would build a cyclic `ExprId`. `false` here is
                // "not ready" (`Ok(false)`), matching
                // `synthesizeSyntheticMVar`'s "try again later" contract
                // — NOT an error.
                if self.mctx.check_occurs(mvar_id, e)? {
                    self.mctx.mctx_mut().assign(mvar_id, e)?;
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
            // oracle: :68-74 — on an ERROR, `postponeOnError` decides
            // between "restore and try again later" (`false`) and "log
            // it and consider the mvar done" (`true`). leanr has no
            // message log, so the `true` branch propagates.
            Err(e) if postpone_on_error => {
                let _ = e;
                Ok(false)
            }
            Err(e) => Err(e),
        }
    }

    /// Rung 3's stand-in. P3 replaces the body with
    /// `synthesizeUsingDefault` / `synthesizeSomeUsingDefaultPrio` /
    /// `synthesizeUsingDefaultPrio` (`SyntheticMVars.lean:215-221`,
    /// `:193-210`, `:113-190`).
    ///
    /// Shape-guarded rather than a blanket `false`: it errors when a
    /// pending `TypeClass` mvar's class has default instances
    /// registered — the exact state in which the real rung would have
    /// done something — and reports "no progress" otherwise. That keeps
    /// the seam from silently skipping a rung the oracle runs, without
    /// building P3's reverse-creation-order walk here.
    pub fn synthesize_using_default(&mut self) -> Result<bool, ElabError> {
        for mvar_id in self.pending_mvars.clone() {
            if !matches!(
                self.synthetic_mvar_decl(mvar_id).map(|d| &d.kind),
                Some(SyntheticMVarKind::TypeClass)
            ) {
                continue;
            }
            let Some(class) = self.pending_class_name(mvar_id)? else {
                continue;
            };
            if !self.mctx.default_instances_of(class).is_empty() {
                return Err(ElabError::UnsupportedSyntax(
                    "default instances for a pending typeclass mvar require \
                     synthesizeUsingDefault — M4b-3 P3"
                        .to_string(),
                ));
            }
        }
        Ok(false)
    }

    /// The head constant of a pending typeclass goal, if it has one.
    /// `Wrap ?m` -> `Wrap`; a goal whose head is not a constant has no
    /// class name and cannot have default instances.
    fn pending_class_name(&mut self, mvar_id: MVarId) -> Result<Option<NameId>, ElabError> {
        let ty = self
            .mctx
            .mctx()
            .decl(mvar_id)
            .expect("pending mvar is declared")
            .ty;
        let ty = self.mctx.instantiate_mvars(ty)?;
        let base = self.view.store;
        let mut cur = ty;
        loop {
            match self.mctx.store().expr_node(Some(base), cur) {
                Node::App { f, .. } => cur = f,
                // Unwrap the same transparent-to-the-head-search nodes
                // `contains_pending_mvar` (above) does: metadata and
                // projections carry no head of their own, so peeling
                // them off before giving up keeps this consistent with
                // that sibling walk rather than under-firing on a
                // metadata-wrapped or projected goal.
                Node::MData { expr, .. } => cur = expr,
                Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => cur = structure,
                Node::Const { name, .. } => return Ok(name),
                _ => return Ok(None),
            }
        }
    }

    /// oracle: `reportStuckSyntheticMVars` (`SyntheticMVars.lean:322-362`)
    /// and `reportStuckSyntheticMVar` (`:292-316`).
    ///
    /// Drains `pending_mvars`, sorts by the oracle's priority order, and
    /// raises on the first entry. The sort is ported (it picks the
    /// reported mvar deterministically); the note/hint prose is not
    /// (design spec § Amendment, item 2).
    pub fn report_stuck_synthetic_mvars(&mut self) -> Result<(), ElabError> {
        let pending = std::mem::take(&mut self.pending_mvars);
        let mut problems: Vec<(MVarId, SyntheticMVarDecl)> = pending
            .into_iter()
            .filter_map(|id| self.synthetic_mvar_decl(id).cloned().map(|d| (id, d)))
            .collect();
        // oracle: :347-360 — non-typeclass problems come FIRST; among
        // typeclass problems, the SMALLER syntactic range wins (an inner
        // `LT ?m` is more informative than the enclosing
        // `Decidable (x < x)`), ties broken by start offset.
        problems.sort_by(|(_, a), (_, b)| {
            use std::cmp::Ordering;
            let tc = |d: &SyntheticMVarDecl| matches!(d.kind, SyntheticMVarKind::TypeClass);
            match (tc(a), tc(b)) {
                (true, true) => {
                    let ra = a.stx.text_range();
                    let rb = b.stx.text_range();
                    if ra.len() != rb.len() {
                        ra.len().cmp(&rb.len())
                    } else {
                        ra.start().cmp(&rb.start())
                    }
                }
                (true, false) => Ordering::Greater,
                (false, true) => Ordering::Less,
                (false, false) => Ordering::Equal,
            }
        });
        let Some((mvar_id, decl)) = problems.into_iter().next() else {
            return Ok(());
        };
        match decl.kind {
            SyntheticMVarKind::TypeClass => {
                let goal = self.mctx.mctx().decl(mvar_id).expect("declared").ty;
                let goal = self.mctx.instantiate_mvars(goal)?;
                Err(ElabError::StuckSyntheticMVar { goal })
            }
            SyntheticMVarKind::Coe { .. } => Err(ElabError::UnsupportedSyntax(
                "stuck coercion reporting requires coercion insertion — M4b-3 P4".to_string(),
            )),
            SyntheticMVarKind::Tactic => Err(ElabError::UnsupportedSyntax(
                "stuck tactic reporting requires the `by` elaborator — later M4".to_string(),
            )),
            // oracle: `| _ => unreachable!` (:316) — `.postponed` never
            // reaches the reporter, because a postponed mvar that could
            // not be resumed has already raised from `resume_postponed`.
            SyntheticMVarKind::Postponed { .. } => Err(ElabError::UnsupportedSyntax(
                "a postponed mvar reached the stuck reporter — M4b-3 P2a invariant".to_string(),
            )),
        }
    }

    /// oracle: `withSynthesizeImp` (`SyntheticMVars.lean:662-672`).
    ///
    /// Save the caller's pending mvars, clear, run `k`, synthesize what
    /// `k` created, then restore by APPENDING the saved list after
    /// whatever is left. The oracle's `finally` means the restore
    /// happens on the error path too.
    ///
    /// The oracle also runs `synthesizeUsingDefaultLoop` when
    /// `postpone == .yes`; that loop is P3's, and P2a's guarded
    /// `synthesize_using_default` stands in for it (design spec
    /// § Amendment, item 3).
    pub fn with_synthesize<R>(
        &mut self,
        postpone: PostponeBehavior,
        kinds: &KindInterner,
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        // `withSynthesizeImp` runs the default loop whenever
        // `postpone == .yes` (`SyntheticMVars.lean:668-669`) — for
        // THIS entry point that is exactly `postpone == Yes`, since
        // `with_synthesize` IS `withSynthesizeImp`.
        self.with_synthesize_impl(postpone, postpone == PostponeBehavior::Yes, kinds, k)
    }

    /// oracle: `withSynthesizeLightImp` (`SyntheticMVars.lean:681-689`)
    /// — as `with_synthesize` with `postpone := .yes` and NO default
    /// loop (`withSynthesize`'s own doc, `:691`, says in as many words
    /// that it "does not use `synthesizeUsingDefault`" — the oracle's
    /// `withSynthesizeLightImp` has no default-loop branch at all,
    /// structurally, regardless of `postpone`). No P2a caller; present
    /// because the ladder's callers arrive in later plans and a
    /// missing sibling reads as an oversight.
    pub fn with_synthesize_light<R>(
        &mut self,
        kinds: &KindInterner,
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        self.with_synthesize_impl(PostponeBehavior::Yes, false, kinds, k)
    }

    /// Shared body of `with_synthesize`/`with_synthesize_light`.
    ///
    /// Review finding (M4b-3 P2a task 6 review, finding 1): the default
    /// loop is a SEPARATE knob from `postpone`, not derived from it.
    /// `withSynthesizeImp` (`SyntheticMVars.lean:662-672`) runs
    /// `synthesizeUsingDefaultLoop` when `postpone == .yes` (`:668-669`),
    /// but `withSynthesizeLightImp` (`:681-689`) NEVER runs it —
    /// unconditionally, not merely when `postpone != .yes` — because it
    /// is a different function that structurally lacks the branch.
    /// `with_synthesize` always passes `postpone == Yes` here (it IS
    /// `withSynthesizeImp`); only `with_synthesize_light` passes `false`
    /// unconditionally, so calling it with `postpone == Yes` can never
    /// accidentally run the loop the oracle's own light variant omits.
    fn with_synthesize_impl<R>(
        &mut self,
        postpone: PostponeBehavior,
        run_default_loop: bool,
        kinds: &KindInterner,
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let saved = std::mem::take(&mut self.pending_mvars);
        // Every exit path below must run `self.pending_mvars.extend(saved)`
        // exactly once — that is the oracle's `finally`. Written as
        // straight-line code with one `saved` consumer per branch rather
        // than a closure, because a closure taking `saved` by value
        // cannot be called on two paths.
        let out = match k(self) {
            Ok(v) => v,
            Err(e) => {
                self.pending_mvars.extend(saved);
                return Err(e);
            }
        };
        let mut synth = self.synthesize_synthetic_mvars(postpone, kinds);
        if synth.is_ok() && run_default_loop {
            // oracle: `synthesizeUsingDefaultLoop` (:653). P3 owns the
            // real loop; the guarded seam stands in.
            synth = self.synthesize_using_default().map(|_| ());
        }
        self.pending_mvars.extend(saved);
        synth?;
        Ok(out)
    }

    /// oracle: `processPostponedUniverseConstraints`
    /// (`SyntheticMVars.lean:409-411`).
    fn process_postponed_universe_constraints(&mut self) -> Result<(), ElabError> {
        if self.mctx.process_postponed_levels()? {
            return Ok(());
        }
        // oracle: `throwStuckAtUniverseCnstr` (:374-389) renders the
        // unique constraint pairs. leanr reports the count; the prose is
        // deferred with the rest (design spec § Amendment, item 2).
        Err(ElabError::UnsupportedSyntax(format!(
            "stuck universe constraints ({} postponed) — diagnostics layer not built",
            self.mctx.postponed_len()
        )))
    }
}
