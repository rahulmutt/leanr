//! The scheduler's LADDER: `synthesizeSyntheticMVarsStep`'s ordering
//! core, the five rungs of `synthesizeSyntheticMVars`, `withSynthesize`,
//! and `resumePostponed`. Oracle: `Lean/Elab/SyntheticMVars.lean`. The
//! decl/error tables and their registration live in `state.rs`; stuck
//! reporting is `report.rs`.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_meta::MVarId;
use leanr_syntax::kind::KindInterner;

use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;

use super::state::{SavedContext, SyntheticMVarKind};

/// oracle: `inductive PostponeBehavior` (`SyntheticMVars.lean:424-440`).
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

/// oracle: `Lean.LOption` as `trySynthInstance` returns it
/// (`SynthInstance.lean:1010-1017`) — `.some` is an answer, `.none` a
/// completed search with no answer, and `.undef` "instance cannot be
/// synthesized right now because `type` contains metavariables".
///
/// Three-valued, not `Option`: reporting `.undef` as `.none` turns every
/// postponable typeclass goal into a hard synthesis failure, and
/// reporting it as `.some` — which is what happens when nothing detects
/// the stuck condition at all — answers the goal by guessing a candidate
/// on the caller's behalf. See `TermElabM::try_synth_instance`.
enum LOptionExpr {
    Some(ExprId),
    Undef,
    None,
}

impl<'e> TermElabM<'e> {
    /// oracle: `Lean.Meta.trySynthInstance` (`SynthInstance.lean:
    /// 1010-1017`) — `synthInstance?` with `isDefEqStuckExceptionId`
    /// caught and reported as `.undef`.
    ///
    /// **Why this is not just `synth_instance` with the error mapped.**
    /// The oracle's `.undef` is a DYNAMIC signal: `synthInstanceCore?`
    /// runs the entire search under `withNewMCtxDepth`
    /// (`SynthInstance.lean:977`) with `isDefEqStuckEx := true`
    /// (`:963`), which makes every metavariable the CALLER already owned
    /// read-only for the duration. When a candidate's unification then
    /// reaches `?a =?= Nat` with `?a` read-only and `Nat` not a
    /// metavariable, neither side is assignable and
    /// `ExprDefEq.lean:1898-1958`'s last branch throws
    /// `isDefEqStuck`, which aborts the whole search — so the answer is
    /// "ask me again once you have assigned `?a`", not "`instWrapNat`".
    ///
    /// `leanr_meta` has no mctx-depth / read-only-mvar model and
    /// constructs `MetaError::IsDefEqStuck` nowhere (this crate's
    /// deferral ledger in `lib.rs` records that gap, whose owner is a
    /// later `leanr_meta` slice; `leanr_meta/src` is behavior-frozen for
    /// M4b-3 P3). Its `synth_instance` therefore treats the caller's
    /// `?a` as an ordinary assignable mvar and answers `Wrap ?a` with
    /// whichever candidate it reaches first — silently choosing the
    /// class's type parameter for the caller. That is a WRONG ANSWER,
    /// not merely a missing postponement: with `Wrap Nat`/`Wrap Unit`
    /// both in scope it picks `instWrapUnit` and then `(useWrap
    /// Nat.zero : Nat)` fails to typecheck its own explicit argument.
    ///
    /// So the stuck condition is reconstructed here, from the goal type,
    /// on the elaborator side of the seam:
    ///
    /// - **Exact in the safe direction.** Every site that can throw
    ///   `isDefEqStuck` under this config — the non-assignable/
    ///   non-assignable branch (`ExprDefEq.lean:1954`), the
    ///   outer-depth `unstuckMVar` rescue (`:1993-2018`), and
    ///   `DiscrTree.getKeyArgs`'s reducible/matcher/recursor cases
    ///   (`DiscrTree/Main.lean:359-386`, all guarded by
    ///   `e.hasExprMVar`) — needs an unassigned EXPR metavariable
    ///   reachable from the goal. A goal with none can never be
    ///   `.undef`, so a ground goal still goes to the real search.
    /// - **Over-approximating in the other direction, and that is the
    ///   residual gap.** A goal that does mention an unassigned expr
    ///   mvar is reported `.undef` here even when the oracle would have
    ///   succeeded — the case where every candidate the search reaches
    ///   is polymorphic in that argument (`instWrapAny : ∀ α, Wrap α`),
    ///   so unification assigns only search-local mvars and never the
    ///   caller's. Closing that residue needs the real depth model, not
    ///   a finer syntactic test; until then this errs toward
    ///   postponement, which the ladder can recover from, rather than
    ///   toward committing to a candidate, which it cannot.
    ///
    /// LEVEL metavariables are deliberately NOT part of the test:
    /// `withNewMCtxDepth (allowLevelAssignments := true)` (`:977`) keeps
    /// outer LEVEL mvars assignable, so `LevelDefEq.lean:167-171`'s
    /// stuck throw needs a level mvar that is non-assignable for some
    /// other reason. `has_expr_mvar` alone is the right predicate.
    ///
    /// The `MetaError::IsDefEqStuck` arm below is kept live: it is the
    /// channel this function should be reading once `leanr_meta` grows
    /// the depth model, at which point the syntactic pre-test becomes
    /// redundant and can be deleted rather than rewritten.
    ///
    /// Precondition: `ty` is already `instantiate_mvars`-ed (the oracle's
    /// own `let type ← instantiateMVars type`, `SynthInstance.lean:969`).
    /// The `has_expr_mvar` bit is recomputed per constructed node, so on
    /// an instantiated type it means exactly "mentions an UNASSIGNED expr
    /// mvar"; on a stale one it would over-report.
    fn try_synth_instance(&mut self, ty: ExprId) -> Result<LOptionExpr, ElabError> {
        let base = self.view.store;
        if self.mctx.store().expr_data(Some(base), ty).has_expr_mvar() {
            return Ok(LOptionExpr::Undef);
        }
        match self.mctx.synth_instance(ty) {
            Ok(Some(val)) => Ok(LOptionExpr::Some(val)),
            Ok(None) => Ok(LOptionExpr::None),
            Err(leanr_meta::MetaError::IsDefEqStuck(_)) => Ok(LOptionExpr::Undef),
            Err(e) => Err(ElabError::from(e)),
        }
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

    /// oracle: `synthesizeSyntheticMVar` (`SyntheticMVars.lean:540-569`).
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
                // `runTactics && !(delayOnMVars && (← mvarId.getType >>=
                // instantiateExprMVars).hasExprMVar)`
                // (`SyntheticMVars.lean:563-569`), and returns `false`
                // otherwise. leanr's `Tactic` variant carries no
                // `delayOnMVars` field (this crate's own doc on the
                // `SyntheticMVarKind` enum) — that sub-condition is
                // UNMODELLED here, so this arm's gate is `run_tactics`
                // alone, not the oracle's full conjunction; the seam
                // below covers less than "every `.tactic` arm run under
                // `run_tactics`", only "every one the oracle would also
                // run given a type with no remaining expr mvar, or
                // `delayOnMVars == false`". Rung 5 is the only caller
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
        // The trichotomy. Preserving `.undef` as "not ready yet" rather
        // than failure is the whole reason postponement works.
        let val = match self.try_synth_instance(ty)? {
            LOptionExpr::Some(val) => val,
            LOptionExpr::Undef => return Ok(false),
            LOptionExpr::None => return Err(ElabError::InstanceSynthesisFailed { goal: ty }),
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
