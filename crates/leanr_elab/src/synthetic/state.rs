//! The scheduler's STATE: the synthetic-mvar decl table, the mvar-error
//! table, and the registration/scoping helpers. Oracle:
//! `Lean/Elab/Term/TermElabM.lean`. The scheduling itself is `ladder.rs`.

use std::collections::HashMap;

use leanr_kernel::bank::{ExprId, NameId};
use leanr_meta::{MVarId, MVarKind, MetaSnapshot};

use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `structure SavedContext` (`TermElabM.lean:46-53`).
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
/// **All four variants exist from P2a**, even though P2a produced only
/// `TypeClass` and `Postponed`: the oracle's control flow branches on
/// the kind in places far from where it is set, and a missing variant is
/// a silent fidelity hole where a missing *arm* is a named seam. M4b-3
/// P4 shipped the `Coe` producer (`coe.rs`'s `mk_coe`) and its two
/// consumer arms (`ladder.rs`'s scheduling arm, `report.rs`'s stuck-
/// coercion reporter arm); P5 task 9 wires up `Tactic`'s own producer
/// (`app/args.rs`'s `mk_tactic_mvar`, mirroring `mkTacticMVar` at its
/// `.autoParam` call site, `App.lean:846`).
///
/// The oracle's message-carrying payloads (`extraErrorMsg?`,
/// `mkErrorMsg?`, `header?`) are omitted: leanr defers the prose layer
/// (design spec § Amendment, item 2). `Coe` keeps the two payloads that
/// are `Expr`s rather than messages, because the `Coe` arm computes with
/// them. `Tactic`'s `param_name` is the same kind of real DATA, not
/// prose: the oracle's own `.tactic` case carries a `TacticMVarKind`
/// (`TermElabM.lean:56-62`), and the `.autoParam (argName : Name)`
/// variant IS that argument name — leanr keeps the rendered name for
/// exactly the reason the oracle keeps the `Name`, to say WHICH
/// parameter is stuck, and renders it once at the single producer call
/// site (`AppElab::render_name`'s own idiom) rather than threading
/// `Store` access into `ladder.rs`/`report.rs`, neither of which needs
/// it for anything else. The oracle's `tacticCode : Syntax` and
/// `ctx : SavedContext` payloads are NOT modelled: leanr never runs the
/// tactic (this slice's own scope boundary — see `mk_tactic_mvar`'s
/// doc), so there is no tactic syntax to save for a later run.
#[derive(Debug, Clone)]
pub enum SyntheticMVarKind {
    TypeClass,
    Coe { expected_type: ExprId, e: ExprId },
    Tactic { param_name: Option<String> },
    Postponed { ctx: SavedContext },
}

/// Shared wording for the `.tactic` seam, so `ladder.rs`'s rung-5 arm
/// (the one actually reachable today — see its own doc) and
/// `report.rs`'s stuck-reporter arm (unreachable today, kept for the
/// day a real tactic evaluator lands in rung 5 and CAN return `false`
/// for a genuinely stuck tactic) cannot drift apart on the same fact:
/// executing an `autoParam` tactic needs the `by` elaborator and the
/// tactic framework, which the roadmap assigns to a later M4 slice.
pub(crate) fn tactic_seam_message(param_name: Option<&str>) -> String {
    match param_name {
        Some(name) => format!(
            "autoParam tactic execution for parameter `{name}` requires the `by` elaborator \
             and the tactic framework — later M4"
        ),
        None => "autoParam tactic execution requires the `by` elaborator and the tactic \
                  framework — later M4"
            .to_string(),
    }
}

/// oracle: `structure SyntheticMVarDecl` (`TermElabM.lean:107`).
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

/// oracle: `structure Term.SavedState` (`TermElabM.lean:206-209`) —
/// `Meta.SavedState × Term.State`, restricted to the `Term.State` fields
/// leanr models. Produced by [`TermElabM::save_term_state`] and consumed
/// by [`TermElabM::restore_term_state`]; private, because
/// [`TermElabM::commit_when`] is the only bracket that needs one.
struct SavedTermState {
    meta: MetaSnapshot,
    pending_mvars: Vec<MVarId>,
    synthetic_mvars: HashMap<MVarId, SyntheticMVarDecl>,
    mvar_error_infos: Vec<MVarErrorInfo>,
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

    /// oracle: `Term.mkInstMVar` (`TermElabM.lean:1925-1930`).
    ///
    /// **Not** `ElabAppArgs`'s same-named `where`-binding
    /// (`App.lean:919-923`, ported at `app/args.rs`'s
    /// `process_inst_implicit_arg`), which mints the mvar, pushes it on
    /// `instMVars` and DEFERS synthesis to `finalize`. This one
    /// synthesizes EAGERLY and registers `.typeClass` only `unless` that
    /// succeeds — the shape a literal needs, since a numeral has no
    /// enclosing application to defer to. The two are deliberately
    /// distinct; do not merge them.
    ///
    /// The oracle's `extraErrorMsg?` is prose (design spec § Amendment,
    /// item 2) and is not carried.
    pub fn mk_inst_mvar(&mut self, ty: ExprId, stx: SynElem) -> Result<ExprId, ElabError> {
        let (mvar, mvar_id) = self.mk_fresh_expr_mvar_of_kind(ty, MVarKind::Synthetic)?;
        if !self.synthesize_inst_mvar_core(mvar_id)? {
            self.register_synthetic_mvar(stx, mvar_id, SyntheticMVarKind::TypeClass);
        }
        Ok(mvar)
    }

    /// oracle: `commitWhen` (`Lean/Util/MonadBacktrack.lean:50-60`) over
    /// `Term.SavedState` (the `MonadBacktrack SavedState TermElabM`
    /// instance, `TermElabM.lean:458-460`) — run `f`; keep its effects
    /// if it returns `true`, roll them back if it returns `false` or
    /// errors.
    ///
    /// **`MetaCtx::checkpoint`/`rollback` alone is NOT enough.**
    /// `Term.SavedState` is `Meta.SavedState × Term.State`
    /// (`TermElabM.lean:206-209`), and both P3 callers can register
    /// synthetic mvars before failing: `synthesizeUsingDefaultInstance`
    /// calls `synthesizePending`, and `synthesizePendingInstMVar'` calls
    /// `synthesizeInstMVarCore`. Rolling back only the mctx would leave
    /// a rejected default instance's subgoals pending forever, and the
    /// ladder would then report them stuck. So the elaborator's three
    /// tables are snapshotted too.
    ///
    /// `level_names` is NOT snapshotted: it is scoped by
    /// `with_saved_context` alone and no path below `f` touches it.
    /// The three fresh-name counters are likewise not restored —
    /// rewinding them would let a rolled-back attempt's names be REUSED
    /// by the next attempt, which is exactly the collision the counters
    /// exist to prevent. That is the oracle's own choice, not an
    /// approximation: `Core.SavedState.restore` (`CoreM.lean:407-410`)
    /// writes back `env`/`messages`/`infoState`/`snapshotTasks` and
    /// deliberately leaves `Core.State.ngen` — the generator behind
    /// every fresh `FVarId`/`MVarId`/`LMVarId` (`CoreM.lean:192-193`) —
    /// running forward.
    ///
    /// `may_postpone` is likewise not snapshotted: the oracle's
    /// `mayPostpone` is a `Context` reader field, not part of
    /// `Term.State` (see [`SavedContext`]'s own doc).
    ///
    /// The mvar DECLARATION table is not rewound either, and this one is
    /// a genuine narrowing rather than a modelling difference: the
    /// oracle's `Meta.SavedState.restore` (`Meta/Basic.lean:594-596`)
    /// writes back the whole `mctx`, declarations included, while
    /// `MetaSnapshot` carries only the expr/level ASSIGNMENT maps and
    /// the postponed queue (its own doc: "NOT declarations — an mvar
    /// stays declared"). So a rejected attempt leaves its freshly
    /// declared mvars behind as orphans. Safe, on two counts, and
    /// recorded rather than fixed because widening `MetaSnapshot` is a
    /// `leanr_meta` behaviour change and this plan freezes that crate:
    /// nothing in `leanr_elab` or `leanr_meta` iterates the declaration
    /// table wholesale (every read is `decl(mvar_id)` for an id the
    /// caller already holds), so an unreferenced declaration is
    /// invisible; and because the fresh-name counters above are
    /// deliberately NOT rewound, a later attempt can never mint a name
    /// that aliases one of those orphans. The cost is memory in a
    /// scratch store that is dropped at the end of the elaboration.
    pub fn commit_when(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<bool, ElabError>,
    ) -> Result<bool, ElabError> {
        // Written as a saved-value struct plus a private restore method
        // rather than a closure: a closure capturing the saved values by
        // move cannot be called on both the `Ok(false)` and the `Err`
        // path, and cloning them into it would double every snapshot on
        // the (common) committing path.
        let saved = self.save_term_state();
        match f(self) {
            Ok(true) => Ok(true),
            Ok(false) => {
                self.restore_term_state(saved);
                Ok(false)
            }
            Err(e) => {
                self.restore_term_state(saved);
                Err(e)
            }
        }
    }

    /// oracle: `Term.saveState` (`TermElabM.lean:417-418`), restricted to
    /// the `Term.State` fields leanr models. See [`TermElabM::commit_when`]
    /// for what is deliberately left out.
    fn save_term_state(&self) -> SavedTermState {
        SavedTermState {
            meta: self.mctx.checkpoint(),
            pending_mvars: self.pending_mvars.clone(),
            synthetic_mvars: self.synthetic_mvars.clone(),
            mvar_error_infos: self.mvar_error_infos.clone(),
        }
    }

    /// oracle: `Term.SavedState.restore` (`TermElabM.lean:420-427`).
    fn restore_term_state(&mut self, saved: SavedTermState) {
        self.mctx.rollback(saved.meta);
        self.pending_mvars = saved.pending_mvars;
        self.synthetic_mvars = saved.synthetic_mvars;
        self.mvar_error_infos = saved.mvar_error_infos;
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
}
