//! The scheduler's stuck REPORT: the pending-typeclass class-name lookup
//! rung 3 uses, and the final priority-sorted stuck report. Oracle:
//! `Lean/Elab/SyntheticMVars.lean`'s `reportStuckSyntheticMVars` /
//! `reportStuckSyntheticMVar`.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::NameId;
use leanr_meta::MVarId;

use crate::elab::TermElabM;
use crate::error::ElabError;

use super::state::{SyntheticMVarDecl, SyntheticMVarKind};

impl<'e> TermElabM<'e> {
    /// The head constant of a pending typeclass goal, if it has one.
    /// `Wrap ?m` -> `Wrap`; a goal whose head is not a constant has no
    /// class name and cannot have default instances.
    ///
    /// `pub(crate)` rather than private since M4b-3 P3 task 1: the split
    /// put its two callers (`ladder.rs`'s rung 3, and `default_inst.rs`
    /// from task 5 on) in sibling modules. The body is unchanged.
    pub(crate) fn pending_class_name(
        &mut self,
        mvar_id: MVarId,
    ) -> Result<Option<NameId>, ElabError> {
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
                // `ladder.rs`'s `contains_pending_mvar` does: metadata and
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
            // oracle: `:304-310` — the arm runs under `mvarId.withContext`
            // (`:305`), unlike the `.typeClass` arm above whose
            // `instantiate_mvars` consults no `lctx`. A `.coe` mvar
            // registered inside a binder carries `e` as a free variable
            // of that binder, so `inferType e` needs the mvar's own
            // local context reinstalled — the binder has closed by the
            // time the reporter runs.
            SyntheticMVarKind::Coe { expected_type, e } => {
                self.with_mvar_local_context(mvar_id, |elab| {
                    let got = elab.mctx.infer_type(e)?;
                    Err(ElabError::StuckCoercion {
                        expected: expected_type,
                        got,
                    })
                })
            }
            // oracle: `SyntheticMVars.lean:311-315`'s `.tactic` arm —
            // reachable only once a real `by`/tactic-framework evaluator
            // occupies rung 5 (`ladder.rs`) and can answer `false` for a
            // genuinely stuck tactic; today rung 5 always errors before
            // this step could see the mvar (`ladder.rs`'s own `Tactic`
            // arm doc). Kept, not collapsed to `unreachable!` like the
            // `Postponed` arm below: unlike a postponed mvar (which the
            // oracle itself asserts can never reach here), a stuck
            // `.tactic` mvar genuinely CAN reach this arm once the later
            // M4 slice lands — this branch is dead FOR NOW, not
            // impossible BY CONSTRUCTION.
            SyntheticMVarKind::Tactic { param_name } => Err(ElabError::UnsupportedSyntax(
                super::state::tactic_seam_message(param_name.as_deref()),
            )),
            // oracle: `| _ => unreachable!` (:316) — `.postponed` never
            // reaches the reporter, because a postponed mvar that could
            // not be resumed has already raised from `resume_postponed`.
            //
            // The message names an INTERNAL INVARIANT, not a slice. It
            // carried "M4b-3 P2a invariant" until this fix wave: under
            // this crate's named-seam discipline an `UnsupportedSyntax`
            // naming a slice reads as "that slice owes an
            // implementation", and P2a is complete — it shipped the
            // `resume_postponed` path that makes this arm unreachable,
            // so it owes nothing here. Retargeting at a later slice
            // would have been a second false claim. Same rewording, and
            // the same reason, as `builtin::lit::inst_mvar_id` and
            // `synthetic::default_inst::mvar_id_of` (task 8).
            SyntheticMVarKind::Postponed { .. } => Err(ElabError::UnsupportedSyntax(
                "internal invariant: a postponed mvar reached the stuck reporter \
                 (synthetic::report — not a deferred construct)"
                    .to_string(),
            )),
        }
    }
}
