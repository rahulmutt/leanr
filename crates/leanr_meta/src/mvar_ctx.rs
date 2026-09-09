//! The metavariable context: declarations and assignments.
//!
//! oracle: `Lean.MetavarContext` (src/Lean/MetavarContext.lean),
//! toolchain leanprover/lean4:v4.33.0-rc1.
//!
//! This lives in `leanr_meta`, not `leanr_kernel`: the kernel's
//! `ExprNode` already carries an `MVar` variant and the `hasExprMVar`
//! cached bit, but the kernel never meets an mvar in a checked term and
//! must not grow the machinery for assigning them (AGENTS.md: the TCB
//! stays minimal).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use leanr_kernel::bank::{ExprId, LevelId, NameId};

use crate::local_snapshot::LocalCtxSnapshot;
use crate::MetaError;

/// A metavariable's identity. Newtype over `NameId` so it cannot be
/// confused with an fvar id, which is also a `NameId`.
///
/// Only derives what `NameId` itself derives (`Debug, Clone, Copy,
/// PartialEq, Eq, Hash`) — `NameId` does not implement `Ord`, so this
/// type cannot either.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MVarId(pub NameId);

/// A level metavariable's identity. Newtype over `NameId`, mirroring
/// `MVarId`; cannot be confused with an expr mvar. oracle:
/// `Lean.LMVarId`. No `Ord` (NameId has none).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LMVarId(pub NameId);

/// oracle: `MetavarKind`. `SyntheticOpaque` must never be assigned by
/// unification — only by the elaborator that created it (e.g. a tactic
/// block or a join point). Unification treating it as `Natural` would
/// silently solve goals the user was meant to solve.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MVarKind {
    Natural,
    Synthetic,
    SyntheticOpaque,
}

/// oracle: `MetavarDecl` (`MetavarContext.lean:305-311`). `lctx` is the
/// local context the mvar was created in — part of the declaration, not
/// ambient state, because an mvar may only be assigned a term whose free
/// variables it can see (`ExprDefEq.lean:1060`).
///
/// The context is shared, not owned: every mvar minted at one binder
/// depth points at the same `LocalCtxSnapshot`.
///
/// No `Debug` derive: `LocalContext` has none.
pub struct MVarDecl {
    pub user_name: Option<NameId>,
    pub ty: ExprId,
    pub lctx: Arc<LocalCtxSnapshot>,
    pub kind: MVarKind,
}

/// oracle: `DelayedMetavarAssignment` (`MetavarContext.lean:335`).
///
/// `?id #[x_1, …, x_n] := ?mvar_id_pending` — read as: once
/// `mvar_id_pending` is assigned, `?id` applied to at least `n`
/// arguments becomes that value with `fvars` abstracted and the
/// arguments substituted in. `elimMVar` (`:1216-1228`) is this
/// crate's only producer: a `syntheticOpaque` metavariable must never
/// be assigned by anything but the elaborator that created it, so the
/// AUXILIARY metavariable is delayed-assigned back to the original
/// rather than the original being assigned outright.
///
/// No `Debug` derive would be a problem here — `ExprId` and `MVarId`
/// both have one — so it derives normally.
#[derive(Debug, Clone)]
pub struct DelayedMVarAssignment {
    pub fvars: Vec<ExprId>,
    pub mvar_id_pending: MVarId,
}

/// Declarations plus assignments.
///
/// No `Debug` derive: `MVarDecl` (a field's value type) has none, for
/// the same reason noted on `MVarDecl`.
#[derive(Default)]
pub struct MetavarContext {
    decls: HashMap<MVarId, MVarDecl>,
    assignments: HashMap<MVarId, ExprId>,
    level_decls: HashSet<LMVarId>,
    level_assignments: HashMap<LMVarId, LevelId>,
    d_assignment: HashMap<MVarId, DelayedMVarAssignment>,
}

impl MetavarContext {
    pub fn new() -> MetavarContext {
        MetavarContext::default()
    }

    /// Declare `id`. Returns the previous declaration if there was one
    /// (callers minting fresh ids should never see `Some`).
    pub fn declare(&mut self, id: MVarId, decl: MVarDecl) -> Option<MVarDecl> {
        self.decls.insert(id, decl)
    }

    pub fn decl(&self, id: MVarId) -> Option<&MVarDecl> {
        self.decls.get(&id)
    }

    pub fn is_assigned(&self, id: MVarId) -> bool {
        self.assignments.contains_key(&id)
    }

    pub fn assignment(&self, id: MVarId) -> Option<ExprId> {
        self.assignments.get(&id).copied()
    }

    /// Assign `id := val`.
    ///
    /// Refuses to reassign an already-assigned mvar: in Lean an
    /// assignment is permanent for the lifetime of the context, and
    /// silently overwriting one turns a unification bug into a wrong
    /// answer instead of an error. Refuses to assign an undeclared
    /// mvar for the same reason.
    ///
    /// The occurs check is NOT performed here — it is the caller's
    /// obligation, and arrives in plan 3 alongside unification (the
    /// first and only place that assigns). Callers differ in what they
    /// do on a positive result (some fail, some fall back to an
    /// approximation), so folding it into `assign` would force one
    /// policy on all of them.
    pub fn assign(&mut self, id: MVarId, val: ExprId) -> Result<(), MetaError> {
        if !self.decls.contains_key(&id) {
            return Err(MetaError::MVar(format!(
                "assign: metavariable {id:?} was never declared"
            )));
        }
        if self.assignments.contains_key(&id) {
            return Err(MetaError::MVar(format!(
                "assign: metavariable {id:?} is already assigned"
            )));
        }
        self.assignments.insert(id, val);
        Ok(())
    }

    /// Record that a level mvar exists. Levels carry no type or lctx,
    /// so unlike `declare` there is nothing else to store. oracle:
    /// fresh `lDepth` entry in `MetavarContext`.
    pub fn declare_level(&mut self, id: LMVarId) {
        self.level_decls.insert(id);
    }

    pub fn is_level_assigned(&self, id: LMVarId) -> bool {
        self.level_assignments.contains_key(&id)
    }

    pub fn level_assignment(&self, id: LMVarId) -> Option<LevelId> {
        self.level_assignments.get(&id).copied()
    }

    /// Assign `id := val`. Refuses an undeclared or already-assigned
    /// level mvar, for the same reason `assign` does: silent overwrite
    /// turns a unification bug into a wrong answer. The occurs check
    /// (`!u.occurs v`) is the caller's obligation in `level.rs`, not
    /// here — callers differ in what they do on a positive result.
    pub fn assign_level(&mut self, id: LMVarId, val: LevelId) -> Result<(), MetaError> {
        if !self.level_decls.contains(&id) {
            return Err(MetaError::MVar(format!(
                "assign_level: level metavariable {id:?} was never declared"
            )));
        }
        if self.level_assignments.contains_key(&id) {
            return Err(MetaError::MVar(format!(
                "assign_level: level metavariable {id:?} is already assigned"
            )));
        }
        self.level_assignments.insert(id, val);
        Ok(())
    }

    /// oracle: `assignDelayedMVar` (`MetavarContext.lean:543`).
    ///
    /// Refuses to redefine an existing delayed assignment, and refuses
    /// an undeclared metavariable, for the same reason `assign` does:
    /// in Lean an assignment is permanent for the lifetime of the
    /// context, and silently overwriting one turns a bug into a wrong
    /// answer instead of an error.
    pub fn assign_delayed(
        &mut self,
        id: MVarId,
        fvars: Vec<ExprId>,
        mvar_id_pending: MVarId,
    ) -> Result<(), MetaError> {
        if !self.decls.contains_key(&id) {
            return Err(MetaError::MVar(format!(
                "assign_delayed: metavariable {id:?} was never declared"
            )));
        }
        if self.d_assignment.contains_key(&id) {
            return Err(MetaError::MVar(format!(
                "assign_delayed: metavariable {id:?} is already delayed-assigned"
            )));
        }
        self.d_assignment.insert(
            id,
            DelayedMVarAssignment {
                fvars,
                mvar_id_pending,
            },
        );
        Ok(())
    }

    /// oracle: `getDelayedMVarAssignment?` (`:425-426`).
    pub fn delayed_assignment(&self, id: MVarId) -> Option<&DelayedMVarAssignment> {
        self.d_assignment.get(&id)
    }

    /// oracle: `MVarId.isDelayedAssigned` (`:449-450`).
    pub fn is_delayed_assigned(&self, id: MVarId) -> bool {
        self.d_assignment.contains_key(&id)
    }

    /// Snapshot/restore support for `checkpointDefEq` (plan 3). Clones
    /// the expr, level, and delayed-assignment maps. Declarations are not
    /// snapshotted (an mvar, once declared, stays declared even across a
    /// failed trial — a rolled-back trial leaves the aux mvar declared but
    /// no longer delayed-assigned).
    pub(crate) fn snapshot_assignments(
        &self,
    ) -> (
        HashMap<MVarId, ExprId>,
        HashMap<LMVarId, LevelId>,
        HashMap<MVarId, DelayedMVarAssignment>,
    ) {
        (
            self.assignments.clone(),
            self.level_assignments.clone(),
            self.d_assignment.clone(),
        )
    }
    pub(crate) fn restore_assignments(
        &mut self,
        expr: HashMap<MVarId, ExprId>,
        level: HashMap<LMVarId, LevelId>,
        delayed: HashMap<MVarId, DelayedMVarAssignment>,
    ) {
        self.assignments = expr;
        self.level_assignments = level;
        self.d_assignment = delayed;
    }
}

#[cfg(test)]
mod tests {
    use super::{MVarDecl, MVarId, MVarKind, MetavarContext};
    use crate::local_snapshot::LocalCtxSnapshot;
    use leanr_kernel::bank::Store;

    fn mk(store: &mut Store, n: &str) -> MVarId {
        let base = store.intern_str(None, n).expect("intern");
        let name = store.name_str(None, None, base).expect("name");
        MVarId(name)
    }

    fn decl(ty: leanr_kernel::bank::ExprId) -> MVarDecl {
        MVarDecl {
            user_name: None,
            ty,
            lctx: LocalCtxSnapshot::empty(),
            kind: MVarKind::Natural,
        }
    }

    // `expr_mvar` takes `Option<NameId>` (an mvar name may be anonymous),
    // so `MVarId`'s inner id is wrapped at the call site.
    fn mvar_expr(store: &mut Store, id: MVarId) -> leanr_kernel::bank::ExprId {
        store.expr_mvar(None, Some(id.0)).expect("mvar")
    }

    fn sort0(store: &mut Store) -> leanr_kernel::bank::ExprId {
        let z = store.level_zero(None).expect("level");
        store.expr_sort(None, z).expect("sort")
    }

    #[test]
    fn declare_then_read_back() {
        let mut store = Store::persistent();
        let ty = sort0(&mut store);
        let id = mk(&mut store, "m1");
        let mut mctx = MetavarContext::new();
        assert!(mctx.decl(id).is_none());
        assert!(mctx.declare(id, decl(ty)).is_none());
        assert_eq!(mctx.decl(id).expect("declared").ty, ty);
        assert!(!mctx.is_assigned(id));
    }

    #[test]
    fn assign_then_read_back() {
        let mut store = Store::persistent();
        let ty = sort0(&mut store);
        let id = mk(&mut store, "m1");
        let mut mctx = MetavarContext::new();
        mctx.declare(id, decl(ty));
        mctx.assign(id, ty).expect("assign");
        assert!(mctx.is_assigned(id));
        assert_eq!(mctx.assignment(id), Some(ty));
    }

    // Reassignment must ERROR, not overwrite. Silently overwriting turns
    // a unification bug into a wrong answer instead of a failure.
    #[test]
    fn reassignment_is_rejected() {
        let mut store = Store::persistent();
        let ty = sort0(&mut store);
        let id = mk(&mut store, "m1");
        let mut mctx = MetavarContext::new();
        mctx.declare(id, decl(ty));
        mctx.assign(id, ty).expect("first assign");
        assert!(mctx.assign(id, ty).is_err());
    }

    #[test]
    fn assigning_an_undeclared_mvar_is_rejected() {
        let mut store = Store::persistent();
        let ty = sort0(&mut store);
        let id = mk(&mut store, "ghost");
        let mut mctx = MetavarContext::new();
        assert!(mctx.assign(id, ty).is_err());
    }

    // An mvar may be assigned a term that mentions another mvar; the
    // context stores it verbatim and does not interpret it. (The occurs
    // check that would reject a CYCLE here arrives in plan 3, where
    // unification first needs it.)
    #[test]
    fn an_assignment_may_mention_another_mvar() {
        let mut store = Store::persistent();
        let ty = sort0(&mut store);
        let a = mk(&mut store, "a");
        let b = mk(&mut store, "b");
        let ma = mvar_expr(&mut store, a);

        let mut mctx = MetavarContext::new();
        mctx.declare(b, decl(ty));
        mctx.assign(b, ma).expect("assign b := ?a");

        assert_eq!(mctx.assignment(b), Some(ma));
        assert!(!mctx.is_assigned(a));
    }

    fn lmk(store: &mut Store, n: &str) -> super::LMVarId {
        let base = store.intern_str(None, n).expect("intern");
        let name = store.name_str(None, None, base).expect("name");
        super::LMVarId(name)
    }

    #[test]
    fn declare_then_assign_a_level_mvar() {
        let mut store = Store::persistent();
        let zero = store.level_zero(None).expect("level zero");
        let id = lmk(&mut store, "u");
        let mut mctx = MetavarContext::new();
        assert!(!mctx.is_level_assigned(id));
        mctx.declare_level(id);
        assert_eq!(mctx.level_assignment(id), None);
        mctx.assign_level(id, zero).expect("assign level");
        assert!(mctx.is_level_assigned(id));
        assert_eq!(mctx.level_assignment(id), Some(zero));
    }

    #[test]
    fn reassigning_a_level_mvar_is_rejected() {
        let mut store = Store::persistent();
        let zero = store.level_zero(None).expect("level zero");
        let id = lmk(&mut store, "u");
        let mut mctx = MetavarContext::new();
        mctx.declare_level(id);
        mctx.assign_level(id, zero).expect("first");
        assert!(mctx.assign_level(id, zero).is_err());
    }

    #[test]
    fn assigning_an_undeclared_level_mvar_is_rejected() {
        let mut store = Store::persistent();
        let zero = store.level_zero(None).expect("level zero");
        let id = lmk(&mut store, "ghost");
        let mut mctx = MetavarContext::new();
        assert!(mctx.assign_level(id, zero).is_err());
    }

    #[test]
    fn delayed_assignment_round_trips_and_refuses_a_second_one() {
        use crate::test_support::{fresh_mvar, with_ctx};

        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            let (_, new_id) = fresh_mvar(ctx, sort0);
            let (_, pending) = fresh_mvar(ctx, sort0);

            assert!(!ctx.mctx().is_delayed_assigned(new_id));
            ctx.mctx_mut()
                .assign_delayed(new_id, vec![sort0], pending)
                .expect("first delayed assignment");
            assert!(ctx.mctx().is_delayed_assigned(new_id));

            let d = ctx.mctx().delayed_assignment(new_id).expect("round-trips");
            assert_eq!(d.fvars, vec![sort0]);
            assert_eq!(d.mvar_id_pending, pending);

            assert!(
                ctx.mctx_mut()
                    .assign_delayed(new_id, vec![], pending)
                    .is_err(),
                "a delayed assignment is permanent, exactly like an ordinary \
                 one — silently overwriting turns a bug into a wrong answer"
            );
        });
    }

    #[test]
    fn get_delayed_mvar_root_follows_a_chain() {
        use crate::test_support::{fresh_mvar, with_ctx};

        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            let (_, a) = fresh_mvar(ctx, sort0);
            let (_, b) = fresh_mvar(ctx, sort0);
            let (_, c) = fresh_mvar(ctx, sort0);

            ctx.mctx_mut().assign_delayed(a, vec![], b).expect("a := b");
            ctx.mctx_mut().assign_delayed(b, vec![], c).expect("b := c");

            assert_eq!(ctx.get_delayed_mvar_root(a), c);
            assert_eq!(ctx.get_delayed_mvar_root(c), c, "a root is its own root");
        });
    }

    #[test]
    fn checkpoint_rollback_undoes_delayed_assignment() {
        use crate::test_support::{fresh_mvar, with_ctx};

        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            let (_, a) = fresh_mvar(ctx, sort0);
            let (_, b) = fresh_mvar(ctx, sort0);
            let (_, pre_assigned) = fresh_mvar(ctx, sort0);

            // Assign one delayed BEFORE checkpoint
            ctx.mctx_mut()
                .assign_delayed(pre_assigned, vec![], b)
                .expect("pre-checkpoint assign");
            assert!(ctx.mctx().is_delayed_assigned(pre_assigned));

            // Take a checkpoint with pre_assigned already delayed-assigned
            let snap = ctx.checkpoint();

            // Inside the trial, assign a second one
            ctx.mctx_mut()
                .assign_delayed(a, vec![], b)
                .expect("assign inside trial");
            assert!(ctx.mctx().is_delayed_assigned(a));

            // Rollback the trial
            ctx.rollback(snap);

            // After rollback, the pre-checkpoint assignment is PRESERVED
            assert!(ctx.mctx().is_delayed_assigned(pre_assigned));

            // But the in-trial assignment is undone
            assert!(!ctx.mctx().is_delayed_assigned(a));

            // And we can assign it now (the permanence guard is not left tripped)
            ctx.mctx_mut()
                .assign_delayed(a, vec![], b)
                .expect("assign after rollback must succeed");
            assert!(ctx.mctx().is_delayed_assigned(a));
        });
    }
}
