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

use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_kernel::LocalContext;

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

/// oracle: `MetavarDecl`. `lctx` is the local context the mvar was
/// created in — it is part of the declaration, not ambient state,
/// because an mvar may only be assigned a term whose free variables it
/// can see.
///
/// No `Debug`/`Clone` derive: `LocalContext` (a foreign type from
/// `leanr_kernel`) implements neither, and the orphan rule forbids
/// adding either impl for it here.
pub struct MVarDecl {
    pub user_name: Option<NameId>,
    pub ty: ExprId,
    pub lctx: LocalContext,
    pub kind: MVarKind,
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
}

#[cfg(test)]
mod tests {
    use super::{MVarDecl, MVarId, MVarKind, MetavarContext};
    use leanr_kernel::bank::Store;
    use leanr_kernel::LocalContext;

    fn mk(store: &mut Store, n: &str) -> MVarId {
        let base = store.intern_str(None, n).expect("intern");
        let name = store.name_str(None, None, base).expect("name");
        MVarId(name)
    }

    fn decl(ty: leanr_kernel::bank::ExprId) -> MVarDecl {
        MVarDecl {
            user_name: None,
            ty,
            lctx: LocalContext::default(),
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
}
