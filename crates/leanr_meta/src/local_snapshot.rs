//! The ambient local context as a shareable value.
//!
//! oracle: `MetavarDecl.lctx` (`MetavarContext.lean:305-311`) — "The
//! local context containing the free variables that the mvar is
//! permitted to depend upon". Lean's `LocalContext` is persistent, so
//! the oracle stores one per metavariable for free; leanr's is a
//! mutate-in-place stack, so a stored context is a copy, and this module
//! is where that copy is made and shared.
//!
//! Two halves travel together because `MetaCtx` keeps a `local_names`
//! index parallel to `lctx`'s decl list and asserts their lockstep on
//! every checkpoint, restore and push. Installing one without the other
//! trips that assertion immediately.

use std::sync::Arc;

use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::LocalContext;

/// A copy of the ambient local context plus `MetaCtx::local_names`.
///
/// Shared behind an `Arc`: every metavariable minted at one binder depth
/// points at the same snapshot, so instance search — which mints one
/// metavariable per candidate-telescope binder — pays one copy per
/// scope, not one per metavariable.
pub struct LocalCtxSnapshot {
    lctx: LocalContext,
    local_names: Vec<(Option<NameId>, ExprId)>,
}

impl LocalCtxSnapshot {
    pub(crate) fn new(lctx: LocalContext, local_names: Vec<(Option<NameId>, ExprId)>) -> Self {
        debug_assert_eq!(
            local_names.len(),
            lctx.save(),
            "local_names/lctx lockstep invariant violated in a snapshot"
        );
        LocalCtxSnapshot { lctx, local_names }
    }

    /// The empty context — what a metavariable minted outside any binder
    /// carries, and what every `#[cfg(test)]` literal that does not care
    /// about scoping uses. A fresh `Arc` each call: an empty `Vec` and an
    /// empty `HashMap` allocate nothing, so there is no singleton to
    /// justify.
    pub fn empty() -> Arc<LocalCtxSnapshot> {
        Arc::new(LocalCtxSnapshot {
            lctx: LocalContext::default(),
            local_names: Vec::new(),
        })
    }

    /// The context itself — read by `check_assignment_scope_body`'s
    /// `FVar` arm via `MVarDecl::lctx`.
    pub fn lctx(&self) -> &LocalContext {
        &self.lctx
    }

    pub fn depth(&self) -> usize {
        self.local_names.len()
    }

    /// Both halves at once — `MetaCtx::install_lctx`'s only caller. The
    /// two fields swap into `self.lctx`/`self.local_names` together
    /// because they are asserted to stay in lockstep at every checkpoint,
    /// restore and push (this struct's own doc comment); an accessor
    /// that returned only one half would let a caller violate that
    /// invariant by construction.
    pub(crate) fn parts(&self) -> (&LocalContext, &[(Option<NameId>, ExprId)]) {
        (&self.lctx, &self.local_names)
    }

    /// The declared fvars in DECLARATION ORDER, paired with their user
    /// names — the enumeration `collect_forward_deps`
    /// (`MetavarContext.lean:1037-1062`) needs and that
    /// `leanr_kernel::LocalContext` does not expose (its `decls`/`index`
    /// are module-private; the public surface is `get(fvar_id)` by id and
    /// `save`/`restore` by count). Positionally parallel to the
    /// `LocalContext`'s own decl list, by this struct's lockstep
    /// invariant, so an index into this slice is an index into that list.
    pub(crate) fn entries(&self) -> &[(Option<NameId>, ExprId)] {
        &self.local_names
    }

    /// oracle: `reduceLocalContext` (`MetavarContext.lean:1065-1067`) —
    /// this context with every fvar in `to_remove` erased. Each entry is
    /// the fvar's `Expr::fvar` reference paired with its `FVarId`:
    /// `LocalContext::erase` is `NameId`-keyed already, so the second
    /// half drives it directly; the first half exists only so the
    /// caller (which has `Store` access) can hand this function a
    /// decode closure keyed the same way `to_remove` itself is.
    ///
    /// The oracle compares by `FVarId` (`decl.fvarId == x.fvarId!`,
    /// `MetavarContext.lean:1057-1058`); this filters `local_names` by
    /// `NameId` too, via `fvar_id_of`, rather than comparing its
    /// `ExprId` entries against `to_remove`'s `ExprId` halves directly.
    /// `LocalCtxSnapshot` has no `Store` reference of its own, so it
    /// cannot decode an `ExprId` into a `NameId` itself — `fvar_id_of`
    /// is supplied by the caller (`MetaCtx::reduce_local_context`),
    /// which has one. Comparing by `ExprId` would coincide with `NameId`
    /// today only because `expr_fvar` interns canonically against
    /// `Some(self.view.store)` everywhere; making the basis uniform with
    /// `NameId` removes a silent-failure mode (entries interned through
    /// a different store generation compare unequal by `ExprId` while
    /// denoting the same fvar) rather than fixing an observed bug —
    /// behavior is unchanged.
    ///
    /// Both halves are filtered together, because `LocalCtxSnapshot::new`
    /// debug-asserts they are in lockstep and every reader of one is
    /// paired with a reader of the other.
    pub(crate) fn reduced(
        &self,
        to_remove: &[(ExprId, NameId)],
        fvar_id_of: impl Fn(ExprId) -> Option<NameId>,
    ) -> LocalCtxSnapshot {
        let mut lctx = self.lctx.clone();
        for (_, fvar_id) in to_remove {
            lctx.erase(*fvar_id);
        }
        let local_names = self
            .local_names
            .iter()
            .filter(|(_, f)| {
                !fvar_id_of(*f).is_some_and(|id| to_remove.iter().any(|(_, rid)| *rid == id))
            })
            .cloned()
            .collect();
        LocalCtxSnapshot::new(lctx, local_names)
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::{fresh_fvar, with_ctx};
    use leanr_kernel::bank::terms::Node;

    /// TDD RED/GREEN for plan task 2. `reduced` must drop the named
    /// fvars from BOTH halves — the `LocalContext` and the parallel
    /// `local_names` index — because `LocalCtxSnapshot::new`'s
    /// `debug_assert` requires them to stay in lockstep, and because
    /// `check_assignment_scope_body` reads `lctx()` while
    /// `lctx_lookup_by_name` reads the other half.
    #[test]
    fn reduced_drops_the_named_fvars_from_both_halves() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let b = fresh_fvar(ctx, sort0, "b");
            let c = fresh_fvar(ctx, sort0, "c");
            let snap = ctx.current_lctx();
            ctx.lctx_restore(cp);

            let id_of = |ctx: &crate::MetaCtx, e| match ctx.node(e) {
                Node::FVar { id: Some(id) } => id,
                other => panic!("expected fvar, got {other:?}"),
            };
            let ib = id_of(ctx, b);

            assert_eq!(snap.entries().len(), 3, "the full context has three decls");

            let reduced = snap.reduced(&[(b, ib)], |f| match ctx.node(f) {
                Node::FVar { id } => id,
                _ => None,
            });

            assert_eq!(reduced.entries().len(), 2, "local_names lost exactly one");
            assert!(
                reduced.lctx().get(ib).is_none(),
                "lctx lost the erased fvar"
            );
            assert!(
                reduced.entries().iter().all(|(_, f)| *f != b),
                "local_names lost the erased fvar too — dropping it from lctx \
                 alone leaves the two halves out of lockstep, which \
                 LocalCtxSnapshot::new debug_asserts against"
            );
            assert_eq!(
                reduced
                    .entries()
                    .iter()
                    .map(|(_, f)| *f)
                    .collect::<Vec<_>>(),
                vec![a, c],
                "declaration order is preserved for the survivors"
            );
        });
    }
}
