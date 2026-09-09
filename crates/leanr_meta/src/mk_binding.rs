//! `MkBinding` — eliminating metavariable dependencies before
//! abstraction.
//!
//! oracle: `Lean.MetavarContext.MkBinding`
//! (`src/Lean/MetavarContext.lean:938-1349`) plus `DependsOn`
//! (`:660-725`), toolchain `leanprover/lean4:v4.33.0-rc1`.
//!
//! The oracle's `mkBinding` never abstracts directly: it abstracts
//! through `abstractRange`, which runs `elimMVarDeps` first. An
//! unassigned metavariable whose own local context contains the free
//! variables being abstracted is replaced by a fresh auxiliary
//! metavariable APPLIED to them, so the occurrence abstracts like any
//! other argument and the original stays assignable in its own context.
//! Without it, such a metavariable assigned LATER — the elaborator's
//! synthetic-metavariable fixpoint resuming a postponed goal after the
//! binder has closed — contributes an unabstracted `fvar` where the
//! oracle emits a `bvar`.
//!
//! Its own file, not part of `metactx.rs`, so a reviewer can diff this
//! transcription against the oracle's namespace in one pass;
//! `metactx.rs` is the crate's accessor surface and is already the
//! second-largest file in it.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};

use crate::{MetaCtx, MetaError};

impl<'e> MetaCtx<'e> {
    /// The `FVarId` behind an `Expr::fvar`, or `None` for anything
    /// else. `xs` and `to_revert` are carried as `Expr::fvar`
    /// references throughout (the oracle carries `Array Expr` too), so
    /// this is the one place the id is read out.
    #[allow(dead_code)]
    pub(crate) fn fvar_id_of(&self, e: ExprId) -> Option<NameId> {
        match self.node(e) {
            Node::FVar { id } => id,
            _ => None,
        }
    }

    /// oracle: `DependsOn` (`MetavarContext.lean:660-725`) reached via
    /// `findExprDependsOn` (`:733`) — does `e` depend on any free
    /// variable in `pf`?
    ///
    /// Two ways to depend, and the second is the one worth stating:
    ///
    /// 1. **Syntactically** — `e` mentions the fvar.
    /// 2. **May-depend** — `e` mentions an unassigned METAVARIABLE
    ///    whose own declared local context contains the fvar
    ///    (`:700-716`). That metavariable may later be assigned a term
    ///    that mentions it, so a dependency that does not exist yet
    ///    still counts. Dropping this case makes
    ///    `collect_forward_deps` miss a forward dependency, which mints
    ///    the auxiliary metavariable at a context that is still too
    ///    permissive — the bug this slice exists to remove, reappearing
    ///    one level down.
    ///
    /// An ASSIGNED metavariable is followed to its value instead
    /// (`:697-699`): its assignment is what the term really is.
    #[allow(dead_code)]
    pub(crate) fn depends_on(&mut self, e: ExprId, pf: &[NameId]) -> Result<bool, MetaError> {
        if pf.is_empty() {
            return Ok(false);
        }
        // Fast path, oracle `:686-689`: a term with neither an fvar nor
        // an expr mvar cannot depend on a free variable by either route.
        let d = self.data(e);
        if !d.has_fvar() && !d.has_expr_mvar() {
            return Ok(false);
        }
        self.step()?;
        self.guarded(|ctx| ctx.depends_on_body(e, pf))
    }

    fn depends_on_body(&mut self, e: ExprId, pf: &[NameId]) -> Result<bool, MetaError> {
        match self.node(e) {
            Node::FVar { id: Some(id) } => Ok(pf.contains(&id)),
            Node::FVar { id: None } => Ok(false),
            Node::MVar { id: Some(id) } => {
                let mid = crate::MVarId(id);
                if let Some(v) = self.mctx.assignment(mid) {
                    return self.depends_on(v, pf);
                }
                let Some(lctx) = self.mvar_lctx(mid) else {
                    return Ok(false);
                };
                Ok(pf.iter().any(|f| lctx.lctx().get(*f).is_some()))
            }
            Node::MVar { id: None } => Ok(false),
            Node::App { f, arg } => Ok(self.depends_on(f, pf)? || self.depends_on(arg, pf)?),
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => Ok(self.depends_on(binder_type, pf)? || self.depends_on(body, pf)?),
            Node::LetE {
                ty, value, body, ..
            } => Ok(self.depends_on(ty, pf)?
                || self.depends_on(value, pf)?
                || self.depends_on(body, pf)?),
            Node::MData { expr, .. } => self.depends_on(expr, pf),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                self.depends_on(structure, pf)
            }
            Node::BVar { .. }
            | Node::BVarBig { .. }
            | Node::Sort { .. }
            | Node::Const { .. }
            | Node::LitNat { .. }
            | Node::LitStr { .. } => Ok(false),
        }
    }

    /// oracle: `findLocalDeclDependsOn` (`:744`) / `localDeclDependsOn`
    /// (`:767`) — does a local declaration depend on any fvar in `pf`?
    /// Its type always counts; its value counts when it has one.
    ///
    /// The oracle's `generalizeNondepLet` parameter is NOT modelled:
    /// leanr's `LocalDecl` carries no `nondep` bit at all
    /// (`leanr_kernel/src/local_ctx.rs:37-43` — `mk_let_binding` takes
    /// it as a caller argument instead), so there is nothing to branch
    /// on. This is the same missing bit that makes `mk_aux_mvar_type`
    /// refuse an ldecl in `to_revert`; see that function's doc.
    #[allow(dead_code)]
    pub(crate) fn local_decl_depends_on(
        &mut self,
        ty: ExprId,
        value: Option<ExprId>,
        pf: &[NameId],
    ) -> Result<bool, MetaError> {
        if self.depends_on(ty, pf)? {
            return Ok(true);
        }
        match value {
            Some(v) => self.depends_on(v, pf),
            None => Ok(false),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::{fresh_fvar, fresh_mvar, with_ctx};
    use leanr_kernel::bank::terms::Node;

    fn fvar_id(ctx: &crate::MetaCtx, e: leanr_kernel::bank::ExprId) -> leanr_kernel::bank::NameId {
        match ctx.node(e) {
            Node::FVar { id: Some(id) } => id,
            other => panic!("expected fvar, got {other:?}"),
        }
    }

    /// TDD RED/GREEN for plan task 3, the SYNTACTIC half.
    #[test]
    fn depends_on_sees_a_direct_fvar_occurrence() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let b = fresh_fvar(ctx, sort0, "b");
            let ia = fvar_id(ctx, a);
            let ib = fvar_id(ctx, b);

            let app = ctx.scratch.expr_app(base, a, sort0).expect("app");

            assert!(ctx.depends_on(app, &[ia]).expect("depends_on"));
            assert!(!ctx.depends_on(app, &[ib]).expect("depends_on"));
            ctx.lctx_restore(cp);
        });
    }

    /// TDD RED/GREEN for plan task 3, the MAY-DEPEND half — the case
    /// that makes this more than a syntactic fvar scan. `e` mentions
    /// `?m` and nothing else; `?m`'s own declared context contains `a`;
    /// so `e` may depend on `a`, because `?m` may later be assigned a
    /// term that mentions it.
    #[test]
    fn depends_on_sees_an_mvar_whose_own_context_holds_the_fvar() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let ia = fvar_id(ctx, a);
            // `?m` is minted HERE, so its declared context contains `a`.
            let (m, _) = fresh_mvar_in_ambient_ctx(ctx, sort0);
            ctx.lctx_restore(cp);

            // `m` mentions no fvar at all, syntactically.
            assert!(
                ctx.depends_on(m, &[ia]).expect("depends_on"),
                "a bare mvar whose own local context contains `a` MAY depend on \
                 `a` — dropping this case is what makes collect_forward_deps \
                 miss a forward dependency and mint an aux mvar at a context \
                 that is still too permissive"
            );
        });
    }

    /// `fresh_mvar` mints with an EMPTY declared context, which is
    /// exactly wrong for the may-depend test above. This mints at the
    /// AMBIENT one, the way production code does.
    fn fresh_mvar_in_ambient_ctx(
        ctx: &mut crate::MetaCtx,
        ty: leanr_kernel::bank::ExprId,
    ) -> (leanr_kernel::bank::ExprId, crate::MVarId) {
        ctx.mk_aux_mvar(ty)
            .expect("mk_aux_mvar mints at current_lctx")
    }

    /// An ASSIGNED metavariable is its value, not its declaration:
    /// `?m := a` depends on `a` even if `?m`'s own context does not
    /// mention it.
    #[test]
    fn depends_on_follows_an_assigned_mvar_to_its_value() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            // `?m` is minted OUTSIDE the binder, so its own context is empty.
            let (m, mid) = fresh_mvar(ctx, sort0);
            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let ia = fvar_id(ctx, a);
            ctx.mctx_mut().assign(mid, a).expect("assign");

            assert!(
                ctx.depends_on(m, &[ia]).expect("depends_on"),
                "an assigned mvar is followed to its value"
            );
            ctx.lctx_restore(cp);
        });
    }
}
