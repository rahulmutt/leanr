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

use std::sync::Arc;

use leanr_kernel::abstract_fvars;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};

use crate::local_snapshot::LocalCtxSnapshot;
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

    /// oracle: `getInScope` (`:1070-1077`) — the members of `xs` that
    /// `lctx` actually declares. Anything else is a binder this
    /// metavariable never saw, and reverting it would be reverting a
    /// variable that is not in its context.
    #[allow(dead_code)]
    pub(crate) fn get_in_scope(&self, lctx: &LocalCtxSnapshot, xs: &[ExprId]) -> Vec<ExprId> {
        xs.iter()
            .filter(|x| {
                self.fvar_id_of(**x)
                    .is_some_and(|id| lctx.lctx().get(id).is_some())
            })
            .copied()
            .collect()
    }

    /// oracle: `collectForwardDeps` (`:1037-1062`) — close `to_revert`
    /// under forward dependencies, walking `lctx` in declaration order
    /// from the earliest reverted declaration onward. A later declaration
    /// joins when it IS one of `to_revert`, or when it depends on
    /// something already collected.
    ///
    /// The oracle's `preserveOrder` branch (`:1042-1050`, which can throw
    /// `Exception.revertFailure`) is NOT modelled: `preserveOrder` is a
    /// tactic-framework flag and leanr has no producer for it — the only
    /// caller here passes the `false` case. Named in the design spec's
    /// § What this ships.
    #[allow(dead_code)]
    pub(crate) fn collect_forward_deps(
        &mut self,
        lctx: &LocalCtxSnapshot,
        to_revert: Vec<ExprId>,
    ) -> Result<Vec<ExprId>, MetaError> {
        if to_revert.is_empty() {
            return Ok(to_revert);
        }
        let entries: Vec<ExprId> = lctx.entries().iter().map(|(_, f)| *f).collect();
        // oracle `getLocalDeclWithSmallestIdx` (`:1052`): start at the
        // earliest declaration that is being reverted. Everything before it
        // is declared earlier than anything reverted, so it cannot depend
        // on one.
        let start = entries
            .iter()
            .position(|f| to_revert.contains(f))
            .unwrap_or(entries.len());

        let mut collected: Vec<ExprId> = Vec::with_capacity(to_revert.len());
        for fvar in entries.into_iter().skip(start) {
            if to_revert.contains(&fvar) {
                collected.push(fvar);
                continue;
            }
            let Some(id) = self.fvar_id_of(fvar) else {
                continue;
            };
            let Some(decl) = lctx.lctx().get(id) else {
                continue;
            };
            let (ty, value) = (decl.ty, decl.value);
            let pf: Vec<NameId> = collected
                .iter()
                .filter_map(|f| self.fvar_id_of(*f))
                .collect();
            if self.local_decl_depends_on(ty, value, &pf)? {
                collected.push(fvar);
            }
        }
        Ok(collected)
    }

    /// oracle: `reduceLocalContext` (`:1065-1067`) — `lctx` with every
    /// fvar in `to_revert` erased. This is the context the auxiliary
    /// metavariable is minted at, and erasing is the whole point: leaving
    /// the reverted fvars in place would let the new metavariable be
    /// assigned the very variable the abstraction is removing, which is
    /// this slice's own bug reappearing one level down.
    #[allow(dead_code)]
    pub(crate) fn reduce_local_context(
        &self,
        lctx: &LocalCtxSnapshot,
        to_revert: &[ExprId],
    ) -> Result<Arc<LocalCtxSnapshot>, MetaError> {
        let pairs: Vec<(ExprId, NameId)> = to_revert
            .iter()
            .filter_map(|f| self.fvar_id_of(*f).map(|id| (*f, id)))
            .collect();
        Ok(Arc::new(lctx.reduced(&pairs)))
    }

    /// oracle: `mkMVarApp` (`:1090-1097`) — `mvar` applied to `xs`, first
    /// declared innermost, so that after abstraction the arguments read
    /// `?new #(n-1) … #0`.
    ///
    /// The oracle's two kind branches (`:1094-1097`) differ only in
    /// whether a LET-bound fvar is applied. Under this port's ldecl
    /// refusal (see `mk_aux_mvar_type`) `xs` never contains one, so the
    /// branches coincide and the `syntheticOpaque` form — apply
    /// everything — is the one written.
    #[allow(dead_code)]
    pub(crate) fn mk_mvar_app(&mut self, mvar: ExprId, xs: &[ExprId]) -> Result<ExprId, MetaError> {
        let mut e = mvar;
        for x in xs {
            e = self.scratch.expr_app(Some(self.view.store), e, *x)?;
        }
        Ok(e)
    }

    /// oracle: `mkAuxMVarType` (`:1123-1168`) — the type of the auxiliary
    /// metavariable `elim_mvar` mints: the original's type abstracted
    /// over `xs` and wrapped in one `forall` per reverted entry,
    /// innermost last.
    ///
    /// **Let-declarations are REFUSED, not handled.** The oracle branches
    /// on `LocalDecl.ldecl (nondep := …)` (`:1131-1160`) and leanr's
    /// `LocalDecl` carries no `nondep` bit at all
    /// (`leanr_kernel/src/local_ctx.rs:37-43`; `mk_let_binding` takes it
    /// as a caller argument, `metactx.rs:653`), so both ldecl arms have
    /// no input. Writing one would be guessing, and a wrong `ExprId` is
    /// worse than a named refusal — the same judgement, for the same
    /// reason, as `mk_binding`'s existing
    /// `"let-decl fvar in a cdecl telescope"` (`metactx.rs:769-772`).
    ///
    /// The METAVARIABLE arm (`:1157-1163`) is transcribed: `xs` may carry
    /// a metavariable as a "may dependency" once `collect_forward_deps`
    /// has run, and the oracle wraps it in a `forall` over the
    /// metavariable's own type with `binderInfoForMVars` (default
    /// `.implicit`).
    ///
    /// The oracle's `kind` and `usedLetOnly` parameters are absent here
    /// because every arm that reads them is an ldecl arm (`:1140-1157`),
    /// and those refuse. Adding parameters no branch can consult would be
    /// surface without a producer.
    ///
    /// Both `abstract_fvars` calls below stand in for the oracle's
    /// `abstractRangeAux` (`:1165-1167`) — `abstract_range` does not
    /// exist until Task 9, which swaps these calls (Task 9 Step 6).
    #[allow(dead_code)]
    pub(crate) fn mk_aux_mvar_type(
        &mut self,
        lctx: &LocalCtxSnapshot,
        xs: &[ExprId],
        ty: ExprId,
    ) -> Result<ExprId, MetaError> {
        let mut e = abstract_fvars(self.scratch, Some(self.view.store), ty, xs, &mut self.guard)?;
        for i in (0..xs.len()).rev() {
            let x = xs[i];
            let (binder_name, binder_ty, binder_info) = match self.fvar_id_of(x) {
                Some(id) => {
                    let decl = lctx.lctx().get(id).ok_or_else(|| {
                        MetaError::Infer(
                            "mk_aux_mvar_type: fvar not declared in the mvar's context".into(),
                        )
                    })?;
                    if decl.value.is_some() {
                        return Err(MetaError::Infer(
                            "mk_aux_mvar_type: let-decl fvar in to_revert (leanr's LocalDecl \
                             carries no `nondep` bit, so the oracle's ldecl arms have no input)"
                                .into(),
                        ));
                    }
                    (decl.binder_name, decl.ty, decl.binder_info)
                }
                None => {
                    // oracle `:1157-1163` — a "may dependency" metavariable.
                    let Node::MVar { id: Some(n) } = self.node(x) else {
                        return Err(MetaError::Infer(
                            "mk_aux_mvar_type: to_revert entry is neither an fvar nor an mvar"
                                .into(),
                        ));
                    };
                    let decl = self.mctx.decl(crate::MVarId(n)).ok_or_else(|| {
                        MetaError::Infer("mk_aux_mvar_type: undeclared may-dependency mvar".into())
                    })?;
                    (decl.user_name, decl.ty, leanr_kernel::BinderInfo::Implicit)
                }
            };
            let binder_ty = abstract_fvars(
                self.scratch,
                Some(self.view.store),
                binder_ty,
                &xs[..i],
                &mut self.guard,
            )?;
            e = self.scratch.expr_forall(
                Some(self.view.store),
                binder_name,
                binder_ty,
                e,
                binder_info,
            )?;
        }
        Ok(e)
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

    /// TDD RED/GREEN for plan task 4. `get_in_scope` keeps only the
    /// members of `xs` that the metavariable's OWN context declares —
    /// oracle `:1070-1077`.
    #[test]
    fn get_in_scope_keeps_only_the_fvars_the_mvar_can_see() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            // Snapshot taken with `a` only — `b` comes later.
            let snap = ctx.current_lctx();
            let b = fresh_fvar(ctx, sort0, "b");
            ctx.lctx_restore(cp);

            let in_scope = ctx.get_in_scope(&snap, &[a, b]);
            assert_eq!(
                in_scope,
                vec![a],
                "only `a` is in the snapshot; keeping `b` would revert a binder \
                 the metavariable never saw"
            );
        });
    }

    /// `collect_forward_deps` closes `to_revert` under forward
    /// dependencies: `y : a` must join when `a` is reverted, or the
    /// auxiliary metavariable is minted at a context holding a
    /// declaration whose type mentions an erased fvar. Oracle `:1037-1062`.
    #[test]
    fn collect_forward_deps_pulls_in_a_dependent_later_decl() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            // `y : a` — its TYPE is the fvar `a`, so it depends on it.
            let y = fresh_fvar(ctx, a, "y");
            let snap = ctx.current_lctx();
            ctx.lctx_restore(cp);

            let closed = ctx
                .collect_forward_deps(&snap, vec![a])
                .expect("collect_forward_deps");
            assert_eq!(
                closed,
                vec![a, y],
                "y : a depends on a, so reverting a must revert y too, in \
                 declaration order"
            );
        });
    }

    /// `collect_forward_deps` must close TRANSITIVELY: a declaration
    /// depending on a declaration that was itself pulled in must also
    /// be pulled in. This test has a 3-level chain where `z : y` and `a`
    /// is reverted, so `y` joins because it depends on `a`, and `z`
    /// joins because `y` joined — not because `z` mentions `a` directly.
    /// This discriminates against a non-transitive implementation that
    /// computes dependencies against the frozen initial `to_revert`
    /// argument instead of the accumulating `collected` list. Such a bug
    /// would pass `collect_forward_deps_pulls_in_a_dependent_later_decl`
    /// (one level only) and all four Step-5 mutations (none touch this
    /// axis).
    #[test]
    fn collect_forward_deps_closes_transitively_through_a_chain() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let y = fresh_fvar(ctx, a, "y");
            // `z : y` — its TYPE is the fvar `y`, which itself was pulled
            // in because it depends on `a`.
            let z = fresh_fvar(ctx, y, "z");
            let snap = ctx.current_lctx();
            ctx.lctx_restore(cp);

            let closed = ctx
                .collect_forward_deps(&snap, vec![a])
                .expect("collect_forward_deps");
            assert_eq!(
                closed,
                vec![a, y, z],
                "z : y depends on y, and y depends on a, so reverting a \
                 must revert y and z. This is transitive closure: z joins \
                 ONLY because y joined, not because z mentions a directly."
            );
        });
    }

    /// `reduce_local_context` removes exactly `to_revert`. Oracle
    /// `:1065-1067`.
    #[test]
    fn reduce_local_context_removes_exactly_the_reverted_fvars() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let b = fresh_fvar(ctx, sort0, "b");
            let snap = ctx.current_lctx();
            ctx.lctx_restore(cp);

            let ia = fvar_id(ctx, a);
            let ib = fvar_id(ctx, b);
            let reduced = ctx
                .reduce_local_context(&snap, &[a])
                .expect("reduce_local_context");

            assert!(reduced.lctx().get(ia).is_none(), "a is erased");
            assert!(reduced.lctx().get(ib).is_some(), "b survives");
        });
    }

    /// `mk_mvar_app` applies the auxiliary metavariable to the reverted
    /// fvars, innermost LAST — the application order that makes
    /// `?new #0` come out right after abstraction. Oracle `:1090-1097`.
    #[test]
    fn mk_mvar_app_applies_the_fvars_in_declaration_order() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let b = fresh_fvar(ctx, sort0, "b");
            let (m, _) = fresh_mvar(ctx, sort0);
            ctx.lctx_restore(cp);

            let app = ctx.mk_mvar_app(m, &[a, b]).expect("mk_mvar_app");
            // Expect `((m a) b)`: the LAST-declared fvar is the OUTERMOST
            // argument.
            match ctx.node(app) {
                Node::App { f, arg } => {
                    assert_eq!(arg, b, "the last fvar is the outermost argument");
                    match ctx.node(f) {
                        Node::App { f: inner, arg: a2 } => {
                            assert_eq!(a2, a);
                            assert_eq!(inner, m);
                        }
                        other => panic!("expected nested App, got {other:?}"),
                    }
                }
                other => panic!("expected App, got {other:?}"),
            }
        });
    }

    /// TDD RED/GREEN for plan task 8. `?m : Sort 0` reverted over
    /// `[a : Sort 0]` gets the type `∀ (a : Sort 0), Sort 0`.
    #[test]
    fn mk_aux_mvar_type_wraps_the_reverted_binders() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let snap = ctx.current_lctx();
            ctx.lctx_restore(cp);

            let ty = ctx
                .mk_aux_mvar_type(&snap, &[a], sort0)
                .expect("mk_aux_mvar_type");
            match ctx.node(ty) {
                Node::Forall {
                    binder_type, body, ..
                } => {
                    assert_eq!(binder_type, sort0, "the reverted binder's type");
                    assert_eq!(body, sort0, "the original type, with nothing to abstract");
                }
                other => panic!("expected Forall, got {other:?}"),
            }
        });
    }

    /// The reverted binder must actually be ABSTRACTED out of the
    /// original type, not merely prefixed: `?m : a` reverted over `[a]`
    /// gets `∀ (a : Sort 0), #0`, never `∀ (a : Sort 0), <fvar a>`.
    #[test]
    fn mk_aux_mvar_type_abstracts_the_reverted_fvar_out_of_the_type() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let snap = ctx.current_lctx();
            ctx.lctx_restore(cp);

            // The metavariable's own type IS the fvar.
            let ty = ctx
                .mk_aux_mvar_type(&snap, &[a], a)
                .expect("mk_aux_mvar_type");
            match ctx.node(ty) {
                Node::Forall { body, .. } => assert!(
                    matches!(ctx.node(body), Node::BVar { idx: 0 }),
                    "the reverted fvar is abstracted to bvar 0 — leaving it as an \
                     fvar is precisely the bug this whole slice removes, one level \
                     down in the auxiliary metavariable's own type"
                ),
                other => panic!("expected Forall, got {other:?}"),
            }
        });
    }

    /// A let-declaration in `to_revert` is REFUSED, not guessed at:
    /// leanr's LocalDecl carries no `nondep` bit, so the oracle's two
    /// ldecl arms have no input.
    #[test]
    fn mk_aux_mvar_type_refuses_a_let_decl_in_to_revert() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let v = ctx
                .push_let_decl(None, sort0, sort0)
                .expect("push_let_decl");
            let snap = ctx.current_lctx();
            ctx.lctx_restore(cp);

            let err = ctx
                .mk_aux_mvar_type(&snap, &[v], sort0)
                .expect_err("a let-decl in to_revert is refused");
            assert!(
                format!("{err:?}").contains("let-decl"),
                "the refusal names itself: {err:?}"
            );
        });
    }

    /// Discriminates the third Step-5 mutation (iterate `0..xs.len()`
    /// forward instead of `.rev()`), which the single-binder test above
    /// cannot see: with one binder, forward vs. reverse iteration visits
    /// the same (only) index, so the wrapping is identical either way.
    /// Two binders with DISTINGUISHABLE types make the nesting order
    /// observable: `[a : Sort 0, b : a]` reverted innermost-last must
    /// produce `∀ (a : Sort 0), ∀ (b : #0), Sort 0` — `a` outermost,
    /// `b` innermost, `b`'s own type abstracted over `a` (bvar 0). A
    /// forward iteration would instead try to bind `b` (whose type
    /// mentions the not-yet-bound `a`) outermost, so `a`'s abstraction
    /// range would exclude `b`, giving a visibly different — and
    /// wrong — nesting: this assertion reads the identity of the
    /// OUTER binder's type (`Sort 0` vs. an abstracted `#0`), which a
    /// test that only counts binders cannot distinguish.
    #[test]
    fn mk_aux_mvar_type_nests_two_reverted_binders_innermost_last() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            // `b`'s type IS the fvar `a` — distinguishable from `Sort 0`.
            let b = fresh_fvar(ctx, a, "b");
            let snap = ctx.current_lctx();
            ctx.lctx_restore(cp);

            let ty = ctx
                .mk_aux_mvar_type(&snap, &[a, b], sort0)
                .expect("mk_aux_mvar_type");
            // Outer forall: binds `a`, whose type must be the UNABSTRACTED
            // `Sort 0` — nothing precedes `a` in `to_revert`.
            match ctx.node(ty) {
                Node::Forall {
                    binder_type: outer_binder_ty,
                    body: inner,
                    ..
                } => {
                    assert_eq!(
                        outer_binder_ty, sort0,
                        "the outer (a) binder's type is Sort 0 unabstracted"
                    );
                    match ctx.node(inner) {
                        Node::Forall {
                            binder_type: inner_binder_ty,
                            body: innermost,
                            ..
                        } => {
                            assert!(
                                matches!(ctx.node(inner_binder_ty), Node::BVar { idx: 0 }),
                                "the inner (b) binder's type was `a`, abstracted over the \
                                 PRECEDING entry only (&xs[..1] = [a]) into bvar 0 — a \
                                 forward iteration would instead try to abstract `a`'s \
                                 type over `&xs[..0] = []` while `b` is still an fvar, \
                                 producing a different nesting entirely"
                            );
                            assert_eq!(
                                innermost, sort0,
                                "the innermost body is the original type, nothing left to abstract"
                            );
                        }
                        other => panic!("expected inner Forall (b), got {other:?}"),
                    }
                }
                other => panic!("expected outer Forall (a), got {other:?}"),
            }
        });
    }
}
