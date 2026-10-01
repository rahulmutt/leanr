//! oracle: `Lean/Meta/Check.lean` (v4.33.0-rc1): `check` (`:331-338`)
//! over `checkAux` (`:288-326`), and `isTypeCorrect` (`:365-370`).
//! The error-message machinery (`throwAppTypeMismatch`,
//! `addPPExplicitToExposeDiff`) is not ported. The only caller,
//! `isTypeCorrect`, discards the message.

use std::collections::HashSet;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelsId, NameId};
use leanr_kernel::instantiate_rev;

use crate::transparency::TransparencyMode;
use crate::{MVarId, MVarKind, MetaCtx, MetaError};

impl<'e> MetaCtx<'e> {
    /// oracle: `check e (transparency := .all)` (`Check.lean:331-338`).
    pub fn check(&mut self, e: ExprId) -> Result<(), MetaError> {
        let mut seen = HashSet::new();
        self.with_transparency(TransparencyMode::All, |ctx| ctx.check_aux(e, &mut seen))
    }

    /// oracle: `isTypeCorrect`, `try check e; true catch _ => false`
    /// (`Check.lean:365-370`). `MetaError::Check` (check's own throws) and
    /// `MetaError::Infer` (inference failures inside it, including
    /// `getLevel`'s "type expected" and unknown constants) are folded into
    /// `false`. NOTE: several leanr-internal invariant failures are also
    /// raised as `MetaError::Infer` (e.g. `metactx.rs` and `infer.rs`
    /// internal-state checks), so those are folded into `false` too; they
    /// cannot be told apart from oracle-shaped inference failures without
    /// re-varianting existing errors, which would change existing callers.
    /// Budget exhaustion, named seams (`Unsupported`) and other variants
    /// PROPAGATE: folding them would turn "leanr cannot answer" into a
    /// confident "ill-typed". `IsDefEqStuck` also propagates, which DIVERGES
    /// from the oracle (its `catch _` catches it and answers `false`);
    /// unreachable today. There is no rollback: mvar assignments made by
    /// `isDefEq` inside `check` persist, as in the oracle.
    pub fn is_type_correct(&mut self, e: ExprId) -> Result<bool, MetaError> {
        match self.check(e) {
            Ok(()) => Ok(true),
            Err(MetaError::Check(_)) | Err(MetaError::Infer(_)) => Ok(false),
            Err(other) => Err(other),
        }
    }

    /// oracle: `checkAux.check` (`Check.lean:288-301`). `checkCache` on
    /// `ExprStructEq` is a visited set: hash-consing makes `ExprId`
    /// equality structural.
    fn check_aux(&mut self, e: ExprId, seen: &mut HashSet<ExprId>) -> Result<(), MetaError> {
        if !seen.insert(e) {
            return Ok(());
        }
        self.step()?;
        match self.node(e) {
            Node::Forall { .. } => self.in_telescope(|ctx| ctx.check_forall(e, seen)),
            Node::Lam { .. } | Node::LetE { .. } => {
                self.in_telescope(|ctx| ctx.check_lambda_let(e, seen))
            }
            Node::Const { name, levels } => self.check_constant(name, levels),
            Node::App { f, arg } => {
                self.check_aux(f, seen)?;
                self.check_aux(arg, seen)?;
                self.check_app(f, arg)
            }
            Node::MData { expr, .. } => self.check_aux(expr, seen),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                self.check_aux(structure, seen)?;
                self.check_proj(e, structure)
            }
            _ => Ok(()),
        }
    }

    /// Run `f` and restore the local context afterwards on every exit
    /// path, `?` early returns included.
    fn in_telescope<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<R, MetaError>,
    ) -> Result<R, MetaError> {
        let cp = self.lctx_checkpoint();
        let r = f(self);
        self.lctx_restore(cp);
        r
    }

    /// oracle: `checkForall` (`Check.lean:319-326`): `forallTelescope`
    /// (non-reducing), `ensureType` + `check` each binder type, then the
    /// body. The caller restores the lctx.
    fn check_forall(&mut self, e: ExprId, seen: &mut HashSet<ExprId>) -> Result<(), MetaError> {
        let base = Some(self.view.store);
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut types: Vec<ExprId> = Vec::new();
        let mut cur = e;
        while let Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = self.node(cur)
        {
            let d = instantiate_rev(self.scratch, base, binder_type, &fvars, &mut self.guard)?;
            let x = self.push_local_decl(binder_name, d, binder_info)?;
            fvars.push(x);
            types.push(d);
            cur = body;
        }
        let b = instantiate_rev(self.scratch, base, cur, &fvars, &mut self.guard)?;
        for t in types {
            self.ensure_type(t)?;
            self.check_aux(t, seen)?;
        }
        self.ensure_type(b)?;
        self.check_aux(b, seen)
    }

    /// oracle: `checkLambdaLet` (`Check.lean:303-317`): `lambdaLetTelescope`,
    /// then per binder `ensureType` + `check` of its type and, for a let,
    /// the value-type defeq and `check` of the value; then the body. The
    /// caller restores the lctx.
    fn check_lambda_let(&mut self, e: ExprId, seen: &mut HashSet<ExprId>) -> Result<(), MetaError> {
        let base = Some(self.view.store);
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut decls: Vec<(ExprId, Option<ExprId>)> = Vec::new();
        let mut cur = e;
        loop {
            match self.node(cur) {
                Node::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    let d =
                        instantiate_rev(self.scratch, base, binder_type, &fvars, &mut self.guard)?;
                    let x = self.push_local_decl(binder_name, d, binder_info)?;
                    fvars.push(x);
                    decls.push((d, None));
                    cur = body;
                }
                Node::LetE {
                    decl_name,
                    ty,
                    value,
                    body,
                    non_dep,
                } => {
                    let t = instantiate_rev(self.scratch, base, ty, &fvars, &mut self.guard)?;
                    let v = instantiate_rev(self.scratch, base, value, &fvars, &mut self.guard)?;
                    let x = self.push_let_decl(decl_name, t, v, non_dep)?;
                    fvars.push(x);
                    decls.push((t, Some(v)));
                    cur = body;
                }
                _ => break,
            }
        }
        let b = instantiate_rev(self.scratch, base, cur, &fvars, &mut self.guard)?;
        for (t, v) in decls {
            self.ensure_type(t)?;
            self.check_aux(t, seen)?;
            if let Some(v) = v {
                let v_ty = self.infer_type(v)?;
                if !self.is_def_eq(t, v_ty)? {
                    return Err(MetaError::Check("let type mismatch".into()));
                }
                self.check_aux(v, seen)?;
            }
        }
        self.check_aux(b, seen)
    }

    /// oracle: `ensureType` (`Check.lean:22-23`): `discard <| getLevel e`.
    /// `getLevel`'s assignable-mvar arm (`InferType.lean:169-175`: the type
    /// of `t` whnfs to an unassigned, assignable `?m`, so assign
    /// `?m := Sort ?u` with a fresh level mvar) is ported HERE rather than
    /// in `get_level`, which stays untouched for its other callers. Without
    /// it a binder type `?a : ?T` would be reported ill-typed. Not
    /// assignable (synthetic opaque while `assign_synthetic_opaque` is off,
    /// or undeclared) throws `type expected` (`:171-172`). The depth half
    /// of `isReadOnlyOrSyntheticOpaque` is the crate's single-depth seam.
    fn ensure_type(&mut self, t: ExprId) -> Result<(), MetaError> {
        let tt = self.infer_type(t)?;
        // oracle: `getLevel` whnfs with `whnfD` (`InferType.lean:166`), i.e.
        // at default transparency even though `check` runs under `.all`.
        let w = self.with_transparency(TransparencyMode::Default, |ctx| ctx.whnf(tt))?;
        match self.node(w) {
            Node::Sort { .. } => Ok(()),
            Node::MVar { id: Some(id) } => {
                let mid = MVarId(id);
                let assignable = match self.mctx.decl(mid) {
                    Some(d) => {
                        !(d.kind == MVarKind::SyntheticOpaque && !self.cfg.assign_synthetic_opaque)
                    }
                    None => false,
                };
                if !assignable {
                    return Err(MetaError::Infer("type expected".into()));
                }
                let (_, lvl) = self.fresh_level_mvar()?;
                let sort = self.scratch.expr_sort(Some(self.view.store), lvl)?;
                self.mctx.assign(mid, sort)
            }
            _ => Err(MetaError::Infer("type expected".into())),
        }
    }

    /// oracle: `checkConstant` (`Check.lean:25-28`). A missing constant is
    /// `getConstVal`'s throw (`Infer`).
    fn check_constant(&mut self, name: Option<NameId>, levels: LevelsId) -> Result<(), MetaError> {
        let info = self.env_get(name)?;
        let n = self
            .scratch
            .level_list_at(Some(self.view.store), levels)
            .len();
        if info.constant_val().level_params.len() != n {
            return Err(MetaError::Check(
                "incorrect number of universe levels".into(),
            ));
        }
        Ok(())
    }

    /// oracle: `checkApp` (`Check.lean:272-280`).
    fn check_app(&mut self, f: ExprId, a: ExprId) -> Result<(), MetaError> {
        let f_ty = self.infer_type(f)?;
        let f_ty = self.whnf(f_ty)?;
        match self.node(f_ty) {
            Node::Forall { binder_type: d, .. } => {
                let a_ty = self.infer_type(a)?;
                if !self.is_def_eq(d, a_ty)? {
                    return Err(MetaError::Check("application type mismatch".into()));
                }
                Ok(())
            }
            _ => Err(MetaError::Check("function expected".into())),
        }
    }

    /// oracle: `checkProj` (`Check.lean:282-286`): `isProp structType &&
    /// !isProp projType` throws.
    fn check_proj(&mut self, proj: ExprId, structure: ExprId) -> Result<(), MetaError> {
        let st = self.infer_type(structure)?;
        let st = self.whnf(st)?;
        let pt = self.infer_type(proj)?;
        if self.is_prop(st)? && !self.is_prop(pt)? {
            return Err(MetaError::Check("invalid projection".into()));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::{app, c, fresh_mvar, with_meta0_ctx};
    use leanr_kernel::BinderInfo;

    /// `fun (x : ?a) => x` with `?a : ?T`: `ensureType ?a` reaches
    /// `getLevel`'s assignable-mvar arm, which assigns `?T := Sort ?u`.
    /// Plain `get_level` would throw `type expected` and `is_type_correct`
    /// would fold that into `false`.
    #[test]
    fn binder_type_mvar_with_mvar_type_is_type_correct_and_assigns_sort() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = c(ctx, "N");
            let ty = ctx.infer_type(n).unwrap();
            let (t, t_id) = fresh_mvar(ctx, ty);
            let (a, _) = fresh_mvar(ctx, t);
            let b0 = ctx
                .scratch
                .expr_bvar(base, &leanr_kernel::Nat::from(0u64))
                .unwrap();
            let lam = ctx
                .scratch
                .expr_lam(base, None, a, b0, BinderInfo::Default)
                .unwrap();
            assert!(ctx.is_type_correct(lam).unwrap());
            assert!(ctx.mctx().is_assigned(t_id), "?T := Sort ?u");
        });
    }

    /// `N.succ N` — `infer_type` answers `N` (it never checks the
    /// argument), `check` rejects it: `N : Type`, not `N`.
    #[test]
    fn ill_typed_application_is_rejected_where_infer_type_succeeds() {
        with_meta0_ctx(|ctx| {
            let succ = c(ctx, "N.succ");
            let n = c(ctx, "N");
            let bad = app(ctx, succ, n);
            assert!(
                ctx.infer_type(bad).is_ok(),
                "the proxy would say type-correct"
            );
            assert!(!ctx.is_type_correct(bad).unwrap());
        });
    }

    #[test]
    fn well_typed_application_is_accepted() {
        with_meta0_ctx(|ctx| {
            let succ = c(ctx, "N.succ");
            let zero = c(ctx, "N.zero");
            let ok = app(ctx, succ, zero);
            assert!(ctx.is_type_correct(ok).unwrap());
        });
    }

    /// `isTypeCorrect` does not roll back: `N.succ ?m` with `?m : ?T`
    /// assigns `?T := N` through `checkApp`'s `isDefEq`.
    #[test]
    fn check_keeps_defeq_assignments() {
        with_meta0_ctx(|ctx| {
            let n = c(ctx, "N");
            let ty = ctx.infer_type(n).unwrap(); // Type
            let (t, t_id) = fresh_mvar(ctx, ty);
            let (m, _) = fresh_mvar(ctx, t);
            let succ = c(ctx, "N.succ");
            let e = app(ctx, succ, m);
            assert!(ctx.is_type_correct(e).unwrap());
            assert!(ctx.mctx().is_assigned(t_id), "?T was assigned by checkApp");
        });
    }

    /// `let y : N := N; y` — the value's type is `Type`, not `N`.
    #[test]
    fn let_value_type_mismatch_is_rejected() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = c(ctx, "N");
            let b0 = ctx
                .scratch
                .expr_bvar(base, &leanr_kernel::Nat::from(0u64))
                .unwrap();
            let e = ctx.scratch.expr_let(base, None, n, n, b0, false).unwrap();
            assert!(!ctx.is_type_correct(e).unwrap());
        });
    }

    /// `N.{0}` — `N` has no universe parameters.
    #[test]
    fn wrong_universe_count_is_rejected() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let s = ctx.scratch.intern_str(base, "N").unwrap();
            let name = ctx.scratch.name_str(base, None, s).unwrap();
            let z = ctx.scratch.level_zero(base).unwrap();
            let levels = ctx.scratch.intern_level_list(base, &[z]).unwrap();
            let e = ctx.scratch.expr_const(base, Some(name), levels).unwrap();
            assert!(!ctx.is_type_correct(e).unwrap());
        });
    }
}
