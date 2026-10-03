//! oracle: `CheckAssignment` and `CheckAssignmentQuick`
//! (`Lean/Meta/ExprDefEq.lean:803-1086`, v4.33.0-rc1), the scope check
//! behind `checkAssignment` (`:1151-1172`, the driver in `assign.rs`).
//!
//! The quick check is a bool predicate. When it says `false` the driver
//! runs the slow path, which REWRITES the value. It can restrict an
//! out-of-scope metavariable to a smaller context (`checkMVar` under
//! `ctxApprox`), follow a genuine let to its value (`checkFVar`),
//! turn `?f x` with `x` out of scope into a constant function
//! (`checkApp` + `assignToConstFun`), and head-beta a redex and retry
//! (`check`). The driver assigns the rewritten term, never the original
//! (spec `2026-10-02-check-assignment-ctx-approx-design.md`).

use std::collections::HashMap;
use std::sync::Arc;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::Nat;

use crate::{LocalCtxSnapshot, MVarId, MVarKind, MetaCtx, MetaError};

/// The oracle's two internal exception ids, `outOfScopeExceptionId` and
/// `checkAssignmentExceptionId`, which `run` (`:840-847`) turns into
/// `none`. A real `MetaError` (budget, depth, an unknown metavariable)
/// is NOT one of them and propagates.
enum CheckErr {
    OutOfScope,
    Failure,
    Meta(MetaError),
}

impl From<MetaError> for CheckErr {
    fn from(e: MetaError) -> Self {
        CheckErr::Meta(e)
    }
}

impl From<leanr_kernel::KernelError> for CheckErr {
    fn from(e: leanr_kernel::KernelError) -> Self {
        CheckErr::Meta(e.into())
    }
}

type CheckResult = Result<ExprId, CheckErr>;

/// oracle: `CheckAssignment.Context` (`:796-802`) plus `State.cache`.
/// The cache lives for one `check_assignment_aux` call, matching `run`'s
/// fresh state, and is keyed by hash-consed `ExprId` (the oracle's
/// `checkCache` is keyed by `Expr`).
struct CheckCtx<'a> {
    mvar_id: MVarId,
    decl_lctx: Arc<LocalCtxSnapshot>,
    fvars: &'a [ExprId],
    has_ctx_locals: bool,
    cache: HashMap<ExprId, ExprId>,
}

impl<'e> MetaCtx<'e> {
    /// The `NameId`s of the fvars among `xs`, which is the shape
    /// `LocalCtxSnapshot::is_sub_prefix_of` takes for `except`.
    pub(crate) fn fvar_ids(&self, xs: &[ExprId]) -> Vec<NameId> {
        xs.iter().filter_map(|x| self.fvar_id_of(*x)).collect()
    }

    /// oracle: `CheckAssignmentQuick.check` (`ExprDefEq.lean:1039-1086`).
    /// A bool predicate. `false` means "the slow path decides", never
    /// "reject". See `check_assignment_aux`.
    pub(crate) fn check_assignment_scope(
        &mut self,
        mvar_id: MVarId,
        fvars: &[ExprId],
        has_ctx_locals: bool,
        e: ExprId,
    ) -> Result<bool, MetaError> {
        if !self.data(e).has_fvar() && !self.data(e).has_expr_mvar() {
            return Ok(true);
        }
        self.guarded(|ctx| ctx.check_assignment_scope_body(mvar_id, fvars, has_ctx_locals, e))
    }

    fn check_assignment_scope_body(
        &mut self,
        mvar_id: MVarId,
        fvars: &[ExprId],
        has_ctx_locals: bool,
        e: ExprId,
    ) -> Result<bool, MetaError> {
        let hcl = has_ctx_locals;
        match self.node(e) {
            Node::FVar { id: Some(fid) } => {
                let in_mvar_lctx = self
                    .mctx
                    .decl(mvar_id)
                    .map(|d| d.lctx.lctx().get(fid).is_some())
                    .unwrap_or(false);
                if in_mvar_lctx {
                    return Ok(true);
                }
                // oracle: `checkFVar` matches `.ldecl (nondep := false)`
                // only; a `have` is "locally a cdecl" and falls through
                // to the `fvars.contains` test (`ExprDefEq.lean:851-878`).
                // A genuine let is `false` here: "need expensive
                // CheckAssignment.check" (`:1066`), which follows it.
                let is_let = self.lctx.get(fid).and_then(|d| d.value).is_some()
                    && self.local_entry(fid).is_some_and(|e| !e.nondep);
                if is_let {
                    return Ok(false);
                }
                Ok(fvars.contains(&e))
            }
            // `:1070-1077`, in the oracle's order.
            Node::MVar { id: Some(n) } => {
                let id = MVarId(n);
                if self.mctx.is_assigned(id) || id == mvar_id {
                    return Ok(false);
                }
                let Some(inner) = self.mctx.decl(id).map(|d| Arc::clone(&d.lctx)) else {
                    return Ok(false);
                };
                if has_ctx_locals {
                    return Ok(false);
                }
                let Some(outer) = self.mctx.decl(mvar_id).map(|d| Arc::clone(&d.lctx)) else {
                    return Ok(false);
                };
                let except = self.fvar_ids(fvars);
                if !inner.is_sub_prefix_of(&outer, &except) {
                    return Ok(false);
                }
                Ok(!self.mctx.is_delayed_assigned(id))
            }
            // visit f <&&> visit a (:1053); rescues are the slow path's
            Node::App { f, arg } => Ok(self.check_assignment_scope(mvar_id, fvars, hcl, f)?
                && self.check_assignment_scope(mvar_id, fvars, hcl, arg)?),
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => Ok(
                self.check_assignment_scope(mvar_id, fvars, hcl, binder_type)?
                    && self.check_assignment_scope(mvar_id, fvars, hcl, body)?,
            ),
            Node::LetE {
                ty, value, body, ..
            } => Ok(self.check_assignment_scope(mvar_id, fvars, hcl, ty)?
                && self.check_assignment_scope(mvar_id, fvars, hcl, value)?
                && self.check_assignment_scope(mvar_id, fvars, hcl, body)?),
            Node::MData { expr, .. } => self.check_assignment_scope(mvar_id, fvars, hcl, expr),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                self.check_assignment_scope(mvar_id, fvars, hcl, structure)
            }
            _ => Ok(true),
        }
    }

    /// oracle: `checkAssignmentAux` (`:954-956`) = `run (check v)`.
    /// `Ok(None)` is either internal failure. Its callers are the
    /// `check_assignment` driver (when the quick check fails) and
    /// `assign_to_const_fun`.
    pub(crate) fn check_assignment_aux(
        &mut self,
        mvar_id: MVarId,
        fvars: &[ExprId],
        has_ctx_locals: bool,
        v: ExprId,
    ) -> Result<Option<ExprId>, MetaError> {
        let decl_lctx = match self.mctx.decl(mvar_id) {
            Some(d) => Arc::clone(&d.lctx),
            None => {
                return Err(MetaError::MVar(format!(
                    "check_assignment_aux: unknown metavariable {mvar_id:?}"
                )))
            }
        };
        let mut cx = CheckCtx {
            mvar_id,
            decl_lctx,
            fvars,
            has_ctx_locals,
            cache: HashMap::new(),
        };
        match self.ca_check(&mut cx, v) {
            Ok(e) => Ok(Some(e)),
            Err(CheckErr::OutOfScope | CheckErr::Failure) => Ok(None),
            Err(CheckErr::Meta(e)) => Err(e),
        }
    }

    /// oracle: `check` (`:987-1035`). Only successes are cached, as with
    /// `checkCache`.
    fn ca_check(&mut self, cx: &mut CheckCtx, e: ExprId) -> CheckResult {
        if !self.data(e).has_expr_mvar() && !self.data(e).has_fvar() {
            return Ok(e);
        }
        if let Some(r) = cx.cache.get(&e) {
            return Ok(*r);
        }
        let r = self.guarded(|s| Ok(s.ca_check_body(cx, e)))??;
        cx.cache.insert(e, r);
        Ok(r)
    }

    fn ca_check_body(&mut self, cx: &mut CheckCtx, e: ExprId) -> CheckResult {
        let st = Some(self.view.store);
        match self.node(e) {
            Node::MData { data, expr } => {
                let b = self.ca_check(cx, expr)?;
                Ok(self.scratch.expr_mdata(st, data, b)?)
            }
            Node::Proj {
                type_name,
                idx,
                structure,
            } => {
                let s = self.ca_check(cx, structure)?;
                Ok(self
                    .scratch
                    .expr_proj(st, type_name, &Nat::from(u64::from(idx)), s)?)
            }
            Node::ProjBig {
                type_name,
                idx,
                structure,
            } => {
                let i = self.scratch.nat_at(st, idx).clone();
                let s = self.ca_check(cx, structure)?;
                Ok(self.scratch.expr_proj(st, type_name, &i, s)?)
            }
            Node::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let d = self.ca_check(cx, binder_type)?;
                let b = self.ca_check(cx, body)?;
                Ok(self.scratch.expr_lam(st, binder_name, d, b, binder_info)?)
            }
            Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let d = self.ca_check(cx, binder_type)?;
                let b = self.ca_check(cx, body)?;
                Ok(self
                    .scratch
                    .expr_forall(st, binder_name, d, b, binder_info)?)
            }
            Node::LetE {
                decl_name,
                ty,
                value,
                body,
                non_dep,
            } => {
                let t = self.ca_check(cx, ty)?;
                let v = self.ca_check(cx, value)?;
                let b = self.ca_check(cx, body)?;
                Ok(self.scratch.expr_let(st, decl_name, t, v, b, non_dep)?)
            }
            Node::FVar { .. } => self.ca_check_fvar(cx, e),
            Node::MVar { .. } => self.ca_check_mvar(cx, e),
            // `:1004-1021`: on either internal failure, a head-beta
            // target is reduced and retried. The oracle's commented-out
            // `whnfR` fallback (`:1024-1034`) is not ported.
            Node::App { .. } => match self.ca_check_app(cx, e) {
                Err(CheckErr::OutOfScope | CheckErr::Failure) if self.is_head_beta_target(e) => {
                    let e2 = self.head_beta(e)?;
                    self.ca_check_app(cx, e2)
                }
                r => r,
            },
            _ => Ok(e),
        }
    }

    /// oracle: `Expr.isHeadBetaTarget` (`useZeta := false`): an
    /// application whose head is a lambda. Only `Lam` is modelled, the
    /// same simplification `head_beta` (`whnf.rs`) makes.
    fn is_head_beta_target(&self, e: ExprId) -> bool {
        matches!(self.node(e), Node::App { .. })
            && matches!(self.node(self.get_app_fn(e)), Node::Lam { .. })
    }

    /// oracle: `checkFVar` (`:851-878`). A genuine let (`nondep :=
    /// false`) in the AMBIENT ctx is followed into its value. A `have`
    /// is "locally a cdecl" and takes the `fvars` test.
    fn ca_check_fvar(&mut self, cx: &mut CheckCtx, e: ExprId) -> CheckResult {
        let Node::FVar { id: Some(fid) } = self.node(e) else {
            return Ok(e);
        };
        if cx.decl_lctx.lctx().get(fid).is_some() {
            return Ok(e);
        }
        let let_value = self
            .lctx
            .get(fid)
            .and_then(|d| d.value)
            .filter(|_| self.local_entry(fid).is_some_and(|en| !en.nondep));
        if let Some(v) = let_value {
            return self.ca_check(cx, v);
        }
        if cx.fvars.contains(&e) {
            Ok(e)
        } else {
            Err(CheckErr::OutOfScope)
        }
    }

    /// oracle: `checkMVar` (`:880-938`).
    fn ca_check_mvar(&mut self, cx: &mut CheckCtx, e: ExprId) -> CheckResult {
        let Node::MVar { id: Some(n) } = self.node(e) else {
            return Ok(e);
        };
        let id = MVarId(n);
        if id == cx.mvar_id {
            return Err(CheckErr::Failure); // occurs check (:883-885)
        }
        if let Some(v) = self.mctx.assignment(id) {
            return self.ca_check(cx, v);
        }
        let Some(decl) = self.mctx.decl(id) else {
            return Err(MetaError::MVar(format!("check_mvar: unknown metavariable {id:?}")).into());
        };
        let (inner_lctx, inner_ty, inner_kind, inner_scope_args) = (
            Arc::clone(&decl.lctx),
            decl.ty,
            decl.kind,
            decl.num_scope_args,
        );
        if cx.has_ctx_locals {
            return Err(CheckErr::Failure); // :890
        }
        if let Some(d) = self.mctx.delayed_assignment(id) {
            // :892-895: occurs-check at the pending mvar.
            let pending = d.mvar_id_pending;
            let pending_e = self
                .scratch
                .expr_mvar(Some(self.view.store), Some(pending.0))?;
            if !self.occurs_check(cx.mvar_id, pending_e)? {
                return Err(CheckErr::Failure);
            }
        }
        let except = self.fvar_ids(cx.fvars);
        if inner_lctx.is_sub_prefix_of(&cx.decl_lctx, &except) {
            return Ok(e); // :897-900
        }
        if self.mctx.expr_mvar_depth(id) != Some(self.mctx.depth())
            || inner_kind == MVarKind::SyntheticOpaque
        {
            return Err(CheckErr::Failure); // :901-903
        }
        if !(self.cfg.ctx_approx && cx.decl_lctx.is_sub_prefix_of(&inner_lctx, &[])) {
            return Err(CheckErr::Failure); // :905-907
        }
        let to_erase = self.ctx_approx_to_erase(&inner_lctx, cx)?;
        // `lctx.erase` for each, plus the `localInstances` filter
        // (:931-933): `reduced` does both.
        let reduced = self.reduce_local_context(&inner_lctx, &to_erase)?;
        let ty = self.ca_check(cx, inner_ty)?;
        // oracle `ExprDefEq.lean:936`: `mkAuxMVar lctx localInsts mvarType
        // mvarDecl.numScopeArgs` — the restricted mvar inherits the count.
        let (aux, _) =
            self.mk_aux_mvar_at(reduced, ty, MVarKind::Natural, None, inner_scope_args)?;
        self.mctx.assign(id, aux)?;
        Ok(aux)
    }

    /// oracle `:920-930`: fold over the INNER ctx in declaration order.
    /// Keep a decl the assigned mvar's ctx has. An entry of `fvars` is
    /// kept unless it depends on something already erased
    /// (`findLocalDeclDependsOn`, `generalizeNondepLet := true` by
    /// default, `MetavarContext.lean:744`). Erase everything else.
    fn ctx_approx_to_erase(
        &mut self,
        inner: &LocalCtxSnapshot,
        cx: &CheckCtx,
    ) -> Result<Vec<ExprId>, MetaError> {
        let fvar_ids = self.fvar_ids(cx.fvars);
        let mut to_erase: Vec<ExprId> = Vec::new();
        let mut erased_ids: Vec<NameId> = Vec::new();
        for entry in inner.entries().to_vec() {
            if cx.decl_lctx.lctx().get(entry.id).is_some() {
                continue;
            }
            if fvar_ids.contains(&entry.id) {
                let Some(d) = inner.lctx().get(entry.id) else {
                    continue;
                };
                let (ty, value) = (d.ty, d.value);
                if !self.local_decl_depends_on(ty, value, entry.nondep, &erased_ids, true)? {
                    continue;
                }
            }
            to_erase.push(entry.fvar);
            erased_ids.push(entry.id);
        }
        Ok(to_erase)
    }

    /// oracle: `checkApp` (`:958-985`).
    fn ca_check_app(&mut self, cx: &mut CheckCtx, e: ExprId) -> CheckResult {
        let f = self.get_app_fn(e);
        let args = self.get_app_args(e);
        let rescuable = matches!(self.node(f), Node::MVar { .. })
            && self.cfg.ctx_approx
            && args
                .iter()
                .all(|a| matches!(self.node(*a), Node::FVar { .. }));
        let f2 = self.ca_check(cx, f)?;
        let mut checked = Vec::with_capacity(args.len());
        for a in &args {
            match self.ca_check(cx, *a) {
                Ok(a2) => checked.push(a2),
                // `catchInternalId outOfScopeExceptionId`: ONLY
                // out-of-scope is caught, and only on the rescuable path.
                Err(CheckErr::OutOfScope) if rescuable => {
                    return self.ctx_approx_const_fun(cx, e, f2, args.len());
                }
                Err(other) => return Err(other),
            }
        }
        Ok(self.mk_app_spine(f2, &checked)?)
    }

    /// The handler arm of `checkApp` (`:966-984`).
    fn ctx_approx_const_fun(
        &mut self,
        cx: &mut CheckCtx,
        e: ExprId,
        f: ExprId,
        num_args: usize,
    ) -> CheckResult {
        let Node::MVar { id: Some(fid) } = self.node(f) else {
            return Err(CheckErr::OutOfScope); // `if !f.isMVar then throw ex`
        };
        if self.mctx.is_delayed_assigned(MVarId(fid)) {
            return Err(CheckErr::OutOfScope);
        }
        let e_ty = self.infer_type(e)?;
        let mvar_ty = self.ca_check(cx, e_ty)?;
        // `mkAuxMVar ctx.mvarDecl.lctx ctx.mvarDecl.localInstances`:
        // the ASSIGNED mvar's ctx. The instances travel inside the
        // snapshot. oracle :977 passes no numScopeArgs (default 0).
        let (new_mvar, _) = self.mk_aux_mvar_at(
            Arc::clone(&cx.decl_lctx),
            mvar_ty,
            MVarKind::Natural,
            None,
            0,
        )?;
        if self.assign_to_const_fun(f, num_args, new_mvar)? {
            Ok(new_mvar)
        } else {
            Err(CheckErr::OutOfScope)
        }
    }

    /// oracle: `assignToConstFun` (`:946-952`). The telescope fvars are
    /// scoped with `lctx_checkpoint`/`lctx_restore`, as `assign_const`
    /// does, because `forall_bounded_telescope` pushes into the ambient
    /// ctx.
    fn assign_to_const_fun(
        &mut self,
        mvar: ExprId,
        num_args: usize,
        new_mvar: ExprId,
    ) -> Result<bool, MetaError> {
        let mvar_ty = self.infer_type(mvar)?;
        let cp = self.lctx_checkpoint();
        let r = self.assign_to_const_fun_body(mvar, mvar_ty, num_args, new_mvar);
        self.lctx_restore(cp);
        r
    }

    fn assign_to_const_fun_body(
        &mut self,
        mvar: ExprId,
        mvar_ty: ExprId,
        num_args: usize,
        new_mvar: ExprId,
    ) -> Result<bool, MetaError> {
        let xs = self.forall_bounded_telescope(mvar_ty, num_args)?;
        if xs.len() != num_args {
            return Ok(false);
        }
        let Some(v) = self.mk_lambda_fvars_with_let_deps(&xs, new_mvar)? else {
            return Ok(false);
        };
        let Node::MVar { id: Some(n) } = self.node(mvar) else {
            return Ok(false);
        };
        let Some(v) = self.check_assignment_aux(MVarId(n), &[], false, v)? else {
            return Ok(false);
        };
        self.check_types_and_assign(mvar, v)
    }
}

#[cfg(test)]
mod tests {
    use leanr_kernel::bank::terms::Node;
    use leanr_kernel::bank::ExprId;
    use leanr_kernel::BinderInfo;

    use crate::test_support::{
        const_dotted, const_named, fresh_fvar, fresh_mvar, with_prelude0_ctx,
    };
    use crate::{MVarId, MVarKind, MetaCtx};

    fn sort0(ctx: &mut MetaCtx) -> ExprId {
        let base = Some(ctx.view.store);
        let z = ctx.scratch.level_zero(base).expect("level");
        ctx.scratch.expr_sort(base, z).expect("sort")
    }

    fn mvar_id(ctx: &MetaCtx, e: ExprId) -> MVarId {
        match ctx.node(e) {
            Node::MVar { id: Some(n) } => MVarId(n),
            _ => panic!("not an mvar"),
        }
    }

    /// oracle `ExprDefEq.lean:936`: the restricted aux mvar inherits the
    /// inner mvar's `numScopeArgs`.
    #[test]
    fn check_mvar_restriction_inherits_num_scope_args() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let _x = fresh_fvar(ctx, n, "x");
            let lctx = ctx.current_lctx();
            let (i, _iid) = ctx
                .mk_aux_mvar_at(lctx, n, MVarKind::Natural, None, 3)
                .expect("inner");
            let out = ctx.check_assignment_aux(oid, &[], false, i).expect("check");
            let aux = out.expect("restricted, not refused");
            assert_eq!(ctx.mctx.decl(mvar_id(ctx, aux)).unwrap().num_scope_args, 3);
            ctx.lctx_restore(cp);
        });
    }

    /// oracle `checkMVar` (`ExprDefEq.lean:880-938`): `?o` (empty ctx)
    /// `:= ?i` (ctx `{x}`). `?i`'s ctx is not a sub-prefix of `?o`'s, the
    /// depths are equal, it is natural, `ctxApprox` is on, and `{}` is a
    /// sub-prefix of `{x}`. So `?i := ?aux` with `x` erased, and the
    /// checked term is `?aux`. This is the restriction that breaks the
    /// spec's § Evidence cycle.
    #[test]
    fn check_mvar_restricts_an_inner_mvar_under_ctx_approx() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let x = fresh_fvar(ctx, n, "x");
            let xid = ctx.fvar_id_of(x).unwrap();
            let (i, iid) = ctx.mk_aux_mvar(n).expect("inner");
            let out = ctx.check_assignment_aux(oid, &[], false, i).expect("check");
            let aux = out.expect("restricted, not refused");
            assert_ne!(aux, i);
            assert_eq!(ctx.mctx.assignment(iid), Some(aux), "inner := ?aux");
            let aux_lctx = ctx.mctx.decl(mvar_id(ctx, aux)).unwrap().lctx.clone();
            assert!(
                aux_lctx.lctx().get(xid).is_none(),
                "x erased from ?aux's ctx"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// Same shape with `ctx_approx` off: refused (`:905`), and nothing
    /// is assigned.
    #[test]
    fn check_mvar_refuses_without_ctx_approx() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = false;
            let n = const_named(ctx, "N");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let _x = fresh_fvar(ctx, n, "x");
            let (i, iid) = ctx.mk_aux_mvar(n).expect("inner");
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, i), Ok(None));
            assert!(!ctx.mctx.is_assigned(iid));
            ctx.lctx_restore(cp);
        });
    }

    /// `:901`: a syntheticOpaque inner mvar, or one at another depth, is
    /// refused.
    #[test]
    fn check_mvar_refuses_synthetic_opaque_and_other_depth() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let _x = fresh_fvar(ctx, n, "x");
            let lctx = ctx.current_lctx();
            let (so, soid) = ctx
                .mk_aux_mvar_at(lctx, n, MVarKind::SyntheticOpaque, None, 0)
                .expect("opaque");
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, so), Ok(None));
            assert!(!ctx.mctx.is_assigned(soid));
            let (i, iid) = ctx.mk_aux_mvar(n).expect("inner");
            let r = ctx.with_new_mctx_depth(false, |c| c.check_assignment_aux(oid, &[], false, i));
            assert_eq!(r, Ok(None), "inner was minted at depth 0, check runs at 1");
            assert!(!ctx.mctx.is_assigned(iid));
            ctx.lctx_restore(cp);
        });
    }

    /// `:890`: under `has_ctx_locals` every unassigned non-self mvar
    /// fails, even a sub-prefix one.
    #[test]
    fn check_mvar_refuses_under_has_ctx_locals() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let (_o, oid) = fresh_mvar(ctx, n);
            let (m, _) = fresh_mvar(ctx, n);
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, m), Ok(Some(m)));
            assert_eq!(ctx.check_assignment_aux(oid, &[], true, m), Ok(None));
        });
    }

    /// `:880-883`: `?o` occurring in its own value fails (occurs check),
    /// and an assigned mvar is followed to its value.
    #[test]
    fn check_mvar_occurs_check_and_follows_assignments() {
        with_prelude0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let zero = const_dotted(ctx, "N", "zero");
            let (o, oid) = fresh_mvar(ctx, n);
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, o), Ok(None));
            let (m, mid) = fresh_mvar(ctx, n);
            ctx.mctx.assign(mid, zero).unwrap();
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, m), Ok(Some(zero)));
        });
    }

    /// `:892-896`: a delayed-assigned `?d` whose pending mvar is `?o`
    /// itself fails the occurs check at the pending mvar.
    #[test]
    fn check_mvar_occurs_check_at_a_delayed_pending_mvar() {
        with_prelude0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let (_o, oid) = fresh_mvar(ctx, n);
            let (d, did) = fresh_mvar(ctx, n);
            ctx.mctx.assign_delayed(did, vec![], oid).unwrap();
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, d), Ok(None));
        });
    }

    /// `:894` calls `Lean.occursCheck`, whose `visitMVar`
    /// (`Util/OccursCheck.lean:26-35`) follows a delayed assignment's
    /// pending mvar transitively: `?d` pends on `?p`, which pends on
    /// `?o`, so `?o := ?d` is refused.
    #[test]
    fn check_mvar_occurs_check_follows_a_delayed_pending_chain() {
        with_prelude0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let (_o, oid) = fresh_mvar(ctx, n);
            let (_p, pid) = fresh_mvar(ctx, n);
            let (d, did) = fresh_mvar(ctx, n);
            ctx.mctx.assign_delayed(pid, vec![], oid).unwrap();
            ctx.mctx.assign_delayed(did, vec![], pid).unwrap();
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, d), Ok(None));
        });
    }

    /// Review Focus #2: `throwUnknownMVar`. A real error, not `None`.
    #[test]
    fn check_mvar_errors_on_an_undeclared_mvar() {
        with_prelude0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let (_o, oid) = fresh_mvar(ctx, n);
            let base = Some(ctx.view.store);
            let s = ctx.scratch.intern_str(base, "_never_declared").unwrap();
            let name = ctx.scratch.name_str(base, None, s).unwrap();
            let ghost = ctx.scratch.expr_mvar(base, Some(name)).unwrap();
            assert!(ctx.check_assignment_aux(oid, &[], false, ghost).is_err());
        });
    }

    /// `to_erase` (`:916-930`): an entry of `fvars` that DEPENDS on an
    /// erased variable is erased too. `x : Sort 0`, `y : x`, inner ctx
    /// `{x, y}`, outer ctx `{}`, `fvars = [y]`. `x` is erased (not in the
    /// outer ctx, not in `fvars`), and so is `y` (it depends on `x`).
    /// Control: `y : N` does not depend on `x`, so it survives.
    #[test]
    fn check_mvar_erases_a_dependent_fvars_entry() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let s0 = sort0(ctx);
            for (y_depends, y_survives) in [(true, false), (false, true)] {
                let cp = ctx.lctx_checkpoint();
                let (_o, oid) = fresh_mvar(ctx, n);
                let x = fresh_fvar(ctx, s0, "x");
                let y = fresh_fvar(ctx, if y_depends { x } else { n }, "y");
                let yid = ctx.fvar_id_of(y).unwrap();
                let (i, _) = ctx.mk_aux_mvar(n).expect("inner");
                let aux = ctx
                    .check_assignment_aux(oid, &[y], false, i)
                    .expect("check")
                    .expect("restricted");
                let lctx = ctx.mctx.decl(mvar_id(ctx, aux)).unwrap().lctx.clone();
                assert_eq!(
                    lctx.lctx().get(yid).is_some(),
                    y_survives,
                    "y_depends={y_depends}"
                );
                ctx.lctx_restore(cp);
            }
        });
    }

    /// `checkFVar` (`:851-878`): a genuine let outside the mvar's ctx is
    /// followed into its value; a `have` is not; a plain fvar is in scope
    /// only through `fvars`.
    #[test]
    fn check_fvar_follows_lets_not_haves() {
        with_prelude0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let zero = const_dotted(ctx, "N", "zero");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let l = ctx.push_let_decl(None, n, zero, false).expect("let");
            let h = ctx.push_let_decl(None, n, zero, true).expect("have");
            let x = fresh_fvar(ctx, n, "x");
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, l), Ok(Some(zero)));
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, h), Ok(None));
            assert_eq!(ctx.check_assignment_aux(oid, &[h], false, h), Ok(Some(h)));
            assert_eq!(ctx.check_assignment_aux(oid, &[], false, x), Ok(None));
            assert_eq!(ctx.check_assignment_aux(oid, &[x], false, x), Ok(Some(x)));
            ctx.lctx_restore(cp);
        });
    }

    /// `check`'s `.app` arm (`:1004-1021`): on an internal failure, a
    /// head-beta target is reduced and retried. `(fun _ : N => N.zero) x`
    /// with `x` out of scope checks to `N.zero`.
    #[test]
    fn check_retries_a_head_beta_target() {
        with_prelude0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let zero = const_dotted(ctx, "N", "zero");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let x = fresh_fvar(ctx, n, "x");
            let base = Some(ctx.view.store);
            let k = ctx
                .scratch
                .expr_lam(base, None, n, zero, BinderInfo::Default)
                .unwrap();
            let redex = ctx.scratch.expr_app(base, k, x).unwrap();
            assert_eq!(
                ctx.check_assignment_aux(oid, &[], false, redex),
                Ok(Some(zero))
            );
            ctx.lctx_restore(cp);
        });
    }

    /// `checkMVar` with the assigned mvar in a NON-empty ctx `{a}`
    /// (`:897-900`): the inner mvar's ctx `{a, y}` with `fvars = [y]` is
    /// a sub-prefix once `y` is subtracted, so it is returned unchanged
    /// and nothing is assigned.
    #[test]
    fn check_mvar_subtracts_fvars_before_the_sub_prefix_test() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let cp = ctx.lctx_checkpoint();
            let _a = fresh_fvar(ctx, n, "a");
            let with_a = ctx.current_lctx();
            let (_o, oid) = ctx
                .mk_aux_mvar_at(with_a, n, MVarKind::Natural, None, 0)
                .unwrap();
            let y = fresh_fvar(ctx, n, "y");
            let (i, iid) = ctx.mk_aux_mvar(n).unwrap();
            assert_eq!(ctx.check_assignment_aux(oid, &[y], false, i), Ok(Some(i)));
            assert!(!ctx.mctx.is_assigned(iid), "a sub-prefix is not restricted");
            ctx.lctx_restore(cp);
        });
    }

    /// `checkMVar`'s `toErase` fold (`:920-930`) with the assigned mvar
    /// in ctx `{a}` and the inner one in `{a, x}`: the restriction KEEPS
    /// `a` (the outer ctx has it) and drops `x`.
    #[test]
    fn check_mvar_restriction_keeps_what_the_outer_ctx_has() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, n, "a");
            let aid = ctx.fvar_id_of(a).unwrap();
            let with_a = ctx.current_lctx();
            let (_o, oid) = ctx
                .mk_aux_mvar_at(with_a, n, MVarKind::Natural, None, 0)
                .unwrap();
            let x = fresh_fvar(ctx, n, "x");
            let xid = ctx.fvar_id_of(x).unwrap();
            let (i, iid) = ctx.mk_aux_mvar(n).unwrap();
            let aux = ctx
                .check_assignment_aux(oid, &[], false, i)
                .unwrap()
                .expect("restricted");
            assert_eq!(ctx.mctx.assignment(iid), Some(aux));
            let lctx = ctx.mctx.decl(mvar_id(ctx, aux)).unwrap().lctx.clone();
            assert!(lctx.lctx().get(aid).is_some(), "a kept");
            assert!(lctx.lctx().get(xid).is_none(), "x erased");
            ctx.lctx_restore(cp);
        });
    }

    /// oracle `CheckAssignmentQuick` mvar arm (`:1070-1077`): each of
    /// the six conditions returns `false` ("use the slow path"). A
    /// declared, unassigned, sub-prefix, non-delayed mvar returns `true`.
    #[test]
    fn quick_check_mvar_arm_falls_through_on_each_condition() {
        with_prelude0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let zero = const_dotted(ctx, "N", "zero");
            let cp = ctx.lctx_checkpoint();
            let (o, oid) = fresh_mvar(ctx, n);
            let (ok, _) = fresh_mvar(ctx, n);
            assert!(
                ctx.check_assignment_scope(oid, &[], false, ok).unwrap(),
                "sub-prefix"
            );
            let (asg, asg_id) = fresh_mvar(ctx, n);
            ctx.mctx.assign(asg_id, zero).unwrap();
            assert!(
                !ctx.check_assignment_scope(oid, &[], false, asg).unwrap(),
                "(1) assigned"
            );
            assert!(
                !ctx.check_assignment_scope(oid, &[], false, o).unwrap(),
                "(2) self"
            );
            let base = Some(ctx.view.store);
            let s = ctx.scratch.intern_str(base, "_never_declared_q").unwrap();
            let name = ctx.scratch.name_str(base, None, s).unwrap();
            let ghost = ctx.scratch.expr_mvar(base, Some(name)).unwrap();
            assert!(
                !ctx.check_assignment_scope(oid, &[], false, ghost).unwrap(),
                "(3) undeclared"
            );
            assert!(
                !ctx.check_assignment_scope(oid, &[], true, ok).unwrap(),
                "(4) has_ctx_locals"
            );
            let _x = fresh_fvar(ctx, n, "x");
            let (inner, _) = ctx.mk_aux_mvar(n).unwrap();
            assert!(
                !ctx.check_assignment_scope(oid, &[], false, inner).unwrap(),
                "(5) not sub-prefix"
            );
            let (d, did) = fresh_mvar(ctx, n);
            let (p, pid) = fresh_mvar(ctx, n);
            let _ = p;
            ctx.mctx.assign_delayed(did, vec![], pid).unwrap();
            assert!(
                !ctx.check_assignment_scope(oid, &[], false, d).unwrap(),
                "(6) delayed"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// The driver returns the REWRITTEN term (`:1164-1168`), never the
    /// original `v`.
    #[test]
    fn driver_returns_the_slow_path_rewrite() {
        with_prelude0_ctx(|ctx| {
            ctx.cfg.ctx_approx = true;
            let n = const_named(ctx, "N");
            let cp = ctx.lctx_checkpoint();
            let (_o, oid) = fresh_mvar(ctx, n);
            let _x = fresh_fvar(ctx, n, "x");
            let (i, iid) = ctx.mk_aux_mvar(n).unwrap();
            let got = ctx
                .check_assignment(oid, &[], i)
                .unwrap()
                .expect("restricted");
            assert_ne!(
                got, i,
                "assigning the original would rebuild the § Evidence cycle"
            );
            assert_eq!(ctx.mctx.assignment(iid), Some(got));
            ctx.lctx_restore(cp);
        });
    }

    /// oracle: `checkFVar` matches `.ldecl (nondep := false)`; a `have` is
    /// "locally a cdecl", judged by membership in the abstracted fvars
    /// (`ExprDefEq.lean:851-878`). The QUICK check (`:1062-1068`) answers
    /// `false` for a genuine let even when it is listed in `fvars`: that
    /// means "slow path", and only the slow path follows its value. The
    /// mvar is minted BEFORE the decls so neither is in its lctx.
    #[test]
    fn quick_check_treats_a_have_as_a_cdecl() {
        with_prelude0_ctx(|ctx| {
            let nat = const_named(ctx, "Nat");
            let zero = const_named(ctx, "Nat.zero");
            let cp = ctx.lctx_checkpoint();
            let (_m, mid) = fresh_mvar(ctx, nat);
            let h = ctx.push_let_decl(None, nat, zero, true).expect("have");
            let l = ctx.push_let_decl(None, nat, zero, false).expect("let");
            assert!(!ctx.check_assignment_scope(mid, &[], false, h).expect("h"));
            assert!(ctx.check_assignment_scope(mid, &[h], false, h).expect("h"));
            assert!(!ctx.check_assignment_scope(mid, &[l], false, l).expect("l"));
            ctx.lctx_restore(cp);
        });
    }

    /// `checkApp`'s `ctxApprox` rescue (`:958-985`) and
    /// `assignToConstFun` (`:946-952`): `?o := ?f x` with `x` out of
    /// `?o`'s scope. `?f := fun _ => ?n`, and the checked term is `?n`,
    /// minted in `?o`'s ctx. Off without `ctx_approx`.
    #[test]
    fn check_app_rescues_an_out_of_scope_mvar_app() {
        for ctx_approx in [true, false] {
            with_prelude0_ctx(|ctx| {
                ctx.cfg.ctx_approx = ctx_approx;
                let n = const_named(ctx, "N");
                let base = Some(ctx.view.store);
                let n_to_n = ctx
                    .scratch
                    .expr_forall(base, None, n, n, BinderInfo::Default)
                    .unwrap();
                let cp = ctx.lctx_checkpoint();
                let (_o, oid) = fresh_mvar(ctx, n);
                let (f, fid) = fresh_mvar(ctx, n_to_n);
                let x = fresh_fvar(ctx, n, "x");
                let fx = ctx.scratch.expr_app(base, f, x).unwrap();
                let out = ctx
                    .check_assignment_aux(oid, &[], false, fx)
                    .expect("check");
                if ctx_approx {
                    let new = out.expect("rescued");
                    assert!(matches!(ctx.node(new), Node::MVar { .. }));
                    let fval = ctx.mctx.assignment(fid).expect("?f assigned");
                    assert!(
                        matches!(ctx.node(fval), Node::Lam { .. }),
                        "?f := fun _ => ?n"
                    );
                } else {
                    assert_eq!(out, None);
                    assert!(!ctx.mctx.is_assigned(fid));
                }
                ctx.lctx_restore(cp);
            });
        }
    }
}
