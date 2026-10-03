//! oracle: `Lean.Meta.Closure` (`Lean/Meta/Closure.lean:100-426`),
//! `mkValueTypeClosure` (`:410-424`) with `zetaDelta := true` hard-wired —
//! the only value `abstractProof` passes (`AbstractNestedProofs.lean:31`).
//!
//! Consequences of `zetaDelta := true`:
//! - `preprocess` (`:168-175`) is just `instantiateMVars`: `check` runs
//!   only when `!zetaDelta`.
//! - No `check` runs, so `zetaDeltaFVarIds` stays empty and `process`'s
//!   `ldecl` arm (`:289-311`) always takes the non-dependent branch:
//!   `newLetDecls` is always empty.
//! - The `mvar` arm (`:201-236`) is an M4c-1 seam: P2 calls this only
//!   after `ensureNoUnassignedMVars` + `instantiateMVars`, so
//!   `newLocalDeclsForMVars` is empty and `sortDecls` (`:364-408`) is the
//!   identity (`:368-369`).

use std::collections::HashMap;

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_kernel::{abstract_fvars, BinderInfo, Nat};

use crate::level_params::append_index_after;
use crate::{MetaCtx, MetaError};

/// oracle: `MkValueTypeClosureResult` (`Closure.lean:339-344`).
#[derive(Debug)]
pub struct ClosureResult {
    pub level_params: Vec<NameId>,
    pub ty: ExprId,
    pub value: ExprId,
    pub level_args: Vec<LevelId>,
    pub expr_args: Vec<ExprId>,
}

/// oracle: `Closure.State` (`Closure.lean:110-122`), minus the fields
/// `zetaDelta := true` keeps empty (`newLocalDeclsForMVars`,
/// `newLetDecls`, `exprMVarArgs`) and `nextExprIdx` (read only by the
/// `mvar` arm's `mkNextUserName`, `:181-185`).
#[derive(Default)]
struct ClosureSt {
    visited_level: HashMap<LevelId, LevelId>,
    visited_expr: HashMap<ExprId, ExprId>,
    level_params: Vec<NameId>,
    /// `nextLevelIdx`, starts at 1 (`:114`).
    next_level_idx: u64,
    level_args: Vec<LevelId>,
    /// (new fvar, user name, collected type, binder info) — `newLocalDecls`.
    new_local_decls: Vec<(ExprId, Option<NameId>, ExprId, BinderInfo)>,
    expr_fvar_args: Vec<ExprId>,
    /// (original fvar id, new fvar) — `toProcess` (`ToProcessElement`,
    /// `:102-105`).
    to_process: Vec<(NameId, ExprId)>,
}

impl MetaCtx<'_> {
    /// oracle: `mkValueTypeClosure` (`Closure.lean:410-424`) with
    /// `zetaDelta := true`, via `mkValueTypeClosureAux` (`:346-351`).
    /// `sortDecls` (`:364-408`) is the identity here (no mvar decls, see
    /// the module doc), and `newLetDecls` is empty, so
    /// `mkForall newLetDecls type` is `type`.
    pub fn mk_value_type_closure(
        &mut self,
        ty: ExprId,
        value: ExprId,
    ) -> Result<ClosureResult, MetaError> {
        let mut st = ClosureSt {
            next_level_idx: 1,
            ..ClosureSt::default()
        };
        let ty = self.closure_collect(&mut st, ty)?;
        let value = self.closure_collect(&mut st, value)?;
        self.closure_process(&mut st)?;
        st.new_local_decls.reverse();
        st.expr_fvar_args.reverse();
        let ty = self.closure_mk_binding(false, &st.new_local_decls, ty)?;
        let value = self.closure_mk_binding(true, &st.new_local_decls, value)?;
        // oracle: `assert! !value.hasFVar` (`:417`).
        debug_assert!(!self.data(value).has_fvar(), "closure value has an fvar");
        Ok(ClosureResult {
            level_params: st.level_params,
            ty,
            value,
            level_args: st.level_args,
            expr_args: st.expr_fvar_args,
        })
    }

    /// oracle: `mkBinding` (`Closure.lean:313-331`), `cdecl` arm only (no
    /// `ldecl` ever lands in `newLocalDecls` here: `pushLocalDecl` builds
    /// a `.cdecl`, `:278`). Abstraction is syntactic: the body over all
    /// `xs` (`b.abstract xs`, `:315`), decl `i`'s type over `xs[..i]`
    /// (`ty.abstractRange i xs`, `:320`).
    fn closure_mk_binding(
        &mut self,
        is_lambda: bool,
        decls: &[(ExprId, Option<NameId>, ExprId, BinderInfo)],
        b: ExprId,
    ) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let xs: Vec<ExprId> = decls.iter().map(|d| d.0).collect();
        let mut b = abstract_fvars(self.scratch, base, b, &xs, &mut self.guard)?;
        for i in (0..decls.len()).rev() {
            let (_, n, ty, bi) = decls[i];
            let ty = abstract_fvars(self.scratch, base, ty, &xs[..i], &mut self.guard)?;
            b = if is_lambda {
                self.scratch.expr_lam(base, n, ty, b, bi)?
            } else {
                self.scratch.expr_forall(base, n, ty, b, bi)?
            };
        }
        Ok(b)
    }

    /// oracle: `collectExpr` (`Closure.lean:246-248`): `preprocess`
    /// (`:168-175`, just `instantiateMVars` under `zetaDelta`) then
    /// `visitExpr collectExprAux`.
    fn closure_collect(&mut self, st: &mut ClosureSt, e: ExprId) -> Result<ExprId, MetaError> {
        let e = self.instantiate_mvars(e)?;
        self.closure_expr(st, e)
    }

    /// oracle: `visitLevel` (`Closure.lean:126-136`) + `collectLevelAux`
    /// (`:156-162`). Level flag bits: `0b01` has-param, `0b10` has-mvar.
    fn closure_level(&mut self, st: &mut ClosureSt, u: LevelId) -> Result<LevelId, MetaError> {
        let base = Some(self.view.store);
        if self.scratch.level_flags(base, u) & 0b11 == 0 {
            return Ok(u);
        }
        if let Some(&v) = st.visited_level.get(&u) {
            return Ok(v);
        }
        self.step()?;
        let v = match *self.scratch.level_row(base, u) {
            LevelRow::Succ(a) => {
                let a2 = self.guarded(|c| c.closure_level(st, a))?;
                self.update_level_succ(u, a2)?
            }
            LevelRow::Max(a, b) => {
                let a2 = self.guarded(|c| c.closure_level(st, a))?;
                let b2 = self.guarded(|c| c.closure_level(st, b))?;
                self.update_level_max(u, a2, b2)?
            }
            LevelRow::IMax(a, b) => {
                let a2 = self.guarded(|c| c.closure_level(st, a))?;
                let b2 = self.guarded(|c| c.closure_level(st, b))?;
                self.update_level_imax(u, a2, b2)?
            }
            LevelRow::Param(_) | LevelRow::MVar(_) => self.closure_new_level_param(st, u)?,
            LevelRow::Zero => u,
        };
        st.visited_level.insert(u, v);
        Ok(v)
    }

    /// oracle: `mkNewLevelParam` (`Closure.lean:150-154`): a fresh
    /// `u_<nextLevelIdx>`; the ORIGINAL level goes to `levelArgs`.
    fn closure_new_level_param(
        &mut self,
        st: &mut ClosureSt,
        u: LevelId,
    ) -> Result<LevelId, MetaError> {
        let base = Some(self.view.store);
        let u_str = self.scratch.intern_str(base, "u")?;
        let u_name = self.scratch.name_str(base, None, u_str)?;
        let p = append_index_after(self.scratch, base, u_name, st.next_level_idx)?;
        st.level_params.push(p);
        st.next_level_idx += 1;
        st.level_args.push(u);
        Ok(self.scratch.level_param(base, Some(p))?)
    }

    /// oracle: `visitExpr` (`Closure.lean:138-148`) + `collectExprAux`
    /// (`:190-244`). Binders are never opened: loose bvars pass through.
    /// The cache keys on the `ExprId`, so one fvar maps to one new fvar.
    fn closure_expr(&mut self, st: &mut ClosureSt, e: ExprId) -> Result<ExprId, MetaError> {
        let d = self.data(e);
        if !d.has_level_param() && !d.has_fvar() && !d.has_expr_mvar() && !d.has_level_mvar() {
            return Ok(e);
        }
        if let Some(&r) = st.visited_expr.get(&e) {
            return Ok(r);
        }
        self.step()?;
        let base = Some(self.view.store);
        let r = match self.node(e) {
            Node::Proj {
                type_name,
                idx,
                structure,
            } => {
                let s2 = self.guarded(|c| c.closure_expr(st, structure))?;
                self.scratch
                    .expr_proj(base, type_name, &Nat::from(idx as u64), s2)?
            }
            Node::ProjBig {
                type_name,
                idx,
                structure,
            } => {
                let n = self.scratch.nat_at(base, idx).clone();
                let s2 = self.guarded(|c| c.closure_expr(st, structure))?;
                self.scratch.expr_proj(base, type_name, &n, s2)?
            }
            Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let d2 = self.guarded(|c| c.closure_expr(st, binder_type))?;
                let b2 = self.guarded(|c| c.closure_expr(st, body))?;
                self.scratch
                    .expr_forall(base, binder_name, d2, b2, binder_info)?
            }
            Node::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let d2 = self.guarded(|c| c.closure_expr(st, binder_type))?;
                let b2 = self.guarded(|c| c.closure_expr(st, body))?;
                self.scratch
                    .expr_lam(base, binder_name, d2, b2, binder_info)?
            }
            Node::LetE {
                decl_name,
                ty,
                value,
                body,
                non_dep,
            } => {
                let t2 = self.guarded(|c| c.closure_expr(st, ty))?;
                let v2 = self.guarded(|c| c.closure_expr(st, value))?;
                let b2 = self.guarded(|c| c.closure_expr(st, body))?;
                self.scratch
                    .expr_let(base, decl_name, t2, v2, b2, non_dep)?
            }
            Node::App { f, arg } => {
                let f2 = self.guarded(|c| c.closure_expr(st, f))?;
                let a2 = self.guarded(|c| c.closure_expr(st, arg))?;
                self.scratch.expr_app(base, f2, a2)?
            }
            Node::MData { data, expr } => {
                let b2 = self.guarded(|c| c.closure_expr(st, expr))?;
                self.scratch.expr_mdata(base, data, b2)?
            }
            Node::Sort { level } => {
                let l2 = self.closure_level(st, level)?;
                self.scratch.expr_sort(base, l2)?
            }
            Node::Const { name, levels } => {
                let ls = self.scratch.level_list_at(base, levels).to_vec();
                let mut out = Vec::with_capacity(ls.len());
                for l in ls {
                    out.push(self.closure_level(st, l)?);
                }
                let ls2 = self.scratch.intern_level_list(base, &out)?;
                self.scratch.expr_const(base, name, ls2)?
            }
            // oracle `:201-236`: abstracts the mvar as a fresh `_x_N`
            // binder (eta-expanding a delayed-assigned one). Unreachable
            // from P2, which closes only fully instantiated terms.
            Node::MVar { .. } => {
                return Err(MetaError::Unsupported(
                    "closure over a metavariable — M4c-1 seam (Closure.lean:201)".into(),
                ))
            }
            // oracle `:237-243`: `zetaDelta := true`, so a VISIBLE let value
            // (`getValue?`, `Meta/Basic.lean:1044`, `allowNondep := false`
            // — a nondep `have` hides it) is inlined; any other fvar
            // becomes a fresh undeclared fvar queued in `toProcess`.
            Node::FVar { id } => {
                let fid = id.ok_or_else(|| MetaError::Infer("closure: anonymous fvar".into()))?;
                let decl = self
                    .lctx
                    .get(fid)
                    .ok_or_else(|| MetaError::Infer("closure: unknown free variable".into()))?;
                let nondep = self.local_entry(fid).is_some_and(|en| en.nondep);
                match decl.value {
                    Some(v) if !nondep => {
                        let v = self.instantiate_mvars(v)?;
                        self.guarded(|c| c.closure_expr(st, v))?
                    }
                    _ => {
                        let new_id =
                            leanr_kernel::fresh_fvar_id(self.scratch, base, &mut self.fvar_gen)?;
                        let new = self.scratch.expr_fvar(base, Some(new_id))?;
                        st.to_process.push((fid, new));
                        new
                    }
                }
            }
            _ => e,
        };
        st.visited_expr.insert(e, r);
        Ok(r)
    }

    /// The oracle's `LocalDecl.index` (`lctx.get! fvarId`, `:254`): the
    /// declaration's position in `local_names`, kept in lockstep with
    /// `lctx`.
    fn closure_lctx_index(&self, fid: NameId) -> Result<usize, MetaError> {
        self.local_names
            .iter()
            .position(|en| en.id == fid)
            .ok_or_else(|| MetaError::Infer("closure: unknown free variable".into()))
    }

    /// oracle: `pickNextToProcess?` (`Closure.lean:261-271`) +
    /// `pickNextToProcessAux` (`:250-259`): pop the back, then scan from
    /// index 0; whenever the scanned element has a GREATER lctx index than
    /// the current pick, swap — the old pick goes into its slot.
    fn closure_pick_next(
        &mut self,
        st: &mut ClosureSt,
    ) -> Result<Option<(NameId, ExprId)>, MetaError> {
        let Some(mut elem) = st.to_process.pop() else {
            return Ok(None);
        };
        let mut elem_idx = self.closure_lctx_index(elem.0)?;
        for i in 0..st.to_process.len() {
            let other = st.to_process[i];
            let other_idx = self.closure_lctx_index(other.0)?;
            if elem_idx < other_idx {
                st.to_process[i] = elem;
                elem = other;
                elem_idx = other_idx;
            }
        }
        Ok(Some(elem))
    }

    /// oracle: `process` (`Closure.lean:280-311`). A cdecl becomes
    /// `pushLocalDecl newFVarId userName type bi` (`:285-288`). An
    /// ldecl reaching here is a nondep `have` (a visible `let` was
    /// inlined by the `fvar` arm); with `zetaDeltaFVarIds` empty it takes
    /// the non-dependent branch (`:292-302`): `pushLocalDecl` with the
    /// default binder info. Either way the ORIGINAL fvar is pushed to
    /// `exprFVarArgs` (`pushFVarArg (mkFVar fvarId)`).
    fn closure_process(&mut self, st: &mut ClosureSt) -> Result<(), MetaError> {
        while let Some((fid, new)) = self.closure_pick_next(st)? {
            self.step()?;
            let decl = self
                .lctx
                .get(fid)
                .ok_or_else(|| MetaError::Infer("closure: unknown free variable".into()))?;
            let (name, ty) = (decl.binder_name, decl.ty);
            let bi = if decl.value.is_some() {
                BinderInfo::Default
            } else {
                decl.binder_info
            };
            // oracle `pushLocalDecl` (`:276-278`): `collectExpr type`.
            let ty = self.closure_collect(st, ty)?;
            st.new_local_decls.push((new, name, ty, bi));
            let orig = self.scratch.expr_fvar(Some(self.view.store), Some(fid))?;
            st.expr_fvar_args.push(orig);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::{app, bvar, c, cu, lit_level, lparam, with_meta0_ctx};
    use crate::MetaError;
    use leanr_kernel::BinderInfo;

    /// probe `foo1._proof_1`: closing `@rfl.{1} N (N.succ n)` over `n : N`.
    #[test]
    fn closure_abstracts_free_fvars_in_lctx_order() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let one = lit_level(ctx, 1);
            let n_ty = c(ctx, "N");
            let succ = c(ctx, "N.succ");
            let n_name = {
                let s = ctx.scratch.intern_str(base, "n").unwrap();
                ctx.scratch.name_str(base, None, s).unwrap()
            };
            let n = ctx
                .push_local_decl(Some(n_name), n_ty, BinderInfo::Default)
                .unwrap();
            let sn = app(ctx, succ, n);
            let eq = cu(ctx, "Eq", &[one]);
            let rfl = cu(ctx, "rfl", &[one]);
            let ty = ctx.mk_app_spine(eq, &[n_ty, sn, sn]).unwrap();
            let val = ctx.mk_app_spine(rfl, &[n_ty, sn]).unwrap();
            let r = ctx.mk_value_type_closure(ty, val).unwrap();
            // ∀ (n : N), @Eq.{1} N (N.succ #0) (N.succ #0)
            let b0 = bvar(ctx, 0);
            let s0 = app(ctx, succ, b0);
            let ty_body = ctx.mk_app_spine(eq, &[n_ty, s0, s0]).unwrap();
            let want_ty = ctx
                .scratch
                .expr_forall(base, Some(n_name), n_ty, ty_body, BinderInfo::Default)
                .unwrap();
            let val_body = ctx.mk_app_spine(rfl, &[n_ty, s0]).unwrap();
            let want_val = ctx
                .scratch
                .expr_lam(base, Some(n_name), n_ty, val_body, BinderInfo::Default)
                .unwrap();
            assert_eq!(r.ty, want_ty);
            assert_eq!(r.value, want_val);
            assert_eq!(r.expr_args, vec![n]);
            assert!(r.level_params.is_empty() && r.level_args.is_empty());
        });
    }

    /// Review Focus 3 / probe `foo2._proof_1.{u_1}`: `u` becomes `u_1`, the
    /// level arg is the original `u`; `α` is pulled in through `a`'s type.
    #[test]
    fn closure_renames_level_params_to_u_n() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let u = lparam(ctx, "u");
            let sort_u = ctx.scratch.expr_sort(base, u).unwrap();
            let alpha = ctx
                .push_local_decl(None, sort_u, BinderInfo::Default)
                .unwrap();
            let a = ctx
                .push_local_decl(None, alpha, BinderInfo::Default)
                .unwrap();
            let id_u = cu(ctx, "id", &[u]);
            let ida = ctx.mk_app_spine(id_u, &[alpha, a]).unwrap();
            let eq_u = cu(ctx, "Eq", &[u]);
            let rfl_u = cu(ctx, "rfl", &[u]);
            let ty = ctx.mk_app_spine(eq_u, &[alpha, ida, ida]).unwrap();
            let val = ctx.mk_app_spine(rfl_u, &[alpha, ida]).unwrap();
            let r = ctx.mk_value_type_closure(ty, val).unwrap();
            assert_eq!(r.level_args, vec![u]);
            let u_1 = {
                let s = ctx.scratch.intern_str(base, "u_1").unwrap();
                ctx.scratch.name_str(base, None, s).unwrap()
            };
            assert_eq!(r.level_params, vec![u_1]);
            assert_eq!(r.expr_args, vec![alpha, a], "α first: lower lctx index");
            // ∀ (α : Sort u_1) (a : α), @Eq.{u_1} α (@id.{u_1} α a) (@id.{u_1} α a)
            let p1 = lparam(ctx, "u_1");
            let sort_p1 = ctx.scratch.expr_sort(base, p1).unwrap();
            let (b0, b1) = (bvar(ctx, 0), bvar(ctx, 1));
            let id_p1 = cu(ctx, "id", &[p1]);
            let eq_p1 = cu(ctx, "Eq", &[p1]);
            let id_ba = ctx.mk_app_spine(id_p1, &[b1, b0]).unwrap();
            let body = ctx.mk_app_spine(eq_p1, &[b1, id_ba, id_ba]).unwrap();
            let inner = ctx
                .scratch
                .expr_forall(base, None, b0, body, BinderInfo::Default)
                .unwrap();
            let want_ty = ctx
                .scratch
                .expr_forall(base, None, sort_p1, inner, BinderInfo::Default)
                .unwrap();
            assert_eq!(r.ty, want_ty);
        });
    }

    /// Final review minor: the renaming is SIMULTANEOUS. Originals `u` and
    /// a literal `u_1` become `u_1` and `u_2` (`mkNewLevelParam`,
    /// `Closure.lean:150-154`, keyed on the ORIGINAL level): the new
    /// `u_1` (from `u`) is never confused with the original `u_1`.
    #[test]
    fn closure_renames_u_and_a_literal_u_1_simultaneously() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let u = lparam(ctx, "u");
            let u1 = lparam(ctx, "u_1");
            let sort_u = ctx.scratch.expr_sort(base, u).unwrap();
            let sort_u1 = ctx.scratch.expr_sort(base, u1).unwrap();
            let alpha = ctx
                .push_local_decl(None, sort_u, BinderInfo::Default)
                .unwrap();
            let beta = ctx
                .push_local_decl(None, sort_u1, BinderInfo::Default)
                .unwrap();
            let a = ctx
                .push_local_decl(None, alpha, BinderInfo::Default)
                .unwrap();
            let b = ctx
                .push_local_decl(None, beta, BinderInfo::Default)
                .unwrap();
            let pprod = cu(ctx, "PProd", &[u, u1]);
            let mk = cu(ctx, "PProd.mk", &[u, u1]);
            let ty = ctx.mk_app_spine(pprod, &[alpha, beta]).unwrap();
            let val = ctx.mk_app_spine(mk, &[alpha, beta, a, b]).unwrap();
            let r = ctx.mk_value_type_closure(ty, val).unwrap();
            let name = |ctx: &mut crate::MetaCtx, s: &str| {
                let id = ctx.scratch.intern_str(base, s).unwrap();
                ctx.scratch.name_str(base, None, id).unwrap()
            };
            let (n1, n2) = (name(ctx, "u_1"), name(ctx, "u_2"));
            assert_eq!(r.level_params, vec![n1, n2]);
            assert_eq!(r.level_args, vec![u, u1], "the ORIGINAL levels, in order");
            assert_eq!(r.expr_args, vec![alpha, beta, a, b]);
            // ∀ (α : Sort u_1) (β : Sort u_2) (a : α) (b : β), PProd.{u_1,u_2} α β
            let p1 = lparam(ctx, "u_1");
            let p2 = lparam(ctx, "u_2");
            let sort_p1 = ctx.scratch.expr_sort(base, p1).unwrap();
            let sort_p2 = ctx.scratch.expr_sort(base, p2).unwrap();
            let pprod_p = cu(ctx, "PProd", &[p1, p2]);
            let (b1, b2, b3) = (bvar(ctx, 1), bvar(ctx, 2), bvar(ctx, 3));
            let body = ctx.mk_app_spine(pprod_p, &[b3, b2]).unwrap();
            let mut want = body;
            for d in [b1, b1, sort_p2, sort_p1] {
                want = ctx
                    .scratch
                    .expr_forall(base, None, d, want, BinderInfo::Default)
                    .unwrap();
            }
            assert_eq!(r.ty, want);
        });
    }

    /// zetaDelta: a `let m := N.succ n` occurring in the term is inlined; the
    /// closure abstracts only `n`.
    #[test]
    fn closure_zeta_expands_let_fvars() {
        with_meta0_ctx(|ctx| {
            let n_ty = c(ctx, "N");
            let succ = c(ctx, "N.succ");
            let n = ctx
                .push_local_decl(None, n_ty, BinderInfo::Default)
                .unwrap();
            let sn = app(ctx, succ, n);
            let m = ctx.push_let_decl(None, n_ty, sn, false).unwrap();
            let sm = app(ctx, succ, m);
            let r = ctx.mk_value_type_closure(n_ty, sm).unwrap();
            assert_eq!(r.expr_args, vec![n]);
            let base = Some(ctx.view.store);
            let b0 = bvar(ctx, 0);
            let s0 = app(ctx, succ, b0);
            let ss0 = app(ctx, succ, s0);
            let want = ctx
                .scratch
                .expr_lam(base, None, n_ty, ss0, BinderInfo::Default)
                .unwrap();
            assert_eq!(r.value, want);
        });
    }

    /// A nondep `have m := N.succ n` hides its value from `getValue?`
    /// (`Meta/Basic.lean:1044`), so it is abstracted like a cdecl (with
    /// default binder info) rather than inlined; `n` is not pulled in,
    /// since `m`'s type `N` does not mention it.
    #[test]
    fn closure_abstracts_nondep_have_instead_of_inlining() {
        with_meta0_ctx(|ctx| {
            let n_ty = c(ctx, "N");
            let succ = c(ctx, "N.succ");
            let n = ctx
                .push_local_decl(None, n_ty, BinderInfo::Default)
                .unwrap();
            let sn = app(ctx, succ, n);
            let m = ctx.push_let_decl(None, n_ty, sn, true).unwrap();
            let sm = app(ctx, succ, m);
            let r = ctx.mk_value_type_closure(n_ty, sm).unwrap();
            assert_eq!(r.expr_args, vec![m]);
            let base = Some(ctx.view.store);
            let b0 = bvar(ctx, 0);
            let s0 = app(ctx, succ, b0);
            let want = ctx
                .scratch
                .expr_lam(base, None, n_ty, s0, BinderInfo::Default)
                .unwrap();
            assert_eq!(r.value, want);
        });
    }

    #[test]
    fn closure_over_an_unassigned_mvar_is_a_named_seam() {
        with_meta0_ctx(|ctx| {
            let n_ty = c(ctx, "N");
            let (m, _) = crate::test_support::fresh_mvar(ctx, n_ty);
            let err = ctx.mk_value_type_closure(n_ty, m).unwrap_err();
            assert!(
                matches!(err, MetaError::Unsupported(ref s) if s.contains("M4c-1 seam")),
                "{err:?}"
            );
        });
    }
}
