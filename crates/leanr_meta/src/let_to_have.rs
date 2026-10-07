//! oracle: `Meta.letToHave` (`Lean/Meta/LetToHave.lean`, v4.33.0-rc1):
//! rewrite every genuine `let` (`nondep := false`) whose value is never
//! definitionally used into a `have`. "Used" is approximated as the oracle
//! does: re-type-check the term, but fully only under a genuine let
//! (`Context.check`, `:111`), with zeta-delta tracking on
//! (`withTrackingZetaDelta`); a let whose fvar was never unfolded becomes a
//! `have` (`finalize`, `:338-368`).
//!
//! Deviations, each output-equivalent:
//! - `visitConst` (`:201-208`) and the `.lit` arm (`:410`) ask
//!   `infer_type`, which runs the same `getConstVal` + level-count check +
//!   `instantiateTypeLevelParams` (`infer.rs`, `infer_const`) and the same
//!   `Literal.type`. Neither can unfold a let.
//! - no `incCount` / trace output (`:121-123`, `:339`, `:417-431`).
//! - `Context.letFVars` (`:87-90`) is one `Vec` in [`Lth`], pushed while a
//!   telescope grows and truncated when it is left: within one telescope
//!   the oracle's list only grows, so the `Vec` always equals the list the
//!   oracle would have in its reader (order aside; only emptiness and the
//!   member set are read).
//! - an error naming a PENDING aux lemma becomes the M4c-1 pending-constant
//!   seam (`pending_lookup_seam`, `who = "letToHave"`): after
//!   `abstractNestedProofs`, `visitConst` on `d._proof_N` under a genuine
//!   let needs a constant the oracle has already added.
//!
//! Telescope declarations are pushed WITHOUT the local-instance `isClass?`
//! test (`push_local_decl_without_instance` /
//! `push_let_decl_without_instance`): the oracle extends a bare
//! `LocalContext` (`lctx.mkLocalDecl` / `lctx.mkLetDecl`, `:280`, `:320`,
//! `:330`) under `withLCtx lctx {}`. `is_class` can `whnf` the declared
//! type, which under tracking would record a let. This is a narrowing, not
//! the full `{}`: the oracle also CLEARS the local instances for the pass,
//! while leanr keeps the caller's outer local instances in scope (it only
//! adds none). That is observable only through instance synthesis reached
//! from inside `isDefEq`/`whnf` during the pass.
//!
//! Every recursive `visit` goes through `guarded` (and `step`), so a deep
//! term ends in `DepthBudgetExhausted`, not a stack overflow.

use std::collections::{HashMap, HashSet};

use leanr_kernel::bank::names::NameRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::{abstract_fvars, instantiate_rev, lower_loose_bvars, ConstantInfo, Nat};

use crate::local_decl_kind::LocalDeclKind;
use crate::{AuxLemmas, MVarId, MetaCtx, MetaError, TransparencyMode};

/// oracle `Result` (`:78-83`).
#[derive(Clone, Copy)]
struct Res {
    expr: ExprId,
    /// `type?`: `None` when the type has not been computed.
    ty: Option<ExprId>,
}

/// oracle `Context` (`:87-90`) + `State.results` (`:92-96`).
#[derive(Default)]
struct Lth {
    /// The genuine lets in scope (`letFVars`).
    let_fvars: Vec<NameId>,
    /// `results`, keyed by the expression (`ExprStructEq`: pointer
    /// equality, which hash-consed `ExprId` equality is).
    results: HashMap<ExprId, Res>,
}

impl Lth {
    /// `Context.check` (`:111`).
    fn check(&self) -> bool {
        !self.let_fvars.is_empty()
    }
}

fn lth_err(msg: &str) -> MetaError {
    MetaError::Infer(format!("letToHave: {msg}"))
}

impl<'e> MetaCtx<'e> {
    /// oracle: `letToHave` (`:440-443`) → `main` (`:416-431`). Returns `e`
    /// (after `instantiateMVars`) unchanged when it has no genuine let.
    pub fn let_to_have(&mut self, aux: &AuxLemmas, e: ExprId) -> Result<ExprId, MetaError> {
        let e = self.instantiate_mvars(e)?;
        if !self.lth_has_dep_let(e) {
            return Ok(e);
        }
        let r = self.with_tracking_zeta_delta(|c| {
            c.with_transparency(TransparencyMode::All, |c| {
                c.with_infer_type_config(|c| {
                    let mut st = Lth::default();
                    c.lth_visit(&mut st, e).map(|r| r.expr)
                })
            })
        });
        r.map_err(|err| self.pending_lookup_seam(aux, err, "letToHave"))
    }

    /// `hasDepLet` (`:67-68`): some `letE (nondep := false)` subterm.
    fn lth_has_dep_let(&self, e: ExprId) -> bool {
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut stack = vec![e];
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.node(t) {
                Node::LetE { non_dep: false, .. } => return true,
                Node::LetE {
                    ty, value, body, ..
                } => stack.extend([ty, value, body]),
                Node::App { f, arg } => stack.extend([f, arg]),
                Node::Lam {
                    binder_type, body, ..
                }
                | Node::Forall {
                    binder_type, body, ..
                } => stack.extend([binder_type, body]),
                Node::MData { expr, .. } => stack.push(expr),
                Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                    stack.push(structure)
                }
                _ => {}
            }
        }
        false
    }

    /// `canSkip` (`:75-76`).
    fn lth_can_skip(&self, e: ExprId, max_depth: u32) -> bool {
        let d = self.data(e);
        !d.has_fvar()
            && !d.has_expr_mvar()
            && (u32::from(d.approx_depth()) <= max_depth && !self.lth_has_dep_let(e))
    }

    /// `Result.type` (`:101-108`).
    fn lth_type(&mut self, st: &mut Lth, r: Res) -> Result<ExprId, MetaError> {
        if let Some(t) = r.ty {
            return Ok(t);
        }
        let t = self.infer_type(r.expr)?;
        st.results.insert(
            r.expr,
            Res {
                expr: r.expr,
                ty: Some(t),
            },
        );
        Ok(t)
    }

    /// `checkCache` (`:137-147`). A hit is returned as is, even one
    /// computed with check off (`type? := none`, `:126-128`).
    fn lth_check_cache(
        &mut self,
        st: &mut Lth,
        e: ExprId,
        f: impl FnOnce(&mut Self, &mut Lth) -> Result<Res, MetaError>,
    ) -> Result<Res, MetaError> {
        if let Some(r) = st.results.get(&e).copied() {
            return Ok(r);
        }
        let r = if self.lth_can_skip(e, 2) {
            Res { expr: e, ty: None }
        } else {
            f(self, st)?
        };
        st.results.insert(e, r);
        Ok(r)
    }

    /// `visit` (`:398-412`).
    fn lth_visit(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        self.step()?;
        self.guarded(|c| c.lth_visit_core(st, e))
    }

    fn lth_visit_core(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        let base = Some(self.view.store);
        match self.node(e) {
            Node::BVar { .. } | Node::BVarBig { .. } => Err(lth_err("unexpected bound variable")),
            // `visitFVar` (`:153-155`).
            Node::FVar { id } => {
                let ty = id
                    .and_then(|id| self.lctx.get(id))
                    .map(|d| d.ty)
                    .ok_or_else(|| lth_err("unknown free variable"))?;
                Ok(Res {
                    expr: e,
                    ty: Some(ty),
                })
            }
            // `visitMVar` (`:196-199`).
            Node::MVar { id } => {
                let id = MVarId(id.ok_or_else(|| lth_err("unknown metavariable"))?);
                let ty = self
                    .mctx
                    .decl(id)
                    .map(|d| d.ty)
                    .ok_or_else(|| lth_err("unknown metavariable"))?;
                if st.check() {
                    self.lth_check_mvar(st, id, &[])?;
                }
                Ok(Res {
                    expr: e,
                    ty: Some(ty),
                })
            }
            Node::Sort { level } => {
                let u = self.scratch.level_succ(base, level)?;
                let ty = self.scratch.expr_sort(base, u)?;
                Ok(Res {
                    expr: e,
                    ty: Some(ty),
                })
            }
            // `visitConst` (`:201-209`): `whenCheck` (`:114-115`), then the
            // instantiated type.
            Node::Const { .. } => {
                if !st.check() {
                    return Ok(Res { expr: e, ty: None });
                }
                let ty = self.infer_type(e)?;
                Ok(Res {
                    expr: e,
                    ty: Some(ty),
                })
            }
            Node::App { .. } => self.lth_check_cache(st, e, |c, st| c.lth_visit_app_args(st, e)),
            Node::Forall { .. } => self.lth_check_cache(st, e, |c, st| c.lth_visit_forall(st, e)),
            Node::Lam { .. } | Node::LetE { .. } => {
                self.lth_check_cache(st, e, |c, st| c.lth_visit_lambda_let(st, e))
            }
            // `.lit v => { type? := v.type }`.
            Node::LitNat { .. } | Node::LitStr { .. } => {
                let ty = self.infer_type(e)?;
                Ok(Res {
                    expr: e,
                    ty: Some(ty),
                })
            }
            // `.mdata` (`:411`): not cached; `updateMData!`.
            Node::MData { data, expr } => {
                let r = self.lth_visit(st, expr)?;
                let e2 = if r.expr == expr {
                    e
                } else {
                    self.scratch.expr_mdata(base, data, r.expr)?
                };
                Ok(Res { expr: e2, ty: r.ty })
            }
            // `.proj` (`:412`): the structure is visited inside the cache.
            Node::Proj { .. } | Node::ProjBig { .. } => {
                self.lth_check_cache(st, e, |c, st| c.lth_visit_proj(st, e))
            }
        }
    }

    /// `FVarId.isLetVar` (`Meta/Basic.lean:1057-1058`, `allowNondep :=
    /// false`): a genuine let (`LocalDecl.isLet`, `LocalContext.lean:106-109`).
    /// Unknown fvars throw, as `getDecl` does.
    fn lth_is_let_var(&self, fid: NameId) -> Result<bool, MetaError> {
        let d = self
            .lctx
            .get(fid)
            .ok_or_else(|| lth_err("unknown free variable"))?;
        Ok(d.value.is_some() && self.local_entry(fid).is_some_and(|en| !en.nondep))
    }

    /// `visitDepExpr` (`:164-175`): mark every genuine let reachable from
    /// `e` through fvars and their types.
    fn lth_visit_dep_expr(&mut self, e: ExprId) -> Result<(), MetaError> {
        let mut visited: HashSet<NameId> = HashSet::new();
        let mut worklist = vec![e];
        while let Some(t) = worklist.pop() {
            let t = self.instantiate_mvars(t)?;
            for fid in self.lth_collect_fvars(t) {
                if visited.insert(fid) {
                    if self.lth_is_let_var(fid)? {
                        self.zeta_delta_fvar_ids.insert(fid);
                    }
                    let ty = self
                        .lctx
                        .get(fid)
                        .map(|d| d.ty)
                        .ok_or_else(|| lth_err("unknown free variable"))?;
                    worklist.push(ty);
                }
            }
        }
        Ok(())
    }

    /// `collectFVars` (`Util/CollectFVars.lean:27-45`): the fvar ids of `e`
    /// in first-visit order.
    fn lth_collect_fvars(&self, e: ExprId) -> Vec<NameId> {
        let mut out = Vec::new();
        let mut seen_ids: HashSet<NameId> = HashSet::new();
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut stack = vec![e];
        while let Some(t) = stack.pop() {
            if !self.data(t).has_fvar() || !seen.insert(t) {
                continue;
            }
            // Children pushed in reverse so they pop in the oracle's order.
            match self.node(t) {
                Node::FVar { id: Some(id) } => {
                    if seen_ids.insert(id) {
                        out.push(id);
                    }
                }
                Node::App { f, arg } => stack.extend([arg, f]),
                Node::Lam {
                    binder_type, body, ..
                }
                | Node::Forall {
                    binder_type, body, ..
                } => stack.extend([body, binder_type]),
                Node::LetE {
                    ty, value, body, ..
                } => stack.extend([body, value, ty]),
                Node::MData { expr, .. } => stack.push(expr),
                Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                    stack.push(structure)
                }
                _ => {}
            }
        }
        out
    }

    /// `checkMVar` (`:183-194`).
    fn lth_check_mvar(
        &mut self,
        st: &mut Lth,
        mvar: MVarId,
        args: &[ExprId],
    ) -> Result<(), MetaError> {
        let Some(d) = self.mctx.delayed_assignment(mvar).cloned() else {
            return Ok(());
        };
        if d.fvars.len() > args.len() {
            // An invalid delayed assignment: inhibit every enclosing let.
            for &f in &st.let_fvars {
                self.zeta_delta_fvar_ids.insert(f);
            }
            return Ok(());
        }
        let pending = self
            .mctx
            .decl(d.mvar_id_pending)
            .map(|p| p.lctx.clone())
            .ok_or_else(|| lth_err("unknown metavariable"))?;
        for (&fvar, &arg) in d.fvars.iter().zip(args) {
            // `pendingDecl.lctx.getFVar!` then `isLet`.
            let fid = self
                .fvar_id_of(fvar)
                .filter(|&fid| pending.lctx().get(fid).is_some())
                .ok_or_else(|| lth_err("unknown free variable in a delayed assignment"))?;
            let is_let = pending.lctx().get(fid).is_some_and(|x| x.value.is_some())
                && pending.entry(fid).is_some_and(|en| !en.nondep);
            if is_let {
                self.lth_visit_dep_expr(arg)?;
            }
        }
        Ok(())
    }

    /// `ensureType` (`:214-226`).
    fn lth_ensure_type(&mut self, st: &mut Lth, r: Res) -> Result<Res, MetaError> {
        if !st.check() {
            return Ok(r);
        }
        let ty = self.lth_type(st, r)?;
        if matches!(self.node(ty), Node::Sort { .. }) {
            return Ok(Res {
                expr: r.expr,
                ty: Some(ty),
            });
        }
        let w = self.whnf(ty)?;
        if !matches!(self.node(w), Node::Sort { .. }) {
            return Err(lth_err("type expected"));
        }
        let r2 = Res {
            expr: r.expr,
            ty: Some(w),
        };
        st.results.insert(r.expr, r2);
        Ok(r2)
    }

    /// `visitType` (`:247-249`).
    fn lth_visit_type(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        let r = self.lth_visit(st, e)?;
        self.lth_ensure_type(st, r)
    }

    /// `Expr.updateApp!`: `e` itself when both children are unchanged.
    fn lth_update_app(&mut self, e: ExprId, f: ExprId, a: ExprId) -> Result<ExprId, MetaError> {
        match self.node(e) {
            Node::App { f: f0, arg: a0 } if f0 == f && a0 == a => Ok(e),
            _ => Ok(self.scratch.expr_app(Some(self.view.store), f, a)?),
        }
    }

    /// `visitApp` (`:231-243`).
    fn lth_visit_app(&mut self, st: &mut Lth, e: ExprId, f: Res, a: Res) -> Result<Res, MetaError> {
        if !st.check() {
            let e2 = self.lth_update_app(e, f.expr, a.expr)?;
            return Ok(Res { expr: e2, ty: None });
        }
        let mut fty = self.lth_type(st, f)?;
        if !matches!(self.node(fty), Node::Forall { .. }) {
            fty = self.whnf(fty)?;
        }
        let Node::Forall {
            binder_type, body, ..
        } = self.node(fty)
        else {
            return Err(lth_err("function expected"));
        };
        let aty = self.lth_type(st, a)?;
        if !self.is_def_eq(binder_type, aty)? {
            return Err(lth_err("application type mismatch"));
        }
        let e2 = self.lth_update_app(e, f.expr, a.expr)?;
        let ty = self.instantiate1(body, a.expr)?;
        Ok(Res {
            expr: e2,
            ty: Some(ty),
        })
    }

    /// `visitAppArgs` (`:251-264`).
    fn lth_visit_app_args(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        if st.check() {
            let head = self.get_app_fn(e);
            if let Node::MVar { id: Some(m) } = self.node(head) {
                let args = self.get_app_args(e);
                self.lth_check_mvar(st, MVarId(m), &args)?;
            }
            self.lth_app_go(st, e)
        } else {
            let r = self.lth_app_go_unchecked(st, e)?;
            Ok(Res { expr: r, ty: None })
        }
    }

    /// `visitAppArgs.go` (`:255-257`): every prefix goes through the cache.
    fn lth_app_go(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        let Node::App { f, arg } = self.node(e) else {
            return self.lth_visit(st, e);
        };
        let fr = self.lth_check_cache(st, f, |c, st| c.guarded(|c| c.lth_app_go(st, f)))?;
        let ar = self.lth_visit(st, arg)?;
        self.lth_visit_app(st, e, fr, ar)
    }

    /// `visitAppArgs.go'` (`:261-263`): unchecked, no prefix caching.
    fn lth_app_go_unchecked(&mut self, st: &mut Lth, e: ExprId) -> Result<ExprId, MetaError> {
        let Node::App { f, arg } = self.node(e) else {
            return Ok(self.lth_visit(st, e)?.expr);
        };
        let f2 = self.guarded(|c| c.lth_app_go_unchecked(st, f))?;
        let a2 = self.lth_visit(st, arg)?.expr;
        self.lth_update_app(e, f2, a2)
    }

    /// `visitForall` (`:266-270`).
    fn lth_visit_forall(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        if self.lth_can_skip(e, 5) {
            return Ok(Res { expr: e, ty: None });
        }
        let cp = self.lctx_checkpoint();
        let r = self.lth_forall_go(st, e);
        self.lctx_restore(cp);
        r
    }

    /// `visitForall.go` (`:272-285`).
    fn lth_forall_go(&mut self, st: &mut Lth, e0: ExprId) -> Result<Res, MetaError> {
        let base = Some(self.view.store);
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut doms: Vec<Res> = Vec::new();
        let mut cur = e0;
        loop {
            // `findCacheNoBVars?` (`:150-151`, `:273-274`).
            if self.data(cur).loose_bvar_range() == 0 {
                if let Some(r) = st.results.get(&cur).copied() {
                    return self.lth_forall_finalize(st, &fvars, &doms, r);
                }
            }
            match self.node(cur) {
                Node::Forall {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    let t0 =
                        instantiate_rev(self.scratch, base, binder_type, &fvars, &mut self.guard)?;
                    let t = self.lth_visit_type(st, t0)?;
                    let x = self.push_local_decl_without_instance(
                        binder_name,
                        t.expr,
                        binder_info,
                        LocalDeclKind::Default,
                    )?;
                    fvars.push(x);
                    doms.push(t);
                    cur = body;
                }
                _ => {
                    let b = instantiate_rev(self.scratch, base, cur, &fvars, &mut self.guard)?;
                    let r = self.lth_visit(st, b)?;
                    return self.lth_forall_finalize(st, &fvars, &doms, r);
                }
            }
        }
    }

    /// `visitForall.finalize` (`:286-294`): `LocalContext.mkForall`
    /// (`LocalContext.lean:554-586`; every telescope decl is a cdecl, so it
    /// is pure abstraction, no head-beta), then under check the
    /// `mkLevelIMax'` fold of the domain levels onto the body's.
    fn lth_forall_finalize(
        &mut self,
        st: &mut Lth,
        fvars: &[ExprId],
        doms: &[Res],
        body: Res,
    ) -> Result<Res, MetaError> {
        let base = Some(self.view.store);
        let mut e2 = abstract_fvars(self.scratch, base, body.expr, fvars, &mut self.guard)?;
        for i in (0..fvars.len()).rev() {
            let (name, ty, bi) = self.lth_decl_parts(fvars[i])?;
            let ty = abstract_fvars(self.scratch, base, ty, &fvars[..i], &mut self.guard)?;
            e2 = self.scratch.expr_forall(base, name, ty, e2, bi)?;
        }
        if !st.check() {
            return Ok(Res { expr: e2, ty: None });
        }
        let bt = self.lth_ensure_type(st, body)?.ty;
        let Some(Node::Sort { level: mut u }) = bt.map(|t| self.node(t)) else {
            return Err(lth_err("type expected"));
        };
        for dom in doms.iter().rev() {
            let dt = self.lth_type(st, *dom)?;
            let Node::Sort { level } = self.node(dt) else {
                return Err(lth_err("type expected"));
            };
            u = self.mk_level_imax_prime(level, u)?;
        }
        let ty = self.scratch.expr_sort(base, u)?;
        Ok(Res {
            expr: e2,
            ty: Some(ty),
        })
    }

    /// A telescope fvar's `(binderName, type, binderInfo)`.
    fn lth_decl_parts(
        &self,
        x: ExprId,
    ) -> Result<(Option<NameId>, ExprId, leanr_kernel::BinderInfo), MetaError> {
        let d = self
            .fvar_id_of(x)
            .and_then(|fid| self.lctx.get(fid))
            .ok_or_else(|| lth_err("unknown free variable"))?;
        Ok((d.binder_name, d.ty, d.binder_info))
    }

    /// `visitLambdaLet` (`:302-306`).
    fn lth_visit_lambda_let(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        if self.lth_can_skip(e, 5) {
            return Ok(Res { expr: e, ty: None });
        }
        let cp = self.lctx_checkpoint();
        let saved = st.let_fvars.len();
        let r = self.lth_lambda_let_go(st, e);
        st.let_fvars.truncate(saved);
        self.lctx_restore(cp);
        r
    }

    /// `visitLambdaLet.go` (`:313-334`). `st.let_fvars` is the oracle's
    /// `letFVars` argument (see the module doc).
    fn lth_lambda_let_go(&mut self, st: &mut Lth, e0: ExprId) -> Result<Res, MetaError> {
        let base = Some(self.view.store);
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut cur = e0;
        loop {
            match self.node(cur) {
                Node::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    let t0 =
                        instantiate_rev(self.scratch, base, binder_type, &fvars, &mut self.guard)?;
                    let t = self.lth_visit_type(st, t0)?;
                    let x = self.push_local_decl_without_instance(
                        binder_name,
                        t.expr,
                        binder_info,
                        LocalDeclKind::Default,
                    )?;
                    fvars.push(x);
                    cur = body;
                }
                Node::LetE {
                    decl_name,
                    ty,
                    value,
                    body,
                    non_dep,
                } => {
                    let t0 = instantiate_rev(self.scratch, base, ty, &fvars, &mut self.guard)?;
                    let t = self.lth_visit_type(st, t0)?;
                    let v0 = instantiate_rev(self.scratch, base, value, &fvars, &mut self.guard)?;
                    let v = self.lth_visit(st, v0)?;
                    // `:325-328`: under an enclosing genuine let, the value's
                    // type must match, in the context BEFORE this let.
                    if st.check() {
                        let vty = self.lth_type(st, v)?;
                        if !self.is_def_eq(t.expr, vty)? {
                            return Err(lth_err("invalid let declaration"));
                        }
                    }
                    let x =
                        self.push_let_decl_without_instance(decl_name, t.expr, v.expr, non_dep)?;
                    if !non_dep {
                        // `fvarId :: letFVars` (`:331`).
                        let fid = self.fvar_id_of(x).ok_or_else(|| lth_err("not an fvar"))?;
                        st.let_fvars.push(fid);
                    }
                    fvars.push(x);
                    cur = body;
                }
                _ => {
                    let b = instantiate_rev(self.scratch, base, cur, &fvars, &mut self.guard)?;
                    let body = self.lth_visit(st, b)?;
                    return self.lth_lambda_let_finalize(&fvars, body);
                }
            }
        }
    }

    /// `visitLambdaLet.finalize` (`:338-368`): rebuild, turning each
    /// genuine let whose fvar was never unfolded into a `have`.
    fn lth_lambda_let_finalize(&mut self, fvars: &[ExprId], body: Res) -> Result<Res, MetaError> {
        let base = Some(self.view.store);
        let mut expr = abstract_fvars(self.scratch, base, body.expr, fvars, &mut self.guard)?;
        let mut ty = match body.ty {
            Some(t) => Some(abstract_fvars(
                self.scratch,
                base,
                t,
                fvars,
                &mut self.guard,
            )?),
            None => None,
        };
        for i in (0..fvars.len()).rev() {
            let fid = self
                .fvar_id_of(fvars[i])
                .ok_or_else(|| lth_err("not an fvar"))?;
            let (name, t, bi, value) = {
                let d = self
                    .lctx
                    .get(fid)
                    .ok_or_else(|| lth_err("unknown free variable"))?;
                (d.binder_name, d.ty, d.binder_info, d.value)
            };
            let t = abstract_fvars(self.scratch, base, t, &fvars[..i], &mut self.guard)?;
            match value {
                None => {
                    expr = self.scratch.expr_lam(base, name, t, expr, bi)?;
                    ty = match ty {
                        Some(ty) => Some(self.scratch.expr_forall(base, name, t, ty, bi)?),
                        None => None,
                    };
                }
                Some(v) => {
                    let decl_nondep = self.local_entry(fid).is_some_and(|en| en.nondep);
                    let nondep = decl_nondep || !self.zeta_delta_fvar_ids.contains(&fid);
                    let v = abstract_fvars(self.scratch, base, v, &fvars[..i], &mut self.guard)?;
                    expr = self.scratch.expr_let(base, name, t, v, expr, nondep)?;
                    ty = match ty {
                        Some(ty) if self.has_loose_bvar(ty, 0)? => {
                            Some(self.scratch.expr_let(base, name, t, v, ty, nondep)?)
                        }
                        Some(ty) => Some(lower_loose_bvars(
                            self.scratch,
                            base,
                            ty,
                            1,
                            1,
                            &mut self.guard,
                        )?),
                        None => None,
                    };
                }
            }
        }
        Ok(Res { expr, ty })
    }

    /// `visitProj` (`:370-396`), with `matchConstStructure`
    /// (`MonadEnv.lean:153-160`).
    fn lth_visit_proj(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        let base = Some(self.view.store);
        let (struct_name, idx, structure) = match self.node(e) {
            Node::Proj {
                type_name,
                idx,
                structure,
            } => (type_name, Nat::from(u64::from(idx)), structure),
            Node::ProjBig {
                type_name,
                idx,
                structure,
            } => (type_name, self.scratch.nat_at(base, idx).clone(), structure),
            _ => return Err(lth_err("not a projection")),
        };
        let s = self.lth_visit(st, structure)?;
        // `e.updateProj! struct`.
        let e2 = if s.expr == structure {
            e
        } else {
            self.scratch.expr_proj(base, struct_name, &idx, s.expr)?
        };
        if !st.check() {
            return Ok(Res { expr: e2, ty: None });
        }
        let failed = || lth_err("invalid projection");
        let sty = self.lth_type(st, s)?;
        let struct_type = self.whnf(sty)?;
        let prop = self.is_prop(struct_type)?;
        // `matchConstStructure structType.getAppFn`.
        let Node::Const {
            name: Some(ind_name),
            levels,
        } = self.node(self.get_app_fn(struct_type))
        else {
            return Err(failed());
        };
        let Some(ConstantInfo::Induct(ival)) = self.view.get(ind_name) else {
            return Err(failed());
        };
        let [ctor_name] = ival.ctors[..] else {
            return Err(failed());
        };
        if !matches!(self.view.get(ctor_name), Some(ConstantInfo::Ctor(_))) {
            return Err(failed());
        }
        if Some(ind_name) != struct_name {
            return Err(failed());
        }
        let struct_type_args = self.get_app_args(struct_type);
        let n_params = ival.num_params.to_usize().ok_or_else(failed)?;
        let n_indices = ival.num_indices.to_usize().ok_or_else(failed)?;
        if n_params + n_indices != struct_type_args.len() {
            return Err(failed());
        }
        let idx = idx.to_usize().ok_or_else(failed)?;
        let ctor = self.scratch.expr_const(base, Some(ctor_name), levels)?;
        let ctor_app = self.mk_app_spine(ctor, &struct_type_args[..n_params])?;
        let mut ctor_type = self.infer_type(ctor_app)?;
        let mut args: Vec<ExprId> = Vec::new();
        let mut j = 0usize;
        let mut last_field_ty = None;
        for i in 0..=idx {
            if !matches!(self.node(ctor_type), Node::Forall { .. }) {
                let t =
                    instantiate_rev(self.scratch, base, ctor_type, &args[j..i], &mut self.guard)?;
                ctor_type = self.whnf(t)?;
                j = i;
            }
            let Node::Forall {
                binder_type, body, ..
            } = self.node(ctor_type)
            else {
                return Err(failed());
            };
            let dom = instantiate_rev(
                self.scratch,
                base,
                binder_type,
                &args[j..i],
                &mut self.guard,
            )?;
            if prop && !self.is_prop(dom)? {
                return Err(failed());
            }
            let pi = self
                .scratch
                .expr_proj(base, struct_name, &Nat::from(i as u64), s.expr)?;
            args.push(pi);
            ctor_type = body;
            last_field_ty = Some(dom);
        }
        let ty = self.lth_cleanup_annotations(last_field_ty.ok_or_else(failed)?);
        Ok(Res {
            expr: e2,
            ty: Some(ty),
        })
    }

    /// `Expr.cleanupAnnotations` (`Lean/Expr.lean:1754-1756`): strip `mdata`
    /// (`consumeMData`) and the `optParam`/`autoParam` (arity 2, keep the
    /// first argument) and `outParam`/`semiOutParam` (arity 1) gadgets
    /// (`consumeTypeAnnotations`, `:1739-1745`; `:1709-1723`), to a
    /// fixpoint.
    fn lth_cleanup_annotations(&self, e: ExprId) -> ExprId {
        let base = Some(self.view.store);
        let mut cur = e;
        loop {
            match self.node(cur) {
                Node::MData { expr, .. } => cur = expr,
                Node::App { .. } => {
                    let Node::Const { name: Some(n), .. } = self.node(self.get_app_fn(cur)) else {
                        return cur;
                    };
                    let NameRow::Str { parent: None, part } = self.scratch.name_row(base, n) else {
                        return cur;
                    };
                    let arity = self.get_app_num_args(cur);
                    let strip = matches!(
                        (self.scratch.str_at(base, *part), arity),
                        ("optParam", 2) | ("autoParam", 2) | ("outParam", 1) | ("semiOutParam", 1)
                    );
                    if !strip {
                        return cur;
                    }
                    cur = self.get_app_args(cur)[0];
                }
                _ => return cur,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use leanr_kernel::bank::terms::Node;
    use leanr_kernel::bank::ExprId;
    use leanr_kernel::BinderInfo;

    use crate::test_support::{
        app, bvar, c, cu, fresh_mvar, fresh_mvar_in_lctx, lit_level, on_8mib_stack, with_meta0_ctx,
        with_prelude0_ctx,
    };
    use crate::{AuxLemmas, MVarId, MetaCtx, MetaError};

    fn aux(ctx: &mut MetaCtx, s: &str) -> AuxLemmas {
        let base = Some(ctx.view.store);
        let s = ctx.scratch.intern_str(base, s).unwrap();
        AuxLemmas::new(ctx.scratch.name_str(base, None, s).unwrap())
    }

    /// The `nondep` bits of the `letE` spine, outermost first, following
    /// let/lambda bodies and application heads.
    fn nondeps(ctx: &MetaCtx, mut e: ExprId) -> Vec<bool> {
        let mut out = Vec::new();
        loop {
            match ctx.node(e) {
                Node::LetE { body, non_dep, .. } => {
                    out.push(non_dep);
                    e = body;
                }
                Node::Lam { body, .. } => e = body,
                Node::App { f, .. } => e = f,
                _ => return out,
            }
        }
    }

    fn type0(ctx: &mut MetaCtx) -> ExprId {
        let base = Some(ctx.view.store);
        let one = lit_level(ctx, 1);
        ctx.scratch.expr_sort(base, one).unwrap()
    }

    fn mk_let(ctx: &mut MetaCtx, ty: ExprId, v: ExprId, b: ExprId, nondep: bool) -> ExprId {
        let base = Some(ctx.view.store);
        ctx.scratch.expr_let(base, None, ty, v, b, nondep).unwrap()
    }

    /// `let x : N := N.zero; x` → `have` (`finalize`, `:354-358`): nothing
    /// unfolds `x` under check.
    #[test]
    fn an_unused_value_becomes_a_have() {
        with_prelude0_ctx(|ctx| {
            let n = c(ctx, "N");
            let zero = c(ctx, "N.zero");
            let b0 = bvar(ctx, 0);
            let e = mk_let(ctx, n, zero, b0, false);
            let a = aux(ctx, "lth");
            let r = ctx.let_to_have(&a, e).unwrap();
            assert_eq!(nondeps(ctx, r), vec![true]);
        });
    }

    /// `let T : Type := N; (fun (z : T) => z) N.zero` keeps `T` a `let`:
    /// visitApp's `isDefEq T N` (`:238`) unfolds `T` under check.
    #[test]
    fn a_definitionally_used_let_stays_a_let() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = c(ctx, "N");
            let zero = c(ctx, "N.zero");
            let ty1 = type0(ctx);
            let b0 = bvar(ctx, 0);
            // fun (z : T) => z — the binder type `#0` is `T` (it sits
            // outside the lambda's own binder); the body `#0` is `z`.
            let lam = ctx
                .scratch
                .expr_lam(base, None, b0, b0, BinderInfo::Default)
                .unwrap();
            let body = app(ctx, lam, zero);
            let e = mk_let(ctx, ty1, n, body, false);
            ctx.infer_type(e).expect("well typed");
            let a = aux(ctx, "lth");
            let r = ctx.let_to_have(&a, e).unwrap();
            assert_eq!(nondeps(ctx, r), vec![false]);
        });
    }

    /// Review Focus 3: no genuine let → the input id itself, and no visit
    /// at all (`hasDepLet` early exit, `:420`). The `have`'s value is deep
    /// enough (`approxDepth` 7) that neither `checkCache`'s `canSkip 2` nor
    /// `visitLambdaLet`'s `canSkip 5` would skip it, so without the early
    /// exit the pass would visit (and step), even though hash-consing
    /// would rebuild the same id.
    #[test]
    fn no_dependent_let_is_the_identity() {
        with_prelude0_ctx(|ctx| {
            let n = c(ctx, "N");
            let succ = c(ctx, "N.succ");
            let mut v = c(ctx, "N.zero");
            for _ in 0..6 {
                v = app(ctx, succ, v);
            }
            let b0 = bvar(ctx, 0);
            let e = mk_let(ctx, n, v, b0, true);
            let a = aux(ctx, "lth");
            // The entry `instantiateMVars` (`:442`) is the only work allowed.
            let s0 = ctx.steps();
            ctx.instantiate_mvars(e).unwrap();
            let inst_steps = ctx.steps() - s0;
            let s1 = ctx.steps();
            assert_eq!(ctx.let_to_have(&a, e).unwrap(), e);
            assert_eq!(
                ctx.steps() - s1,
                inst_steps,
                "the early exit visits nothing"
            );
        });
    }

    /// `let T : Type := N; let y : T := N.zero; N.zero`: the inner value is
    /// checked against its declared type (`isDefEq T N`, `:325-328`) because
    /// an outer genuine let is in scope, which unfolds `T`; `y` is unused.
    #[test]
    fn a_value_check_under_a_let_records_the_outer_let() {
        with_prelude0_ctx(|ctx| {
            let n = c(ctx, "N");
            let zero = c(ctx, "N.zero");
            let ty = type0(ctx);
            let b0 = bvar(ctx, 0);
            let inner = mk_let(ctx, b0, zero, zero, false);
            let e = mk_let(ctx, ty, n, inner, false);
            ctx.infer_type(e).expect("well typed");
            let a = aux(ctx, "lth");
            let r = ctx.let_to_have(&a, e).unwrap();
            assert_eq!(nondeps(ctx, r), vec![false, true]);
        });
    }

    /// The telescope extends a bare local context (`lctx.mkLetDecl`,
    /// `:330`), with no `isClass?` test. `let T : Type := N; fun (z : (fun A
    /// => A) T) => let y : (fun A => A) T := z; y`: nothing the oracle runs
    /// unfolds `T` (the value check is `isDefEq` of one expression with
    /// itself), so both lets become `have`s. `is_class` on `y`'s type would
    /// `whnf` the beta-redex to `T` and unfold it, recording `T`.
    #[test]
    fn a_let_is_declared_without_a_class_test() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = c(ctx, "N");
            let ty = type0(ctx);
            let b0 = bvar(ctx, 0);
            let b1 = bvar(ctx, 1);
            let id_ty = ctx
                .scratch
                .expr_lam(base, None, ty, b0, BinderInfo::Default)
                .unwrap();
            // Under `T` (#0): `(fun A => A) T`; under `T, z` (#1 is `T`).
            let redex0 = app(ctx, id_ty, b0);
            let redex1 = app(ctx, id_ty, b1);
            let inner = mk_let(ctx, redex1, b0, b0, false);
            let lam = ctx
                .scratch
                .expr_lam(base, None, redex0, inner, BinderInfo::Default)
                .unwrap();
            let e = mk_let(ctx, ty, n, lam, false);
            ctx.infer_type(e).expect("well typed");
            let a = aux(ctx, "lth");
            let r = ctx.let_to_have(&a, e).unwrap();
            assert_eq!(nondeps(ctx, r), vec![true, true]);
        });
    }

    /// Review Focus 1: a deep chain of let BODIES (the telescope loop) ends
    /// in Ok or DepthBudgetExhausted, never a stack overflow.
    #[test]
    fn a_deep_let_chain_never_overflows() {
        on_8mib_stack(|| {
            with_prelude0_ctx(|ctx| {
                let n = c(ctx, "N");
                let zero = c(ctx, "N.zero");
                let mut e = bvar(ctx, 0);
                for _ in 0..5000 {
                    e = mk_let(ctx, n, zero, e, false);
                }
                let a = aux(ctx, "lth");
                match ctx.let_to_have(&a, e) {
                    Ok(r) => assert!(nondeps(ctx, r).iter().all(|&b| b)),
                    Err(MetaError::DepthBudgetExhausted) => {}
                    Err(other) => panic!("unexpected {other:?}"),
                }
            });
        });
    }

    /// Review Focus 1, the recursive shape: lets nested in let VALUES
    /// (`let x := (let y := (…); y); x`) recurse through `visit`, which
    /// must go through `guarded`.
    #[test]
    fn a_deep_let_nest_in_values_never_overflows() {
        on_8mib_stack(|| {
            with_prelude0_ctx(|ctx| {
                let n = c(ctx, "N");
                let mut e = c(ctx, "N.zero");
                let b0 = bvar(ctx, 0);
                for _ in 0..20_000 {
                    e = mk_let(ctx, n, e, b0, false);
                }
                let a = aux(ctx, "lth");
                match ctx.let_to_have(&a, e) {
                    Ok(_) | Err(MetaError::DepthBudgetExhausted) => {}
                    Err(other) => panic!("unexpected {other:?}"),
                }
            });
        });
    }

    /// Review Focus 4: `checkCache` (`:137-147`) returns a cached result even
    /// when it was computed with check OFF. `bad := N.succ (fun (z : N) =>
    /// N.succ (N.succ z))` applies `N.succ` to a function, and is deep
    /// enough (`approxDepth` 4) that `canSkip 2` does not skip it. In
    /// `N.succ bad (let x : N := N.zero; bad)` the head application is
    /// visited unchecked (no let in scope), caching `bad` with `type? :=
    /// none`; under the let, the same `bad` is a cache hit and is NOT
    /// re-checked, so the pass succeeds. A re-visit would run visitApp's
    /// `isDefEq N (N → N)` (`:238`) and throw. (The ill-typed input is what
    /// makes the reuse observable: on a well-typed subterm a re-check
    /// reaches the same verdict.)
    #[test]
    fn cached_unchecked_subterm_is_not_rechecked() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = c(ctx, "N");
            let zero = c(ctx, "N.zero");
            let succ = c(ctx, "N.succ");
            let b0 = bvar(ctx, 0);
            let s1 = app(ctx, succ, b0);
            let s2 = app(ctx, succ, s1);
            let f = ctx
                .scratch
                .expr_lam(base, None, n, s2, BinderInfo::Default)
                .unwrap();
            let bad = app(ctx, succ, f);
            let inner = mk_let(ctx, n, zero, bad, false);
            let head = app(ctx, succ, bad);
            let e = app(ctx, head, inner);
            let a = aux(ctx, "lth");
            let r = ctx.let_to_have(&a, e).expect("the cached result is reused");
            let Node::App { arg, .. } = ctx.node(r) else {
                panic!("an app")
            };
            assert_eq!(nondeps(ctx, arg), vec![true]);
        });
    }

    /// `checkMVar` (`:183-194`): `let x : N := N.zero; ?m x` where `?m` is
    /// delayed-assigned over a pending mvar whose context binds the matching
    /// fvar as a genuine let. Under check the mvar marks `x` (through
    /// `visitDepExpr` on the argument, and again through `visitMVar`'s
    /// empty-args call, `:198`), so `x` stays a `let`.
    #[test]
    fn a_delayed_assigned_mvar_under_a_let_keeps_the_let() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = c(ctx, "N");
            let zero = c(ctx, "N.zero");
            let cp = ctx.lctx_checkpoint();
            let y = ctx.push_let_decl(None, n, zero, false).unwrap();
            let pending = fresh_mvar_in_lctx(ctx, n);
            ctx.lctx_restore(cp);
            let Node::MVar { id: Some(pid) } = ctx.node(pending) else {
                panic!("an mvar")
            };
            let arrow = ctx
                .scratch
                .expr_forall(base, None, n, n, BinderInfo::Default)
                .unwrap();
            let (m, mid) = fresh_mvar(ctx, arrow);
            ctx.mctx_mut()
                .assign_delayed(mid, vec![y], MVarId(pid))
                .unwrap();
            let b0 = bvar(ctx, 0);
            let body = app(ctx, m, b0);
            let e = mk_let(ctx, n, zero, body, false);
            let a = aux(ctx, "lth");
            let r = ctx.let_to_have(&a, e).unwrap();
            assert_eq!(nondeps(ctx, r), vec![false]);
        });
    }

    /// `checkMVar`'s argument path (`:191-194`) after a prefix-cache hit.
    /// `PProd.mk N N (let a : N := N.zero; ?m a) (let x : N := N.succ N.zero;
    /// ?m x)`, `?m` delayed-assigned over a genuine-let fvar. The outer
    /// application is unchecked. In the first let scope, `go` caches the
    /// bare head `?m` through `checkCache f` (`:257`); its visitMVar
    /// (`:198`) marks `a`. In the second scope `?m` is a cache hit, so
    /// visitMVar never runs: only `checkMVar ?m #[x]` → `visitDepExpr x`
    /// marks `x`. Both lets stay `let`s.
    #[test]
    fn a_delayed_mvar_head_cached_in_a_sibling_let_still_marks_the_arg() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = c(ctx, "N");
            let zero = c(ctx, "N.zero");
            let cp = ctx.lctx_checkpoint();
            let y = ctx.push_let_decl(None, n, zero, false).unwrap();
            let pending = fresh_mvar_in_lctx(ctx, n);
            ctx.lctx_restore(cp);
            let Node::MVar { id: Some(pid) } = ctx.node(pending) else {
                panic!("an mvar")
            };
            let arrow = ctx
                .scratch
                .expr_forall(base, None, n, n, BinderInfo::Default)
                .unwrap();
            let (m, mid) = fresh_mvar(ctx, arrow);
            ctx.mctx_mut()
                .assign_delayed(mid, vec![y], MVarId(pid))
                .unwrap();
            let b0 = bvar(ctx, 0);
            let body = app(ctx, m, b0);
            let l1 = mk_let(ctx, n, zero, body, false);
            // A different value, so the two lets are distinct terms and the
            // second is not itself a cache hit.
            let succ = c(ctx, "N.succ");
            let one_n = app(ctx, succ, zero);
            let l2 = mk_let(ctx, n, one_n, body, false);
            let one = lit_level(ctx, 1);
            let mk = cu(ctx, "PProd.mk", &[one, one]);
            let e = ctx.mk_app_spine(mk, &[n, n, l1, l2]).unwrap();
            ctx.infer_type(e).expect("well typed");
            let a = aux(ctx, "lth");
            let r = ctx.let_to_have(&a, e).unwrap();
            let args = ctx.get_app_args(r);
            assert_eq!(nondeps(ctx, args[2]), vec![false], "first scope");
            assert_eq!(nondeps(ctx, args[3]), vec![false], "second scope");
        });
    }

    /// `visitProj` (`:370-396`): `let T : Type := PProd.{1,1} N N; fun (p :
    /// T) => p.1`. The projection's `whnf` of the structure type (`:373`)
    /// unfolds `T`, so it stays a `let`; nothing else under check can.
    #[test]
    fn a_projection_through_a_let_typed_structure_keeps_the_let() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = c(ctx, "N");
            let one = lit_level(ctx, 1);
            let pprod = cu(ctx, "PProd", &[one, one]);
            let pnn = ctx.mk_app_spine(pprod, &[n, n]).unwrap();
            let ty = type0(ctx);
            let b0 = bvar(ctx, 0);
            let pprod_name = {
                let Node::Const { name, .. } = ctx.node(pprod) else {
                    panic!("a const")
                };
                name
            };
            let proj = ctx
                .scratch
                .expr_proj(base, pprod_name, &leanr_kernel::Nat::from(0u64), b0)
                .unwrap();
            let lam = ctx
                .scratch
                .expr_lam(base, None, b0, proj, BinderInfo::Default)
                .unwrap();
            let e = mk_let(ctx, ty, pnn, lam, false);
            ctx.infer_type(e).expect("well typed");
            let a = aux(ctx, "lth");
            let r = ctx.let_to_have(&a, e).unwrap();
            assert_eq!(nondeps(ctx, r), vec![false]);
        });
    }

    /// An abstracted proof under a genuine let: check mode's `visitConst`
    /// (`:201-208`) looks up `fooP._proof_1`, which is only pending, and
    /// the error becomes the named M4c-1 seam.
    #[test]
    fn a_pending_aux_constant_under_a_let_is_the_named_seam() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = c(ctx, "N");
            let zero = c(ctx, "N.zero");
            let succ = c(ctx, "N.succ");
            let one = lit_level(ctx, 1);
            let sz = app(ctx, succ, zero);
            let eq = cu(ctx, "Eq", &[one]);
            let eq_ty = ctx.mk_app_spine(eq, &[n, sz, sz]).unwrap();
            let rfl = cu(ctx, "rfl", &[one]);
            let pf = ctx.mk_app_spine(rfl, &[n, sz]).unwrap();
            // let x : N := N.zero; (fun (h : N.succ N.zero = N.succ N.zero) => x) rfl
            let b1 = bvar(ctx, 1);
            let lam = ctx
                .scratch
                .expr_lam(base, None, eq_ty, b1, BinderInfo::Default)
                .unwrap();
            let body = app(ctx, lam, pf);
            let e = mk_let(ctx, n, zero, body, false);
            ctx.infer_type(e).expect("well typed");
            let mut a = aux(ctx, "fooP");
            let e = ctx.abstract_nested_proofs(&mut a, e).unwrap();
            assert_eq!(a.pending().len(), 1, "the rfl is abstracted");
            match ctx.let_to_have(&a, e) {
                Err(MetaError::Unsupported(m)) => assert_eq!(
                    m,
                    "letToHave: lookup of pending aux lemma fooP._proof_1 — \
                     M4c-1 seam (needs pending-constant overlay)"
                ),
                other => panic!("expected the seam, got {:?}", other.map(|_| ())),
            }
        });
    }
}
