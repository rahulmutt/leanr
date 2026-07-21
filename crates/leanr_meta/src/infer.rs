//! Meta-level type inference: `MetaCtx::infer_type` and its per-arm
//! helpers.
//!
//! oracle: `Lean.Meta.inferTypeImp` and its private per-arm helpers,
//! `src/lean/Lean/Meta/InferType.lean`, toolchain
//! leanprover/lean4:v4.33.0-rc1. Every arm below cites the exact line
//! range read from that file (not from memory — see the module's own
//! git history / task report for the read).
//!
//! **Inference never checks**: no defeq of argument types anywhere.
//! The kernel (`leanr_kernel::tc`) is the independent checker; any
//! shape violation this module meets becomes `MetaError::Infer`, never
//! a panic — incompleteness, never unsoundness (spec § infer.rs, and
//! `MetaError`'s own module doc).
//!
//! # Recursion: `infer_type`, not `infer_core`, for every subterm
//!
//! Every arm below that needs the type of a DIFFERENT subterm calls
//! `self.infer_type(x)` (the guarded, step-counted public entry), not
//! `self.infer_core(x)` directly. This is a deliberate departure from
//! this task's own brief, which sketched `infer_app`'s loop as
//! `infer_core(f)`: the oracle's `inferTypeImp` wraps the WHOLE
//! dispatch in `withIncRecDepth` exactly once and its per-arm helpers
//! (`inferAppType`, `inferForallType`, ...) all call the PUBLIC
//! `inferType` — which re-enters `inferTypeImp`, and so re-enters
//! `withIncRecDepth` — for every subterm; the only bypass is
//! `inferTypeImp`'s own local `.mdata _ e => infer e` shortcut, kept
//! below in `infer_core`'s own `MData` arm. Mirroring the brief's
//! `infer_core(f)` literally would mean `guard_depth` (capped at
//! `MAX_REC_DEPTH = 1_000_000`) and `stacker::maybe_grow`'s stack
//! reservation both fire ONLY at the outermost `infer_type` call, so a
//! deeply nested (not even adversarial — just deep) term would recurse
//! through `infer_core`'s Rust call stack with NO depth cap and no
//! further stack growth, i.e. a real, ungraceful stack overflow rather
//! than `MetaError::DepthBudgetExhausted`. `leanr_kernel::tc.rs`'s own
//! `infer_type_core` (the checker's twin of this function) already
//! re-enters `self.guarded(..)` on every recursive call for exactly
//! this reason; this module matches that real, tested precedent
//! instead of the brief's illustrative pseudocode.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, LevelsId, NameId};
use leanr_kernel::{
    abstract_fvars, instantiate, instantiate_level_params, instantiate_rev, ConstantInfo, Level,
    Nat,
};

use crate::{MVarId, MetaCtx, MetaError};

impl<'e> MetaCtx<'e> {
    /// oracle: `inferTypeImp` (InferType.lean:238-254). Inference
    /// without checking — the kernel re-checks everything downstream.
    pub fn infer_type(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        self.step()?;
        self.guarded(|s| s.infer_core(e))
    }

    /// oracle: `inferTypeImp`'s local `infer` (InferType.lean:239-253)
    /// plus `checkInferTypeCache` (:206-219) folded into the cache
    /// probe/insert around the match, as the brief's skeleton lays out.
    fn infer_core(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let key = (self.cfg().cache_key(), e);
        let use_cache = self.cacheable(e);
        if use_cache {
            if let Some(&t) = self.infer_cache.get(&key) {
                return Ok(t);
            }
        }
        let t = match self.node(e) {
            Node::Const { name, levels } => self.infer_const(name, levels)?,
            Node::Proj { .. } | Node::ProjBig { .. } => self.infer_proj(e)?,
            Node::App { .. } => self.infer_app(e)?,
            Node::MVar { id } => self.infer_mvar(id)?,
            Node::FVar { id } => self.infer_fvar(id)?,
            Node::BVar { .. } | Node::BVarBig { .. } => {
                return Err(MetaError::Infer("unexpected bound variable".into()))
            }
            // oracle: `.mdata _ e => infer e` (:248) — the ONE arm that
            // recurses through the local `infer` shortcut rather than
            // the public `inferType`; see this module's doc comment.
            Node::MData { expr, .. } => self.infer_core(expr)?,
            Node::LitNat { .. } => self.lit_type("Nat")?,
            Node::LitStr { .. } => self.lit_type("String")?,
            Node::Sort { level } => self.sort_succ(level)?,
            Node::Forall { .. } => self.infer_forall(e)?,
            Node::Lam { .. } | Node::LetE { .. } => self.infer_lambda(e)?,
        };
        if use_cache {
            self.infer_cache.insert(key, t);
        }
        Ok(t)
    }

    /// oracle: `inferConstType` (InferType.lean:121-126). Level-param
    /// arity mismatch is `Infer`, never a panic (oracle
    /// `throwIncorrectNumberOfLevels`, :118-119).
    fn infer_const(&mut self, name: Option<NameId>, levels: LevelsId) -> Result<ExprId, MetaError> {
        let info = self.env_get(name)?;
        let cv = info.constant_val();
        let level_ids: Vec<LevelId> = self
            .scratch
            .level_list_at(Some(self.view.store), levels)
            .to_vec();
        if cv.level_params.len() != level_ids.len() {
            let nm = self.scratch.to_name(Some(self.view.store), name);
            return Err(MetaError::Infer(format!(
                "incorrect number of universe levels for '{nm}': expected {}, got {}",
                cv.level_params.len(),
                level_ids.len()
            )));
        }
        let (ty, params) = (cv.ty, cv.level_params.clone());
        Ok(instantiate_level_params(
            self.scratch,
            Some(self.view.store),
            ty,
            &params,
            &level_ids,
            &mut self.guard,
        )?)
    }

    /// oracle: `inferAppType` (InferType.lean:106-116). Shared by the
    /// `App` arm and `inferProjType`'s constructor-parameter
    /// application (:140), exactly as the oracle reuses one function
    /// for both.
    ///
    /// Both instantiations of `f_type` use `instantiate_beta_rev`, not
    /// plain `instantiate_rev` — oracle: `fType.instantiateBetaRevRange
    /// j i args` / `fType.instantiateBetaRevRange j args.size args`
    /// (InferType.lean:113, :116). The plain substitution was this
    /// module's oracle-fast divergence (task 9 burn-down, 15/80 corpus
    /// records — every recursor-shaped `infer` query: `count`, `add`,
    /// `N.noConfusionType`, `N.brecOn.go`, `Eq.ndrec`, ...): a recursor's
    /// motive parameter is substituted with a literal `fun x => T`, and
    /// plain `instantiate_rev` leaves the unreduced redex `(fun x => T)
    /// major` where the oracle's beta-aware substitution produces
    /// `T[major/x]` directly (`instantiateBetaRevRange`'s own doc
    /// comment cites this exact `motive`-substitution scenario as its
    /// reason for existing).
    fn infer_app_type(&mut self, f: ExprId, args: &[ExprId]) -> Result<ExprId, MetaError> {
        let mut f_type = self.infer_type(f)?;
        let mut j = 0usize;
        let nargs = args.len();
        for i in 0..nargs {
            if let Node::Forall { body, .. } = self.node(f_type) {
                f_type = body;
            } else {
                let pending = self.instantiate_beta_rev(f_type, &args[j..i])?;
                let w = self.whnf(pending)?;
                match self.node(w) {
                    Node::Forall { body, .. } => {
                        j = i;
                        f_type = body;
                    }
                    _ => return Err(MetaError::Infer("function expected".into())),
                }
            }
        }
        self.instantiate_beta_rev(f_type, &args[j..nargs])
    }

    /// oracle: `Expr.instantiateBetaRevRange` (Lean/Meta/InferType.lean:
    /// 19-99, toolchain leanprover/lean4:v4.33.0-rc1). `instantiate_rev`'s
    /// pure-substitution twin, except: whenever a substitution replaces a
    /// bvar sitting at the HEAD of an application spine, the (already
    /// substituted) spine is beta-reduced against it too (`Expr.betaRev`,
    /// `ibr_app`/`beta_rev` below) — see `infer_app_type`'s doc comment
    /// for why this matters. `subst` follows `instantiate_rev`'s own
    /// convention (innermost-first: `subst[subst.len()-1]` replaces
    /// `#0`).
    fn instantiate_beta_rev(&mut self, e: ExprId, subst: &[ExprId]) -> Result<ExprId, MetaError> {
        if subst.is_empty() {
            return Ok(e);
        }
        self.ibr_visit(e, 0, subst)
    }

    /// Guarded recursive entry (the `infer_type`/`whnf` idiom: one
    /// `guarded` call per logical recursive step, re-entered on every
    /// call rather than grouped per-node like the kernel's own
    /// `instantiate_go` — this module's established style, see this
    /// file's own doc comment on recursing via guarded public entries).
    fn ibr_visit(&mut self, e: ExprId, offset: u32, subst: &[ExprId]) -> Result<ExprId, MetaError> {
        if (self.data(e).loose_bvar_range() as u64) <= offset as u64 {
            return Ok(e);
        }
        self.guarded(|s| s.ibr_visit_core(e, offset, subst))
    }

    fn ibr_visit_core(
        &mut self,
        e: ExprId,
        offset: u32,
        subst: &[ExprId],
    ) -> Result<ExprId, MetaError> {
        match self.node(e) {
            Node::BVar { idx } => self.ibr_bvar(e, idx as u64, offset, subst),
            Node::BVarBig { idx } => {
                let n = self.scratch.nat_at(Some(self.view.store), idx).clone();
                let idxv = n.to_usize().ok_or_else(|| {
                    MetaError::Infer(
                        "instantiate_beta_rev: bvar index too large to represent".into(),
                    )
                })? as u64;
                self.ibr_bvar(e, idxv, offset, subst)
            }
            // oracle: `visit`'s own comment — these atoms never carry
            // loose bvars, so the range check above already short-
            // circuited whenever it applies; kept as a non-panicking
            // fallback.
            Node::FVar { .. }
            | Node::MVar { .. }
            | Node::Sort { .. }
            | Node::Const { .. }
            | Node::LitNat { .. }
            | Node::LitStr { .. } => Ok(e),
            Node::App { .. } => self.ibr_app(e, offset, subst),
            Node::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.ibr_visit(binder_type, offset, subst)?;
                let b2 = self.ibr_visit(body, offset + 1, subst)?;
                if t2 == binder_type && b2 == body {
                    Ok(e)
                } else {
                    Ok(self.scratch.expr_lam(
                        Some(self.view.store),
                        binder_name,
                        t2,
                        b2,
                        binder_info,
                    )?)
                }
            }
            Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.ibr_visit(binder_type, offset, subst)?;
                let b2 = self.ibr_visit(body, offset + 1, subst)?;
                if t2 == binder_type && b2 == body {
                    Ok(e)
                } else {
                    Ok(self.scratch.expr_forall(
                        Some(self.view.store),
                        binder_name,
                        t2,
                        b2,
                        binder_info,
                    )?)
                }
            }
            Node::LetE {
                decl_name,
                ty,
                value,
                body,
                non_dep,
            } => {
                let t2 = self.ibr_visit(ty, offset, subst)?;
                let v2 = self.ibr_visit(value, offset, subst)?;
                let b2 = self.ibr_visit(body, offset + 1, subst)?;
                if t2 == ty && v2 == value && b2 == body {
                    Ok(e)
                } else {
                    Ok(self.scratch.expr_let(
                        Some(self.view.store),
                        decl_name,
                        t2,
                        v2,
                        b2,
                        non_dep,
                    )?)
                }
            }
            Node::MData { data, expr } => {
                let e2 = self.ibr_visit(expr, offset, subst)?;
                if e2 == expr {
                    Ok(e)
                } else {
                    Ok(self.scratch.expr_mdata(Some(self.view.store), data, e2)?)
                }
            }
            Node::Proj {
                type_name,
                idx,
                structure,
            } => {
                let s2 = self.ibr_visit(structure, offset, subst)?;
                if s2 == structure {
                    Ok(e)
                } else {
                    Ok(self.scratch.expr_proj(
                        Some(self.view.store),
                        type_name,
                        &Nat::from(idx as u64),
                        s2,
                    )?)
                }
            }
            Node::ProjBig {
                type_name,
                idx,
                structure,
            } => {
                let idxn = self.scratch.nat_at(Some(self.view.store), idx).clone();
                let s2 = self.ibr_visit(structure, offset, subst)?;
                if s2 == structure {
                    Ok(e)
                } else {
                    Ok(self
                        .scratch
                        .expr_proj(Some(self.view.store), type_name, &idxn, s2)?)
                }
            }
        }
    }

    /// oracle: `instantiateBetaRevRange`'s `visitBVar` (InferType.lean:
    /// 51-58), reverse convention (`instantiate_rev`'s own doc comment /
    /// `subst.rs::instantiate_bvar`'s `rev` branch — mirrored exactly:
    /// `sub_idx = n - 1 - rel`).
    fn ibr_bvar(
        &mut self,
        e: ExprId,
        idx: u64,
        offset: u32,
        subst: &[ExprId],
    ) -> Result<ExprId, MetaError> {
        let off = offset as u64;
        if idx < off {
            // Refers to a binder outside this substitution's window,
            // untouched — mirrors `subst.rs::instantiate_bvar`'s
            // `idx.0 < s1_big` early return (defensive: `ibr_visit`'s
            // range check makes this unreachable in practice, since any
            // subterm containing only sub-`offset` bvars has
            // `loose_bvar_range <= offset` and is filtered out earlier).
            return Ok(e);
        }
        let n = subst.len() as u64;
        if idx < off + n {
            let rel = idx - off;
            let sub_idx = (n - 1 - rel) as usize;
            let chosen = subst[sub_idx];
            if offset == 0 {
                Ok(chosen)
            } else {
                Ok(leanr_kernel::lift_loose_bvars(
                    self.scratch,
                    Some(self.view.store),
                    chosen,
                    0,
                    offset,
                    &mut self.guard,
                )?)
            }
        } else {
            let new_idx = idx - n;
            Ok(self
                .scratch
                .expr_bvar(Some(self.view.store), &Nat::from(new_idx))?)
        }
    }

    /// oracle: `instantiateBetaRevRange`'s `App` arm (InferType.lean:
    /// 84-93): if the WHOLE spine's head is syntactically a raw bvar,
    /// substitute head and every argument, then beta-reduce
    /// (`beta_rev` below); otherwise fall back to plain per-layer
    /// recursion on `f`/`arg` (`visitApp`, :69-71) — which, since `f`'s
    /// own spine head is the SAME as `e`'s (same spine), re-derives the
    /// identical "not a bvar" verdict on its own recursive call, making
    /// a separate `visitWithoutBeta` mode unnecessary here.
    fn ibr_app(&mut self, e: ExprId, offset: u32, subst: &[ExprId]) -> Result<ExprId, MetaError> {
        let head = self.get_app_fn(e);
        let head_is_bvar = matches!(self.node(head), Node::BVar { .. } | Node::BVarBig { .. });
        if head_is_bvar {
            let args = self.get_app_args(e);
            let head2 = self.ibr_visit(head, offset, subst)?;
            let mut args2 = Vec::with_capacity(args.len());
            for a in args {
                args2.push(self.ibr_visit(a, offset, subst)?);
            }
            self.beta_rev(head2, &args2)
        } else {
            let (f, arg) = match self.node(e) {
                Node::App { f, arg } => (f, arg),
                _ => unreachable!("ibr_app called on a non-App node"),
            };
            let f2 = self.ibr_visit(f, offset, subst)?;
            let arg2 = self.ibr_visit(arg, offset, subst)?;
            if f2 == f && arg2 == arg {
                Ok(e)
            } else {
                Ok(self.scratch.expr_app(Some(self.view.store), f2, arg2)?)
            }
        }
    }

    // `Expr.betaRev` itself: reuse `whnf.rs`'s existing `beta_rev`
    // (oracle: `Expr.betaRev`, `Expr.lean:1592-1617`) rather than
    // duplicating it — same `args`-in-application-order convention as
    // `get_app_args`, which is exactly what `ibr_app` collects above.

    /// oracle: `inferTypeImp`'s `App` arm (`.app f .. =>
    /// inferAppType f.getAppFn e.getAppArgs`, :244).
    fn infer_app(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let f = self.get_app_fn(e);
        let args = self.get_app_args(e);
        self.infer_app_type(f, &args)
    }

    /// oracle: `inferProjType` (InferType.lean:128-153). Every
    /// malformed shape ⇒ `Infer` (oracle's `failed`, :131-132), never a
    /// panic.
    fn infer_proj(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let (proj_name, idx, structure) = match self.node(e) {
            Node::Proj {
                type_name,
                idx,
                structure,
            } => (type_name, Nat::from(idx as u64), structure),
            Node::ProjBig {
                type_name,
                idx,
                structure,
            } => (
                type_name,
                self.scratch.nat_at(Some(self.view.store), idx).clone(),
                structure,
            ),
            _ => return Err(MetaError::Infer("infer_proj: not a projection".into())),
        };
        let sty = self.infer_type(structure)?;
        let sty = self.whnf(sty)?;
        let idxv = idx
            .to_usize()
            .ok_or_else(|| MetaError::Infer("invalid projection: index too large".into()))?;

        let head = self.get_app_fn(sty);
        let struct_args = self.get_app_args(sty);
        let (i_name, i_levels) = match self.node(head) {
            Node::Const { name, levels } => (name, levels),
            _ => {
                return Err(MetaError::Infer(
                    "invalid projection: structure type has no const head".into(),
                ))
            }
        };
        if i_name != proj_name {
            return Err(MetaError::Infer(
                "invalid projection: type name mismatch".into(),
            ));
        }
        let i_info = self.env_get(i_name)?;
        let i_val = match i_info {
            ConstantInfo::Induct(v) => v,
            _ => {
                return Err(MetaError::Infer(
                    "invalid projection: not an inductive".into(),
                ))
            }
        };
        if i_val.ctors.len() != 1 {
            return Err(MetaError::Infer(
                "invalid projection: not a single-constructor type".into(),
            ));
        }
        let nparams = i_val
            .num_params
            .to_usize()
            .ok_or_else(|| MetaError::Infer("invalid projection: numParams overflow".into()))?;
        let nindices = i_val
            .num_indices
            .to_usize()
            .ok_or_else(|| MetaError::Infer("invalid projection: numIndices overflow".into()))?;
        if struct_args.len() != nparams + nindices {
            return Err(MetaError::Infer(
                "invalid projection: structure type argument count mismatch".into(),
            ));
        }
        let ctor_name = i_val.ctors[0];

        let ctor_const =
            self.scratch
                .expr_const(Some(self.view.store), Some(ctor_name), i_levels)?;
        let mut ctor_type = self.infer_app_type(ctor_const, &struct_args[..nparams])?;

        for i in 0..idxv {
            ctor_type = self.whnf(ctor_type)?;
            match self.node(ctor_type) {
                Node::Forall { body, .. } => {
                    if self.data(body).loose_bvar_range() != 0 {
                        let proj_i = self.scratch.expr_proj(
                            Some(self.view.store),
                            proj_name,
                            &Nat::from(i as u64),
                            structure,
                        )?;
                        ctor_type = instantiate(
                            self.scratch,
                            Some(self.view.store),
                            body,
                            proj_i,
                            &mut self.guard,
                        )?;
                    } else {
                        ctor_type = body;
                    }
                }
                _ => {
                    return Err(MetaError::Infer(
                        "invalid projection: expected forall".into(),
                    ))
                }
            }
        }
        ctor_type = self.whnf(ctor_type)?;
        match self.node(ctor_type) {
            // oracle: `return d.consumeTypeAnnotations` (InferType.lean
            // :152) strips `outParam`/`optParam`/`autoParam` WRAPPER
            // APPLICATIONS off the field's domain (Expr.lean:1737-1743)
            // — NOT `mdata` (that's `consumeMData`, a separate helper
            // `consumeTypeAnnotations` doesn't call). Elided: those are
            // named-constant elaborator markers (typeclass
            // out-params/optional-params/auto-params) this crate has no
            // concept of yet — no "is this the `outParam` constant"
            // helper exists in `leanr_kernel`/`leanr_meta` to build one
            // against. Returning the bare domain is correct whenever it
            // ISN'T one of those three wrapper forms (the common case);
            // seam for whichever later task adds typeclass out-param
            // support.
            Node::Forall { binder_type, .. } => Ok(binder_type),
            _ => Err(MetaError::Infer(
                "invalid projection: expected forall".into(),
            )),
        }
    }

    /// oracle: `inferMVarType` (InferType.lean:196-199).
    fn infer_mvar(&self, id: Option<NameId>) -> Result<ExprId, MetaError> {
        let id = id.ok_or_else(|| MetaError::Infer("unknown metavariable".into()))?;
        self.mctx
            .decl(MVarId(id))
            .map(|d| d.ty)
            .ok_or_else(|| MetaError::Infer("unknown metavariable".into()))
    }

    /// oracle: `inferFVarType` (InferType.lean:201-204).
    fn infer_fvar(&self, id: Option<NameId>) -> Result<ExprId, MetaError> {
        let id = id.ok_or_else(|| MetaError::Infer("unknown free variable".into()))?;
        self.lctx
            .get(id)
            .map(|d| d.ty)
            .ok_or_else(|| MetaError::Infer("unknown free variable".into()))
    }

    /// oracle: `inferForallType` (InferType.lean:178-185): telescope
    /// over nested `Forall` binders with fresh fvars, then `Sort` of
    /// the `imax`-fold (right-to-left, oracle's `foldrM`) of every
    /// binder's own level and the body's level (`getLevel`, :164-176).
    ///
    /// Save/restore wraps the telescope (`leanr_kernel`'s own
    /// `TypeChecker::infer_pi`/`infer_lambda` idiom, `tc.rs:1008-1013`/
    /// `1067-1072` — `LocalContext::save`/`restore` are `pub` precisely
    /// so this crate can mirror it): `infer_forall_body` mints fresh
    /// fvars via `self.lctx.mk_local_decl`, and every exit path —
    /// including an early `?` return from any fallible step — restores
    /// the checkpoint before the error propagates, since the body runs
    /// to completion (as a plain `Result`, not yet unwound) before this
    /// wrapper ever looks at it.
    fn infer_forall(&mut self, e0: ExprId) -> Result<ExprId, MetaError> {
        let checkpoint = self.lctx.save();
        let r = self.infer_forall_body(e0);
        self.lctx.restore(checkpoint);
        r
    }

    fn infer_forall_body(&mut self, e0: ExprId) -> Result<ExprId, MetaError> {
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut us: Vec<LevelId> = Vec::new();
        let mut e = e0;
        while let Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = self.node(e)
        {
            let d = instantiate_rev(
                self.scratch,
                Some(self.view.store),
                binder_type,
                &fvars,
                &mut self.guard,
            )?;
            let lvl = self.get_level(d)?;
            us.push(lvl);
            let fvar = self.lctx.mk_local_decl(
                self.scratch,
                Some(self.view.store),
                &mut self.fvar_gen,
                binder_name,
                d,
                binder_info,
            )?;
            fvars.push(fvar);
            e = body;
        }
        let inst = instantiate_rev(
            self.scratch,
            Some(self.view.store),
            e,
            &fvars,
            &mut self.guard,
        )?;
        // oracle: `xs.foldrM (init := lvl) fun x lvl => .. mkLevelIMax'
        // xTypeLvl lvl` then `mkSort lvl.normalize` (InferType.lean:
        // 181-185) — the fold via the SIMPLIFYING `mkLevelIMax'`
        // (Level.lean:549-551, `mkLevelIMaxCore` :542-547), not plain
        // interning, then a final `.normalize`.
        //
        // `Level::mk_imax_pair` (level.rs:273, citing kernel
        // `level.cpp:112-121`) is the public primitive this crate can
        // reach for the fold; it agrees with `mkLevelIMax'` on every
        // branch (never-zero RHS ⇒ delegate to max; RHS zero ⇒ RHS;
        // LHS zero ⇒ RHS; structurally equal ⇒ either) EXCEPT one extra
        // case Lean's `mkLevelIMaxCore` does not have: `l1` is
        // syntactically `1` (`is_one`, level.rs:284) also short-circuits
        // to `l2`. Oracle wins where they'd diverge — but the final
        // `Level::normalize` below (kernel `level.cpp:439-501`, which
        // Lean's own `Level.normalize` used at :185 is bound to) rebuilds
        // any `IMax` node's canonical form via `to_offset` and this SAME
        // `mk_imax_pair` regardless of how the input was folded, so this
        // extra intermediate simplification cannot change the final,
        // normalized `Sort` this method returns.
        let body_lvl = self.get_level(inst)?;
        let mut r = self.scratch.to_level(Some(self.view.store), body_lvl);
        let mut i = us.len();
        while i > 0 {
            i -= 1;
            let x_lvl = self.scratch.to_level(Some(self.view.store), us[i]);
            r = Level::mk_imax_pair(x_lvl, r, &mut self.guard)?;
        }
        let r = Level::normalize(&r, &mut self.guard)?;
        let r_id = self.scratch.intern_level(Some(self.view.store), &r)?;
        Ok(self.scratch.expr_sort(Some(self.view.store), r_id)?)
    }

    /// oracle: `inferLambdaType` (InferType.lean:188-191); `LetE` takes
    /// this same arm (`.letE .. => inferLambdaType e`, :253) via the
    /// oracle's `lambdaLetTelescope`, so this method also walks `LetE`
    /// nodes. Same save/restore wrapping as `infer_forall` (and its doc
    /// comment's rationale) — `mk_pi`'s kernel-side `decl_for` call
    /// (which `rebuild_forall` below mirrors) needs the telescope's
    /// fvars still declared in `self.lctx` while it runs, so the
    /// checkpoint is taken before `infer_lambda_body` and restored only
    /// after `rebuild_forall` has consumed them.
    fn infer_lambda(&mut self, e0: ExprId) -> Result<ExprId, MetaError> {
        let checkpoint = self.lctx.save();
        let r = self.infer_lambda_body(e0);
        self.lctx.restore(checkpoint);
        r
    }

    fn infer_lambda_body(&mut self, e0: ExprId) -> Result<ExprId, MetaError> {
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut e = e0;
        loop {
            match self.node(e) {
                Node::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    let d = instantiate_rev(
                        self.scratch,
                        Some(self.view.store),
                        binder_type,
                        &fvars,
                        &mut self.guard,
                    )?;
                    let fvar = self.lctx.mk_local_decl(
                        self.scratch,
                        Some(self.view.store),
                        &mut self.fvar_gen,
                        binder_name,
                        d,
                        binder_info,
                    )?;
                    fvars.push(fvar);
                    e = body;
                }
                Node::LetE {
                    decl_name,
                    ty,
                    value,
                    body,
                    ..
                } => {
                    let t = instantiate_rev(
                        self.scratch,
                        Some(self.view.store),
                        ty,
                        &fvars,
                        &mut self.guard,
                    )?;
                    let v = instantiate_rev(
                        self.scratch,
                        Some(self.view.store),
                        value,
                        &fvars,
                        &mut self.guard,
                    )?;
                    let fvar = self.lctx.mk_let_decl(
                        self.scratch,
                        Some(self.view.store),
                        &mut self.fvar_gen,
                        decl_name,
                        t,
                        v,
                    )?;
                    fvars.push(fvar);
                    e = body;
                }
                _ => break,
            }
        }
        let inst = instantiate_rev(
            self.scratch,
            Some(self.view.store),
            e,
            &fvars,
            &mut self.guard,
        )?;
        let body_ty = self.infer_type(inst)?;
        self.rebuild_forall(&fvars, body_ty)
    }

    /// oracle: `getLevel` (InferType.lean:164-176), the assignable
    /// `Sort`-mvar branch (:169-175) elided: this plan has no
    /// meta-level level-mvar allocator yet, so a type whose whnf is not
    /// syntactically a `Sort` is simply `Infer`, matching the oracle's
    /// final `throwTypeExpected` fallback (:176).
    fn get_level(&mut self, ty: ExprId) -> Result<LevelId, MetaError> {
        let tty = self.infer_type(ty)?;
        let w = self.whnf(tty)?;
        match self.node(w) {
            Node::Sort { level } => Ok(level),
            _ => Err(MetaError::Infer("type expected".into())),
        }
    }

    /// Rebuild a telescope over `fvars` around `body_ty` — oracle:
    /// `mkForallFVars (generalizeNondepLet := false) xs type`
    /// (`inferLambdaType`'s only caller, InferType.lean:191; `usedOnly`/
    /// `usedLetOnly` stay at `mkForallFVars`'s own defaults `false`/
    /// `true`, Basic.lean:1144). `mkForallFVars` itself just forwards to
    /// `MetavarContext.mkForall` (Basic.lean:1144, MetavarContext.lean:
    /// 1370-1371, `isLambda := false`), which forwards to the private
    /// `MkBinding.mkBinding` (MetavarContext.lean:1312-1338) — the real
    /// per-binder logic transcribed below.
    ///
    /// A LET-bound telescope entry (`decl.value.is_some()`) is NOT
    /// always rebuilt as a `Forall`: `MkBinding.mkBinding`'s `ldecl` arm
    /// (:1327-1335) only takes the `handleCDecl` (regular-binder) path
    /// when `generalizeNondepLet && nondep` — always false here since
    /// `inferLambdaType` hardcodes `generalizeNondepLet := false` — so a
    /// let entry always falls to `else if !usedLetOnly || e.hasLooseBVar
    /// 0`; since `usedLetOnly = true`, that's exactly `e.hasLooseBVar 0`
    /// on the JUST-abstracted body: if the let-bound variable is
    /// actually used, wrap in `LetE` (:1333); if not, DROP the binder
    /// entirely (`e.lowerLooseBVars 1 1`, :1335) — the accumulated body
    /// is already correct as-is, since nothing in it refers to this
    /// slot. This is genuinely different machinery from `leanr_kernel`'s
    /// own `subst::mk_binding` (`subst.rs:1020-1048`, oracle
    /// `local_ctx.cpp:93-115`): that kernel-internal telescope helper
    /// also branches on `decl.value` (`Some` ⇒ `expr_let`), but it is a
    /// DIFFERENT function serving kernel-internal admission and has no
    /// "unused let is dropped" case at all — it always wraps. The
    /// value-branch here is shared with it; the unused-let drop is not,
    /// and is transcribed from `MetavarContext.lean` alone. `abstract_fvars`
    /// (re-exported; `mk_pi`/`mk_lambda`/`mk_binding` are not — see the
    /// git history for the compile probe that confirmed this) stands in
    /// for `abstractRange`.
    ///
    /// No `lowerLooseBVars` primitive is exposed by this crate for the
    /// drop case, but none is needed: `abstract_go`'s every combinator
    /// (subst.rs:589-729) reconstructs a node only when a child actually
    /// changed, else returns the untouched input id, so abstracting an
    /// fvar that never occurs in `r` is a structural no-op — `r` is
    /// already exactly the "with this slot removed" result. Comparing
    /// the abstraction's output against its input (`used = r != before`)
    /// is therefore an exact stand-in for the oracle's `hasLooseBVar 0`
    /// probe on the freshly-abstracted body.
    fn rebuild_forall(&mut self, fvars: &[ExprId], body_ty: ExprId) -> Result<ExprId, MetaError> {
        let mut r = body_ty;
        let mut i = fvars.len();
        while i > 0 {
            i -= 1;
            let before = r;
            r = abstract_fvars(
                self.scratch,
                Some(self.view.store),
                r,
                std::slice::from_ref(&fvars[i]),
                &mut self.guard,
            )?;
            let used = r != before;
            let (binder_name, ty, binder_info, value) = match self.node(fvars[i]) {
                Node::FVar { id: Some(id) } => {
                    let decl = self.lctx.get(id).ok_or_else(|| {
                        MetaError::Infer("rebuild_forall: telescope fvar not declared".into())
                    })?;
                    (decl.binder_name, decl.ty, decl.binder_info, decl.value)
                }
                _ => {
                    return Err(MetaError::Infer(
                        "rebuild_forall: telescope entry is not an fvar".into(),
                    ))
                }
            };
            r = match value {
                // Unused let: drop the binder entirely (`r` is already
                // correct — see this method's doc comment).
                Some(_) if !used => r,
                Some(value) => {
                    let ty2 = abstract_fvars(
                        self.scratch,
                        Some(self.view.store),
                        ty,
                        &fvars[..i],
                        &mut self.guard,
                    )?;
                    let value2 = abstract_fvars(
                        self.scratch,
                        Some(self.view.store),
                        value,
                        &fvars[..i],
                        &mut self.guard,
                    )?;
                    self.scratch.expr_let(
                        Some(self.view.store),
                        binder_name,
                        ty2,
                        value2,
                        r,
                        false,
                    )?
                }
                None => {
                    let ty2 = abstract_fvars(
                        self.scratch,
                        Some(self.view.store),
                        ty,
                        &fvars[..i],
                        &mut self.guard,
                    )?;
                    self.scratch.expr_forall(
                        Some(self.view.store),
                        binder_name,
                        ty2,
                        r,
                        binder_info,
                    )?
                }
            };
        }
        Ok(r)
    }

    /// oracle: `.sort lvl => return mkSort (mkLevelSucc lvl)`
    /// (InferType.lean:250).
    fn sort_succ(&mut self, level: LevelId) -> Result<ExprId, MetaError> {
        let l2 = self.scratch.level_succ(Some(self.view.store), level)?;
        Ok(self.scratch.expr_sort(Some(self.view.store), l2)?)
    }

    /// oracle: `.lit v => return v.type` (InferType.lean:249) —
    /// `Literal.type` maps a nat/string literal to the bare `Nat`/
    /// `String` constant, no universe params.
    fn lit_type(&mut self, name: &str) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let s = self.scratch.intern_str(base, name)?;
        let n = self.scratch.name_str(base, None, s)?;
        let no_levels = self.scratch.intern_level_list(base, &[])?;
        Ok(self.scratch.expr_const(base, Some(n), no_levels)?)
    }

    /// Env lookup with a region-correct error path, mirroring
    /// `leanr_kernel::tc::TypeChecker::env_get_with`'s own doc comment:
    /// `EnvView::get_with` would bridge a MISS's `NameId` via
    /// `to_name(None, ..)` (persistent-store-only resolution), which is
    /// wrong for a scratch-region id, so on a genuine miss this builds
    /// the name via `self.scratch.to_name(Some(self.view.store), ..)`
    /// instead — the region-correct bridge — rather than calling
    /// `EnvView::get_with` directly.
    fn env_get(&self, name: Option<NameId>) -> Result<&'e ConstantInfo, MetaError> {
        match name {
            Some(n) => self.view.get(n).ok_or_else(|| {
                let nm = self.scratch.to_name(Some(self.view.store), Some(n));
                MetaError::Infer(format!("unknown constant '{nm}'"))
            }),
            None => Err(MetaError::Infer("unknown constant (anonymous)".into())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanr_kernel::{BinderInfo, LocalContext};

    use crate::test_support::with_prelude0_ctx;
    use crate::{MVarDecl, MVarKind};

    /// `Name::Str { parent: Name::Str { parent: Anonymous, part: a },
    /// part: b }`, resolved through the persistent store (`Some(base)`)
    /// so it dedups against Prelude0's own already-interned "N.zero"/
    /// "N.succ" rather than minting an unrelated scratch-region id (see
    /// `env_get`'s doc comment on region correctness).
    fn dotted(ctx: &mut MetaCtx, a: &str, b: &str) -> NameId {
        let base = Some(ctx.view.store);
        let a_str = ctx.scratch.intern_str(base, a).expect("intern");
        let a_name = ctx.scratch.name_str(base, None, a_str).expect("name");
        let b_str = ctx.scratch.intern_str(base, b).expect("intern");
        ctx.scratch
            .name_str(base, Some(a_name), b_str)
            .expect("name")
    }

    fn single(ctx: &mut MetaCtx, a: &str) -> NameId {
        let base = Some(ctx.view.store);
        let a_str = ctx.scratch.intern_str(base, a).expect("intern");
        ctx.scratch.name_str(base, None, a_str).expect("name")
    }

    /// A no-universe-argument `Expr.const` for `name`.
    fn const_expr(ctx: &mut MetaCtx, name: NameId) -> ExprId {
        let base = Some(ctx.view.store);
        let no_levels = ctx.scratch.intern_level_list(base, &[]).expect("levels");
        ctx.scratch
            .expr_const(base, Some(name), no_levels)
            .expect("const")
    }

    // All tests reconcile Store constructor names against bank/terms.rs.
    // `with_prelude0_ctx` is this file's env helper: replay Prelude0.olean
    // per check_fixtures.rs::prelude0_replays_from_empty_env, build the
    // EnvView per schedule.rs:324, wrap in MetaCtx::new(view, scratch,
    // Config::default(), &md.reducibility, &md.matchers).
    // Exemplar (the rest follow this pattern — write every body in full
    // before implementing):
    #[test]
    fn sort_infers_to_succ() {
        with_prelude0_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).expect("level");
            let sort0 = ctx.scratch.expr_sort(None, z).expect("sort");
            let t = ctx.infer_type(sort0).expect("infer");
            let one = ctx.scratch.level_succ(None, z).expect("succ");
            let sort1 = ctx.scratch.expr_sort(None, one).expect("sort");
            assert_eq!(t, sort1, "infer(Sort 0) must be Sort 1 (same interned id)");
        });
    }

    #[test]
    fn const_type_instantiates_levels() {
        with_prelude0_ctx(|ctx| {
            let n_name = single(ctx, "N");
            let info = ctx.view.get(n_name).expect("N declared by Prelude0");
            let cv = info.constant_val().clone();
            let base = Some(ctx.view.store);
            let level_ids: Vec<LevelId> = cv
                .level_params
                .iter()
                .map(|_| ctx.scratch.level_zero(base).expect("level"))
                .collect();
            let levels = ctx
                .scratch
                .intern_level_list(base, &level_ids)
                .expect("levels");
            let n_const = ctx
                .scratch
                .expr_const(base, Some(n_name), levels)
                .expect("const");

            let t = ctx.infer_type(n_const).expect("infer");

            let expected = leanr_kernel::instantiate_level_params(
                ctx.scratch,
                base,
                cv.ty,
                &cv.level_params,
                &level_ids,
                &mut ctx.guard,
            )
            .expect("instantiate");
            assert_eq!(t, expected, "infer(const N) must equal N's declared type");
        });
    }

    #[test]
    fn lambda_infers_to_pi() {
        with_prelude0_ctx(|ctx| {
            let n_name = single(ctx, "N");
            let n_ty = const_expr(ctx, n_name);
            let base = Some(ctx.view.store);
            let bvar0 = ctx.scratch.expr_bvar(base, &Nat::from(0u64)).expect("bvar");
            let lam = ctx
                .scratch
                .expr_lam(base, None, n_ty, bvar0, BinderInfo::Default)
                .expect("lam");

            let t = ctx.infer_type(lam).expect("infer");

            let expected = ctx
                .scratch
                .expr_forall(base, None, n_ty, n_ty, BinderInfo::Default)
                .expect("forall");
            assert_eq!(t, expected, "infer(fun (x : N) => x) must equal N -> N");
        });
    }

    #[test]
    fn app_consumes_foralls() {
        with_prelude0_ctx(|ctx| {
            let zero_name = dotted(ctx, "N", "zero");
            let succ_name = dotted(ctx, "N", "succ");
            let n_name = single(ctx, "N");

            let zero = const_expr(ctx, zero_name);
            let succ = const_expr(ctx, succ_name);
            let app = ctx
                .scratch
                .expr_app(Some(ctx.view.store), succ, zero)
                .expect("app");

            let t = ctx.infer_type(app).expect("infer");

            let n_ty = const_expr(ctx, n_name);
            assert_eq!(t, n_ty, "infer(N.succ N.zero) must equal N");
        });
    }

    #[test]
    fn mvar_infers_from_decl() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let z = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, z).expect("sort");
            let m_name = single(ctx, "m_test");
            let mid = MVarId(m_name);
            ctx.mctx_mut().declare(
                mid,
                MVarDecl {
                    user_name: None,
                    ty: sort0,
                    lctx: LocalContext::default(),
                    kind: MVarKind::Natural,
                },
            );
            let mexpr = ctx.scratch.expr_mvar(base, Some(m_name)).expect("mvar");

            let t = ctx.infer_type(mexpr).expect("infer");
            assert_eq!(t, sort0, "infer(?m) must equal ?m's declared type");
        });
    }

    #[test]
    fn loose_bvar_is_an_error() {
        with_prelude0_ctx(|ctx| {
            let b0 = ctx
                .scratch
                .expr_bvar(Some(ctx.view.store), &Nat::from(0u64))
                .expect("bvar");
            let r = ctx.infer_type(b0);
            assert!(
                matches!(r, Err(MetaError::Infer(_))),
                "a loose bvar must be MetaError::Infer, got {r:?}"
            );
        });
    }

    #[test]
    fn infer_caches_closed_terms() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let z = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, z).expect("sort");

            ctx.infer_type(sort0).expect("first infer");
            let after_first = ctx.infer_cache.len();
            assert!(after_first > 0, "a closed term's result must be cached");

            ctx.infer_type(sort0).expect("second infer");
            let after_second = ctx.infer_cache.len();
            assert_eq!(
                after_first, after_second,
                "the second infer must hit the cache, not grow it"
            );
        });
    }

    /// Pins `infer_forall`/`infer_lambda`'s save/restore discipline:
    /// `LocalContext::save` (now `pub`) is a legitimate outside
    /// observer of the decl count, so a telescope that restored
    /// correctly must leave it exactly where it started.
    #[test]
    fn telescopes_restore_the_local_context() {
        with_prelude0_ctx(|ctx| {
            let n_name = single(ctx, "N");
            let n_ty = const_expr(ctx, n_name);
            let base = Some(ctx.view.store);
            let checkpoint = ctx.lctx.save();

            let bvar0 = ctx.scratch.expr_bvar(base, &Nat::from(0u64)).expect("bvar");
            let lam = ctx
                .scratch
                .expr_lam(base, None, n_ty, bvar0, BinderInfo::Default)
                .expect("lam");
            ctx.infer_type(lam).expect("infer lambda");
            assert_eq!(
                ctx.lctx.save(),
                checkpoint,
                "infer_lambda's telescope must leave no residue in the local context"
            );

            let forall_e = ctx
                .scratch
                .expr_forall(base, None, n_ty, n_ty, BinderInfo::Default)
                .expect("forall");
            ctx.infer_type(forall_e).expect("infer forall");
            assert_eq!(
                ctx.lctx.save(),
                checkpoint,
                "infer_forall's telescope must leave no residue in the local context"
            );
        });
    }

    /// oracle: `MkBinding.mkBinding`'s `ldecl` arm
    /// (`MetavarContext.lean:1327-1335`), reached via `inferLambdaType`'s
    /// `mkForallFVars (generalizeNondepLet := false) xs type`
    /// (`InferType.lean:191`). `x`'s inferred TYPE (`N`) never mentions
    /// `x` itself, so abstracting `x` out of it is a structural no-op —
    /// the fold's `usedLetOnly` check (`e.hasLooseBVar 0` on that
    /// abstracted TYPE, not on the original term) sees "unused" and
    /// drops the let-binder entirely, even though `x` **is** the whole
    /// body term. `infer(let x := N.zero; x)` must therefore equal `N`
    /// exactly — no `Forall` (the pre-fix bug: rebuilding unconditionally
    /// as `Forall` gave the spurious `N -> N`), and not even a residual
    /// `LetE` wrapper.
    #[test]
    fn let_binding_does_not_produce_a_spurious_forall() {
        with_prelude0_ctx(|ctx| {
            let n_name = single(ctx, "N");
            let n_ty = const_expr(ctx, n_name);
            let zero_name = dotted(ctx, "N", "zero");
            let zero = const_expr(ctx, zero_name);
            let base = Some(ctx.view.store);

            let bvar0 = ctx.scratch.expr_bvar(base, &Nat::from(0u64)).expect("bvar");
            let let_e = ctx
                .scratch
                .expr_let(base, None, n_ty, zero, bvar0, false)
                .expect("let");

            let t = ctx.infer_type(let_e).expect("infer");

            assert_eq!(t, n_ty, "let x := N.zero; x must infer to N, not N -> N");
            assert!(
                !matches!(ctx.node(t), Node::Forall { .. }),
                "infer(let x := N.zero; x) must not have a Forall head, got {:?}",
                ctx.node(t)
            );
        });
    }

    /// oracle: `inferForallType`'s final `mkSort lvl.normalize`
    /// (`InferType.lean:185`). `∀ (x : N), N`'s two binder levels are
    /// both `1` (`N : Sort 1`), so the imax fold produces `imax 1 1`;
    /// unnormalized that is a distinct `IMax` level row, but `imax 1 1`
    /// is definitionally `1`, and `Level::normalize` must collapse it to
    /// the SAME interned id as `Sort (succ zero)` — pinning that the
    /// fold+normalize path, not a raw `level_imax` intern, is what runs.
    #[test]
    fn forall_sort_level_is_normalized() {
        with_prelude0_ctx(|ctx| {
            let n_name = single(ctx, "N");
            let n_ty = const_expr(ctx, n_name);
            let base = Some(ctx.view.store);

            let forall_e = ctx
                .scratch
                .expr_forall(base, None, n_ty, n_ty, BinderInfo::Default)
                .expect("forall");

            let t = ctx.infer_type(forall_e).expect("infer");

            let z = ctx.scratch.level_zero(base).expect("level");
            let one = ctx.scratch.level_succ(base, z).expect("succ");
            let sort1 = ctx.scratch.expr_sort(base, one).expect("sort");
            assert_eq!(
                t, sort1,
                "infer_type(forall (x : N), N) must equal Sort 1 (same interned id as \
                 expr_sort(succ zero)) — imax 1 1 must normalize away"
            );
        });
    }
}
