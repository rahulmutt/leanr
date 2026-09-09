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
use leanr_kernel::Nat;

use crate::local_snapshot::LocalCtxSnapshot;
use crate::{MetaCtx, MetaError};

/// oracle: `MkBinding.State.cache` (`:956-960`). Scoped to one
/// `elim_mvar_deps` call and reset again inside `elim_mvar` before
/// `mk_aux_mvar_type` (`:1205`, "we must reset the cache because
/// `toRevert` may not be equal to `xs`"), which is why it is a
/// threaded parameter rather than a `MetaCtx` field: its lifetime is a
/// matter of type here, not of discipline.
#[derive(Default)]
pub(crate) struct ElimCache(std::collections::HashMap<ExprId, ExprId>);

impl<'e> MetaCtx<'e> {
    /// The `FVarId` behind an `Expr::fvar`, or `None` for anything
    /// else. `xs` and `to_revert` are carried as `Expr::fvar`
    /// references throughout (the oracle carries `Array Expr` too), so
    /// this is the one place the id is read out.
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
    pub(crate) fn collect_forward_deps(
        &mut self,
        lctx: &LocalCtxSnapshot,
        to_revert: Vec<ExprId>,
    ) -> Result<Vec<ExprId>, MetaError> {
        if to_revert.is_empty() {
            return Ok(to_revert);
        }
        // oracle compares by `FVarId` (`decl.fvarId == x.fvarId!`,
        // `:1057-1058`); `get_in_scope`, two functions earlier, already
        // compares by `NameId` (leanr's `FVarId` equivalent), so
        // comparing `to_revert` against `entries` by raw `ExprId` here
        // mixed the module's basis. The two coincide today because
        // `expr_fvar` interns against `Some(self.view.store)`
        // everywhere; making this uniform removes a silent-failure mode
        // (a mismatched `ExprId` producing an empty `to_revert` and a
        // bare `?m := ?new` with no error) rather than fixing an
        // observed bug — behavior is unchanged.
        let to_revert_ids: Vec<NameId> = to_revert
            .iter()
            .filter_map(|f| self.fvar_id_of(*f))
            .collect();
        let entries: Vec<ExprId> = lctx.entries().iter().map(|(_, f)| *f).collect();
        // oracle `getLocalDeclWithSmallestIdx` (`:1052`): start at the
        // earliest declaration that is being reverted. Everything before it
        // is declared earlier than anything reverted, so it cannot depend
        // on one.
        let start = entries
            .iter()
            .position(|f| {
                self.fvar_id_of(*f)
                    .is_some_and(|id| to_revert_ids.contains(&id))
            })
            .unwrap_or(entries.len());

        let mut collected: Vec<ExprId> = Vec::with_capacity(to_revert.len());
        let mut collected_ids: Vec<NameId> = Vec::with_capacity(to_revert.len());
        for fvar in entries.into_iter().skip(start) {
            let Some(id) = self.fvar_id_of(fvar) else {
                continue;
            };
            if to_revert_ids.contains(&id) {
                collected.push(fvar);
                collected_ids.push(id);
                continue;
            }
            let Some(decl) = lctx.lctx().get(id) else {
                continue;
            };
            let (ty, value) = (decl.ty, decl.value);
            if self.local_decl_depends_on(ty, value, &collected_ids)? {
                collected.push(fvar);
                collected_ids.push(id);
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
    pub(crate) fn reduce_local_context(
        &self,
        lctx: &LocalCtxSnapshot,
        to_revert: &[ExprId],
    ) -> Result<Arc<LocalCtxSnapshot>, MetaError> {
        let pairs: Vec<(ExprId, NameId)> = to_revert
            .iter()
            .filter_map(|f| self.fvar_id_of(*f).map(|id| (*f, id)))
            .collect();
        // `reduced` filters `local_names` by `NameId` too (see that
        // function's doc), which needs an `ExprId -> NameId` decode it
        // cannot do itself — `LocalCtxSnapshot` holds no `Store`
        // reference. `Self::fvar_id_of` supplies it here, where one is
        // in hand.
        Ok(Arc::new(lctx.reduced(&pairs, |f| self.fvar_id_of(f))))
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
    pub(crate) fn mk_mvar_app(&mut self, mvar: ExprId, xs: &[ExprId]) -> Result<ExprId, MetaError> {
        let mut e = mvar;
        for x in xs {
            e = self.scratch.expr_app(Some(self.view.store), e, *x)?;
        }
        Ok(e)
    }

    /// oracle: `elimMVarDeps` (`:1252-1257`).
    ///
    /// Returns `e` unchanged when it carries no expr metavariable — the
    /// fast path that makes every `mk_binding` call over a
    /// metavariable-free body a strict no-op. For a body that DOES carry
    /// one, behavior genuinely changes; see the design spec's § Risk
    /// item 1 and the Task 1 findings document.
    pub(crate) fn elim_mvar_deps(&mut self, xs: &[ExprId], e: ExprId) -> Result<ExprId, MetaError> {
        if !self.data(e).has_expr_mvar() {
            return Ok(e);
        }
        let mut cache = ElimCache::default();
        self.elim(xs, e, &mut cache)
    }

    /// oracle: `abstractRange` (`:1277-1279`) — `elimMVarDeps` over the
    /// FULL `xs`, then abstract only the first `i`. The asymmetry is
    /// deliberate and is the oracle's, not a simplification: a binder
    /// type at position `i` has its metavariable dependencies eliminated
    /// with respect to every telescope variable, including ones declared
    /// after it.
    pub(crate) fn abstract_range(
        &mut self,
        xs: &[ExprId],
        i: usize,
        e: ExprId,
    ) -> Result<ExprId, MetaError> {
        let e = self.elim_mvar_deps(xs, e)?;
        Ok(abstract_fvars(
            self.scratch,
            Some(self.view.store),
            e,
            &xs[..i],
            &mut self.guard,
        )?)
    }

    /// oracle: `abstractRangeAux` (`:1165-1167`) — the oracle's
    /// STRUCTURAL `elim` over the FULL `xs`, carrying the CALLER's
    /// cache, then abstract only the first `i`.
    ///
    /// Two things distinguish it from `abstract_range` above, and both
    /// are the oracle's:
    ///
    /// 1. **The cache is the caller's.** The only reset in `MkBinding`
    ///    is `withFreshCache do mkAuxMVarType …` (`:1205`), so every
    ///    abstraction site inside one `mkAuxMVarType` shares one cache.
    ///    A fresh cache per site would re-elaborate a NESTED shared
    ///    subterm and mint a second auxiliary metavariable for it.
    /// 2. **The entry is structural**, `visit_guarded` and not `elim`:
    ///    oracle `:1166` calls `elim`, the structural function, which
    ///    does not reach `visit`'s `checkCache` (`:1102`). So a subterm
    ///    shared as the whole of two sites' inputs re-enters `elimMVar`
    ///    at each, minting one auxiliary metavariable per site — while a
    ///    subterm shared NESTED inside them is reached through `elim`
    ///    from within `visit` and hits the cache, minting one in total.
    fn abstract_range_aux(
        &mut self,
        xs: &[ExprId],
        i: usize,
        e: ExprId,
        cache: &mut ElimCache,
    ) -> Result<ExprId, MetaError> {
        let e = self.visit_guarded(xs, e, cache)?;
        Ok(abstract_fvars(
            self.scratch,
            Some(self.view.store),
            e,
            &xs[..i],
            &mut self.guard,
        )?)
    }

    /// oracle: `visit` (`:1101`) — this port calls it `elim`. The
    /// cached entry to the traversal: the `hasMVar` guard, then
    /// `checkCache` (`:1102`), then the structural function.
    ///
    /// **The port's two names are INVERTED relative to the oracle's**,
    /// and the inversion is a trap worth naming: in `v4.33.0-rc1` the
    /// oracle's `visit` (`:1101`) is this cached entry and the oracle's
    /// `elim` (`:1104`) is the structural function, while here the names
    /// are the other way round. So a call reading `self.elim(…)` enters
    /// at the CACHED level, not the structural one — which is why the
    /// two sites that must enter structurally (`abstract_range_aux`,
    /// oracle `:1166`; and `elim_app`'s post-beta re-entry, oracle
    /// `:1238`) go through `visit_guarded` instead. `checkCache` appears
    /// exactly once in the whole `MkBinding` traversal, at oracle
    /// `:1102`, which is this function.
    fn elim(
        &mut self,
        xs: &[ExprId],
        e: ExprId,
        cache: &mut ElimCache,
    ) -> Result<ExprId, MetaError> {
        if !self.data(e).has_expr_mvar() {
            return Ok(e);
        }
        if let Some(hit) = cache.0.get(&e) {
            return Ok(*hit);
        }
        self.step()?;
        let out = self.guarded(|ctx| ctx.visit(xs, e, cache))?;
        cache.0.insert(e, out);
        Ok(out)
    }

    /// The oracle's STRUCTURAL `elim` (`:1104`) entered directly — this
    /// port's `visit`, under the same budget and depth guard `elim`
    /// applies, but with NO cache lookup and no cache insert.
    ///
    /// Its two callers are the two places the oracle names `elim` rather
    /// than `visit`: `abstractRangeAux` (`:1166`) and `elimApp`'s
    /// post-beta re-entry (`:1238`). Entering at `elim` there instead
    /// would consult a cache the oracle does not consult at those
    /// points, and for a shared TOP-LEVEL subterm that is observable:
    /// the oracle re-enters `elimMVar` per site and mints one auxiliary
    /// metavariable each, where a cache hit would mint one in total.
    /// Nested shared subterms still share, because the recursive calls
    /// `visit` makes go through `elim` and so do hit the cache — which
    /// is exactly the oracle's split.
    fn visit_guarded(
        &mut self,
        xs: &[ExprId],
        e: ExprId,
        cache: &mut ElimCache,
    ) -> Result<ExprId, MetaError> {
        self.step()?;
        self.guarded(|ctx| ctx.visit(xs, e, cache))
    }

    /// oracle: `elim` (`:1104`) — this port calls it `visit` (see
    /// `elim` above on the inverted names). The structural arms; no
    /// cache is consulted or populated here. An application is
    /// decomposed into head plus arguments and routed to `elim_app`,
    /// because the head being a metavariable is what `elim_mvar` needs to
    /// see.
    fn visit(
        &mut self,
        xs: &[ExprId],
        e: ExprId,
        cache: &mut ElimCache,
    ) -> Result<ExprId, MetaError> {
        match self.node(e) {
            Node::App { .. } => {
                let f = self.get_app_fn(e);
                let args = self.get_app_args(e);
                self.elim_app(xs, f, &args, cache)
            }
            // `id: Some(_)`, not `..`: an ANONYMOUS mvar node has no
            // id for `elim_app`'s own `Some(n)` guard to match, so
            // routing it there would fall through to `elim(f)` with
            // `f == e` — a self-recursion the cache cannot break
            // (`elim` inserts only after `visit` returns) that ends at
            // `DepthBudgetExhausted`. No producer in the workspace mints
            // one, but the catch-all below is the right answer for it.
            Node::MVar { id: Some(_) } => self.elim_app(xs, e, &[], cache),
            Node::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t = self.elim(xs, binder_type, cache)?;
                let b = self.elim(xs, body, cache)?;
                if t == binder_type && b == body {
                    Ok(e)
                } else {
                    Ok(self.scratch.expr_lam(
                        Some(self.view.store),
                        binder_name,
                        t,
                        b,
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
                let t = self.elim(xs, binder_type, cache)?;
                let b = self.elim(xs, body, cache)?;
                if t == binder_type && b == body {
                    Ok(e)
                } else {
                    Ok(self.scratch.expr_forall(
                        Some(self.view.store),
                        binder_name,
                        t,
                        b,
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
                let t = self.elim(xs, ty, cache)?;
                let v = self.elim(xs, value, cache)?;
                let b = self.elim(xs, body, cache)?;
                if t == ty && v == value && b == body {
                    Ok(e)
                } else {
                    Ok(self
                        .scratch
                        .expr_let(Some(self.view.store), decl_name, t, v, b, non_dep)?)
                }
            }
            // oracle `:1110` (`.mdata … updateMData! (← visit xs b)`) and
            // `:1106` (`.proj … updateProj! (← visit xs s)`). Not
            // unreachable: `has_expr_mvar` propagates through both
            // constructors (`terms.rs:569`, `:596`), so `elim`'s fast
            // path does NOT fire on them and the catch-all would return
            // — and cache — a term still carrying the metavariable this
            // pass exists to rewrite. Same shape as the crate's sibling
            // traversals, `instantiate_mvars` (`assign.rs:1408-1446`)
            // and this module's own `depends_on_body`.
            Node::MData { data, expr } => {
                let x = self.elim(xs, expr, cache)?;
                if x == expr {
                    Ok(e)
                } else {
                    Ok(self.scratch.expr_mdata(Some(self.view.store), data, x)?)
                }
            }
            Node::Proj {
                type_name,
                idx,
                structure,
            } => {
                let s2 = self.elim(xs, structure, cache)?;
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
                // `expr_proj` re-selects the `Proj`/`ProjBig`
                // representation itself from the index's magnitude, so
                // one constructor serves both arms.
                let idxn = self.scratch.nat_at(Some(self.view.store), idx).clone();
                let s2 = self.elim(xs, structure, cache)?;
                if s2 == structure {
                    Ok(e)
                } else {
                    Ok(self
                        .scratch
                        .expr_proj(Some(self.view.store), type_name, &idxn, s2)?)
                }
            }
            _ => Ok(e),
        }
    }

    /// oracle: `elimApp` (`:1230-1249`).
    fn elim_app(
        &mut self,
        xs: &[ExprId],
        f: ExprId,
        args: &[ExprId],
        cache: &mut ElimCache,
    ) -> Result<ExprId, MetaError> {
        if let Node::MVar { id: Some(n) } = self.node(f) {
            let mid = crate::MVarId(n);
            match self.mctx.assignment(mid) {
                Some(new_f) => {
                    if matches!(self.node(new_f), Node::Lam { .. }) {
                        // oracle `:1236-1239`: arguments can become
                        // irrelevant after beta, so beta FIRST, then elim.
                        let mut visited = Vec::with_capacity(args.len());
                        for a in args {
                            visited.push(self.elim(xs, *a, cache)?);
                        }
                        // NOT reversed. The oracle writes
                        // `newF.betaRev args.reverse` because Lean's
                        // `Expr.betaRev` takes its arguments in REVERSE
                        // application order; this crate's `beta_rev`
                        // (`whnf.rs:1743`) takes them in CALL order —
                        // `whnf_core_app` hands it `get_app_args`' result
                        // straight through (`whnf.rs:423`), and
                        // `instantiate_delayed_app` (`assign.rs`) does the
                        // same with a test pinning the mapping
                        // (`instantiate_mvars_delayed_app_maps_multiple_args_to_fvars_in_order`).
                        // `visited` is already in call order, so it is
                        // passed as-is; reversing here would swap which
                        // binder each argument substitutes for.
                        let applied = self.beta_rev(new_f, &visited)?;
                        // `visit_guarded`, not `elim`: oracle `:1238`
                        // writes `elim xs <| newF.betaRev …`, the
                        // STRUCTURAL function, so the beta-reduct is not
                        // looked up in — nor added to — the cache. Same
                        // cached-vs-structural distinction as
                        // `abstract_range_aux`; see `elim`'s note on the
                        // port's inverted names.
                        return self.visit_guarded(xs, applied, cache);
                    }
                    return self.elim_app(xs, new_f, args, cache);
                }
                None => {
                    let (out, _) = self.elim_mvar(xs, mid, args, cache)?;
                    return Ok(out);
                }
            }
        }
        let f2 = self.elim(xs, f, cache)?;
        let mut out = f2;
        for a in args {
            let a2 = self.elim(xs, *a, cache)?;
            out = self.scratch.expr_app(Some(self.view.store), out, a2)?;
        }
        Ok(out)
    }

    /// oracle: `elimMVar` (`:1176-1229`). Returns the rewritten
    /// occurrence and the `to_revert` list, mirroring the oracle's pair
    /// (the second component is `revert`'s, which leanr has no caller
    /// for, but keeping the shape keeps the transcription readable).
    fn elim_mvar(
        &mut self,
        xs: &[ExprId],
        mvar_id: crate::MVarId,
        args: &[ExprId],
        cache: &mut ElimCache,
    ) -> Result<(ExprId, Vec<ExprId>), MetaError> {
        let Some(decl) = self.mctx.decl(mvar_id) else {
            return Err(MetaError::MVar(format!(
                "elim_mvar: metavariable {mvar_id:?} was never declared"
            )));
        };
        let kind = decl.kind;
        let decl_ty = decl.ty;
        let mvar_lctx = Arc::clone(&decl.lctx);

        let to_revert = self.get_in_scope(&mvar_lctx, xs);
        let mvar_expr = self
            .scratch
            .expr_mvar(Some(self.view.store), Some(mvar_id.0))?;
        if to_revert.is_empty() {
            // oracle `:1180-1182`: nothing in this metavariable's context
            // is being abstracted, so it stands; only the arguments are
            // visited.
            let mut out = mvar_expr;
            for a in args {
                let a2 = self.elim(xs, *a, cache)?;
                out = self.scratch.expr_app(Some(self.view.store), out, a2)?;
            }
            return Ok((out, Vec::new()));
        }

        let mut visited = Vec::with_capacity(args.len());
        for a in args {
            visited.push(self.elim(xs, *a, cache)?);
        }

        let to_revert = self.collect_forward_deps(&mvar_lctx, to_revert)?;
        let new_lctx = self.reduce_local_context(&mvar_lctx, &to_revert)?;
        // oracle `:1205`, `withFreshCache do mkAuxMVarType …` — ONE
        // fresh cache, spanning the whole of `mk_aux_mvar_type`, because
        // the entries the caller's cache holds were computed for `xs`
        // and everything below eliminates over `to_revert`, which may
        // differ. Fresh here and shared across `mk_aux_mvar_type`'s own
        // abstraction sites is the oracle's scope exactly: narrower
        // (one per site) would mint duplicate auxiliary metavariables
        // for a `syntheticOpaque` subterm shared between the type and a
        // binder type; wider (the caller's) would reuse rewrites keyed
        // to the wrong variable set.
        let mut aux_cache = ElimCache::default();
        let new_ty = self.mk_aux_mvar_type_with(&mvar_lctx, &to_revert, decl_ty, &mut aux_cache)?;
        let (new_mvar, new_id) = self.mk_aux_mvar_at(new_lctx, new_ty, kind)?;
        let result = self.mk_mvar_app(new_mvar, &to_revert)?;

        if kind != crate::MVarKind::SyntheticOpaque {
            // oracle `:1214-1215`.
            self.mctx.assign(mvar_id, result)?;
        } else {
            // oracle `:1216-1228`. A syntheticOpaque metavariable must
            // only ever be assigned by the elaborator that created it, so
            // the NEW one is delayed-assigned back to the original
            // instead. `nested` carries any delayed assignment the
            // original already had (`:1224-1226`).
            let (pending, nested) = match self.mctx.delayed_assignment(mvar_id) {
                Some(d) => (d.mvar_id_pending, d.fvars.clone()),
                None => (mvar_id, Vec::new()),
            };
            let mut fvars = to_revert.clone();
            fvars.extend(nested);
            self.mctx.assign_delayed(new_id, fvars, pending)?;
        }

        let mut out = result;
        for a in visited {
            out = self.scratch.expr_app(Some(self.view.store), out, a)?;
        }
        Ok((out, to_revert))
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
    /// as a caller argument, `metactx.rs:830` — `mk_let_expr`), so both
    /// ldecl arms have no input. Writing one would be guessing, and a
    /// wrong `ExprId` is
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
    /// Both abstractions below go through `abstract_range_aux`, this
    /// port's `abstractRangeAux` (`:1165-1167`): eliminate metavariable
    /// dependencies over the whole of `xs` FIRST, then abstract the
    /// prefix. They SHARE one cache — the oracle's `withFreshCache`
    /// (`:1205`) wraps this whole function, not each abstraction inside
    /// it. This entry point supplies that one fresh cache; `elim_mvar`
    /// calls `mk_aux_mvar_type_with` and supplies its own, for the same
    /// single-reset scope.
    /// Test-only: production reaches the same code through
    /// `mk_aux_mvar_type_with`, which supplies the caller's cache
    /// (`elim_mvar`, `:638`). This wrapper exists so the tests below can
    /// exercise `mkAuxMVarType` on its own with the `withFreshCache`
    /// scope the oracle gives it at `:1205`. `#[cfg(test)]` rather than
    /// `#[allow(dead_code)]`: it states the fact instead of hiding it.
    #[cfg(test)]
    pub(crate) fn mk_aux_mvar_type(
        &mut self,
        lctx: &LocalCtxSnapshot,
        xs: &[ExprId],
        ty: ExprId,
    ) -> Result<ExprId, MetaError> {
        let mut cache = ElimCache::default();
        self.mk_aux_mvar_type_with(lctx, xs, ty, &mut cache)
    }

    /// `mk_aux_mvar_type` with the `withFreshCache` scope (`:1205`)
    /// chosen by the caller. Same body; the split exists only so that
    /// `elim_mvar` can own the reset, which is where the oracle puts it.
    fn mk_aux_mvar_type_with(
        &mut self,
        lctx: &LocalCtxSnapshot,
        xs: &[ExprId],
        ty: ExprId,
        cache: &mut ElimCache,
    ) -> Result<ExprId, MetaError> {
        let mut e = self.abstract_range_aux(xs, xs.len(), ty, cache)?;
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
                    // oracle `:1130-1131` (cdecl arm): `let type :=
                    // type.headBeta` before `abstractRangeAux`. An
                    // earlier controller ruling parked this on the
                    // (factually wrong) grounds that leanr has no
                    // `headBeta`; `head_beta` exists (`whnf.rs:1789`)
                    // and is `pub(crate)`. Applied BEFORE the
                    // abstraction below, matching the oracle's
                    // placement.
                    let ty = self.head_beta(decl.ty)?;
                    (decl.binder_name, ty, decl.binder_info)
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
                    let user_name = decl.user_name;
                    let ty = decl.ty;
                    // oracle `:1160-1161` (mvar arm): same `headBeta`,
                    // before the abstraction below.
                    let ty = self.head_beta(ty)?;
                    (user_name, ty, leanr_kernel::BinderInfo::Implicit)
                }
            };
            let binder_ty = self.abstract_range_aux(xs, i, binder_ty, cache)?;
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

    /// Final-review fix wave, item 4: `local_decl_depends_on`'s VALUE
    /// branch (`:147-148`) had no direct test — every existing caller
    /// reaches it only through `collect_forward_deps`'s corpus-shaped
    /// fixtures, none of which isolate a let-decl whose TYPE is clean
    /// but whose VALUE alone carries the dependency. Measured: mutating
    /// that branch to `Ok(false)` left the entire workspace suite green;
    /// this is the test that splits on it.
    #[test]
    fn local_decl_depends_on_sees_a_dependency_carried_only_by_the_value() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let ia = fvar_id(ctx, a);

            // The TYPE is `Sort 0` — mentions nothing, so
            // `local_decl_depends_on`'s first check (the type) must
            // return false and fall through to the value. The VALUE is
            // `a` itself.
            assert!(
                !ctx.depends_on(sort0, &[ia]).expect("depends_on"),
                "the type must NOT depend on `a`, or this test would not \
                 discriminate the value branch at all"
            );
            assert!(
                ctx.local_decl_depends_on(sort0, Some(a), &[ia])
                    .expect("local_decl_depends_on"),
                "the VALUE mentions `a`; a let-decl with a clean type and \
                 a dependent value must still be judged dependent — \
                 oracle `findLocalDeclDependsOn`/`localDeclDependsOn` \
                 (`:744`, `:767`) checks the value whenever one is \
                 present"
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

    /// Task 8 fix round 1: the METAVARIABLE "may dependency" arm
    /// (`:1157-1163`) had zero test coverage — none of the tests above
    /// puts an `mvar` in `xs`. This reaches it directly: `xs = [m]`
    /// where `m` is a bare, unassigned mvar (never routed through the
    /// fvar path at all), and pins the THREE things that arm reads off
    /// `MVarDecl` that the cdecl arm never would: the binder type is
    /// the mvar's OWN type (`decl.ty`, not anything from `lctx`), the
    /// binder name is the mvar's `user_name`, and — the part that makes
    /// this more than a smoke test, because it is the one choice this
    /// arm makes that the cdecl arm structurally cannot (a cdecl reads
    /// `decl.binder_info` off the LOCAL CONTEXT; this arm hardcodes
    /// `binderInfoForMVars`) — the binder info is `Implicit`.
    #[test]
    fn mk_aux_mvar_type_wraps_a_reverted_mvar_with_its_own_type_and_implicit_binder_info() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            // `fresh_mvar` always mints `user_name: None`; overwrite the
            // declaration in place (same id, same lctx, same kind) so the
            // binder-name propagation is pinned too, not just the type.
            let (m, mid) = fresh_mvar(ctx, sort0);
            let name_str = ctx
                .scratch
                .intern_str(base, "m")
                .expect("interning a tiny fixed name is infallible");
            let uname = ctx
                .scratch
                .name_str(base, None, name_str)
                .expect("interning a tiny fixed name is infallible");
            let lctx = ctx
                .mctx()
                .decl(mid)
                .expect("fresh_mvar declared it")
                .lctx
                .clone();
            ctx.mctx_mut().declare(
                mid,
                crate::MVarDecl {
                    user_name: Some(uname),
                    ty: sort0,
                    lctx,
                    kind: crate::MVarKind::Natural,
                },
            );

            let snap = ctx.current_lctx();
            let ty = ctx
                .mk_aux_mvar_type(&snap, &[m], sort0)
                .expect("mk_aux_mvar_type");
            match ctx.node(ty) {
                Node::Forall {
                    binder_name,
                    binder_type,
                    binder_info,
                    ..
                } => {
                    assert_eq!(
                        binder_type, sort0,
                        "the forall's binder type is the mvar's OWN type (decl.ty), \
                         not anything read off lctx"
                    );
                    assert_eq!(
                        binder_name,
                        Some(uname),
                        "the binder name comes from the mvar's user_name"
                    );
                    assert_eq!(
                        binder_info,
                        leanr_kernel::BinderInfo::Implicit,
                        "binderInfoForMVars — the one choice this arm makes that the \
                         cdecl arm structurally cannot, since a cdecl reads binder_info \
                         off the local context instead of hardcoding it"
                    );
                }
                other => panic!("expected Forall, got {other:?}"),
            }
        });
    }

    /// TDD RED/GREEN for plan task 9, the DELAYED branch. A
    /// `SyntheticOpaque` metavariable minted under `a`, met while
    /// abstracting `[a]`, is replaced by `?new a`; the ORIGINAL is left
    /// unassigned (it must only be assigned by the elaborator that made
    /// it) and the NEW one is delayed-assigned back to it.
    ///
    /// **The context is TWO binders and only `a` is reverted**
    /// (elimMVarDeps task 11). That is what makes the closing
    /// assertions discriminate `reduce_local_context`
    /// (`reduceLocalContext`, `:1065-1067`) IN BOTH DIRECTIONS: the
    /// auxiliary metavariable's declared context must have `a` ERASED
    /// and `b` STILL PRESENT. The one-binder version this replaces
    /// asserted only `depth() == 0`, which an implementation erasing
    /// the WHOLE context satisfies — measured: erasing everything left
    /// the old assertion green and fails the `b`-present one below,
    /// while erasing nothing fails the `depth`/`a`-absent ones.
    #[test]
    fn elim_mvar_deps_delays_a_synthetic_opaque_metavariable() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            // `b` is declared AFTER `a` and is NOT reverted: it is the
            // survivor `reduce_local_context` must leave in place.
            let b = fresh_fvar(ctx, sort0, "b");
            let lctx = ctx.current_lctx();
            let (m, mid) = ctx
                .mk_aux_mvar_at(lctx, sort0, crate::MVarKind::SyntheticOpaque)
                .expect("opaque mvar under the binder");

            let out = ctx.elim_mvar_deps(&[a], m).expect("elim_mvar_deps");

            assert_ne!(out, m, "the occurrence was rewritten");
            match ctx.node(out) {
                Node::App { f, arg } => {
                    assert_eq!(arg, a, "applied to the reverted fvar");
                    let Node::MVar { id: Some(n) } = ctx.node(f) else {
                        panic!("head should be the auxiliary metavariable");
                    };
                    let new_id = crate::MVarId(n);
                    assert_ne!(new_id, mid, "a FRESH metavariable");
                    assert!(
                        ctx.mctx().assignment(mid).is_none(),
                        "the syntheticOpaque original is NOT assigned — only the \
                         elaborator that created it may assign it"
                    );
                    let d = ctx
                        .mctx()
                        .delayed_assignment(new_id)
                        .expect("the new one is delayed-assigned back to the original");
                    assert_eq!(d.mvar_id_pending, mid);
                    assert_eq!(d.fvars, vec![a]);
                    let new_lctx =
                        std::sync::Arc::clone(&ctx.mctx().decl(new_id).expect("declared").lctx);
                    assert_eq!(
                        new_lctx.depth(),
                        1,
                        "minted at the REDUCED context — exactly one of the two \
                         declarations survives"
                    );
                    assert!(
                        new_lctx.lctx().get(fvar_id(ctx, a)).is_none(),
                        "`a` — the reverted fvar — is ERASED from the auxiliary \
                         metavariable's context. Leaving it would let the new \
                         metavariable be assigned the very variable the abstraction \
                         is removing (`reduce_local_context`'s own doc), which is \
                         this slice's bug reappearing one level down"
                    );
                    assert!(
                        new_lctx.lctx().get(fvar_id(ctx, b)).is_some(),
                        "`b` — declared alongside `a` but NOT reverted — SURVIVES. \
                         `reduceLocalContext` erases exactly `to_revert`, not the \
                         whole context: an auxiliary metavariable that lost `b` \
                         could no longer be assigned any term mentioning it"
                    );
                }
                other => panic!("expected App, got {other:?}"),
            }
            ctx.lctx_restore(cp);
        });
    }

    /// The PLAIN-ASSIGN branch: a `Synthetic` metavariable is assigned
    /// outright, `?m := ?new a`. Oracle `:1214-1215`.
    #[test]
    fn elim_mvar_deps_assigns_a_synthetic_metavariable_outright() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let lctx = ctx.current_lctx();
            let (m, mid) = ctx
                .mk_aux_mvar_at(lctx, sort0, crate::MVarKind::Synthetic)
                .expect("synthetic mvar under the binder");

            let _ = ctx.elim_mvar_deps(&[a], m).expect("elim_mvar_deps");

            let assigned = ctx
                .mctx()
                .assignment(mid)
                .expect("a non-opaque original IS assigned outright");
            match ctx.node(assigned) {
                Node::App { arg, .. } => assert_eq!(arg, a),
                other => panic!("expected `?new a`, got {other:?}"),
            }
            assert!(
                !ctx.mctx().is_delayed_assigned(mid),
                "the plain branch uses no delayed assignment"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// A metavariable whose own context does NOT contain any of `xs` is
    /// left completely alone — `getInScope` is empty, oracle `:1180-1182`.
    #[test]
    fn elim_mvar_deps_leaves_an_out_of_scope_metavariable_alone() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            // Minted OUTSIDE the binder: empty declared context.
            let (m, mid) = ctx.mk_aux_mvar(sort0).expect("mvar");
            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");

            let out = ctx.elim_mvar_deps(&[a], m).expect("elim_mvar_deps");
            assert_eq!(out, m, "untouched");
            assert!(ctx.mctx().assignment(mid).is_none());
            assert!(!ctx.mctx().is_delayed_assigned(mid));
            ctx.lctx_restore(cp);
        });
    }

    /// The fast path: a term with no expr metavariable is returned
    /// unchanged, allocating nothing. Oracle `:1253-1254`.
    #[test]
    fn elim_mvar_deps_is_identity_on_a_metavariable_free_term() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let app = ctx.scratch.expr_app(base, a, sort0).expect("app");
            assert_eq!(ctx.elim_mvar_deps(&[a], app).expect("elim"), app);
            ctx.lctx_restore(cp);
        });
    }
    /// The shape `elim_mvar` leaves behind for a one-element
    /// `to_revert`: a FRESH auxiliary metavariable applied to the
    /// reverted fvar.
    fn assert_rewritten_to_aux_app(
        ctx: &crate::MetaCtx,
        out: leanr_kernel::bank::ExprId,
        orig: crate::MVarId,
        x: leanr_kernel::bank::ExprId,
    ) {
        match ctx.node(out) {
            Node::App { f, arg } => {
                assert_eq!(arg, x, "applied to the reverted fvar");
                let Node::MVar { id: Some(n) } = ctx.node(f) else {
                    panic!("head should be the auxiliary metavariable");
                };
                assert_ne!(crate::MVarId(n), orig, "a FRESH metavariable");
            }
            other => panic!("expected `?new x`, got {other:?}"),
        }
    }

    /// Fix round 1 (task 9 review, Important 1): `visit`'s `Proj`,
    /// `ProjBig` and `MData` arms — oracle `:1106` and `:1110`. These are
    /// NOT unreachable: `has_expr_mvar` propagates through all three
    /// constructors, so `elim`'s fast path does not fire and a catch-all
    /// would silently return (and cache) a term still carrying the
    /// metavariable this pass exists to rewrite.
    ///
    /// Three separate metavariables and three separate `elim_mvar_deps`
    /// calls, so each arm is measured on its own rather than riding on a
    /// cache entry another arm populated.
    #[test]
    fn elim_mvar_deps_descends_into_proj_projbig_and_mdata() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");

            // -- Proj (small index: fits in a u32 row field) --
            let (m1, id1) = ctx.mk_aux_mvar(sort0).expect("mvar under `a`");
            let proj = ctx
                .scratch
                .expr_proj(base, None, &leanr_kernel::Nat::from(0u64), m1)
                .expect("proj");
            let out = ctx.elim_mvar_deps(&[a], proj).expect("elim_mvar_deps");
            assert_ne!(out, proj, "the projection was rebuilt");
            match ctx.node(out) {
                Node::Proj { idx, structure, .. } => {
                    assert_eq!(idx, 0, "the field index is preserved");
                    assert_rewritten_to_aux_app(ctx, structure, id1, a);
                }
                other => panic!("expected Proj, got {other:?}"),
            }

            // -- ProjBig (index too large for the u32 field) --
            let big = leanr_kernel::Nat::from(1u64 << 40);
            let (m2, id2) = ctx.mk_aux_mvar(sort0).expect("mvar under `a`");
            let projbig = ctx
                .scratch
                .expr_proj(base, None, &big, m2)
                .expect("projbig");
            assert!(
                matches!(ctx.node(projbig), Node::ProjBig { .. }),
                "the index chose the big representation"
            );
            let out = ctx.elim_mvar_deps(&[a], projbig).expect("elim_mvar_deps");
            assert_ne!(out, projbig, "the projection was rebuilt");
            match ctx.node(out) {
                Node::ProjBig { idx, structure, .. } => {
                    assert_eq!(
                        *ctx.scratch.nat_at(base, idx),
                        big,
                        "the big field index is preserved"
                    );
                    assert_rewritten_to_aux_app(ctx, structure, id2, a);
                }
                other => panic!("expected ProjBig, got {other:?}"),
            }

            // -- MData --
            let kv = ctx
                .scratch
                .intern_kvmap_rows(base, Vec::new())
                .expect("empty kvmap");
            let (m3, id3) = ctx.mk_aux_mvar(sort0).expect("mvar under `a`");
            let md = ctx.scratch.expr_mdata(base, kv, m3).expect("mdata");
            let out = ctx.elim_mvar_deps(&[a], md).expect("elim_mvar_deps");
            assert_ne!(out, md, "the mdata wrapper was rebuilt");
            match ctx.node(out) {
                Node::MData { data, expr } => {
                    assert_eq!(data, kv, "the annotation is preserved");
                    assert_rewritten_to_aux_app(ctx, expr, id3, a);
                }
                other => panic!("expected MData, got {other:?}"),
            }

            ctx.lctx_restore(cp);
        });
    }

    /// Fix round 1 (task 9 review, Important 2): `elim_app`'s
    /// ASSIGNED-head beta branch (oracle `:1236-1239`), and with it the
    /// argument order handed to `beta_rev`.
    ///
    /// `?m := fun x y => x` applied to two DISTINCT arguments `b`, `c`.
    /// The answer is `b`, because this crate's `beta_rev`
    /// (`whnf.rs:1743`) takes its arguments in CALL order — it consumes
    /// a PREFIX of the slice, so `args[0]` belongs to the OUTERMOST
    /// binder. The oracle writes `newF.betaRev args.reverse` only
    /// because Lean's `Expr.betaRev` takes the reversed order; porting
    /// that `.reverse()` literally would answer `c`, and this assertion
    /// is what says so out loud.
    #[test]
    fn elim_mvar_deps_betas_an_assigned_lambda_head_in_call_order() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let x = fresh_fvar(ctx, sort0, "x");
            let y = fresh_fvar(ctx, sort0, "y");
            let b = fresh_fvar(ctx, sort0, "b");
            let c = fresh_fvar(ctx, sort0, "c");

            // `fun x y => x` — asymmetric in its binders, so a swapped
            // argument mapping answers `c` instead of `b`.
            let lam = ctx.mk_lambda(&[x, y], x).expect("mk_lambda");
            let (m, mid) = ctx.mk_aux_mvar(sort0).expect("mvar");
            ctx.mctx_mut().assign(mid, lam).expect("?m := fun x y => x");

            let app = ctx.scratch.expr_app(base, m, b).expect("?m b");
            let app = ctx.scratch.expr_app(base, app, c).expect("?m b c");

            let out = ctx.elim_mvar_deps(&[a], app).expect("elim_mvar_deps");
            assert_eq!(
                out, b,
                "`(fun x y => x) b c` is `b`: `beta_rev` takes CALL order, so the \
                 FIRST argument belongs to the OUTERMOST binder"
            );
            assert_ne!(out, c, "reversing the arguments would answer `c`");
            ctx.lctx_restore(cp);
        });
    }

    /// Fix round 1 (task 9 review, Important 2): `elim_app`'s other
    /// assigned-head branch (oracle `:1240`) — an assignment that is not
    /// a lambda is followed with the SAME argument list, so the
    /// arguments survive the hop and reappear after the reverted fvars.
    #[test]
    fn elim_mvar_deps_follows_a_non_lambda_assignment_carrying_its_args() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            // `?n` sees `a`; `?m := ?n`, and `?n` is left UNASSIGNED so
            // the hop lands in `elim_mvar`.
            let (n, nid) = ctx.mk_aux_mvar(sort0).expect("?n under `a`");
            let (m, mid) = ctx.mk_aux_mvar(sort0).expect("?m under `a`");
            ctx.mctx_mut().assign(mid, n).expect("?m := ?n");
            let b = fresh_fvar(ctx, sort0, "b");

            let app = ctx.scratch.expr_app(base, m, b).expect("?m b");
            let out = ctx.elim_mvar_deps(&[a], app).expect("elim_mvar_deps");

            assert_eq!(
                ctx.get_app_args(out),
                vec![a, b],
                "`?new a b`: the reverted fvar first, then the argument the hop \
                 through `?m := ?n` carried across"
            );
            let head = ctx.get_app_fn(out);
            let Node::MVar { id: Some(h) } = ctx.node(head) else {
                panic!("head should be the auxiliary metavariable");
            };
            assert_ne!(crate::MVarId(h), nid, "a FRESH metavariable, not `?n`");
            assert!(
                ctx.mctx().assignment(nid).is_some(),
                "`?n` — the metavariable actually reached — is the one assigned"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// Final-review fix wave, item 5: `elim_app`'s post-beta re-entry
    /// (oracle `:1238`) must use the STRUCTURAL `visit_guarded`, not the
    /// cached `elim` — the port's own doc on `elim`'s inverted names
    /// already says so (see `elim`'s doc comment above), but until now
    /// nothing measured it: a prior round's mutation of that one call
    /// site left the FULL suite green.
    ///
    /// `?o`, `syntheticOpaque` and minted UNDER `a`, is reached TWICE
    /// while eliminating `h ?o (?m c)`: once directly, as the first
    /// argument (which mints aux1 and populates `cache[?o]`), and once
    /// again after `?m := fun x => ?o` — a CONSTANT lambda; its body
    /// never mentions `x` — beta-reduces `?m c` to the exact SAME
    /// `ExprId` as `?o`. The oracle's structural re-entry at that second
    /// site does not consult the cache, so it re-enters `elim_mvar` and
    /// mints a SECOND, DIFFERENT auxiliary metavariable (aux2). Measured:
    /// swapping `visit_guarded` for the cached `elim` at that call site
    /// turns the second occurrence into a cache HIT that answers aux1
    /// again, and the assertion below flips.
    #[test]
    fn elim_app_post_beta_reentry_is_structural_not_cached() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let h = fresh_fvar(ctx, sort0, "h");
            let c = fresh_fvar(ctx, sort0, "c");
            // `?o` is minted UNDER `a`, so `a` is in ITS OWN declared
            // context — the precondition `elim_mvar`'s `getInScope`
            // needs to touch it at all.
            let lctx_with_a = ctx.current_lctx();
            let (o, _oid) = ctx
                .mk_aux_mvar_at(lctx_with_a, sort0, crate::MVarKind::SyntheticOpaque)
                .expect("?o under `a`");

            // `x` is the lambda's own fresh binder; only its scope is
            // irrelevant — what matters is that the BODY (`o`) never
            // mentions it, so beta substitutes nothing and the result is
            // literally the same `ExprId` as `o`.
            let x = fresh_fvar(ctx, sort0, "x");
            let lam = ctx.mk_lambda(&[x], o).expect("mk_lambda: fun x => ?o");
            let (m, mid) = ctx.mk_aux_mvar(sort0).expect("?m");
            ctx.mctx_mut()
                .assign(mid, lam)
                .expect("?m := fun x => ?o, a CONSTANT lambda in x");

            let m_c = ctx.scratch.expr_app(base, m, c).expect("?m c");
            let h_o = ctx.scratch.expr_app(base, h, o).expect("h ?o");
            let app = ctx.scratch.expr_app(base, h_o, m_c).expect("h ?o (?m c)");

            let out = ctx.elim_mvar_deps(&[a], app).expect("elim_mvar_deps");

            let args = ctx.get_app_args(out);
            assert_eq!(
                args.len(),
                2,
                "`h` applied to exactly the two original arguments' rewrites"
            );
            let aux_mvar_id = |ctx: &crate::MetaCtx, occurrence: leanr_kernel::bank::ExprId| {
                let head = ctx.get_app_fn(occurrence);
                match ctx.node(head) {
                    Node::MVar { id: Some(n) } => crate::MVarId(n),
                    other => panic!(
                        "expected the rewritten occurrence's head to be an mvar, got {other:?}"
                    ),
                }
            };
            let aux1 = aux_mvar_id(ctx, args[0]);
            let aux2 = aux_mvar_id(ctx, args[1]);
            assert_ne!(
                aux1, aux2,
                "the first argument (`?o` directly) and the second (`?m c`, \
                 which beta-reduces to the SAME `ExprId` as `?o`) must mint \
                 TWO DIFFERENT auxiliary metavariables — the oracle's \
                 structural re-entry after beta does not consult the cache. \
                 A cached re-entry would answer the same aux id for both, \
                 which is exactly the regression this test exists to catch"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// Fix round 1 (task 9 review, follow-on 5): the `nested` carry,
    /// oracle `:1224-1226`. When the syntheticOpaque original ALREADY
    /// has a delayed assignment, the new one inherits that assignment's
    /// PENDING metavariable — not the original — and its fvars are
    /// appended after `to_revert`.
    #[test]
    fn elim_mvar_deps_carries_a_nested_delayed_assignment() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let lctx = ctx.current_lctx();
            let (m, mid) = ctx
                .mk_aux_mvar_at(lctx, sort0, crate::MVarKind::SyntheticOpaque)
                .expect("opaque mvar under the binder");
            let (_, pending) = ctx.mk_aux_mvar(sort0).expect("the pending mvar");
            // `z` is minted AFTER `?m`, so it is not in `?m`'s context
            // and cannot join `to_revert` — it can only arrive by the
            // `nested` route.
            let z = fresh_fvar(ctx, sort0, "z");
            ctx.mctx_mut()
                .assign_delayed(mid, vec![z], pending)
                .expect("?m #[z] := ?pending");

            let out = ctx.elim_mvar_deps(&[a], m).expect("elim_mvar_deps");
            let head = ctx.get_app_fn(out);
            let Node::MVar { id: Some(h) } = ctx.node(head) else {
                panic!("head should be the auxiliary metavariable");
            };
            let new_id = crate::MVarId(h);

            let d = ctx
                .mctx()
                .delayed_assignment(new_id)
                .expect("the new one is delayed-assigned");
            assert_eq!(
                d.mvar_id_pending, pending,
                "the ORIGINAL's pending mvar is inherited, not the original itself"
            );
            assert_ne!(d.mvar_id_pending, mid);
            assert_eq!(
                d.fvars,
                vec![a, z],
                "`to_revert ++ nested` — the reverted fvar, then the fvars the \
                 original's own delayed assignment already abstracted"
            );
            ctx.lctx_restore(cp);
        });
    }
    /// Fix round 1 (task 9 review, Important 3), retargeted in fix
    /// round 2: the `withFreshCache` SCOPE, oracle `:1205`. The reset
    /// wraps the whole of `mkAuxMVarType`, not each abstraction inside
    /// it, and the difference is observable rather than merely a matter
    /// of recomputation.
    ///
    /// `?o : Sort 0` is an unassigned `syntheticOpaque` metavariable
    /// whose context holds `a`. It appears NESTED — as `f ?o`, the
    /// original `?m`'s own type, and as `g ?o`, `b`'s binder type — so
    /// `mk_aux_mvar_type` meets it at two different abstraction sites,
    /// each time below an application node.
    ///
    /// Nested is the configuration the oracle genuinely shares, and the
    /// nesting is load-bearing, not incidental. `abstractRangeAux`
    /// (`:1166`) enters at the oracle's STRUCTURAL `elim`, which does
    /// not consult the cache; the cache is consulted only from the
    /// oracle's `visit` (`checkCache`, `:1102`), which is where the
    /// recursive descent into `f ?o`'s argument goes. So a subterm
    /// shared BELOW the top of two sites is eliminated once and both
    /// sites name the same auxiliary metavariable, while a subterm that
    /// IS the whole of both sites' inputs re-enters `elimMVar` at each
    /// and gets one auxiliary metavariable per site. This test pins the
    /// first case; `visit_guarded` is what keeps the second one honest.
    #[test]
    fn elim_mvar_deps_mints_one_aux_for_a_nested_opaque_subterm_shared_across_sites() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            // `f` and `g` are declared BEFORE `a`, so neither can join
            // `to_revert`; they exist only to put `?o` under an
            // application node at both sites.
            let f = fresh_fvar(ctx, sort0, "f");
            let g = fresh_fvar(ctx, sort0, "g");
            let a = fresh_fvar(ctx, sort0, "a");
            let lctx_a = ctx.current_lctx();
            let (o, _oid) = ctx
                .mk_aux_mvar_at(lctx_a, sort0, crate::MVarKind::SyntheticOpaque)
                .expect("`?o` under `a`");
            let g_o = ctx.scratch.expr_app(base, g, o).expect("`g ?o`");
            let f_o = ctx.scratch.expr_app(base, f, o).expect("`f ?o`");
            // `b : g ?o`, so `?o` is nested in a binder type of
            // `to_revert`; `?m : f ?o` nests it in the original's own
            // type.
            let b = fresh_fvar(ctx, g_o, "b");
            let lctx_ab = ctx.current_lctx();
            let (m, _mid) = ctx
                .mk_aux_mvar_at(lctx_ab, f_o, crate::MVarKind::Natural)
                .expect("`?m : f ?o` under `a`, `b`");

            let out = ctx.elim_mvar_deps(&[a, b], m).expect("elim_mvar_deps");
            let new_head = ctx.get_app_fn(out);
            let Node::MVar { id: Some(h) } = ctx.node(new_head) else {
                panic!("head should be the auxiliary metavariable");
            };
            let new_ty = ctx.mctx().decl(crate::MVarId(h)).expect("declared").ty;

            // `forall (a : Sort 0) (b : g (?aux #0)), f (?aux #1)` — the
            // two occurrences differ only in de Bruijn index, because the
            // binder type is abstracted over a shorter prefix.
            let Node::Forall { body: inner, .. } = ctx.node(new_ty) else {
                panic!("expected the outer `a` binder, got {:?}", ctx.node(new_ty));
            };
            let Node::Forall {
                binder_type: b_ty,
                body: inner_body,
                ..
            } = ctx.node(inner)
            else {
                panic!("expected the `b` binder, got {:?}", ctx.node(inner));
            };
            let Node::App { arg: in_binder, .. } = ctx.node(b_ty) else {
                panic!("expected `g (?aux #0)`, got {:?}", ctx.node(b_ty));
            };
            let Node::App { arg: in_body, .. } = ctx.node(inner_body) else {
                panic!("expected `f (?aux #1)`, got {:?}", ctx.node(inner_body));
            };
            let head_in_binder = ctx.get_app_fn(in_binder);
            let head_in_body = ctx.get_app_fn(in_body);
            let (Node::MVar { id: Some(hb) }, Node::MVar { id: Some(hy) }) =
                (ctx.node(head_in_binder), ctx.node(head_in_body))
            else {
                panic!("both occurrences should be headed by a metavariable");
            };
            assert_eq!(
                crate::MVarId(hb),
                crate::MVarId(hy),
                "ONE auxiliary metavariable for the NESTED shared `?o`: the \
                 oracle's `withFreshCache` wraps the whole of `mkAuxMVarType` \
                 (`:1205`), so both sites share a cache, and a nested occurrence \
                 is reached through the cached entry"
            );
            ctx.lctx_restore(cp);
        });
    }
    /// The other half of `visit_guarded`'s split, and the half fix round
    /// 1 got wrong: a subterm shared as the WHOLE of two abstraction
    /// sites' inputs gets one auxiliary metavariable PER SITE.
    ///
    /// Same shape as the nested test above with the applications
    /// removed: `?o` is `?m`'s own type outright, and `b`'s binder type
    /// outright. `abstractRangeAux` (`:1166`) enters at the oracle's
    /// structural `elim`, which never reaches `checkCache` (`:1102`), so
    /// each site re-enters `elimMVar` and mints its own. No wrong term
    /// results — both auxiliaries are delayed-assigned back to the same
    /// `?o` over the same fvars, which this test also pins — but the
    /// COUNT differs, and a count that drifts from the oracle's drifts
    /// the name generator with it.
    #[test]
    fn elim_mvar_deps_mints_one_aux_per_site_for_a_top_level_shared_opaque_subterm() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");

            let cp = ctx.lctx_checkpoint();
            let a = fresh_fvar(ctx, sort0, "a");
            let lctx_a = ctx.current_lctx();
            let (o, oid) = ctx
                .mk_aux_mvar_at(lctx_a, sort0, crate::MVarKind::SyntheticOpaque)
                .expect("`?o` under `a`");
            let b = fresh_fvar(ctx, o, "b");
            let lctx_ab = ctx.current_lctx();
            let (m, _mid) = ctx
                .mk_aux_mvar_at(lctx_ab, o, crate::MVarKind::Natural)
                .expect("`?m : ?o` under `a`, `b`");

            let out = ctx.elim_mvar_deps(&[a, b], m).expect("elim_mvar_deps");
            let new_head = ctx.get_app_fn(out);
            let Node::MVar { id: Some(h) } = ctx.node(new_head) else {
                panic!("head should be the auxiliary metavariable");
            };
            let new_ty = ctx.mctx().decl(crate::MVarId(h)).expect("declared").ty;

            // `forall (a : Sort 0) (b : ?aux1 #0), ?aux2 #1`.
            let Node::Forall { body: inner, .. } = ctx.node(new_ty) else {
                panic!("expected the outer `a` binder, got {:?}", ctx.node(new_ty));
            };
            let Node::Forall {
                binder_type: b_ty,
                body: inner_body,
                ..
            } = ctx.node(inner)
            else {
                panic!("expected the `b` binder, got {:?}", ctx.node(inner));
            };
            let (Node::MVar { id: Some(hb) }, Node::MVar { id: Some(hy) }) = (
                ctx.node(ctx.get_app_fn(b_ty)),
                ctx.node(ctx.get_app_fn(inner_body)),
            ) else {
                panic!("both occurrences should be headed by a metavariable");
            };
            let (aux1, aux2) = (crate::MVarId(hb), crate::MVarId(hy));
            assert_ne!(
                aux1, aux2,
                "one auxiliary metavariable PER SITE for a TOP-LEVEL shared `?o`: \
                 `abstractRangeAux` (`:1166`) enters at the oracle's structural \
                 `elim`, which never reaches `checkCache` (`:1102`)"
            );
            for aux in [aux1, aux2] {
                let d = ctx
                    .mctx()
                    .delayed_assignment(aux)
                    .expect("each auxiliary is delayed-assigned");
                assert_eq!(
                    d.mvar_id_pending, oid,
                    "both point back at the SAME original — the extra mint is a \
                     count difference, not a wrong term"
                );
                assert_eq!(d.fvars, vec![a], "over the same reverted fvars");
            }
            assert!(
                ctx.mctx().assignment(oid).is_none(),
                "the syntheticOpaque original stays unassigned throughout"
            );
            ctx.lctx_restore(cp);
        });
    }
}
