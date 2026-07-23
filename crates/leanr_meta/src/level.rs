//! Universe-level unification: `is_level_def_eq`, its approximations,
//! and postponement (spec plan 3).
//!
//! oracle: `Lean/Meta/LevelDefEq.lean` (the mutual `solve`/
//! `isLevelDefEqAuxImpl` block, lines 99-177) + `Lean/Meta/Basic.lean`
//! (`isListLevelDefEqAux` :2347-2349, `processPostponedStep`/
//! `processPostponed` :2388-2422), toolchain leanprover/lean4:v4.33.0-rc1.
//!
//! # Depth / read-only seam (repeats at every site it applies)
//!
//! `isMVarWithGreaterDepth` and `mvarId.isReadOnly` (LevelDefEq.lean:
//! 104-118) depend on `MetavarContext`'s per-mvar `depth` vs. the
//! context's own `levelAssignDepth`/`depth` — machinery this crate does
//! not model (tier 1 has a single, flat mctx depth; every declared
//! level mvar is assignable and none is ever "read-only"). Depth
//! arrives with typeclass synthesis / `withNewMCtxDepth` (plan 4). Every
//! site below that would branch on it instead hard-codes the tier-1
//! answer (`isReadOnly` := `false`, "greater depth" := unreachable) with
//! its own citation, rather than silently dropping the branch.
//!
//! # `isDefEqStuckEx` seam
//!
//! `Config.isDefEqStuckEx` (Basic.lean:134, default `false`) is set
//! `true` in exactly one place in the oracle: `SynthInstance.lean:963`,
//! typeclass search (`withConfig (fun config => { config with
//! isDefEqStuckEx := true, .. })`), out of scope this plan (plan 4). So
//! at tier 1 the flag is always `false`, and every `if
//! cfg.isDefEqStuckEx && .. then throwIsDefEqStuck else <else>` in this
//! module collapses to its `<else>` branch unconditionally — this is
//! why `config.rs`'s own doc comment says the flag deliberately has no
//! `Config` field here at all (a typed error variant, `MetaError::
//! IsDefEqStuck`, is reserved for the EXPR-level stuck condition,
//! ExprDefEq.lean, a different call site entirely).
//!
//! # Id-native discipline
//!
//! Every traversal below walks `LevelId`s through `Store::level_row`
//! (the `oracle_fast.rs::encode_level` idiom), never materializing an
//! `Arc<Level>` except in the two leaf helpers where a kernel routine
//! has no id-native twin: [`MetaCtx::level_normalize`] (`Level::
//! normalize` — sorting/dedup has no cheap id-native port) is the only
//! one. `to_offset`'s `Succ`-peeling loop, by contrast, DOES have a
//! trivial id-native twin ([`MetaCtx::level_to_offset`]) so it is
//! reimplemented directly rather than materializing.
//!
//! `Level::occurs`, `strictOccursMax`, `mkMaxArgsDiff`, `mkLevelMax'`,
//! and `decAux?`/`decLevel?` have NO existing Rust port anywhere in
//! `leanr_kernel` (that crate only carries the KERNEL's own `mk_max`/
//! `Level::mk_max_pair`, a stricter full canonicalization `mkLevelMax'`
//! is explicitly NOT — see [`MetaCtx::mk_level_max_prime`]'s doc
//! comment), so this module transcribes all of them fresh, id-native,
//! from `Lean/Level.lean` and `Lean/Meta/LevelDefEq.lean`/`DecLevel.lean`
//! directly.

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::LevelId;
use leanr_kernel::{Level, Nat};

use crate::{LMVarId, MetaCtx, MetaError};

impl<'e> MetaCtx<'e> {
    // ===================================================================
    // Public entry points
    // ===================================================================

    /// The level-layer entry point `defeq.rs` calls from inside
    /// `is_def_eq_quick`/`is_def_eq_expensive`. oracle: this IS
    /// `isLevelDefEqAuxImpl` (`isLevelDefEqAux`, LevelDefEq.lean:
    /// 145-177) directly — NOT the `checkpointDefEq`-wrapped standalone
    /// `isLevelDefEq` (Basic.lean:2470-2471), which resets its own
    /// transient cache and its own postponed-queue diff on every call.
    /// A level compare that happens INSIDE expr defeq shares the
    /// enclosing `is_def_eq`'s single checkpoint/postponed-queue (task
    /// 3's `is_def_eq`, defeq.rs) — running a second, nested
    /// `checkpointDefEq` around every `Sort`/`Const`-levels pair would
    /// double-checkpoint and is not what the oracle's own call sites do
    /// either (`isDefEqQuick`'s `.sort`/`.const` arms and
    /// `isExprDefEqExpensive`'s call all read `isLevelDefEqAux`
    /// directly, never `isLevelDefEq`).
    pub(crate) fn is_level_def_eq(&mut self, u: LevelId, v: LevelId) -> Result<bool, MetaError> {
        self.is_level_def_eq_aux(u, v)
    }

    /// oracle: `isListLevelDefEqAux` (Basic.lean:2347-2349) — pairwise
    /// `isLevelDefEqAux`, short-circuiting (`<&&>`) on the first
    /// mismatch; mismatched lengths are a plain `false`, not an error
    /// (the `_, _ => return false` fallthrough covers every length
    /// mismatch, since the recursive `u::us, v::vs` arm only matches
    /// equal-length prefixes).
    pub(crate) fn is_def_eq_levels(
        &mut self,
        us: &[LevelId],
        vs: &[LevelId],
    ) -> Result<bool, MetaError> {
        if us.len() != vs.len() {
            return Ok(false);
        }
        for (&u, &v) in us.iter().zip(vs.iter()) {
            if !self.is_level_def_eq(u, v)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    // ===================================================================
    // isLevelDefEqAux / solve — the mutual block
    // ===================================================================

    /// oracle: `isLevelDefEqAuxImpl` (LevelDefEq.lean:145-177), the
    /// second half of the mutual block with [`MetaCtx::solve`].
    fn is_level_def_eq_aux(&mut self, lhs: LevelId, rhs: LevelId) -> Result<bool, MetaError> {
        self.step()?;
        self.guarded(|ctx| {
            // `Level.succ lhs, Level.succ rhs => isLevelDefEqAux lhs rhs`
            // (:145-146).
            if let (LevelRow::Succ(l), LevelRow::Succ(r)) = (
                *ctx.scratch.level_row(Some(ctx.view.store), lhs),
                *ctx.scratch.level_row(Some(ctx.view.store), rhs),
            ) {
                return ctx.is_level_def_eq_aux(l, r);
            }

            // `if lhs.getLevelOffset == rhs.getLevelOffset then return
            // lhs.getOffset == rhs.getOffset` (:150-151).
            let (lhs_base, lhs_k) = ctx.level_to_offset(lhs);
            let (rhs_base, rhs_k) = ctx.level_to_offset(rhs);
            if lhs_base == rhs_base {
                return Ok(lhs_k == rhs_k);
            }

            // `instantiateLevelMVars` + `.normalize` both sides, recurse
            // if EITHER changed (:152-158). `LevelId` equality here is
            // exact structural equality (levels are hash-consed), so
            // `!=` is exactly the oracle's `lhs != lhs'`.
            let lhs2 = ctx.instantiate_level_mvars(lhs)?;
            let lhs2 = ctx.level_normalize(lhs2)?;
            let rhs2 = ctx.instantiate_level_mvars(rhs)?;
            let rhs2 = ctx.level_normalize(rhs2)?;
            if lhs2 != lhs || rhs2 != rhs {
                return ctx.is_level_def_eq_aux(lhs2, rhs2);
            }

            // `solve lhs rhs`, else `solve rhs lhs` (:159-166).
            if let Some(b) = ctx.solve(lhs, rhs)? {
                return Ok(b);
            }
            if let Some(b) = ctx.solve(rhs, lhs)? {
                return Ok(b);
            }

            // Both undef: stuck/postpone tail (:167-177).
            let assignable =
                ctx.has_assignable_level_mvar(lhs)? || ctx.has_assignable_level_mvar(rhs)?;
            if !assignable {
                // SEAM: `isDefEqStuckEx` (module doc) — always `false`
                // at tier 1, so this always takes the oracle's `else
                // return false` branch; `throwIsDefEqStuck` is never
                // reached here.
                Ok(false)
            } else {
                ctx.postponed.push((lhs, rhs));
                Ok(true)
            }
        })
    }

    /// oracle: `solve` (LevelDefEq.lean:99-144), the first half of the
    /// mutual block. `Result<Option<bool>, MetaError>` stands in for
    /// `LBool` (`None` == `LBool.undef`).
    fn solve(&mut self, u: LevelId, v: LevelId) -> Result<Option<bool>, MetaError> {
        let u_row = *self.scratch.level_row(Some(self.view.store), u);
        let v_row = *self.scratch.level_row(Some(self.view.store), v);

        // `Level.mvar mvarId, _` (:101-116).
        if let LevelRow::MVar(name) = u_row {
            let Some(n) = name else {
                // An anonymous level mvar (no `NameId`) can never be
                // declared in / looked up from `MetavarContext` (same
                // convention `whnf.rs`'s `id.and_then(|i| ..)` uses for
                // anonymous EXPR mvars), so it behaves as permanently
                // read-only from this crate's point of view — same
                // verdict (`undef`) the oracle's `isReadOnly` check
                // below reaches, for a tier-1-specific reason.
                return Ok(None);
            };
            let mvar_id = LMVarId(n);
            // SEAM: `mvarId.isReadOnly` (:104, module doc) — always
            // `false` at tier 1.
            let is_read_only = false;
            if is_read_only {
                return Ok(None);
            }
            // SEAM: `isMVarWithGreaterDepth` (:107-108, :96-99, module
            // doc) — unreachable at tier 1 (a single flat mctx depth
            // means no mvar is ever "greater depth" than another).
            if !self.level_occurs(u, v)? {
                self.mctx.assign_level(mvar_id, v)?;
                return Ok(Some(true));
            }
            if matches!(v_row, LevelRow::Max(_, _)) && !self.strict_occurs_max(u, v)? {
                self.solve_self_max(mvar_id, v)?;
                return Ok(Some(true));
            }
            return Ok(None);
        }
        // `_, Level.mvar .. => return LBool.undef -- let solve v u handle`
        // (:117).
        if matches!(v_row, LevelRow::MVar(_)) {
            return Ok(None);
        }

        match (u_row, v_row) {
            // `Level.zero, Level.max v1 v2` (:118-119). `<&&>`
            // short-circuits; Rust's `&&` over two `?`-unwrapped `bool`s
            // has the same short-circuit shape (the right operand's `?`
            // is only evaluated if the left was `true`).
            (LevelRow::Zero, LevelRow::Max(v1, v2)) => Ok(Some(
                self.is_level_def_eq_aux(u, v1)? && self.is_level_def_eq_aux(u, v2)?,
            )),
            // `Level.zero, Level.imax _ v2` (:120-121).
            (LevelRow::Zero, LevelRow::IMax(_, v2)) => Ok(Some(self.is_level_def_eq_aux(u, v2)?)),
            // `Level.zero, Level.succ .. => return LBool.false` (:122).
            (LevelRow::Zero, LevelRow::Succ(_)) => Ok(Some(false)),
            // `Level.succ u, v` (:123-131). `pred` renames the oracle's
            // shadowing inner `u` (the succ's predecessor) to avoid
            // clashing with this function's own outer `u` parameter.
            (LevelRow::Succ(pred), _) => {
                if matches!(v_row, LevelRow::Param(_)) {
                    return Ok(Some(false));
                }
                let pred_is_mvar = matches!(
                    *self.scratch.level_row(Some(self.view.store), pred),
                    LevelRow::MVar(_)
                );
                if pred_is_mvar && self.level_occurs(pred, v)? {
                    return Ok(None);
                }
                match self.dec_level_top(v)? {
                    Some(v2) => Ok(Some(self.is_level_def_eq_aux(pred, v2)?)),
                    None => Ok(None),
                }
            }
            // `_, _` (:132-138): the `univApprox`-gated approximation
            // fallback. Also covers every combination the oracle's own
            // explicit arms above don't reach from here (e.g.
            // `Param, Param`, `Param, Zero` — none of solve's own
            // patterns name them, so they fall to this same wildcard in
            // the oracle too).
            _ => {
                if self.cfg.univ_approx {
                    if self.try_approx_self_max(u, v)? {
                        return Ok(Some(true));
                    }
                    if self.try_approx_max_max(u, v)? {
                        return Ok(Some(true));
                    }
                }
                Ok(None)
            }
        }
    }

    // ===================================================================
    // occurs check / strictOccursMax / solveSelfMax / mkMaxArgsDiff
    // ===================================================================

    /// oracle: `Level.occurs` (Level.lean:261-264) — no existing port in
    /// `leanr_kernel` (module doc); id-native, checking whole-node
    /// equality at every level before descending (matching the
    /// oracle's `u == v || occurs u v₁` shape exactly, rather than only
    /// checking equality at the leaves).
    fn level_occurs(&mut self, u: LevelId, v: LevelId) -> Result<bool, MetaError> {
        if u == v {
            return Ok(true);
        }
        self.guarded(
            |ctx| match *ctx.scratch.level_row(Some(ctx.view.store), v) {
                LevelRow::Succ(a) => ctx.level_occurs(u, a),
                LevelRow::Max(a, b) | LevelRow::IMax(a, b) => {
                    Ok(ctx.level_occurs(u, a)? || ctx.level_occurs(u, b)?)
                }
                _ => Ok(false),
            },
        )
    }

    /// oracle: `strictOccursMax` (LevelDefEq.lean:16-22) — true iff
    /// `lvl` is a PROPER subterm of some flattened `max` argument of
    /// `l` (i.e. occurs, but is not itself one of the immediate
    /// post-flattening `max` arms). `l` is expected to be a `Max` node
    /// (the only caller checks `v.isMax` first); a non-`Max` `l` is the
    /// oracle's own defensive `| _ => false`.
    fn strict_occurs_max(&mut self, lvl: LevelId, l: LevelId) -> Result<bool, MetaError> {
        match *self.scratch.level_row(Some(self.view.store), l) {
            LevelRow::Max(u, v) => Ok(
                self.strict_occurs_max_visit(lvl, u)? || self.strict_occurs_max_visit(lvl, v)?
            ),
            _ => Ok(false),
        }
    }

    /// oracle: `strictOccursMax.visit` (LevelDefEq.lean:20-22) — flatten
    /// through nested `Max` nodes, else `u != lvl && lvl.occurs u`.
    fn strict_occurs_max_visit(&mut self, lvl: LevelId, u: LevelId) -> Result<bool, MetaError> {
        self.guarded(|ctx| {
            if let LevelRow::Max(a, b) = *ctx.scratch.level_row(Some(ctx.view.store), u) {
                return Ok(
                    ctx.strict_occurs_max_visit(lvl, a)? || ctx.strict_occurs_max_visit(lvl, b)?
                );
            }
            Ok(u != lvl && ctx.level_occurs(lvl, u)?)
        })
    }

    /// oracle: `mkMaxArgsDiff` (LevelDefEq.lean:26-29) — fold `l`'s
    /// flattened `max` arguments into `acc`, dropping the one argument
    /// that is exactly `mvarId` itself. Evaluation order matches the
    /// oracle exactly: `u` folds in before `v` (`mkMaxArgsDiff v
    /// (mkMaxArgsDiff u acc)`).
    fn mk_max_args_diff(
        &mut self,
        mvar_id: LMVarId,
        l: LevelId,
        acc: LevelId,
    ) -> Result<LevelId, MetaError> {
        self.guarded(
            |ctx| match *ctx.scratch.level_row(Some(ctx.view.store), l) {
                LevelRow::Max(u, v) => {
                    let acc2 = ctx.mk_max_args_diff(mvar_id, u, acc)?;
                    ctx.mk_max_args_diff(mvar_id, v, acc2)
                }
                LevelRow::MVar(name) => {
                    if name.map(LMVarId) == Some(mvar_id) {
                        Ok(acc)
                    } else {
                        ctx.mk_level_max_prime(acc, l)
                    }
                }
                _ => ctx.mk_level_max_prime(acc, l),
            },
        )
    }

    /// oracle: `solveSelfMax` (LevelDefEq.lean:32-37) — solves `?m =?=
    /// max ?m v` by minting a fresh `?n` and assigning `?m := ` the
    /// flattened `max` arguments of `v` (minus `?m` itself) combined
    /// with `?n`. The oracle's `assert! v.isMax` is the caller's own
    /// `v.isMax` check (this function's only call site, in
    /// [`MetaCtx::solve`]'s mvar-left arm) — not re-asserted here.
    fn solve_self_max(&mut self, mvar_id: LMVarId, v: LevelId) -> Result<(), MetaError> {
        let (_fresh_id, fresh_level) = self.fresh_level_mvar()?;
        let v2 = self.mk_max_args_diff(mvar_id, v, fresh_level)?;
        self.mctx.assign_level(mvar_id, v2)?;
        Ok(())
    }

    // ===================================================================
    // univApprox: tryApproxSelfMax / tryApproxMaxMax
    // ===================================================================

    /// oracle: `tryApproxSelfMax` (LevelDefEq.lean:39-52) — `u =?= max u
    /// ?m` (or the `max ?m u` variant) solves as `?m := u`, ignoring the
    /// (also-valid) solution `?m := 0`. An approximation: named,
    /// gated on `cfg.univ_approx` by the sole caller ([`MetaCtx::solve`]).
    fn try_approx_self_max(&mut self, u: LevelId, v: LevelId) -> Result<bool, MetaError> {
        let LevelRow::Max(a, b) = *self.scratch.level_row(Some(self.view.store), v) else {
            return Ok(false);
        };
        let (vp, mvar_id) = match (
            *self.scratch.level_row(Some(self.view.store), a),
            *self.scratch.level_row(Some(self.view.store), b),
        ) {
            (_, LevelRow::MVar(Some(n))) => (a, LMVarId(n)),
            (LevelRow::MVar(Some(n)), _) => (b, LMVarId(n)),
            _ => return Ok(false),
        };
        if u == vp {
            self.mctx.assign_level(mvar_id, u)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// oracle: `tryApproxMaxMax` (LevelDefEq.lean:57-73) — `max u1 u2
    /// =?= max u1 ?m` (or a variant swapping which side of `u`/`v`
    /// matches which arm) solves as `?m := u2`, ignoring the (also-valid)
    /// solution `?m := max u1 u2`. An approximation, same gating as
    /// [`MetaCtx::try_approx_self_max`].
    fn try_approx_max_max(&mut self, u: LevelId, v: LevelId) -> Result<bool, MetaError> {
        let LevelRow::Max(u1, u2) = *self.scratch.level_row(Some(self.view.store), u) else {
            return Ok(false);
        };
        let LevelRow::Max(a, b) = *self.scratch.level_row(Some(self.view.store), v) else {
            return Ok(false);
        };
        let (vp, mvar_id) = match (
            *self.scratch.level_row(Some(self.view.store), a),
            *self.scratch.level_row(Some(self.view.store), b),
        ) {
            (_, LevelRow::MVar(Some(n))) => (a, LMVarId(n)),
            (LevelRow::MVar(Some(n)), _) => (b, LMVarId(n)),
            _ => return Ok(false),
        };
        if u1 == vp {
            self.mctx.assign_level(mvar_id, u2)?;
            Ok(true)
        } else if u2 == vp {
            self.mctx.assign_level(mvar_id, u1)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    // ===================================================================
    // decLevel? / decAux?
    // ===================================================================

    /// oracle: `decLevel?` (DecLevel.lean:57-62) — the public wrapper
    /// [`MetaCtx::solve`]'s succ-arm calls (`Meta.decLevel?`,
    /// LevelDefEq.lean:135). Snapshots mctx before attempting; on
    /// failure (`none`) rolls back any partial mvar assignment the
    /// attempt made. NONE of this crate's current call sites can
    /// actually trigger a partial assignment here (see
    /// [`MetaCtx::dec_level`]'s own doc comment: reaching a bare,
    /// assignable `.mvar` node in `decAux?` requires `canAssignMVars`
    /// to still be `true`, and it is only ever `true` on this call's own
    /// top-level argument — which [`MetaCtx::solve`]'s succ-arm never
    /// passes a bare `.mvar` as, since `(_, mvar ..)` is caught earlier
    /// in `solve` itself) — the checkpoint/rollback is kept anyway to
    /// stay faithful to the oracle's own defensive wrapper.
    fn dec_level_top(&mut self, u: LevelId) -> Result<Option<LevelId>, MetaError> {
        let snap = self.checkpoint();
        match self.dec_level(u, true)? {
            Some(v) => Ok(Some(v)),
            None => {
                self.rollback(snap);
                Ok(None)
            }
        }
    }

    /// oracle: `decAux?` (DecLevel.lean:20-53), specialized: the
    /// `DecLevelContext.canAssignMVars` reader field becomes a plain
    /// parameter (this crate threads no reader monad).
    fn dec_level(
        &mut self,
        l: LevelId,
        can_assign_mvars: bool,
    ) -> Result<Option<LevelId>, MetaError> {
        self.guarded(
            |ctx| match *ctx.scratch.level_row(Some(ctx.view.store), l) {
                LevelRow::Zero => Ok(None),
                LevelRow::Param(_) => Ok(None),
                LevelRow::MVar(name) => {
                    let Some(n) = name else {
                        // Anonymous mvar: unassignable/unfindable in this
                        // crate's `MetavarContext` (the same convention
                        // `solve`'s mvar-left arm documents) — behaves like
                        // the oracle's `isReadOnly` branch (`none`), for a
                        // different, tier-1-specific reason.
                        return Ok(None);
                    };
                    let mvar_id = LMVarId(n);
                    if let Some(assigned) = ctx.mctx.level_assignment(mvar_id) {
                        return ctx.dec_level(assigned, can_assign_mvars);
                    }
                    // SEAM: `mvarId.isReadOnly` (module doc) — always
                    // `false` at tier 1.
                    let is_read_only = false;
                    if is_read_only || !can_assign_mvars {
                        return Ok(None);
                    }
                    let (_fresh_id, fresh_level) = ctx.fresh_level_mvar()?;
                    let succ_n = ctx.scratch.level_succ(Some(ctx.view.store), fresh_level)?;
                    ctx.mctx.assign_level(mvar_id, succ_n)?;
                    Ok(Some(fresh_level))
                }
                LevelRow::Succ(a) => Ok(Some(a)),
                // `processMax`, always `canAssignMVars := false` for the
                // children regardless of the incoming flag (DecLevel.lean:
                // 41-49) — `Level.max`/`Level.imax` share the exact same
                // decrement rule (the doc comment at :43-46 explains why
                // `imax`'s rule reuses `max`'s: if `decAux? v` succeeds,
                // `imax u v` and `max u v` are equivalent).
                LevelRow::Max(a, b) | LevelRow::IMax(a, b) => match ctx.dec_level(a, false)? {
                    None => Ok(None),
                    Some(a2) => match ctx.dec_level(b, false)? {
                        None => Ok(None),
                        Some(b2) => Ok(Some(ctx.mk_level_max_prime(a2, b2)?)),
                    },
                },
            },
        )
    }

    // ===================================================================
    // Small id-native Level primitives with no existing port
    // ===================================================================

    /// oracle: `mkLevelMax'`/`mkLevelMaxCore` (Level.lean:518-538) — a
    /// CHEAP, non-canonicalizing simplification, distinct from the
    /// kernel's full `mk_max`/[`Level::mk_max_pair`] (level.cpp:81-98,
    /// leanr_kernel's `level.rs`): no sorting, no flattening beyond one
    /// level, just five quick special cases before falling back to a
    /// raw (unsimplified) `Max` node. Used only by `decAux?`'s
    /// `processMax` and `mkMaxArgsDiff` (both LevelDefEq.lean/
    /// DecLevel.lean call sites use `mkLevelMax'`, never the kernel's
    /// `mkLevelMax`/`mk_max_pair`), so reusing `leanr_kernel`'s
    /// `mk_max_pair` here would be transcribing the WRONG function.
    fn mk_level_max_prime(&mut self, u: LevelId, v: LevelId) -> Result<LevelId, MetaError> {
        if u == v {
            return Ok(u);
        }
        if self.level_is_zero(u) {
            return Ok(v);
        }
        if self.level_is_zero(v) {
            return Ok(u);
        }
        if self.level_subsumes(u, v) {
            return Ok(u);
        }
        if self.level_subsumes(v, u) {
            return Ok(v);
        }
        let (ub, uk) = self.level_to_offset(u);
        let (vb, vk) = self.level_to_offset(v);
        if ub == vb {
            return Ok(if uk >= vk { u } else { v });
        }
        Ok(self.scratch.level_max(Some(self.view.store), u, v)?)
    }

    /// oracle: the `subsumes` local of `mkLevelMaxCore` (Level.lean:
    /// 520-525): `v` explicit and `u`'s offset already covers it, or `u`
    /// is a `max` that already lists `v` as one of its two immediate
    /// arguments.
    fn level_subsumes(&self, u: LevelId, v: LevelId) -> bool {
        if self.level_is_explicit(v) && self.level_to_offset(u).1 >= self.level_to_offset(v).1 {
            return true;
        }
        match *self.scratch.level_row(Some(self.view.store), u) {
            LevelRow::Max(u1, u2) => v == u1 || v == u2,
            _ => false,
        }
    }

    /// oracle: `Level.isExplicit` (Level.lean:231-233): a pure numeral
    /// `succ^k(zero)`. Via [`MetaCtx::level_to_offset`], same rationale
    /// as `leanr_kernel`'s own `is_explicit` (level.rs) — equivalent by
    /// construction, no extra recursion needed.
    fn level_is_explicit(&self, l: LevelId) -> bool {
        let (base, _) = self.level_to_offset(l);
        matches!(
            *self.scratch.level_row(Some(self.view.store), base),
            LevelRow::Zero
        )
    }

    fn level_is_zero(&self, l: LevelId) -> bool {
        matches!(
            *self.scratch.level_row(Some(self.view.store), l),
            LevelRow::Zero
        )
    }

    /// oracle: `Level.getLevelOffset`/`Level.getOffset` (Level.lean:
    /// 246-248, 239-243) combined, id-native: peel `Succ` nodes into
    /// `(base, k)`. A `while` loop, not recursion (mirrors
    /// `leanr_kernel::Level::to_offset`'s own non-recursive posture —
    /// this is the id-native twin the module doc promises), so it needs
    /// no `guarded` wrapper even on an adversarially deep `Succ` chain.
    fn level_to_offset(&self, l: LevelId) -> (LevelId, u64) {
        let mut cur = l;
        let mut k: u64 = 0;
        while let LevelRow::Succ(a) = *self.scratch.level_row(Some(self.view.store), cur) {
            cur = a;
            k = k.saturating_add(1);
        }
        (cur, k)
    }

    /// oracle: `Level.normalize` (level.cpp:439-501, ported as
    /// [`Level::normalize`] in `leanr_kernel`). No id-native twin exists
    /// (the sort/dedup pass genuinely needs the `Arc<Level>` shape), so
    /// this is the one sanctioned `Store::to_level`/`intern_level`
    /// materialize-then-rebuild leaf the module doc promises.
    fn level_normalize(&mut self, l: LevelId) -> Result<LevelId, MetaError> {
        let arc = self.scratch.to_level(Some(self.view.store), l);
        let normalized = Level::normalize(&arc, &mut self.guard)?;
        Ok(self
            .scratch
            .intern_level(Some(self.view.store), &normalized)?)
    }

    /// oracle: `instantiateLevelMVars`/`instantiateLevelMVarsImp`
    /// (MetavarContext.lean:569-573) — an `@[extern]` opaque (compiled),
    /// so no Lean source to transcribe line-by-line; this is a
    /// semantically equivalent id-native recursive substitution
    /// (assigned `.mvar` nodes replaced by their, recursively
    /// instantiated, assignment; everything else rebuilt only if a
    /// child actually changed, preserving the dedup-sharing the Arc side
    /// gets from `Arc::ptr_eq`). Pure substitution — no renormalization
    /// — matching that `isLevelDefEqAuxImpl` always follows this call
    /// with a SEPARATE `.normalize` (:154-157), so whether this helper
    /// simplifies eagerly cannot change the net result either way.
    fn instantiate_level_mvars(&mut self, l: LevelId) -> Result<LevelId, MetaError> {
        match *self.scratch.level_row(Some(self.view.store), l) {
            LevelRow::Zero | LevelRow::Param(_) => Ok(l),
            LevelRow::MVar(name) => {
                match name.and_then(|n| self.mctx.level_assignment(LMVarId(n))) {
                    Some(v) => self.guarded(|ctx| ctx.instantiate_level_mvars(v)),
                    None => Ok(l),
                }
            }
            LevelRow::Succ(a) => {
                let a2 = self.guarded(|ctx| ctx.instantiate_level_mvars(a))?;
                if a2 == a {
                    Ok(l)
                } else {
                    Ok(self.scratch.level_succ(Some(self.view.store), a2)?)
                }
            }
            LevelRow::Max(a, b) => {
                let (a2, b2) = self.guarded(|ctx| {
                    Ok((
                        ctx.instantiate_level_mvars(a)?,
                        ctx.instantiate_level_mvars(b)?,
                    ))
                })?;
                if a2 == a && b2 == b {
                    Ok(l)
                } else {
                    Ok(self.scratch.level_max(Some(self.view.store), a2, b2)?)
                }
            }
            LevelRow::IMax(a, b) => {
                let (a2, b2) = self.guarded(|ctx| {
                    Ok((
                        ctx.instantiate_level_mvars(a)?,
                        ctx.instantiate_level_mvars(b)?,
                    ))
                })?;
                if a2 == a && b2 == b {
                    Ok(l)
                } else {
                    Ok(self.scratch.level_imax(Some(self.view.store), a2, b2)?)
                }
            }
        }
    }

    /// oracle: `hasAssignableLevelMVar` (HasAssignableMVar.lean:17-21).
    /// Skips the oracle's `lvl.hasMVar` cached-bit early-exit shortcuts
    /// (this crate decodes without retaining that cache, same posture
    /// as every other "no single oracle line" traversal in
    /// `leanr_kernel::Level`) — a pure performance difference, not a
    /// semantic one. `isLevelMVarAssignable` (MetavarContext.lean:
    /// 471-474, depth-gated) collapses to simply "is a named mvar" at
    /// tier 1: this is always called on an ALREADY
    /// `instantiate_level_mvars`-d level (its only call site,
    /// `is_level_def_eq_aux`'s stuck/postpone tail, runs it on `lhs`/
    /// `rhs` right after that instantiate+normalize pass), so any
    /// surviving `.mvar` node is, by construction, unassigned — combined
    /// with the tier-1 depth collapse (module doc), "assignable" reduces
    /// to `name.is_some()` (the anonymous-mvar convention this module
    /// uses throughout).
    fn has_assignable_level_mvar(&mut self, l: LevelId) -> Result<bool, MetaError> {
        self.guarded(
            |ctx| match *ctx.scratch.level_row(Some(ctx.view.store), l) {
                LevelRow::Zero | LevelRow::Param(_) => Ok(false),
                LevelRow::MVar(name) => Ok(name.is_some()),
                LevelRow::Succ(a) => ctx.has_assignable_level_mvar(a),
                LevelRow::Max(a, b) | LevelRow::IMax(a, b) => {
                    Ok(ctx.has_assignable_level_mvar(a)? || ctx.has_assignable_level_mvar(b)?)
                }
            },
        )
    }

    /// oracle: `mkFreshLevelMVar` (Basic.lean:861-863) — mints a
    /// globally-fresh `LMVarId` and declares it (`addLevelMVarDecl`).
    /// This crate has no name-generator type of its own, so this
    /// mirrors `local_ctx.rs::fresh_fvar_id`'s "distinct fixed prefix +
    /// monotone counter" idiom instead: `_leanr_lvl_fresh.<n>`.
    pub(crate) fn fresh_level_mvar(&mut self) -> Result<(LMVarId, LevelId), MetaError> {
        let idx = self.level_mvar_gen;
        self.level_mvar_gen += 1;
        let base = Some(self.view.store);
        let prefix_str = self.scratch.intern_str(base, "_leanr_lvl_fresh")?;
        let prefix = self.scratch.name_str(base, None, prefix_str)?;
        let idx_id = self.scratch.intern_nat(base, &Nat::from(idx))?;
        let name = self.scratch.name_num(base, Some(prefix), idx_id)?;
        let id = LMVarId(name);
        self.mctx.declare_level(id);
        let level_id = self.scratch.level_mvar(base, Some(name))?;
        Ok((id, level_id))
    }

    // ===================================================================
    // processPostponed / processPostponedStep
    // ===================================================================

    /// oracle: `processPostponedStep` (Basic.lean:2388-2396) — one pass
    /// over the CURRENT postponed queue, re-attempting `isLevelDefEqAux`
    /// on each. `exceptionOnFailure` is hardcoded `false`: this crate's
    /// only caller (`process_postponed`, in turn only called from
    /// `is_def_eq`, defeq.rs) matches `checkpointDefEq`'s own call
    /// `processPostponed mayPostpone` (Basic.lean:2453), which passes no
    /// `exceptionOnFailure` argument — so the oracle's own default
    /// (`false`) is what the ONLY real call path ever uses. The
    /// "throw a pretty diagnostic" branch (:2392-2394) is therefore
    /// unreachable here and not transcribed.
    fn process_postponed_step(&mut self) -> Result<bool, MetaError> {
        let ps = std::mem::take(&mut self.postponed);
        for (lhs, rhs) in ps {
            if !self.is_level_def_eq_aux(lhs, rhs)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// oracle: `processPostponed` (Basic.lean:2398-2422), `mayPostpone :=
    /// true` hardcoded (this crate's only caller passes no other value,
    /// matching `isLevelDefEq`/`checkpointDefEq`'s own default,
    /// Basic.lean:2453, 2470). The `!mayPostpone && ..` univ-approx-retry
    /// branch (:2419-2420) is therefore dead code with `mayPostpone`
    /// fixed `true` and is not transcribed; the "no progress" branch
    /// (:2421) becomes the unconditional `return Ok(true)` below.
    pub(crate) fn process_postponed(&mut self) -> Result<bool, MetaError> {
        if self.postponed.is_empty() {
            return Ok(true);
        }
        loop {
            let num_before = self.postponed.len();
            if !self.process_postponed_step()? {
                return Ok(false);
            }
            let num_after = self.postponed.len();
            if num_after == 0 {
                return Ok(true);
            } else if num_after < num_before {
                continue;
            } else {
                return Ok(true);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::with_ctx;

    #[test]
    fn ground_levels() {
        with_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).unwrap();
            let s1 = ctx.scratch.level_succ(None, z).unwrap();
            assert!(ctx.is_level_def_eq(z, z).unwrap());
            assert!(!ctx.is_level_def_eq(z, s1).unwrap());
            // max 0 u == u  (normalize)
            let s = ctx.scratch.intern_str(None, "u").unwrap();
            let un = ctx.scratch.name_str(None, None, s).unwrap();
            let u = ctx.scratch.level_param(None, Some(un)).unwrap();
            let m = ctx.scratch.level_max(None, z, u).unwrap();
            assert!(ctx.is_level_def_eq(m, u).unwrap());
        });
    }

    #[test]
    fn assigns_a_level_mvar() {
        with_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).unwrap();
            let s = ctx.scratch.intern_str(None, "?u").unwrap();
            let un = ctx.scratch.name_str(None, None, s).unwrap();
            let mv = ctx.scratch.level_mvar(None, Some(un)).unwrap();
            let id = crate::LMVarId(un);
            ctx.mctx.declare_level(id);
            assert!(ctx.is_level_def_eq(mv, z).unwrap()); // ?u =?= 0  -> assign
            assert_eq!(ctx.mctx.level_assignment(id), Some(z));
        });
    }

    // Distinct params, no mvars: genuinely unequal, not just
    // "not decidable yet" — pins that the stuck/postpone tail's
    // `hasAssignableLevelMVar` check correctly falls to `false` rather
    // than postponing forever.
    #[test]
    fn distinct_params_are_not_level_def_eq() {
        with_ctx(|ctx| {
            let su = ctx.scratch.intern_str(None, "u").unwrap();
            let un = ctx.scratch.name_str(None, None, su).unwrap();
            let u = ctx.scratch.level_param(None, Some(un)).unwrap();
            let sv = ctx.scratch.intern_str(None, "v").unwrap();
            let vn = ctx.scratch.name_str(None, None, sv).unwrap();
            let v = ctx.scratch.level_param(None, Some(vn)).unwrap();
            assert!(!ctx.is_level_def_eq(u, v).unwrap());
        });
    }

    // succ distributes over max under normalize: `succ (max u v) =?=
    // max (succ u) (succ v)` — exercises normalize's `Max` branch
    // producing a DIFFERENT tree shape than either side started with,
    // not just the trivial `max 0 u` subsumption `ground_levels` already
    // covers.
    #[test]
    fn succ_distributes_over_max() {
        with_ctx(|ctx| {
            let su = ctx.scratch.intern_str(None, "u").unwrap();
            let un = ctx.scratch.name_str(None, None, su).unwrap();
            let u = ctx.scratch.level_param(None, Some(un)).unwrap();
            let sv = ctx.scratch.intern_str(None, "v").unwrap();
            let vn = ctx.scratch.name_str(None, None, sv).unwrap();
            let v = ctx.scratch.level_param(None, Some(vn)).unwrap();

            let max_uv = ctx.scratch.level_max(None, u, v).unwrap();
            let lhs = ctx.scratch.level_succ(None, max_uv).unwrap();

            let su2 = ctx.scratch.level_succ(None, u).unwrap();
            let sv2 = ctx.scratch.level_succ(None, v).unwrap();
            let rhs = ctx.scratch.level_max(None, su2, sv2).unwrap();

            assert!(ctx.is_level_def_eq(lhs, rhs).unwrap());
        });
    }

    // `?m =?= max ?m v` (self-max): exercises `solveSelfMax`/
    // `mkMaxArgsDiff`'s fresh-mvar mint, not just the plain
    // `assign_level` path `assigns_a_level_mvar` covers.
    #[test]
    fn self_max_assigns_via_fresh_mvar() {
        with_ctx(|ctx| {
            let sm = ctx.scratch.intern_str(None, "?m").unwrap();
            let mn = ctx.scratch.name_str(None, None, sm).unwrap();
            let mv = ctx.scratch.level_mvar(None, Some(mn)).unwrap();
            let id = crate::LMVarId(mn);
            ctx.mctx.declare_level(id);

            let sv = ctx.scratch.intern_str(None, "v").unwrap();
            let vn = ctx.scratch.name_str(None, None, sv).unwrap();
            let v = ctx.scratch.level_param(None, Some(vn)).unwrap();

            let rhs = ctx.scratch.level_max(None, mv, v).unwrap();
            assert!(ctx.is_level_def_eq(mv, rhs).unwrap());
            assert!(ctx.mctx.is_level_assigned(id));
        });
    }

    // `process_postponed` actually drains: a postponed constraint that
    // becomes decidable once revisited (here: trivially true already,
    // pinning the drain loop itself rather than any specific solve rule)
    // must not block `is_def_eq`'s overall verdict.
    #[test]
    fn process_postponed_drains_a_trivial_constraint() {
        with_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).unwrap();
            ctx.postponed.push((z, z));
            assert!(ctx.process_postponed().unwrap());
            assert!(ctx.postponed.is_empty());
        });
    }
}
