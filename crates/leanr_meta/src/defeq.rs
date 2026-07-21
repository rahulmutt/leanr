//! `is_def_eq` — the elaborator's definitional equality (spec plan 3).
//!
//! oracle: `Lean/Meta/ExprDefEq.lean` + `Lean/Meta/Basic.lean`,
//! toolchain leanprover/lean4:v4.33.0-rc1. NOT the kernel's `is_def_eq`
//! (`leanr_kernel::tc`): this one is over open terms, mvar-assigning
//! (task 5+), transparency-gated, and DELIBERATELY INCOMPLETE where the
//! oracle itself is (the `*_approx` flags, `isDefEqStuck`). Lean's
//! source is the specification; every arm below cites the exact region
//! read from the pinned toolchain (never transcribed from memory).
//!
//! # This task's slice of the ladder
//!
//! The full ladder (`isExprDefEqAuxImpl`, ExprDefEq.lean:2285) is:
//! `checkpointDefEq` wrapper -> `isDefEqQuick` (structural + mvar fast
//! paths) -> `isDefEqProofIrrel` -> `whnfCoreAtDefEq` both sides
//! (`proj := yesWithDeltaI`), recurse if either changed ->
//! `instantiateMVars` -> defeq cache -> `isExprDefEqExpensive` (eta,
//! proj, whnfCore-again, native/nat/offset/delta, eta-struct,
//! const-levels/app-args congruence, projInst/stringLit/unitLike,
//! onFailure).
//!
//! This task builds ONLY: the `checkpointDefEq` wrapper (task 2's
//! `checkpoint`/`rollback`/`postponed`), `isDefEqQuick`'s structural
//! leaf cases, the `whnfCoreAtDefEq` loop, and `isExprDefEqExpensive`'s
//! **congruence** arms (Const-with-equal-levels, App head+args,
//! Lam/Forall binder congruence, Sort). No delta, no mvar assignment,
//! no approximations, no proof irrelevance — those are tasks 4-7, and
//! every one of them is a named seam below, never a silent `false`.
//!
//! # A transcription correction (brief vs. pinned source)
//!
//! The task brief filed Lam/Forall binder congruence under
//! `isExprDefEqExpensive`. Reading the pinned source shows this is
//! wrong: the real `isExprDefEqExpensive` (ExprDefEq.lean:2205-2232)
//! has NO Lam/Forall arm at all — binder congruence is decided
//! entirely inside `isDefEqQuick` itself (`.lam .., .lam ..` /
//! `.forallE .., .forallE ..`, ExprDefEq.lean:1827-1828, via
//! `isDefEqBinding`/`isDefEqBindingAux`, :459-477). This module places
//! it in [`MetaCtx::is_def_eq_quick`] to match; see
//! [`MetaCtx::is_def_eq_binding_shallow`]'s doc comment for a second
//! correction (binder-info equality is NOT part of the real check —
//! `isDefEqBindingAux` never compares it) and for how this task's
//! simplified single-binder fvar substitution relates to the oracle's
//! full telescope.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::{instantiate, BinderInfo};

use crate::{MetaCtx, MetaError, ProjReduction};

impl<'e> MetaCtx<'e> {
    /// oracle: `isDefEq`/`isExprDefEq` (Basic.lean:2474-2509) +
    /// `checkpointDefEq` (:2438-2461). Clears the transient cache,
    /// resets postponed, runs the core, and on success processes +
    /// merges postponed; on failure or throw, rolls back.
    ///
    /// Two oracle steps are deliberately NOT ported here:
    /// `resetDefEqPermCaches` (:2477) — moot, this task's
    /// `is_def_eq_expensive` never reads or writes `defeq_cache_perm`,
    /// which lands task 8 — and the `defEqCtx?` reader bump
    /// (:2475-2476), elaborator-context this crate does not model.
    pub fn is_def_eq(&mut self, t: ExprId, s: ExprId) -> Result<bool, MetaError> {
        let snap = self.checkpoint();
        self.defeq_cache_transient.clear();
        let saved_postponed = std::mem::take(&mut self.postponed);
        match self.is_def_eq_core(t, s) {
            Ok(true) => {
                if self.process_postponed()? {
                    // merge saved + newly-postponed (task 4 provides a
                    // real `process_postponed`; until then it is a
                    // no-op stub returning `true`, so there is nothing
                    // new to merge yet).
                    let mut merged = saved_postponed;
                    merged.append(&mut self.postponed);
                    self.postponed = merged;
                    Ok(true)
                } else {
                    self.rollback(snap);
                    Ok(false)
                }
            }
            Ok(false) => {
                self.rollback(snap);
                Ok(false)
            }
            Err(e) => {
                self.rollback(snap);
                Err(e)
            }
        }
    }

    /// oracle: `isExprDefEqAuxImpl` (ExprDefEq.lean:2285-2354). The
    /// `instantiateMVars` + defeq-cache stage (:2333-2354) is a named
    /// seam (task 8): until then this recomputes on every call, never
    /// caches — correct, only slower.
    fn is_def_eq_core(&mut self, t: ExprId, s: ExprId) -> Result<bool, MetaError> {
        self.step()?;
        self.guarded(|ctx| {
            if let Some(b) = ctx.is_def_eq_quick(t, s)? {
                return Ok(b);
            }
            // SEAM: isDefEqProofIrrel (ExprDefEq.lean:1766-1780) — task 6.
            let t2 = ctx.whnf_core_at_defeq(t)?;
            let s2 = ctx.whnf_core_at_defeq(s)?;
            if t2 != t || s2 != s {
                return ctx.is_def_eq_core(t2, s2);
            }
            // SEAM: instantiateMVars + defeq cache (task 8) — recompute,
            // never cache, until then.
            ctx.is_def_eq_expensive(t2, s2)
        })
    }

    /// oracle: `whnfCoreAtDefEq` (ExprDefEq.lean:2277-2281): `whnfCore`
    /// with `proj := yesWithDeltaI` for this reduction only (the
    /// `backward.isDefEq.lazyWhnfCore` option gate is not modeled —
    /// this crate has no options table; its `else` branch, plain
    /// `whnfCore`, is the one behavior it would always take if the
    /// option WERE read, so the omission changes nothing observable).
    fn whnf_core_at_defeq(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let saved = self.cfg.proj;
        self.cfg.proj = ProjReduction::YesWithDeltaI;
        let r = self.whnf_core(e);
        self.cfg.proj = saved;
        r
    }

    /// oracle: `processPostponed` (Basic.lean:2401-2418) — drains
    /// postponed level-equality constraints. SEAM (task 4): until
    /// `is_level_def_eq` exists, nothing is ever postponed (this
    /// task's `is_def_eq_quick` decides levels only when structurally
    /// equal, or escalates without postponing), so a no-op `Ok(true)`
    /// is exact here, not an approximation.
    fn process_postponed(&mut self) -> Result<bool, MetaError> {
        Ok(true)
    }

    /// oracle: `isDefEqQuick` / `isDefEqQuickOther` (ExprDefEq.lean:
    /// 1819-1927). This task's subset: pointer equality, same-shape
    /// leaf decisions (`Lit`, `BVar`/`BVarBig`, `Sort` via structural
    /// level compare, `Const` via name + structural level compare),
    /// and Lam/Forall binder congruence. Returns `Ok(None)` to
    /// escalate to `is_def_eq_core`'s `whnf_core` loop, exactly like
    /// the oracle's `LBool.undef`.
    ///
    /// Two placements here are a task-3 SHORTCUT, not literal oracle
    /// structure (see the module doc's transcription-correction note
    /// for why they still are not WRONG):
    /// - `BVar`/`BVarBig`, `Const`: the real `isDefEqQuick` does not
    ///   special-case either — a same-index bvar pair or a same-name/
    ///   same-levels const pair is ALREADY caught by the leading
    ///   `t == s` check (`ExprId`s are hash-consed: identical index /
    ///   identical name+levels interns to the identical `ExprId`), and
    ///   a MISMATCHED pair otherwise falls through
    ///   `isDefEqQuickOther`'s generic mvar-head dispatch to `.undef`
    ///   (:1873, `if !tFn.isMVar && !sFn.isMVar then return
    ///   LBool.undef`) — decided later by `isExprDefEqExpensive`'s
    ///   Const-congruence arm (:2225-2226) for Const, or (for a bvar
    ///   pair, which can never reduce further) by simply never
    ///   matching either congruence arm there and falling to `false`.
    ///   Deciding both directly here just skips a no-op `whnf_core`
    ///   round trip; the verdict is identical either way.
    /// - Lam/Forall: real oracle location, see module doc.
    fn is_def_eq_quick(&mut self, t: ExprId, s: ExprId) -> Result<Option<bool>, MetaError> {
        if t == s {
            return Ok(Some(true));
        }
        match (self.node(t), self.node(s)) {
            (Node::LitNat { v: v1 }, Node::LitNat { v: v2 }) => Ok(Some(v1 == v2)),
            (Node::LitStr { v: v1 }, Node::LitStr { v: v2 }) => Ok(Some(v1 == v2)),
            (Node::BVar { idx: i1 }, Node::BVar { idx: i2 }) => Ok(Some(i1 == i2)),
            (Node::BVarBig { idx: i1 }, Node::BVarBig { idx: i2 }) => Ok(Some(i1 == i2)),
            (Node::Sort { level: l1 }, Node::Sort { level: l2 }) => {
                // SEAM: the real `.sort u, .sort v` arm calls
                // `isLevelDefEqAux` (LevelDefEq.lean), a decisive
                // procedure (always true or false) — task 4's
                // `is_level_def_eq`. Until then: `LevelId` equality
                // *is* full structural equality (levels are
                // hash-consed), so a structural mismatch does NOT mean
                // "not defeq" (e.g. `max u u` vs `u`) — only "not
                // decidable here yet". Punt (`None`) rather than
                // assert a wrong `false`.
                if l1 == l2 {
                    Ok(Some(true))
                } else {
                    Ok(None)
                }
            }
            (
                Node::Const {
                    name: n1,
                    levels: ls1,
                },
                Node::Const {
                    name: n2,
                    levels: ls2,
                },
            ) => {
                if n1 != n2 {
                    // Name mismatch escalates to is_def_eq_expensive,
                    // where isDefEqDelta (ExprDefEq.lean:2217) runs BEFORE
                    // the const-congruence arm (:2225-2226), allowing
                    // delta-equal distinct-named consts (e.g. `def a := b`)
                    // to still unify. Task 7 (delta) will implement this;
                    // until then, is_def_eq_expensive returns false for
                    // distinct names, as correct.
                    Ok(None)
                } else if ls1 == ls2 {
                    // SEAM: is_level_def_eq (task 4) — `LevelsId`
                    // equality is structural, not semantic; see the
                    // `Sort` arm above for why a mismatch punts rather
                    // than asserts `false`.
                    Ok(Some(true))
                } else {
                    Ok(None)
                }
            }
            (
                Node::Lam {
                    binder_type: d1,
                    body: b1,
                    ..
                },
                Node::Lam {
                    binder_type: d2,
                    body: b2,
                    ..
                },
            )
            | (
                Node::Forall {
                    binder_type: d1,
                    body: b1,
                    ..
                },
                Node::Forall {
                    binder_type: d2,
                    body: b2,
                    ..
                },
            ) => Ok(Some(self.is_def_eq_binding_shallow(d1, b1, d2, b2)?)),
            // SEAM: mvar arms (`isDefEqQuickMVarMVar` / `processAssignment`,
            // :1855-1927, :1963-1977) — assignment lands task 5.
            (Node::MVar { .. }, _) | (_, Node::MVar { .. }) => Ok(None),
            _ => Ok(None),
        }
    }

    /// oracle: `isDefEqBinding`/`isDefEqBindingAux` (ExprDefEq.lean:
    /// 459-477). Domain compared before body, matching the oracle's
    /// order.
    ///
    /// TWO corrections/simplifications vs. the literal source, both
    /// deliberate for this task's scope:
    /// - Binder-info equality is NOT checked: the real
    ///   `isDefEqBindingAux` never compares it (`.lam n d1 b1 _, .lam _
    ///   d2 b2 _` — the trailing `_` discards BOTH sides' info). It
    ///   affects elaboration/pretty-printing only, never definitional
    ///   equality. (The brief's "binder-info equal" wording was wrong;
    ///   fixed here.)
    /// - The real algorithm opens a full fvar TELESCOPE across a chain
    ///   of same-kind binders, instantiating each later domain against
    ///   every earlier fvar before it ever recurses on the bodies
    ///   (`isDefEqBindingAux`'s own loop, :459-472). This task opens
    ///   exactly ONE fresh fvar per call (for THIS binder alone) and
    ///   recurses via `is_def_eq_core` on the substituted bodies — a
    ///   nested Lam/Forall inside those bodies gets its OWN fresh fvar
    ///   from a NEW call to this same function, one recursion level
    ///   at a time, rather than one accumulated telescope. This is
    ///   semantically equivalent for the shapes this task's fixtures
    ///   exercise (no domain in a later binder depends on an
    ///   assignment made while checking an earlier one — there is no
    ///   assignment yet at all, task 5's job) and, critically, it is
    ///   SAFE: substituting a real fvar for the bound variable BEFORE
    ///   recursing means `is_def_eq_core`/`whnf_core` never meet a raw
    ///   loose bvar (which `whnf_easy_cases`, whnf.rs, legitimately
    ///   treats as ill-formed input and errors on) — e.g. a body like
    ///   `f x` (the bound `x` as an application ARGUMENT is fine, but
    ///   `x arg`, the bound variable as an application HEAD, is a
    ///   completely ordinary shape that a naive raw-bvar recursion
    ///   would crash on, since `whnf_core`'s app case peels the spine
    ///   down to its head and calls `whnf_core` on THAT directly).
    fn is_def_eq_binding_shallow(
        &mut self,
        d1: ExprId,
        b1: ExprId,
        d2: ExprId,
        b2: ExprId,
    ) -> Result<bool, MetaError> {
        if !self.is_def_eq_core(d1, d2)? {
            return Ok(false);
        }
        let checkpoint = self.lctx.save();
        let r = self.is_def_eq_binding_shallow_body(d1, b1, b2);
        self.lctx.restore(checkpoint);
        r
    }

    fn is_def_eq_binding_shallow_body(
        &mut self,
        d1: ExprId,
        b1: ExprId,
        b2: ExprId,
    ) -> Result<bool, MetaError> {
        // `binder_name`/`binder_info` are inert placeholders on this
        // fvar's own decl: neither is ever consulted by `is_def_eq`
        // (see this function's doc comment on binder-info), so a
        // fixed `None`/`Default` is exactly as faithful as threading
        // either side's real value through.
        let fvar = self.lctx.mk_local_decl(
            self.scratch,
            Some(self.view.store),
            &mut self.fvar_gen,
            None,
            d1,
            BinderInfo::Default,
        )?;
        let ib1 = instantiate(
            self.scratch,
            Some(self.view.store),
            b1,
            fvar,
            &mut self.guard,
        )?;
        let ib2 = instantiate(
            self.scratch,
            Some(self.view.store),
            b2,
            fvar,
            &mut self.guard,
        )?;
        self.is_def_eq_core(ib1, ib2)
    }

    /// oracle: `isExprDefEqExpensive` (ExprDefEq.lean:2205-2232). This
    /// task's subset is congruence ONLY — `Const`/`Const` (:2225-2226)
    /// and `App`/`App` via `isDefEqApp`'s spine walk (:2166-2178,
    /// simplified below). Every other rule the oracle defines here is
    /// a named, uncommitted seam, landing tasks 4-7:
    /// - `isDefEqEta` x2 (:183-195, called at :2206-2207) — task 6.
    /// - `isDefEqProj` (:2099-2165, called at :2208) — task 6/7 (proj
    ///   reduction machinery: `whnf_core_at_defeq` above already runs
    ///   `proj := yesWithDeltaI`, but the dedicated projection-vs-
    ///   projection unifier itself is not built).
    /// - the internal plain-`whnfCore` round with recurse-if-changed
    ///   (:2209-2212) — this task's `is_def_eq_core` already ran
    ///   `whnf_core_at_defeq` (a DIFFERENT `proj` setting) immediately
    ///   before calling this function; re-running plain `whnfCore` here
    ///   too is a scope cut, since delta (the main thing a second pass
    ///   could still change) is not built either.
    /// - `isDefEqNative`/`isDefEqNat`/`isDefEqOffset` (:2214-2216) —
    ///   task 7 (`isDefEqNative` is permanently out of scope: no
    ///   native-code evaluator in a pure-Rust toolchain, same posture
    ///   as `whnf.rs`'s own `reduceNative?` stub).
    /// - `isDefEqDelta` (:2217) — task 7: lazy delta reduction, the
    ///   single biggest remaining ladder rung.
    /// - `isDefEqEtaStruct` x2 (:2219-2221) — task 6 (structure eta).
    /// - a non-structurally-equal `Sort`/`Sort` pair reaching here (its
    ///   levels differ under `LevelId` equality but might still be
    ///   `is_level_def_eq`, task 4) — falls to this function's own
    ///   `false` below; an incompleteness, not the oracle's own
    ///   ladder shape (the real `isDefEqQuick` always fully resolves
    ///   `Sort`, so the real `isExprDefEqExpensive` never sees one).
    /// - `isDefEqProjInst`/`isDefEqStringLit`/`isDefEqUnitLike`
    ///   (:2229-2231) — task 6/7.
    /// - `isDefEqOnFailure` (:2232, unification hints :2022-2028) —
    ///   task 7.
    ///
    /// All of the above fall through to this function's single
    /// documented `false` — incompleteness, never unsoundness (spec §
    /// Error handling): every fixture this task commits is chosen so
    /// none of these seams are actually needed to reach the oracle's
    /// own verdict.
    fn is_def_eq_expensive(&mut self, t: ExprId, s: ExprId) -> Result<bool, MetaError> {
        match (self.node(t), self.node(s)) {
            (
                Node::Const {
                    name: n1,
                    levels: ls1,
                },
                Node::Const {
                    name: n2,
                    levels: ls2,
                },
            ) => {
                if n1 != n2 {
                    Ok(false)
                } else {
                    // SEAM: is_level_def_eq (task 4); structural only.
                    Ok(ls1 == ls2)
                }
            }
            (Node::App { .. }, Node::App { .. }) => {
                let t_fn = self.get_app_fn(t);
                let s_fn = self.get_app_fn(s);
                if !self.is_def_eq_core(t_fn, s_fn)? {
                    return Ok(false);
                }
                let t_args = self.get_app_args(t);
                let s_args = self.get_app_args(s);
                if t_args.len() != s_args.len() {
                    return Ok(false);
                }
                // Plain pairwise comparison (oracle's assignment-aware
                // `isDefEqArgsFirstPass`, ExprDefEq.lean:298-370, is
                // task 5 — no higher-order/postponed-implicit handling
                // here yet).
                for (&a, &b) in t_args.iter().zip(s_args.iter()) {
                    if !self.is_def_eq_core(a, b)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::with_ctx;

    #[test]
    fn reflexive_and_structural() {
        with_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap(); // Sort 0
            let s1u = ctx.scratch.level_succ(None, z).unwrap();
            let s1 = ctx.scratch.expr_sort(None, s1u).unwrap(); // Sort 1
            assert!(ctx.is_def_eq(s0, s0).unwrap()); // pointer-eq
            assert!(!ctx.is_def_eq(s0, s1).unwrap()); // Sort 0 != Sort 1
        });
    }

    #[test]
    fn beta_via_whnf_core() {
        with_ctx(|ctx| {
            // (fun (x : Sort 0) => x) Sort0  =?=  Sort0
            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap();
            let bv = ctx
                .scratch
                .expr_bvar(None, &leanr_kernel::Nat::from(0u64))
                .unwrap();
            let lam = ctx
                .scratch
                .expr_lam(None, None, s0, bv, leanr_kernel::BinderInfo::Default)
                .unwrap();
            let app = ctx.scratch.expr_app(None, lam, s0).unwrap();
            assert!(ctx.is_def_eq(app, s0).unwrap());
        });
    }

    #[test]
    fn distinct_consts_are_not_def_eq() {
        with_ctx(|ctx| {
            let a_s = ctx.scratch.intern_str(None, "A").unwrap();
            let a_n = ctx.scratch.name_str(None, None, a_s).unwrap();
            let b_s = ctx.scratch.intern_str(None, "B").unwrap();
            let b_n = ctx.scratch.name_str(None, None, b_s).unwrap();
            let empty_levels = ctx.scratch.intern_level_list(None, &[]).unwrap();
            let a = ctx
                .scratch
                .expr_const(None, Some(a_n), empty_levels)
                .unwrap();
            let b = ctx
                .scratch
                .expr_const(None, Some(b_n), empty_levels)
                .unwrap();
            assert!(!ctx.is_def_eq(a, b).unwrap());
        });
    }

    #[test]
    fn app_congruence_recurses_into_args() {
        with_ctx(|ctx| {
            // f ((fun (x : Sort 0) => x) Sort0)  =?=  f Sort0 —
            // exercises App congruence (same head `f`) recursing via
            // is_def_eq_core into an arg pair that only agrees after a
            // beta reduction (whnf_core), not by pointer/structural
            // equality alone.
            let f_s = ctx.scratch.intern_str(None, "f").unwrap();
            let f_n = ctx.scratch.name_str(None, None, f_s).unwrap();
            let f = ctx.scratch.expr_fvar(None, Some(f_n)).unwrap();

            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap();
            let bv = ctx
                .scratch
                .expr_bvar(None, &leanr_kernel::Nat::from(0u64))
                .unwrap();
            let lam = ctx
                .scratch
                .expr_lam(None, None, s0, bv, leanr_kernel::BinderInfo::Default)
                .unwrap();
            let arg_lhs = ctx.scratch.expr_app(None, lam, s0).unwrap(); // (fun x => x) Sort0

            let lhs = ctx.scratch.expr_app(None, f, arg_lhs).unwrap();
            let rhs = ctx.scratch.expr_app(None, f, s0).unwrap();
            assert!(ctx.is_def_eq(lhs, rhs).unwrap());
        });
    }

    #[test]
    fn lam_congruence_opens_one_fvar_and_recurses_on_bodies() {
        with_ctx(|ctx| {
            // (fun (x : Sort 0) => x) vs (fun (x : Sort 0) => (fun y =>
            // y) x) — same domain; bodies only agree after whnf_core
            // reduces the RHS body's redex. Exercises
            // `is_def_eq_binding_shallow`'s fvar substitution: the
            // RHS body's own bound variable `x` (a bvar referencing the
            // OUTER binder, at the same depth as the inner lambda's
            // application) must be substituted correctly around the
            // untouched inner binder.
            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap();
            let bv0 = ctx
                .scratch
                .expr_bvar(None, &leanr_kernel::Nat::from(0u64))
                .unwrap();
            let lhs = ctx
                .scratch
                .expr_lam(None, None, s0, bv0, leanr_kernel::BinderInfo::Default)
                .unwrap();

            // inner (fun y => y) applied to bvar 0 (the outer `x`).
            let inner_lam = ctx
                .scratch
                .expr_lam(None, None, s0, bv0, leanr_kernel::BinderInfo::Default)
                .unwrap();
            let rhs_body = ctx.scratch.expr_app(None, inner_lam, bv0).unwrap();
            let rhs = ctx
                .scratch
                .expr_lam(None, None, s0, rhs_body, leanr_kernel::BinderInfo::Default)
                .unwrap();
            assert!(ctx.is_def_eq(lhs, rhs).unwrap());
        });
    }

    #[test]
    fn forall_binder_info_mismatch_still_def_eq() {
        with_ctx(|ctx| {
            // {x : Sort 0} -> Sort 0  vs  (x : Sort 0) -> Sort 0 —
            // differ ONLY in binder-info (implicit vs default); must
            // still be def-eq, pinning the module doc's correction
            // that binder-info is never part of the check.
            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap();
            let lhs = ctx
                .scratch
                .expr_forall(None, None, s0, s0, leanr_kernel::BinderInfo::Implicit)
                .unwrap();
            let rhs = ctx
                .scratch
                .expr_forall(None, None, s0, s0, leanr_kernel::BinderInfo::Default)
                .unwrap();
            assert!(ctx.is_def_eq(lhs, rhs).unwrap());
        });
    }

    #[test]
    fn forall_domain_mismatch_is_not_def_eq() {
        with_ctx(|ctx| {
            // (x : Sort 0) -> Sort 0  vs  (x : Sort 1) -> Sort 0 —
            // domains differ (and are not structurally-equal-level
            // Sorts), so binder congruence must reject the pair, not
            // fall through to a vacuous "bodies matched" true. Pins
            // that `is_def_eq_binding_shallow` actually threads `d2`
            // into the domain check (a real bug this test caught: the
            // first draft of this function silently dropped `d2`).
            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap();
            let one = ctx.scratch.level_succ(None, z).unwrap();
            let s1 = ctx.scratch.expr_sort(None, one).unwrap();
            let lhs = ctx
                .scratch
                .expr_forall(None, None, s0, s0, leanr_kernel::BinderInfo::Default)
                .unwrap();
            let rhs = ctx
                .scratch
                .expr_forall(None, None, s1, s0, leanr_kernel::BinderInfo::Default)
                .unwrap();
            assert!(!ctx.is_def_eq(lhs, rhs).unwrap());
        });
    }
}
