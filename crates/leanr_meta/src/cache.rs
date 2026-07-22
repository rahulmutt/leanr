//! The defeq cache: split into a permanent table (mvar-free pairs
//! under a standard config) and a transient table (everything else).
//!
//! oracle: `DefEqCacheKind`/`getDefEqCacheKind` (ExprDefEq.lean:2233-
//! 2242), `mkCacheKey` (:2251-2254), `getCachedResult`/`cacheResult`
//! (:2256-2274). Wired into the ladder at `defeq.rs::is_def_eq_core`'s
//! task-8 seam, matching `isExprDefEqAuxImpl`'s own
//! `instantiateMVars` -> cache -> `isExprDefEqExpensive` sequence
//! (:2333-2354). The postponed-count guard (`numPostponed ==
//! getNumPostponed`, :2350-2353) is applied AT THAT SEAM, not in this
//! module: it needs `self.postponed.len()` both before and after the
//! `is_def_eq_expensive` call, and this module is not the one that
//! runs it — [`MetaCtx::cache_store`] below is called only once the
//! caller has already checked the guard.
//!
//! # A transcription correction (brief vs. pinned source)
//!
//! The task brief (and this plan's own design spec,
//! `docs/superpowers/specs/2026-07-21-m4a-defeq-design.md`) describe
//! `getDefEqCacheKind` as "permanent for mvar/fvar-free pairs". The
//! pinned source disagrees:
//!
//! ```text
//! private def getDefEqCacheKind (t s : Expr) : MetaM DefEqCacheKind := do
//!   if t.hasMVar || s.hasMVar || (← read).canUnfold?.isSome then
//!     return .transient
//!   else
//!     return .permanent
//! ```
//!
//! It tests only `hasMVar` — and `Expr.hasMVar` (Expr.lean:567-572) is
//! `d.hasExprMVar || d.hasLevelMVar`: level metavariables are folded
//! into the SAME flag as expr metavariables; there is no separate
//! `hasLevelMVar` check to add. It never tests `hasFVar` at all. This
//! is not an oversight: an `FVarId`, once minted, is never reused and
//! its local declaration is immutable for its entire lifetime
//! (`leanr_kernel::local_ctx::FVarIdGen`/`LocalContext::restore` here
//! never decrement the id counter or mutate a live decl; the oracle's
//! `local_ctx.h`/`.cpp` carry the identical invariant) — a term's
//! meaning is fully determined by which fvars it MENTIONS, independent
//! of which *other* fvars are in scope when the cache is consulted
//! again, so caching an fvar-mentioning pair permanently is sound.
//! Fixed here: [`MetaCtx::defeq_cache_kind`] checks `has_expr_mvar()`
//! and `has_level_mvar()` on both sides (together, the oracle's
//! `hasMVar`), never `has_fvar()`.

use leanr_kernel::bank::ExprId;

use crate::{MetaCtx, MetaError};

/// oracle: `DefEqCacheKind` (ExprDefEq.lean:2233-2236).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DefEqCacheKind {
    /// "problem does not have mvars and we are using standard config,
    /// we can use one persistent cache."
    Permanent,
    /// "problem has mvars or is using nonstandard configuration, we
    /// should use transient cache."
    Transient,
}

impl<'e> MetaCtx<'e> {
    /// oracle: `getDefEqCacheKind` (ExprDefEq.lean:2238-2242). See this
    /// module's doc comment for the hasFVar transcription correction.
    /// `can_unfold_override` is this crate's own stand-in for
    /// `(← read).canUnfold?.isSome` (`metactx.rs`'s own doc comment on
    /// that field cites the same oracle predicate, `whnf.rs`'s
    /// `whnf_matcher`).
    pub(crate) fn defeq_cache_kind(&self, t: ExprId, s: ExprId) -> DefEqCacheKind {
        let dt = self.data(t);
        let ds = self.data(s);
        let has_mvar =
            dt.has_expr_mvar() || dt.has_level_mvar() || ds.has_expr_mvar() || ds.has_level_mvar();
        if has_mvar || self.can_unfold_override {
            DefEqCacheKind::Transient
        } else {
            DefEqCacheKind::Permanent
        }
    }

    /// oracle: `mkCacheKey` (:2251-2254) + `getCachedResult` (:2256-
    /// 2262). Key = `(Config::cache_key(), t, s)` (plan 1's
    /// `Config::cache_key` covers every field, so this cache is safe
    /// under config changes with no extra mechanism); looked up in the
    /// kind's own map (task 2's `defeq_cache_perm`/
    /// `defeq_cache_transient`).
    ///
    /// Note: the oracle's `mkCacheKey` (Basic.lean:667) canonicalizes
    /// the pair via `Expr.quickLt` before hashing, so `(t, s)` and
    /// `(s, t)` share one entry there. This crate keys on the UNORDERED
    /// — i.e. positional, not canonicalized — `(config, t, s)` pair
    /// instead, deliberately: a swapped-order re-query simply misses
    /// and recomputes rather than reusing the other order's entry.
    /// Fewer hits, never a false hit — sound, just less complete. Not a
    /// bug to "fix" by restoring `quickLt` ordering.
    pub(crate) fn cache_lookup(&self, kind: DefEqCacheKind, t: ExprId, s: ExprId) -> Option<bool> {
        let key = (self.cfg.cache_key(), t, s);
        match kind {
            DefEqCacheKind::Permanent => self.defeq_cache_perm.get(&key).copied(),
            DefEqCacheKind::Transient => self.defeq_cache_transient.get(&key).copied(),
        }
    }

    /// oracle: `cacheResult` (:2263-2274). The permanent branch stores
    /// under the key as-is: `t`/`s` are already mvar-free whenever this
    /// kind is reached (`defeq_cache_kind` above), so re-instantiating
    /// them would be a no-op. The transient branch re-runs
    /// `instantiateMVars` on `t`/`s` FIRST: the `is_def_eq_expensive`
    /// call this result came from may itself have assigned mvars that
    /// were still unassigned when `t`/`s` were first built (the
    /// `defeq.rs` seam instantiates once, before that call), and
    /// storing under the stale pre-assignment key would serve a wrong
    /// result once that assignment is later backtracked — the oracle's
    /// own comment cites lean4 issue #1870 for exactly this failure
    /// mode.
    pub(crate) fn cache_store(
        &mut self,
        kind: DefEqCacheKind,
        t: ExprId,
        s: ExprId,
        result: bool,
    ) -> Result<(), MetaError> {
        match kind {
            DefEqCacheKind::Permanent => {
                let key = (self.cfg.cache_key(), t, s);
                self.defeq_cache_perm.insert(key, result);
            }
            DefEqCacheKind::Transient => {
                let t2 = self.instantiate_mvars(t)?;
                let s2 = self.instantiate_mvars(s)?;
                let key = (self.cfg.cache_key(), t2, s2);
                self.defeq_cache_transient.insert(key, result);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::cache::DefEqCacheKind;
    use crate::test_support::{fresh_mvar, with_ctx};

    /// oracle: `getDefEqCacheKind` (ExprDefEq.lean:2238-2242) — the
    /// invariant this task's split rests on: a query over two mvar-free
    /// terms is permanent (safe to reuse forever, across any mctx
    /// state), a query touching an mvar-headed term is transient
    /// (its verdict depends on the CURRENT mctx and must not survive a
    /// backtrack). Reuses `test_support`'s `with_ctx`/`fresh_mvar`
    /// rather than duplicating either (task-8 cross-task note).
    #[test]
    fn permanent_cache_only_for_mvar_free_terms() {
        with_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap();
            assert_eq!(ctx.defeq_cache_kind(s0, s0), DefEqCacheKind::Permanent);
            // a term with an mvar head is transient.
            let (m, _id) = fresh_mvar(ctx, s0);
            assert_eq!(ctx.defeq_cache_kind(m, s0), DefEqCacheKind::Transient);
        });
    }

    /// Fix-wave-1 regression (Critical finding on task 8): oracle
    /// `resetDefEqPermCaches` (Basic.lean:2477-2495) is called at the
    /// START of every top-level `isDefEq`/`isExprDefEq`, precisely
    /// because a permanent-cache entry can be sound at the moment it is
    /// stored yet become stale later: `getDefEqCacheKind`
    /// (ExprDefEq.lean:2238-2242, `defeq_cache_kind` above) only checks
    /// `hasMVar` on `t`/`s` themselves, not whether some fvar THEY
    /// mention has a declared type that still contains an unassigned
    /// mvar. Once that mvar gets assigned, the old verdict for the same
    /// `(config, t, s)` key is no longer trustworthy — but nothing else
    /// in this crate invalidates the permanent-cache entry, so the only
    /// thing standing between a reused `MetaCtx` and a stale (possibly
    /// wrongly-`true`) verdict is this per-top-level-call reset.
    ///
    /// This test plants a permanent-cache entry directly (playing the
    /// role of "an earlier top-level `is_def_eq` call populated it"),
    /// then makes one further top-level `is_def_eq` call — deliberately
    /// a trivial `s0 == s0` query, which resolves via `is_def_eq_quick`'s
    /// leading pointer-equality check and never itself reads or writes
    /// `defeq_cache_perm` — and asserts the map is empty immediately
    /// after. `defeq_cache_perm` is `pub(crate)`, so the assertion reads
    /// it directly rather than inferring it from an observable side
    /// effect.
    ///
    /// This discriminates the fix precisely: pre-fix, `is_def_eq`
    /// (`defeq.rs`) clears only `defeq_cache_transient` and never
    /// touches `defeq_cache_perm`, so the planted entry survives the
    /// call and the final assertion FAILS. Post-fix, `is_def_eq` clears
    /// `defeq_cache_perm` unconditionally at entry (before running
    /// `is_def_eq_core`), so the planted entry is gone and the
    /// assertion PASSES.
    #[test]
    fn top_level_is_def_eq_resets_permanent_cache() {
        with_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).unwrap();
            let s0 = ctx.scratch.expr_sort(None, z).unwrap();

            // Plant a stale permanent-cache entry, as if an earlier
            // top-level `is_def_eq` call had populated it.
            let key = (ctx.cfg.cache_key(), s0, s0);
            ctx.defeq_cache_perm.insert(key, true);
            assert!(!ctx.defeq_cache_perm.is_empty());

            assert!(ctx.is_def_eq(s0, s0).unwrap());
            assert!(
                ctx.defeq_cache_perm.is_empty(),
                "defeq_cache_perm must be cleared at the start of every \
                 top-level is_def_eq call (resetDefEqPermCaches, \
                 Basic.lean:2477-2495)"
            );
        });
    }
}
