//! Weak head normal form: `MetaCtx::whnf` (delta-including) and
//! `MetaCtx::whnf_core` (the no-delta loop it calls into).
//!
//! oracle: `src/lean/Lean/Meta/WHNF.lean`, toolchain
//! leanprover/lean4:v4.33.0-rc1. Every method below cites the exact
//! line range read from that file (not from memory — see the task
//! report for the per-rule citation table). Structure, per the
//! oracle's own file layout:
//!
//! - `whnf_easy_cases` (:385-414) — leaves (`Forall`/`Lam`/`Sort`/
//!   `LitNat`/`LitStr`) and the `FVar`/`MVar`/`MData` dereference
//!   chains; everything else (`Const`/`App`/`Proj`/`LetE`) is a "hard"
//!   case passed on. Rust has no `k`-continuation, so this returns an
//!   explicit `EasyOrHard` instead of taking a callback.
//! - `whnf_core` (:648-715) — the no-delta reduction loop: beta, zeta
//!   (`LetE`), iota (recursor/quotient/matcher), and projection.
//! - `whnf` / `whnf_imp` (:1102-1121) — easy cases → cache → `whnf_core`
//!   → `reduce_nat?` → `unfold_definition?` (plain delta) → loop.
//!
//! **Never transcribed from memory**: every rule here was checked
//! against the open oracle file, rule by rule; corrections found this
//! way are recorded in this crate's commit history for this module.
//!
//! # Named seams (task 6/7/plan-3 landing points)
//!
//! Every one of these is a documented function returning an
//! "unimplemented" answer (never a wrong one, never a panic) for the
//! oracle behavior it stands in for:
//!
//! - [`MetaCtx::unfold_definition`] — its final oracle shape (task 7,
//!   :871-957): the `can_unfold_at_matcher` gate-swap (task 6) plus the
//!   `_sunfold` smart-unfolding channel (`smart_unfolding_reduce`,
//!   :747-776) ahead of plain delta.
//! - [`MetaCtx::get_structural_rec_arg_pos`] (task 7) — the forward-
//!   declared `getStructuralRecArgPos?` extern (:49-56; the real
//!   implementation lives in the elaborator's
//!   `Structural/Eqns.lean`, out of reach for a decode-only crate).
//!   Always `None`; per the oracle's OWN doc comment (:...,
//!   `unfoldDefinition?`'s "Remark 4"), a `none` here takes the SAME
//!   branch the oracle itself takes for Binport-imported (Lean-3-era)
//!   `.olean`s that never recorded a rec-arg position at all — this is
//!   the oracle's own documented fallback, not merely an
//!   approximation of it.
//! - [`MetaCtx::synth_pending`] — LANDED (PR-B task B6): `Meta.synthPending`
//!   (`Basic.lean:840`, real impl `synthPendingImp`,
//!   `SynthInstance.lean:1031-1061`), resolving a pending typeclass-
//!   synthesis problem blocking a stuck smart-unfolding match, now that
//!   B4/B5's tabled `synth_instance` exists. See its own doc comment for
//!   the four oracle conditions and the `synth_pending_depth` guard.
//! - [`MetaCtx::unfold_proj_inst_when_instances`] — LANDED (PR-B task
//!   B6): `unfoldProjInstWhenInstances?`/`unfoldProjInst?` (:814-818,
//!   :793-806, gated at `unfoldDefinition?`'s own :874), now that
//!   `projection_fns` decodes `getProjectionFnInfo?`'s own registry. See
//!   `unfold_proj_inst`'s own doc comment.
//! - the `Defn` arm of `whnf_core_app`'s recursor dispatch — aux-recursor
//!   (`casesOn`/`brecOn`-shaped) unfolding inside `whnf_core` itself
//!   (:696-701); lands with the extension that identifies
//!   `isAuxRecursor`-equivalent definitions.
//! - [`MetaCtx::whnf_delayed_assigned`] — delayed-mvar-assignment
//!   expansion (:587-606); this plan's `MetavarContext` has no
//!   delayed-assignment channel at all (`assign.rs`'s own citation) —
//!   lands with plan 4 / M4b.
//! - [`MetaCtx::to_ctor_when_k`] — compares structurally (`ExprId`
//!   equality after `whnf`) instead of via `isDefEq`. `defeq.rs::
//!   is_def_eq` (this plan's own unifier) now exists, but this call
//!   site was never rewired to use it; open gap for a later task.
//! - [`MetaCtx::cleanup_nat_offset_major`] — offset-constraint cleanup
//!   (:218-226; lands whenever `Config.offsetCnstrs` does — same gate
//!   `isDefEqOffset` cites, `lazy_delta.rs`).
//! - [`MetaCtx::to_ctor_if_lit`]'s `LitStr` arm — string-literal
//!   `toCtorIfLit` (:27-28; no tier-1 corpus query needs it yet).
//! - the `FVar` arm of `whnf_easy_cases` — `isImplementationDetail`/
//!   `zetaDeltaSet`/`trackZetaDelta` (:399-407) are elaborator-context
//!   channels that do not exist yet; only `cfg.zeta_delta` is modeled.
//!   Arrives with the term elaborator (M4b).
//! - (task 6) `hasMatchPatternAttribute` (:504-505, inside
//!   `can_unfold_at_matcher`) — the `@[match_pattern]` attribute
//!   extension is undecoded; always `false` here.
//! - (task 6) `getAuxParentProjectionInfo?` (:367, inside
//!   `get_stuck_mvar_proj_fn`) — the diamond-inheritance auxiliary-
//!   parent-projection registry does not exist (task B6 decoded
//!   `getProjectionFnInfo?`/`projection_fns`, its OWN sibling at :347,
//!   but never this one — out of that task's stated scope); always
//!   `None` there (same posture as `to_ctor_when_structure`'s `mkProjFn`
//!   elision, below).
//! - (task B6, opus review round 1) `synth_pending`'s missing
//!   `catchInternalId isDefEqStuckExceptionId` (`SynthInstance.lean:
//!   1052`): the oracle CATCHES an internal `isDefEqStuck` exception
//!   raised by the nested `synthInstance?` attempt and returns `false`
//!   in its place; this crate's `synth_pending_body` instead lets
//!   `MetaError::IsDefEqStuck` escape (via `?`) all the way out through
//!   `sunfold_go_match` to `whnf`'s own caller. Direction: safe — an
//!   `Err` surfaces where the oracle would have produced an `Ok`
//!   ANSWER, never a WRONG one — but it IS a genuine, currently
//!   unreconciled divergence in observable control flow (the
//!   differential gate will report an ERROR where the oracle recorded
//!   an answer for any query that routes a stuck sub-defeq through
//!   here), not merely a stricter restatement of the oracle's own
//!   discipline. See `synth_pending`'s own doc comment for why this
//!   crate's Global Constraints forbid the alternative (collapsing
//!   `IsDefEqStuck` to `false`) without also fixing this by actually
//!   catching-and-reconciling it. Owner: M4b / future — no task number
//!   assigned yet; this is a deliberate, tracked divergence, not a
//!   silent one.

use leanr_kernel::bank::pools::DataValueRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelsId, NameId};
use leanr_kernel::{
    abstract_fvars, instantiate, instantiate_level_params, instantiate_rev, BinderInfo,
    ConstantInfo, Nat, QuotKind, QuotVal, RecursorRule, RecursorVal,
};
use leanr_olean::ReducibilityStatus;

use crate::metactx::NatOp;
use crate::{MVarId, MVarKind, MetaCtx, MetaError, ProjReduction, TransparencyMode};

/// oracle: `exponentiation.threshold`, default `256`
/// (`SafeExponentiation.lean:15-22`), consulted by `checkExponent`
/// (`SafeExponentiation.lean:29-36`), which `reducePow` (WHNF.lean:1042-1047)
/// guards its exponent with — THIS is the guard `reduce_nat`'s `pow` arm
/// ports, restated as a plain constant since this crate has no options
/// table to read `exponentiation.threshold` from. Deliberately NOT
/// `leanr_kernel::tc`'s private `REDUCE_POW_MAX_EXP = 1 << 24`
/// (`type_checker.cpp:586`): that is the KERNEL's own, separate,
/// much-larger threshold for `Nat.rec`/`whnf`'s internal reduction (a
/// different oracle layer entirely) — the two must not be conflated.
const EXPONENTIATION_THRESHOLD: usize = 256;

/// oracle: `maxSynthPendingDepth`, default `1` (`Meta/Basic.lean:458-
/// 461`), consulted by `synthPendingImp` (`SynthInstance.lean:1044-
/// 1048`) against its own reader-context `synthPendingDepth` counter
/// (`Meta/Basic.lean:502`) — restated as a plain constant for the same
/// "no options table" reason `EXPONENTIATION_THRESHOLD` above is. See
/// `MetaCtx::synth_pending_depth`'s own doc (`metactx.rs`) for why this
/// is a SEPARATE counter/bound from the general `guard_depth`/
/// `MAX_REC_DEPTH` recursion guard.
const MAX_SYNTH_PENDING_DEPTH: u32 = 1;

/// oracle: `canUnfoldAtMatcher`'s allowlist (WHNF.lean:506-520),
/// beyond `hasMatchPatternAttribute` — root (fully-qualified) names
/// unfolded to expose constructors in match discriminants regardless
/// of the const's own reducibility status, at `.reducible`/
/// `.instances`/`.implicit` transparency specifically.
const MATCHER_UNFOLD_ALLOWLIST: &[&str] = &[
    "OfNat.ofNat",
    "NatCast.natCast",
    "Zero.zero",
    "One.one",
    "decEq",
    "Nat.decEq",
    "Char.ofNat",
    "Char.ofNatAux",
    "String.decEq",
    "List.hasDecEq",
    "Fin.ofNat",
    "UInt8.ofNat",
    "UInt8.decEq",
    "UInt16.ofNat",
    "UInt16.decEq",
    "UInt32.ofNat",
    "UInt32.decEq",
    "UInt64.ofNat",
    "UInt64.decEq",
    "HMod.hMod",
    "Mod.mod",
];

/// oracle: `ReduceMatcherResult` (WHNF.lean:432-436). All four variants
/// are constructed by `reduce_matcher`'s real transcription (task 6).
/// `Stuck`'s own payload is consumed by `sunfold_go_match` (task 7, via
/// `get_stuck_mvar`) exactly as the oracle's own `smartUnfoldingReduce?`
/// does (:770-772) — `whnf_core`'s OWN call site still discards it
/// (`| .stuck _ => pure e`, WHNF.lean:687), unchanged from task 6.
pub(crate) enum ReduceMatcherResult {
    Reduced(ExprId),
    Stuck(ExprId),
    NotMatcher,
    PartialApp,
}

/// The easy/hard split `whnfEasyCases`' `k`-continuation stands in for
/// (no continuations in Rust — see the module doc).
enum EasyOrHard {
    Easy(ExprId),
    Hard(ExprId),
}

impl<'e> MetaCtx<'e> {
    /// oracle: `whnfImp` (WHNF.lean:1102-1121). `reduceNative?` is
    /// permanently out of scope (no native-code evaluator in a pure-Rust
    /// toolchain — same posture as
    /// `leanr_kernel::tc::TypeChecker::reduce_native`'s own stub).
    pub fn whnf(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        self.step()?;
        self.guarded(|s| s.whnf_imp(e))
    }

    fn whnf_imp(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let e = match self.whnf_easy_cases(e)? {
            EasyOrHard::Easy(v) => return Ok(v),
            EasyOrHard::Hard(v) => v,
        };
        let key = (self.cfg.cache_key(), e);
        let use_cache = self.cacheable(e);
        if use_cache {
            if let Some(&r) = self.whnf_cache.get(&key) {
                return Ok(r);
            }
        }
        let e1 = self.whnf_core(e)?;
        let r = if let Some(v) = self.reduce_nat(e1)? {
            v
        } else if let Some(e2) = self.unfold_definition(e1)? {
            self.guarded(|s| s.whnf_imp(e2))?
        } else {
            e1
        };
        if use_cache {
            self.whnf_cache.insert(key, r);
        }
        Ok(r)
    }

    /// oracle: `whnfEasyCases` (WHNF.lean:385-414). Loops rather than
    /// takes a continuation. The `MVar`/`FVar` dereference chains have
    /// no occurs-check guard yet (plan 3's job), so `step()` is called
    /// every iteration — hardening against a hypothetical assignment
    /// cycle (`?a := ?b`, `?b := ?a`, both legal under the current
    /// `MetavarContext::assign`, which has no cycle detection): a
    /// deterministic `StepBudgetExhausted`, never a hang.
    fn whnf_easy_cases(&mut self, mut e: ExprId) -> Result<EasyOrHard, MetaError> {
        loop {
            self.step()?;
            e = match self.node(e) {
                Node::Forall { .. }
                | Node::Lam { .. }
                | Node::Sort { .. }
                | Node::LitNat { .. }
                | Node::LitStr { .. } => return Ok(EasyOrHard::Easy(e)),
                // oracle panics (`panic! "loose bvar in expression"`,
                // :391); Global Constraints forbid a panic here — this
                // is incompleteness, never unsoundness.
                Node::BVar { .. } | Node::BVarBig { .. } => {
                    return Err(MetaError::Infer("loose bvar in whnf".into()))
                }
                Node::LetE { .. }
                | Node::Const { .. }
                | Node::App { .. }
                | Node::Proj { .. }
                | Node::ProjBig { .. } => return Ok(EasyOrHard::Hard(e)),
                Node::MData { expr, .. } => expr,
                // oracle (:397-409): the pattern match itself
                // (`.ldecl (value := v) (nondep := false) ..`) only
                // even considers a decl where `nondep` is FALSE — i.e.
                // a genuine `let`, not a `have` (`nondep := true`,
                // matched by the oracle's fallback `_ => return e` and
                // NEVER followed, regardless of `cfg.zetaDelta`). Of
                // those genuine lets, the VALUE is followed only when
                // gated by `cfg.zetaDelta` (the `isImplementationDetail`/
                // `zetaDeltaSet`/`trackZetaDelta` channels are
                // elaborator context this crate does not have yet —
                // seam, see module doc).
                //
                // This crate's own `LocalDecl`
                // (`leanr_kernel::local_ctx`, ported from the KERNEL's
                // `local_ctx.h`, not the elaborator's `Lean.LocalDecl`)
                // carries NO `nondep` bit at all, so it cannot
                // distinguish a `have` from a `let` the way the oracle
                // does. The result is an OVER-APPROXIMATION: under
                // `cfg.zeta_delta`, this follows the value of EVERY
                // let-bound fvar, including ones the oracle would have
                // left alone as a `have`. This is sound for defeq
                // (unfolding a "have" value can only do more reduction
                // work than the oracle, never produce a definitionally
                // wrong answer) but is a real, documented divergence,
                // not merely a renamed case of the same gap.
                Node::FVar { id } => {
                    let followed = id
                        .and_then(|i| self.lctx.get(i))
                        .and_then(|d| d.value)
                        .filter(|_| self.cfg.zeta_delta);
                    match followed {
                        Some(v) => v,
                        None => return Ok(EasyOrHard::Easy(e)),
                    }
                }
                Node::MVar { id } => match id.and_then(|i| self.mctx.assignment(MVarId(i))) {
                    Some(v) => v,
                    None => return Ok(EasyOrHard::Easy(e)),
                },
            };
        }
    }

    /// oracle: `whnfCore` (WHNF.lean:648-715).
    pub fn whnf_core(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        self.step()?;
        self.guarded(|s| s.whnf_core_body(e))
    }

    fn whnf_core_body(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let e = match self.whnf_easy_cases(e)? {
            EasyOrHard::Easy(v) => return Ok(v),
            EasyOrHard::Hard(v) => v,
        };
        let key = (self.cfg.cache_key(), e);
        let use_cache = self.cacheable(e);
        if use_cache {
            if let Some(&r) = self.whnf_core_cache.get(&key) {
                return Ok(r);
            }
        }
        let r = match self.node(e) {
            // oracle: `.const .. => pure e` (:655) — delta happens in
            // `whnf` only, never in `whnf_core`.
            Node::Const { .. } => e,
            Node::LetE { .. } => self.whnf_core_let(e)?,
            Node::App { .. } => self.whnf_core_app(e)?,
            Node::Proj { .. } | Node::ProjBig { .. } => self.whnf_core_proj(e)?,
            _ => unreachable!("whnf_easy_cases only returns Hard for Const/App/Proj/LetE"),
        };
        if use_cache {
            self.whnf_core_cache.insert(key, r);
        }
        Ok(r)
    }

    /// oracle: `whnfCore`'s `.letE` arm (WHNF.lean:656-663).
    fn whnf_core_let(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let (value, body, non_dep) = match self.node(e) {
            Node::LetE {
                value,
                body,
                non_dep,
                ..
            } => (value, body, non_dep),
            _ => unreachable!("whnf_core_let: caller already matched LetE"),
        };
        if self.cfg.zeta && (!non_dep || self.cfg.zeta_have) {
            let expanded = self.expand_let(body, vec![value], self.cfg.zeta_have)?;
            self.whnf_core(expanded)
        } else if self.cfg.zeta_unused && self.data(body).loose_bvar_range() == 0 {
            let consumed = self.consume_unused_let(body);
            self.whnf_core(consumed)
        } else {
            Ok(e)
        }
    }

    /// oracle: `expandLet` (WHNF.lean:622-629). `vs` starts as `[value]`
    /// (the caller already pushed the outer `LetE`'s own value, per the
    /// call site `expandLet b #[v]`, WHNF.lean:659).
    fn expand_let(
        &mut self,
        mut e: ExprId,
        mut vs: Vec<ExprId>,
        zeta_have: bool,
    ) -> Result<ExprId, MetaError> {
        loop {
            match self.node(e) {
                // The `!non_dep || zeta_have` guard is folded into the
                // match arm (clippy::collapsible_match): a `LetE` that
                // fails it falls through to the same `_` arm below as a
                // non-`LetE` term — both do exactly the same
                // `instantiate_rev(e, vs)` over the CURRENT `e`.
                Node::LetE {
                    value,
                    body,
                    non_dep,
                    ..
                } if !non_dep || zeta_have => {
                    let v = instantiate_rev(
                        self.scratch,
                        Some(self.view.store),
                        value,
                        &vs,
                        &mut self.guard,
                    )?;
                    vs.push(v);
                    e = body;
                }
                _ => {
                    return Ok(instantiate_rev(
                        self.scratch,
                        Some(self.view.store),
                        e,
                        &vs,
                        &mut self.guard,
                    )?)
                }
            }
        }
    }

    /// oracle: `consumeUnusedLet` (WHNF.lean:639-642), called with the
    /// default `consumeNondep := false` (the only call site inside
    /// `whnfCore`, :661) — so a non-dependent let ("have") is NEVER
    /// consumed via this path, only a genuine unused `let`.
    fn consume_unused_let(&self, e: ExprId) -> ExprId {
        let mut cur = e;
        loop {
            match self.node(cur) {
                Node::LetE { body, non_dep, .. } => {
                    if non_dep || self.data(body).loose_bvar_range() != 0 {
                        return cur;
                    }
                    cur = body;
                }
                _ => return cur,
            }
        }
    }

    /// oracle: `whnfCore`'s `.app` arm (WHNF.lean:664-703).
    fn whnf_core_app(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let args = self.get_app_args(e);
        let f = self.get_app_fn(e);
        let f_was_lambda = matches!(self.node(f), Node::Lam { .. });
        let f_prime = self.whnf_core(f)?;

        if matches!(self.node(f_prime), Node::Lam { .. }) && (self.cfg.beta || !f_was_lambda) {
            let applied = self.beta_rev(f_prime, &args)?;
            return self.whnf_core(applied);
        }
        if let Some(new_e) = self.whnf_delayed_assigned(f_prime, e)? {
            return self.whnf_core(new_e);
        }
        let e2 = if f == f_prime {
            e
        } else {
            self.mk_app_spine(f_prime, &args)?
        };
        if !self.cfg.iota {
            return Ok(e2);
        }
        match self.reduce_matcher(e2)? {
            ReduceMatcherResult::Reduced(new_e) => return self.whnf_core(new_e),
            ReduceMatcherResult::PartialApp | ReduceMatcherResult::Stuck(_) => return Ok(e2),
            ReduceMatcherResult::NotMatcher => {}
        }
        let head2 = self.get_app_fn(e2);
        let (cname, clevels) = match self.node(head2) {
            Node::Const {
                name: Some(n),
                levels,
            } => (n, levels),
            _ => return Ok(e2),
        };
        let cinfo = match self.view.get(cname) {
            Some(i) => i,
            None => return Ok(e2),
        };
        match cinfo {
            ConstantInfo::Rec(rec_val) => match self.reduce_rec(rec_val, clevels, &args)? {
                Some(rhs) => self.whnf_core(rhs),
                None => Ok(e2),
            },
            ConstantInfo::Quot(qv) => match self.reduce_quot_rec(qv, &args)? {
                Some(rhs) => self.whnf_core(rhs),
                None => Ok(e2),
            },
            // SEAM: aux-recursor unfolding inside `whnf_core` itself
            // (oracle :696-701 — `isAuxDef`/`isAuxRecursor`). This
            // crate's environment does not carry that predicate yet;
            // ordinary (non-aux) definitions still unfold via plain
            // delta in `whnf` (`unfold_definition`), which is what the
            // tier-1 corpus exercises. Lands with the extension that
            // identifies `casesOn`/`brecOn`-shaped aux definitions.
            ConstantInfo::Defn(_) => Ok(e2),
            _ => Ok(e2),
        }
    }

    /// SEAM: oracle `whnfDelayedAssigned?` (WHNF.lean:587-606). The
    /// delayed-mvar-assignment channel (`getDelayedMVarAssignment?`)
    /// does not exist on this plan's `MetavarContext` at all — a later
    /// plan (plan 4 / M4b), not this one (`assign.rs`'s own citation
    /// on why this crate has no delayed-assignment concept yet). Always
    /// `None`.
    fn whnf_delayed_assigned(
        &mut self,
        _f_prime: ExprId,
        _e: ExprId,
    ) -> Result<Option<ExprId>, MetaError> {
        Ok(None)
    }

    /// oracle: `reduceMatcher?` (WHNF.lean:536-575). `numAlts` is
    /// `info.alt_infos.len()` (`MatcherInfo.numAlts`,
    /// MatcherInfo.lean:76-77); the per-alternative arity formula
    /// (`MatcherInfo.altNumParams`, MatcherInfo.lean:106-108) is NOT
    /// needed here at all — `reduceMatcher?` itself never calls it
    /// (verified by grepping the oracle file: `altNumParams`/
    /// `getNumDiscrEqs` appear nowhere in `WHNF.lean`). The bounded
    /// telescope below peels exactly `numAlts` foralls of the applied
    /// prefix's OWN inferred type; each hypothesis stands for one
    /// whole alternative as an opaque function, never decomposed
    /// field-by-field.
    pub(crate) fn reduce_matcher(&mut self, e: ExprId) -> Result<ReduceMatcherResult, MetaError> {
        // oracle: `e.consumeMData` (:537).
        let mut cur = e;
        while let Node::MData { expr, .. } = self.node(cur) {
            cur = expr;
        }
        let head = self.get_app_fn(cur);
        let (decl_name, decl_levels) = match self.node(head) {
            Node::Const {
                name: Some(n),
                levels,
            } => (n, levels),
            _ => return Ok(ReduceMatcherResult::NotMatcher),
        };
        let info = match self.matcher_of(decl_name) {
            Some(m) => m.clone(),
            None => return Ok(ReduceMatcherResult::NotMatcher),
        };
        let args = self.get_app_args(cur);
        // Defensive fallbacks (never exercised by any real matcher —
        // these `Nat`s come from a `.olean`-decoded arity, always tiny
        // in practice): a `Nat` too big for `usize` is treated as "not
        // a matcher we can handle" rather than panicking or erroring.
        let num_params = match info.num_params.to_usize() {
            Some(v) => v,
            None => return Ok(ReduceMatcherResult::NotMatcher),
        };
        let num_discrs = match info.num_discrs.to_usize() {
            Some(v) => v,
            None => return Ok(ReduceMatcherResult::NotMatcher),
        };
        let num_alts = info.alt_infos.len();
        let prefix_sz = num_params + 1 + num_discrs;
        if args.len() < prefix_sz + num_alts {
            return Ok(ReduceMatcherResult::PartialApp);
        }
        // oracle: `getConstInfo declName` (:547) — the matcher aux's
        // OWN value is grabbed UNCONDITIONALLY here, with no
        // `canUnfold`/transparency gate at all (unlike ordinary delta,
        // `unfold_definition`'s job): this is exactly the escape hatch
        // the module doc above (:447-471) explains — a match
        // expression must reduce at ANY transparency, including
        // `.reducible`, regardless of the aux decl's own reducibility
        // status.
        let defn = match self.view.get(decl_name) {
            Some(ConstantInfo::Defn(v)) => v,
            // A matcher's aux decl is always a plain `def`; anything
            // else here means malformed/inconsistent environment state
            // (untrusted-input posture: never a wrong answer or panic,
            // just "not usable as a matcher").
            _ => return Ok(ReduceMatcherResult::NotMatcher),
        };
        let level_ids = self
            .scratch
            .level_list_at(Some(self.view.store), decl_levels)
            .to_vec();
        if defn.val.level_params.len() != level_ids.len() {
            return Ok(ReduceMatcherResult::NotMatcher);
        }
        let mut f = instantiate_level_params(
            self.scratch,
            Some(self.view.store),
            defn.value,
            &defn.val.level_params,
            &level_ids,
            &mut self.guard,
        )?;
        // oracle :551-553.
        if matches!(
            self.cfg.transparency,
            TransparencyMode::Reducible | TransparencyMode::Instances | TransparencyMode::Implicit
        ) {
            f = self.unfold_nested_dite(f)?;
        }
        let aux_app = self.mk_app_spine(f, &args[..prefix_sz])?;
        let aux_app_type = self.infer_type(aux_app)?;

        // oracle: `forallBoundedTelescope auxAppType info.numAlts fun hs
        // _ => ..` (:555) — the bounded telescope mints one fresh fvar
        // per alternative; `LocalContext::save`/`restore` bracket every
        // exit path (`infer.rs`'s `_body`-split idiom), never leaking a
        // telescope fvar past this call.
        let checkpoint = self.lctx.save();
        let result =
            self.reduce_matcher_telescope(aux_app, aux_app_type, num_alts, prefix_sz, &args);
        self.lctx.restore(checkpoint);
        result
    }

    /// The body of `reduce_matcher`'s bounded telescope (oracle
    /// :555-563, inside `forallBoundedTelescope`'s continuation).
    /// Split out only so `reduce_matcher` can restore the lctx
    /// checkpoint on every exit path (including this method's own
    /// early returns) uniformly.
    fn reduce_matcher_telescope(
        &mut self,
        aux_app: ExprId,
        aux_app_type: ExprId,
        num_alts: usize,
        prefix_sz: usize,
        args: &[ExprId],
    ) -> Result<ReduceMatcherResult, MetaError> {
        let mut hs: Vec<ExprId> = Vec::new();
        let mut cur_ty = aux_app_type;
        for _ in 0..num_alts {
            // `forallTelescopeReducingAuxAux`'s own `reducing := true`
            // branch (Basic.lean:1472-1478, the helper
            // `forallBoundedTelescope` — :1607 — delegates to):
            // whnf when the raw structure runs out of syntactic
            // `Forall`s before `numAlts` binders are minted, rather
            // than assuming the type is already saturated with exactly
            // that many. A well-formed matcher's own declared type
            // always has this shape directly, so this only matters for
            // pathological/rewritten types — included for oracle
            // fidelity, not exercised by this plan's fixture.
            let ty = if matches!(self.node(cur_ty), Node::Forall { .. }) {
                cur_ty
            } else {
                self.whnf(cur_ty)?
            };
            let (binder_name, binder_type, body, binder_info) = match self.node(ty) {
                Node::Forall {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => (binder_name, binder_type, body, binder_info),
                // Fewer than `numAlts` binders available even after
                // whnf: stop early with a short `hs` (the oracle would
                // do the same — `k` just gets called with whatever
                // `fvars` accumulated so far).
                _ => break,
            };
            let d = instantiate_rev(
                self.scratch,
                Some(self.view.store),
                binder_type,
                &hs,
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
            hs.push(fvar);
            cur_ty = body;
        }

        // oracle :556-557: `whnfMatcher (mkAppN auxApp hs)`.
        let applied = self.mk_app_spine(aux_app, &hs)?;
        let whnf_applied = self.whnf_matcher(applied)?;
        let aux_app_fn = self.get_app_fn(whnf_applied);
        for (k, &h) in hs.iter().enumerate() {
            if aux_app_fn == h {
                // oracle :560-563: `mkAppN args[i]! auxApp.getAppArgs`,
                // then the trailing over-application args, then
                // `headBeta`.
                let i = prefix_sz + k;
                let alt_args = self.get_app_args(whnf_applied);
                let mut result = self.mk_app_spine(args[i], &alt_args)?;
                result = self.mk_app_spine(result, &args[prefix_sz + num_alts..])?;
                let result = self.head_beta(result)?;
                return Ok(ReduceMatcherResult::Reduced(result));
            }
        }
        // oracle :564: `.stuck auxApp`.
        Ok(ReduceMatcherResult::Stuck(whnf_applied))
    }

    /// oracle: `whnfMatcher` (WHNF.lean:521-534).
    fn whnf_matcher(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        if matches!(
            self.cfg.transparency,
            TransparencyMode::Reducible | TransparencyMode::Instances | TransparencyMode::Implicit
        ) {
            let saved = self.can_unfold_override;
            self.can_unfold_override = true;
            let r = self.whnf(e);
            self.can_unfold_override = saved;
            r
        } else {
            // oracle :532-533: do NOT use `canUnfoldAtMatcher` here —
            // it would not affect all/default reducibility and would
            // inhibit caching (`unfold_definition`'s gate only swaps
            // predicates when `can_unfold_override` is set, and
            // `cacheable` already keys caching off that same flag —
            // see `metactx.rs`'s own doc on both).
            self.whnf(e)
        }
    }

    /// oracle: `canUnfoldAtMatcher` (WHNF.lean:498-520). Called from
    /// `unfold_definition`'s gate whenever `can_unfold_override` is set
    /// (i.e. only from inside a `whnf_matcher` call).
    pub(crate) fn can_unfold_at_matcher(
        &mut self,
        name: NameId,
        status: ReducibilityStatus,
    ) -> Result<bool, MetaError> {
        if crate::can_unfold(self.cfg.transparency, status) {
            return Ok(true);
        }
        // SEAM: `hasMatchPatternAttribute` (:504-505) — see the module
        // doc's "Named seams" list.
        if self.has_match_pattern_attribute(name) {
            return Ok(true);
        }
        for dotted in MATCHER_UNFOLD_ALLOWLIST {
            if self.intern_dotted(dotted)? == name {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// SEAM: oracle `hasMatchPatternAttribute` (WHNF.lean:504-505) — the
    /// `@[match_pattern]` attribute extension is undecoded by this
    /// plan; revisit when a corpus divergence implicates it
    /// (Mathlib-scale exposure arrives with the nightly in plan 4).
    fn has_match_pattern_attribute(&self, _name: NameId) -> bool {
        false
    }

    /// Intern a dotted name (`"OfNat.ofNat"`, or a bare `"decEq"` with
    /// no dot) against the CURRENT store, resolved through the
    /// persistent base the same way the `#[cfg(test)]` `const_named`
    /// helper does (below) — used by `can_unfold_at_matcher` /
    /// `unfold_nested_dite` to compare a candidate `NameId` against a
    /// small fixed allowlist by identity. Interning is idempotent (the
    /// dedup pool returns the same id on every call past the first),
    /// so rebuilding these names per call rather than caching them as
    /// `MetaCtx` fields is cheap and keeps this task's change scoped to
    /// `whnf.rs`.
    fn intern_dotted(&mut self, dotted: &str) -> Result<NameId, MetaError> {
        let base = Some(self.view.store);
        let mut name = None;
        for part in dotted.split('.') {
            let s = self.scratch.intern_str(base, part)?;
            name = Some(self.scratch.name_str(base, name, s)?);
        }
        Ok(name.expect("MATCHER_UNFOLD_ALLOWLIST entries are non-empty strings"))
    }

    /// oracle: `unfoldNestedDIte` (WHNF.lean:483-495). Unreachable for
    /// this plan's own fixture (`Matcher.lean` has no `dite` at all —
    /// see that file's own module doc), so `expr_contains_const` always
    /// returns `false` here and this is the identity — but transcribed
    /// in full (not stubbed) since it must be correct once a
    /// `dite`-shaped match (numeric/decidable-instance patterns) shows
    /// up in a larger corpus (plan 4).
    fn unfold_nested_dite(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let dite = self.intern_dotted("dite")?;
        if !self.expr_contains_const(e, dite)? {
            return Ok(e);
        }
        self.dite_transform(e, dite)
    }

    /// oracle: `e.find? (fun e => e.isAppOf \`\`dite)` (:484) — does `e`
    /// contain a `Const dite` node ANYWHERE in its subterm tree
    /// (`isAppOf` on a subterm matches its own bare head, so this is
    /// exactly "does `e` contain that `Const` at all", applied or not).
    ///
    /// `step()`/`guarded`-wrapped like every other recursive descent in
    /// this file (`whnf`/`whnf_core`/`get_stuck_mvar`'s own idiom):
    /// unreachable by this plan's own fixture (see `unfold_nested_dite`'s
    /// doc), but real matchers compile TO `dite` (WHNF.lean module doc
    /// :438-467) and this recursion tracks raw AST depth, so it WILL
    /// run on adversarial-depth terms once a larger corpus (plan 4)
    /// exercises it — an unguarded recursion here would be a stack
    /// overflow (a panic-class failure the Global Constraints forbid),
    /// not merely incompleteness.
    fn expr_contains_const(&mut self, e: ExprId, target: NameId) -> Result<bool, MetaError> {
        self.step()?;
        self.guarded(|s| s.expr_contains_const_body(e, target))
    }

    fn expr_contains_const_body(&mut self, e: ExprId, target: NameId) -> Result<bool, MetaError> {
        match self.node(e) {
            Node::Const { name: Some(n), .. } => Ok(n == target),
            Node::App { f, arg } => Ok(
                self.expr_contains_const(f, target)? || self.expr_contains_const(arg, target)?
            ),
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => Ok(self.expr_contains_const(binder_type, target)?
                || self.expr_contains_const(body, target)?),
            Node::LetE {
                ty, value, body, ..
            } => Ok(self.expr_contains_const(ty, target)?
                || self.expr_contains_const(value, target)?
                || self.expr_contains_const(body, target)?),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                self.expr_contains_const(structure, target)
            }
            Node::MData { expr, .. } => self.expr_contains_const(expr, target),
            _ => Ok(false),
        }
    }

    /// oracle: `Core.transform e fun e => ..` (:485-492) — replace
    /// every `Const dite` subterm with `dite`'s own instantiated value,
    /// WITHOUT recursing further into the replacement (`.done`, not
    /// `.continue`): `dite`'s own body cannot itself mention `dite`, so
    /// this is a safety guard against a hypothetical self-referential
    /// rewrite, not something this corpus exercises.
    ///
    /// `step()`/`guarded`-wrapped for the same reason
    /// `expr_contains_const` (above) is: this recursion tracks raw AST
    /// depth and real matchers compile to `dite`-shaped terms, so an
    /// unguarded version of this specific function would be the one
    /// most likely to actually run at Mathlib scale (plan 4).
    fn dite_transform(&mut self, e: ExprId, target: NameId) -> Result<ExprId, MetaError> {
        self.step()?;
        self.guarded(|s| s.dite_transform_body(e, target))
    }

    fn dite_transform_body(&mut self, e: ExprId, target: NameId) -> Result<ExprId, MetaError> {
        match self.node(e) {
            Node::Const {
                name: Some(n),
                levels,
            } if n == target => {
                let defn = match self.view.get(n) {
                    Some(ConstantInfo::Defn(v)) => v,
                    _ => return Ok(e),
                };
                let level_ids = self
                    .scratch
                    .level_list_at(Some(self.view.store), levels)
                    .to_vec();
                if defn.val.level_params.len() != level_ids.len() {
                    return Ok(e);
                }
                Ok(instantiate_level_params(
                    self.scratch,
                    Some(self.view.store),
                    defn.value,
                    &defn.val.level_params,
                    &level_ids,
                    &mut self.guard,
                )?)
            }
            Node::App { f, arg } => {
                let f2 = self.dite_transform(f, target)?;
                let a2 = self.dite_transform(arg, target)?;
                if f2 == f && a2 == arg {
                    Ok(e)
                } else {
                    Ok(self.scratch.expr_app(Some(self.view.store), f2, a2)?)
                }
            }
            Node::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.dite_transform(binder_type, target)?;
                let b2 = self.dite_transform(body, target)?;
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
                let t2 = self.dite_transform(binder_type, target)?;
                let b2 = self.dite_transform(body, target)?;
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
                let t2 = self.dite_transform(ty, target)?;
                let v2 = self.dite_transform(value, target)?;
                let b2 = self.dite_transform(body, target)?;
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
            Node::Proj {
                type_name,
                idx,
                structure,
            } => {
                let s2 = self.dite_transform(structure, target)?;
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
                let s2 = self.dite_transform(structure, target)?;
                if s2 == structure {
                    Ok(e)
                } else {
                    let n = self.scratch.nat_at(Some(self.view.store), idx).clone();
                    Ok(self
                        .scratch
                        .expr_proj(Some(self.view.store), type_name, &n, s2)?)
                }
            }
            Node::MData { data, expr } => {
                let e2 = self.dite_transform(expr, target)?;
                if e2 == expr {
                    Ok(e)
                } else {
                    Ok(self.scratch.expr_mdata(Some(self.view.store), data, e2)?)
                }
            }
            _ => Ok(e),
        }
    }

    /// oracle: `getStuckMVar?` (WHNF.lean:322-378), together with its
    /// `isRecStuck?`/`isQuotRecStuck?` mutual-block siblings
    /// (:295-320). Needed by task 7's smart-unfolding stuck path.
    ///
    /// `instantiateMVars` (:327, :335) is elided: only the HEAD mvar
    /// occurrence is substituted from its own assignment
    /// (`self.mctx.assignment`), not a full deep instantiation of every
    /// mvar occurrence in `e` — same posture as `to_ctor_when_k`'s own
    /// elision (this module, above): sound for this predicate (it can
    /// only under-report a blocking mvar, incompleteness rather than a
    /// wrong answer).
    ///
    /// `getProjectionFnInfo?`/`getAuxParentProjectionInfo?` (:347,
    /// :367) — the class-projection and diamond-inheritance-projection
    /// registries — are SEAMS (see the module doc's "Named seams"
    /// list): always `None`.
    ///
    /// `sunfold_go_match` (task 7's `smartUnfoldingReduce?` port) is its
    /// first real caller.
    pub(crate) fn get_stuck_mvar(&mut self, e: ExprId) -> Result<Option<MVarId>, MetaError> {
        self.step()?;
        self.guarded(|s| s.get_stuck_mvar_body(e))
    }

    fn get_stuck_mvar_body(&mut self, e: ExprId) -> Result<Option<MVarId>, MetaError> {
        match self.node(e) {
            Node::MData { expr, .. } => self.get_stuck_mvar(expr),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                let w = self.whnf(structure)?;
                self.get_stuck_mvar(w)
            }
            Node::MVar { id } => match id.and_then(|i| self.mctx.assignment(MVarId(i))) {
                Some(v) => self.get_stuck_mvar(v),
                None => Ok(id.map(MVarId)),
            },
            Node::App { .. } => {
                let f = self.get_app_fn(e);
                match self.node(f) {
                    Node::MVar { id } => match id.and_then(|i| self.mctx.assignment(MVarId(i))) {
                        Some(assigned) => {
                            let args = self.get_app_args(e);
                            let rebuilt = self.mk_app_spine(assigned, &args)?;
                            match self.node(self.get_app_fn(rebuilt)) {
                                Node::MVar { id: Some(mv) } => Ok(Some(MVarId(mv))),
                                _ => self.get_stuck_mvar(rebuilt),
                            }
                        }
                        None => Ok(id.map(MVarId)),
                    },
                    Node::Const { name: Some(n), .. } => {
                        let args = self.get_app_args(e);
                        match self.view.get(n) {
                            Some(ConstantInfo::Rec(rec_val)) => self.is_rec_stuck(rec_val, &args),
                            Some(ConstantInfo::Quot(qv)) => self.is_quot_rec_stuck(qv, &args),
                            _ => self.get_stuck_mvar_proj_fn(e, f, n, &args),
                        }
                    }
                    Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                        let w = self.whnf(structure)?;
                        self.get_stuck_mvar(w)
                    }
                    _ => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }

    /// oracle: `getStuckMVar?`'s `Const` arm's own fallback (WHNF.lean:
    /// 343-374), reached once neither `Rec`/`Quot` matched `n`. `e` is
    /// the WHOLE application (`f` applied to `args`); `f`/`n`/`args` are
    /// the SAME decomposition `get_stuck_mvar_body`'s caller already
    /// computed, passed through rather than re-derived.
    ///
    /// `unless e.hasExprMVar do return none` (:344) — a bare `Const`
    /// (`Node::Const`, no mvar anywhere in `f` itself) can still have an
    /// mvar buried in `args`, so this checks the WHOLE app `e`'s cached
    /// bit, not just `f`'s.
    ///
    /// `getAuxParentProjectionInfo?` (:367) — the diamond-inheritance
    /// auxiliary-parent-projection registry — is a SEAM this task does
    /// not decode (out of scope: the brief names only
    /// `projection_fns`/`ProjectionFnInfo`, PR-A's own decode of
    /// `projectionFnInfoExt`, never the separate
    /// `getAuxParentProjectionInfo?` extension). Always `None` there,
    /// same posture the module doc's "Named seams" list already
    /// recorded for this whole branch before this task landed —
    /// incompleteness only: a diamond-inheritance-shaped stuck term
    /// simply is not detected as stuck (falls through to the whnf
    /// caller's own generic "irreducible, return unchanged" answer),
    /// never a wrong verdict.
    fn get_stuck_mvar_proj_fn(
        &mut self,
        e: ExprId,
        f: ExprId,
        n: NameId,
        args: &[ExprId],
    ) -> Result<Option<MVarId>, MetaError> {
        if !self.data(e).has_expr_mvar() {
            return Ok(None);
        }
        let Some(info) = self.projection_fns.get(&n).cloned() else {
            // SEAM: `getAuxParentProjectionInfo?` (see this method's doc).
            return Ok(None);
        };
        if !info.from_class {
            return Ok(None);
        }
        // oracle :350-353: "First check whether `e`'s instance is
        // stuck" -- `args[projInfo.numParams]?`, `whnf`'d, then
        // recursed into (NOT the raw arg -- `is_rec_stuck`'s own major-
        // arg convention, above, does the same `whnf`-before-recurse).
        if let Some(&major) = args.get(info.num_params) {
            let w = self.whnf(major)?;
            if let Some(mv) = self.get_stuck_mvar(w)? {
                return Ok(Some(mv));
            }
        }
        // oracle :354-364: "recurse on the explicit arguments" -- zip
        // `f`'s own `ParamInfo`s (here: `param_binder_infos`, B1/B2's
        // `discr_path.rs` primitive, widened `pub(crate)` for this
        // reuse -- see that method's own doc) against `args`, stopping
        // at whichever is shorter (`param_binder_infos(f, args.len())`
        // already caps its own output at `args.len()`, reproducing the
        // oracle's `for .. in .., .. in ..` zip exactly). Each EXPLICIT
        // position (`BinderInfo::Default`, `ParamInfo.isExplicit`,
        // `Meta/Basic.lean:291-292`) is recursed into RAW (no `whnf`
        // first -- unlike the major-instance-arg check just above).
        let infos = self.param_binder_infos(f, args.len())?;
        for (i, &a) in args.iter().enumerate() {
            if matches!(infos.get(i), Some(BinderInfo::Default)) {
                if let Some(mv) = self.get_stuck_mvar(a)? {
                    return Ok(Some(mv));
                }
            }
        }
        Ok(None)
    }

    /// oracle: `isRecStuck?` (WHNF.lean:295-306).
    fn is_rec_stuck(
        &mut self,
        rec_val: &RecursorVal,
        args: &[ExprId],
    ) -> Result<Option<MVarId>, MetaError> {
        if rec_val.k {
            // oracle TODO (:297: "improve this case") — always none.
            return Ok(None);
        }
        let major_idx = match (
            rec_val.num_params.to_usize(),
            rec_val.num_motives.to_usize(),
            rec_val.num_minors.to_usize(),
            rec_val.num_indices.to_usize(),
        ) {
            (Some(a), Some(b), Some(c), Some(d)) => a + b + c + d,
            _ => return Ok(None),
        };
        if major_idx >= args.len() {
            return Ok(None);
        }
        let major = self.whnf(args[major_idx])?;
        self.get_stuck_mvar(major)
    }

    /// oracle: `isQuotRecStuck?` (WHNF.lean:308-319). Same `majorPos`
    /// values as `reduce_quot_rec`, above.
    fn is_quot_rec_stuck(
        &mut self,
        quot_val: &QuotVal,
        args: &[ExprId],
    ) -> Result<Option<MVarId>, MetaError> {
        let pos = match quot_val.kind {
            QuotKind::Lift => 5usize,
            QuotKind::Ind => 4usize,
            _ => return Ok(None),
        };
        if pos >= args.len() {
            return Ok(None);
        }
        let major = self.whnf(args[pos])?;
        self.get_stuck_mvar(major)
    }

    /// oracle: `mkSmartUnfoldingNameFor` (WHNF.lean:50-51) —
    /// `Name.mkStr declName smartUnfoldingSuffix` (`smartUnfoldingSuffix
    /// := "_sunfold"`, :49). `Name.mkStr` APPENDS a NEW component onto
    /// `declName` (this is not string concatenation on the last
    /// component) — `f._sunfold` is `f ++ "_sunfold"` as its own name
    /// component, built via the bank's own `name_str`, the same
    /// primitive `mk_name2`/`intern_dotted` (above) use for every other
    /// multi-part name in this file.
    fn smart_unfolding_name_for(&mut self, decl_name: NameId) -> Result<NameId, MetaError> {
        let base = Some(self.view.store);
        let s = self.scratch.intern_str(base, "_sunfold")?;
        Ok(self.scratch.name_str(base, Some(decl_name), s)?)
    }

    /// oracle: `Expr.annotation?` (`Expr.lean:2096-2100`) — `e = .mdata d
    /// b` where `d.size == 1 && d.getBool kind false`; reconciled
    /// against THIS bank's `KVMapRow` shape (`Store::kvmap_at`) rather
    /// than rebuilding a full `leanr_kernel::KVMap` via the (Arc-
    /// bridging) `Store::to_kvmap`, since only a length-1, single-key,
    /// `DataValueRow::Bool(true)` shape is ever tested for here — the
    /// two `mkAnnotation` kinds `smartUnfoldingReduce?` reads
    /// (`` `sunfoldMatch ``/`` `sunfoldMatchAlt ``, WHNF.lean:64-70).
    /// Returns the annotation's INNER expression (`b`), matching
    /// `annotation?`'s own `some b`, not the whole `MData` node.
    pub(crate) fn annotation(&self, e: ExprId, kind: NameId) -> Option<ExprId> {
        match self.node(e) {
            Node::MData { data, expr } => {
                let row = self.scratch.kvmap_at(Some(self.view.store), data);
                match row.0.as_ref() {
                    [(Some(k), DataValueRow::Bool(true))] if *k == kind => Some(expr),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// oracle `Meta.synthPending` (`Basic.lean:840`, `@[extern
    /// "lean_synth_pending"] protected opaque synthPending : MVarId →
    /// MetaM Bool`), extern-swapped for its real implementation,
    /// `synthPendingImp` (`SynthInstance.lean:1031-1061`) — attempts to
    /// resolve a PENDING typeclass-synthesis problem blocking a stuck
    /// metavariable, now that B4/B5's tabled synthesis engine
    /// (`synth_instance`) exists. Four oracle conditions, all modeled
    /// (task B6 — the brief's own paraphrase names only the third; the
    /// other three are this method's own read of the real source):
    ///
    /// 1. `withIncRecDepth` (:1033) — the general `MetaM` recursion-depth
    ///    guard: `self.guarded` around the whole body (`guard_depth` /
    ///    `MAX_REC_DEPTH`, `metactx.rs`), the SAME mechanism every other
    ///    `MetaM`-shaped entry point in this crate already uses. This is
    ///    what actually bounds the `synth_pending` → `synth_instance` →
    ///    `is_def_eq` → `whnf` → `synth_pending` cycle the task brief
    ///    warns about: each hop through that cycle is itself wrapped in
    ///    a `guarded` call (`synth_instance`'s own `self.guarded`,
    ///    `synth.rs:1564`), so `guard_depth` strictly increases per lap
    ///    and the cycle terminates in a bounded, deterministic
    ///    `MetaError::DepthBudgetExhausted` rather than a stack overflow.
    /// 2. `mvarDecl.kind matches .syntheticOpaque => return false`
    ///    (:1035-1036) — a syntheticOpaque mvar is never resolved by
    ///    unification/synthesis, only by the elaborator that created it
    ///    (`MVarKind`'s own doc, `mvar_ctx.rs`); modeled identically.
    /// 3. `isClass? mvarDecl.type` (:1040-1042) — SEAM: approximated as
    ///    "`get_app_fn` of the mvar's declared type is a `Const`" (no
    ///    independent class registry exists anywhere in this crate to
    ///    confirm that `Const` truly names a REGISTERED class — the same
    ///    posture `discr_path.rs`'s and `lazy_delta.rs`'s own
    ///    `isClass?`/`isClass` seams already document).
    ///
    ///    **Correction (opus review, round 1): the direction is NOT
    ///    "strictly more, never fewer" — an earlier draft of this doc
    ///    claimed that, and it is false.** The real oracle predicate is
    ///    wider than a bare `Const`-head test in BOTH directions, not
    ///    just one: `isClassQuick?` (`Basic.lean:1366`) recurses through
    ///    `.forallE` binders (so `∀ α, Inhabited α` IS a class type to
    ///    the oracle, but its head is a `Forall`, never a `Const`), and
    ///    `isClassExpensive?` (:1520-1522, reached whenever the quick
    ///    check is inconclusive) runs `forallTelescopeReducingAux ..
    ///    (whnfType := true)` BEFORE its own `isClassApp?` check (so a
    ///    `.letE`-/`.proj`-headed type, or one that only reduces to a
    ///    class head under `whnf`, also counts to the oracle —
    ///    `Basic.lean:1358-1381,1508-1528`). So this seam actually
    ///    diverges in both directions at once:
    ///    - WIDER than the oracle on plain `Const`-headed NON-class
    ///      types (e.g. `N`, `Eq a b`): the oracle's `isClassApp?`
    ///      rejects these after checking the real class-extension
    ///      registry (`Basic.lean:1350-1356,1510-1518`), while this approximation
    ///      accepts any `Const` head unconditionally;
    ///    - NARROWER than the oracle on pi-/`letE`-/`proj`-headed types
    ///      and on types that only reduce to a class head under `whnf`:
    ///      the oracle accepts these (`Basic.lean:1366,1508-1528`), but
    ///      a `Forall`/`LetE`/`Proj` node handed to `get_app_fn` is never
    ///      a `Const` node, so this approximation rejects all of them.
    ///
    ///    Both directions are still safe overall — the failure mode is
    ///    always incompleteness-or-refusal, never a wrong synthesis —
    ///    but for two DIFFERENT reasons, not one shared one:
    ///    - the WIDER direction is safe because `InstanceTable`'s
    ///      discrimination tree is keyed ONLY by real class `Const`s
    ///      (every key comes from `mk_path` on some registered
    ///      INSTANCE's own declared type, `instances.rs`'s
    ///      `InstanceTable::build`), so a query under a non-class
    ///      `Const` name structurally cannot match any stored candidate
    ///      — `synth_instance` itself returns `Ok(None)`, the exact same
    ///      `false` outcome the oracle's own quick check would have
    ///      produced, just reached one call layer further in (never a
    ///      WRONG synthesis result, only extra unproductive work);
    ///    - the NARROWER direction is safe because refusing to even
    ///      ATTEMPT a legitimate pending synthesis is pure incompleteness
    ///      (the oracle would have made progress here; this crate leaves
    ///      the mvar unresolved and returns `false` instead) — the same
    ///      "refuse rather than guess" posture every other named seam in
    ///      this module already takes, never a wrong verdict.
    ///
    ///    `instantiateMVars` (also :1040, folded into `isClass?`'s own
    ///    argument) is elided per this module's established posture
    ///    elsewhere (`get_stuck_mvar`'s own doc): only a bare head-mvar
    ///    dereference is threaded through here (via `mctx.decl`'s
    ///    already-fully-substituted `ty`, since a metavariable's
    ///    DECLARED type is fixed at `declare` time and never itself
    ///    carries a not-yet-assigned "outer" mvar-of-a-mvar layer worth
    ///    chasing beyond what `get_app_fn` alone already sees).
    /// 4. `synthPendingDepth > maxSynthPendingDepth` (:1044-1048) — this
    ///    crate's own `synth_pending_depth` counter against
    ///    `MAX_SYNTH_PENDING_DEPTH` (both above), bumped for the
    ///    DURATION of the `synth_instance` attempt exactly as
    ///    `withIncSynthPending` (:1177) scopes it — a SEPARATE, much
    ///    tighter bound than `guard_depth`'s (condition 1's own doc
    ///    explains why the two must not be conflated).
    ///
    /// `mvarId.withContext` (`SynthInstance.lean:1033`) — NAMED SEAM
    /// (opus review round 1; not previously called out): the oracle
    /// runs the WHOLE `synthPendingImp` body under `mvarDecl.lctx` (the
    /// mvar's OWN local context at declaration time), not whatever local
    /// context happens to be ambient at the call site. This method never
    /// swaps `self.lctx` to `decl.lctx` before calling `synth_instance`
    /// below — a silent drop, not an undecoded-oracle-feature gap:
    /// `MVarDecl.lctx` (`mvar_ctx.rs`) carries exactly this context, and
    /// `assign.rs:734` (`mk_aux_mvar_for`) already has precedent for
    /// consulting it. Effect: incompleteness only (a subgoal needing a
    /// local hypothesis visible only under the mvar's OWN context, not
    /// the ambient one, may fail to synthesize where the oracle would
    /// have succeeded) — never a wrong synthesis, since a term assigned
    /// under a mismatched local context would fail the kernel's own
    /// re-check rather than pass it silently.
    ///
    /// `catchInternalId isDefEqStuckExceptionId` (:1052) is NOT
    /// replicated here — NAMED SEAM (see the module doc's "Named seams"
    /// list, above, for the full citation and owner): `IsDefEqStuck` is
    /// this crate's own typed `MetaError` variant, not an internal
    /// exception id, and this method's `?` on `synth_instance`'s result
    /// PROPAGATES it untouched rather than catching it and returning
    /// `false` the way the oracle's own `catch _ => pure none` does.
    /// Direction: safe (an `Err` surfaces where the oracle would have
    /// produced an `Ok` ANSWER, never a WRONG one) — but this crate's own
    /// discipline (Global Constraints: `IsDefEqStuck` never collapses to
    /// `false`) is a reason NOT to fix this by catching it here, not a
    /// reason the divergence isn't real: a caller expecting bit-for-bit
    /// oracle control flow will observe an `Err` where the oracle returns
    /// `Ok(false)`.
    ///
    /// The final `mvarId.isAssigned` re-check (:1057-1058) is folded into
    /// an UPFRONT short-circuit here instead (`synth_pending`, below,
    /// checks `is_assigned` before even reading `mvarDecl`): the oracle
    /// itself has no such upfront check (its own call sites, `getStuckMVar?`'s
    /// `.mvar` arm and `WHNF.lean:773`, only ever pass an UNASSIGNED mvar
    /// by construction, so the check never actually fires there before
    /// synthesis), but on an ALREADY-assigned mvar the oracle would run
    /// the whole synthesis attempt and then return `false` at this exact
    /// final check anyway — same answer, strictly less work, and the
    /// FINAL check is kept too (a nested `synth_instance` call could in
    /// principle assign this SAME mvar via its own subgoal unification
    /// before returning here) so double-assignment is impossible either
    /// way.
    fn synth_pending(&mut self, mvar: MVarId) -> Result<bool, MetaError> {
        self.guarded(|s| s.synth_pending_body(mvar))
    }

    fn synth_pending_body(&mut self, mvar: MVarId) -> Result<bool, MetaError> {
        if self.mctx.is_assigned(mvar) {
            return Ok(false);
        }
        // oracle: `mvarId.getDecl` (`MetavarContext.lean`) THROWS
        // `throwUnknownMVarAt` on an undeclared mvar rather than
        // returning `false` — reconciled here (opus review round 1;
        // every OTHER `false` in this method carries an oracle line,
        // this one used to carry none). `get_stuck_mvar`'s `Node::MVar
        // { id }` arm (this module) can hand back an id that was never
        // `declare`d in THIS `MetavarContext` (e.g. a bank `MVar` node
        // reached by traversal that this crate itself never minted), so
        // the case is real, not merely hypothetical. Reuses the crate's
        // existing "caller-bug" error variant (`MetaError::MVar`, the
        // SAME one `assign.rs`/`synth.rs` already raise for this exact
        // oracle exception) rather than inventing a new one.
        let Some(decl) = self.mctx.decl(mvar) else {
            return Err(MetaError::MVar(format!(
                "synth_pending: mvar {mvar:?} is not declared"
            )));
        };
        if decl.kind == MVarKind::SyntheticOpaque {
            return Ok(false);
        }
        let ty = decl.ty;
        // SEAM (condition 3, doc above): "is a class" approximated as
        // "concrete `Const` head".
        if !matches!(
            self.node(self.get_app_fn(ty)),
            Node::Const { name: Some(_), .. }
        ) {
            return Ok(false);
        }
        if self.synth_pending_depth > MAX_SYNTH_PENDING_DEPTH {
            return Ok(false);
        }
        // `synth_instance` (B5, `synth.rs`) already wraps ITSELF in
        // `self.guarded` (its own `withIncRecDepth`-equivalent, one
        // `guard_depth` bump per attempt) -- calling it directly here,
        // rather than wrapping it in a SECOND `guarded`, matches the
        // oracle exactly: `synthPendingImp` (:1033) has exactly ONE
        // `withIncRecDepth`, around the WHOLE function (this method's
        // own outer `self.guarded` call, above), not a second one
        // around just the `synthInstance?` sub-call.
        self.synth_pending_depth += 1;
        let val = self.synth_instance(ty);
        self.synth_pending_depth -= 1;
        match val? {
            None => Ok(false),
            Some(val) => {
                if self.mctx.is_assigned(mvar) {
                    return Ok(false);
                }
                self.mctx.assign(mvar, val)?;
                Ok(true)
            }
        }
    }

    /// oracle: `smartUnfoldingReduce?` (WHNF.lean:747-776) — entry
    /// point; `go`/`goMatch` are its `where`-clause mutual helpers,
    /// split below into `sunfold_go`/`sunfold_go_match` (each
    /// step+guarded, the `expr_contains_const`/`dite_transform` idiom
    /// this file already uses for every other adversarial-depth
    /// recursion).
    pub fn smart_unfolding_reduce(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        self.sunfold_go(e)
    }

    fn sunfold_go(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        self.step()?;
        self.guarded(|s| s.sunfold_go_body(e))
    }

    /// oracle: `go` (WHNF.lean:750-761). `None` propagates from any
    /// child (the `OptionT` monad's `failure`); every non-failing arm
    /// rebuilds via the SAME store constructors the rest of this file
    /// uses (never `Store::to_expr`).
    fn sunfold_go_body(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        match self.node(e) {
            // oracle :752: `mapLetDecl n t (← go v) (nondep := nondep)
            // fun x => go (b.instantiate1 x)` — `t` itself is NEVER
            // recursed into (only `v` is), matching the oracle exactly.
            Node::LetE {
                decl_name,
                ty,
                value,
                body,
                non_dep,
            } => {
                let v2 = match self.sunfold_go(value)? {
                    Some(v) => v,
                    None => return Ok(None),
                };
                let checkpoint = self.lctx.save();
                let r = self.sunfold_go_let(decl_name, ty, v2, body, non_dep);
                self.lctx.restore(checkpoint);
                r
            }
            // oracle :753: `lambdaTelescope e fun xs b => mkLambdaFVars
            // xs (← go b)` — mints one fvar per LEADING `Lam` binder
            // only (never descends through a `LetE`, unlike
            // `infer_lambda_body`'s mixed telescope); save/restore
            // brackets the mint (`reduce_matcher`'s own idiom, above).
            Node::Lam { .. } => {
                let checkpoint = self.lctx.save();
                let r = self.sunfold_go_lam(e);
                self.lctx.restore(checkpoint);
                r
            }
            Node::App { f, arg } => {
                let f2 = match self.sunfold_go(f)? {
                    Some(v) => v,
                    None => return Ok(None),
                };
                let a2 = match self.sunfold_go(arg)? {
                    Some(v) => v,
                    None => return Ok(None),
                };
                Ok(Some(self.scratch.expr_app(
                    Some(self.view.store),
                    f2,
                    a2,
                )?))
            }
            Node::Proj {
                type_name,
                idx,
                structure,
            } => {
                let s2 = match self.sunfold_go(structure)? {
                    Some(v) => v,
                    None => return Ok(None),
                };
                Ok(Some(self.scratch.expr_proj(
                    Some(self.view.store),
                    type_name,
                    &Nat::from(idx as u64),
                    s2,
                )?))
            }
            Node::ProjBig {
                type_name,
                idx,
                structure,
            } => {
                let s2 = match self.sunfold_go(structure)? {
                    Some(v) => v,
                    None => return Ok(None),
                };
                let n = self.scratch.nat_at(Some(self.view.store), idx).clone();
                Ok(Some(self.scratch.expr_proj(
                    Some(self.view.store),
                    type_name,
                    &n,
                    s2,
                )?))
            }
            // oracle :756-760: `sunfoldMatch`-annotated => `goMatch`;
            // else recurse into the mdata's own child and rewrap.
            Node::MData { data, expr } => {
                if let Some(m) = self.annotation(e, self.sunfold_match) {
                    self.sunfold_go_match(m)
                } else {
                    let b2 = match self.sunfold_go(expr)? {
                        Some(v) => v,
                        None => return Ok(None),
                    };
                    Ok(Some(self.scratch.expr_mdata(
                        Some(self.view.store),
                        data,
                        b2,
                    )?))
                }
            }
            // oracle :761: `| _ => return e` — every other node shape
            // (leaves: `Const`/`Sort`/`FVar`/`MVar`/`BVar`/`Lit*`/
            // `Forall`) is returned unchanged.
            _ => Ok(Some(e)),
        }
    }

    /// The body of `sunfold_go`'s `LetE` arm: oracle `mapLetDecl`
    /// (`Basic.lean:1925-1927`) = `withLetDecl` (mint a genuine let-fvar
    /// in `lctx`, mirroring `infer_lambda_body`'s own `mk_let_decl`
    /// call) then `mkLetFVars (usedLetOnly := true) (generalizeNondepLet
    /// := false) #[x] result` — abstract the fvar back out; if it never
    /// occurs in the (already go'd) result, DROP the let entirely
    /// (`result` is already correct as-is), else rewrap as a `LetE`
    /// preserving the original `non_dep`. Same "abstract, compare
    /// against the pre-abstraction value" idiom as `infer.rs`'s
    /// `rebuild_forall`.
    fn sunfold_go_let(
        &mut self,
        decl_name: Option<NameId>,
        ty: ExprId,
        value: ExprId,
        body: ExprId,
        non_dep: bool,
    ) -> Result<Option<ExprId>, MetaError> {
        let fvar = self.lctx.mk_let_decl(
            self.scratch,
            Some(self.view.store),
            &mut self.fvar_gen,
            decl_name,
            ty,
            value,
        )?;
        let inst_body = instantiate(
            self.scratch,
            Some(self.view.store),
            body,
            fvar,
            &mut self.guard,
        )?;
        let r = match self.sunfold_go(inst_body)? {
            Some(v) => v,
            None => return Ok(None),
        };
        let abstracted = abstract_fvars(
            self.scratch,
            Some(self.view.store),
            r,
            std::slice::from_ref(&fvar),
            &mut self.guard,
        )?;
        if abstracted == r {
            // `fvar` did not occur in `r`: unused let, drop it (`r` is
            // already fvar-free and correct as-is).
            Ok(Some(r))
        } else {
            Ok(Some(self.scratch.expr_let(
                Some(self.view.store),
                decl_name,
                ty,
                value,
                abstracted,
                non_dep,
            )?))
        }
    }

    /// The body of `sunfold_go`'s `Lam` arm: peel every LEADING `Lam`
    /// binder with a fresh fvar (oracle `lambdaTelescope`'s own
    /// `Lam`-only walk — never a `LetE`), recurse `go` on the fully-
    /// instantiated body, then rebuild via `rebuild_lambda`.
    fn sunfold_go_lam(&mut self, e0: ExprId) -> Result<Option<ExprId>, MetaError> {
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut e = e0;
        while let Node::Lam {
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
        let r = match self.sunfold_go(inst)? {
            Some(v) => v,
            None => return Ok(None),
        };
        self.rebuild_lambda(&fvars, r)
    }

    /// oracle: `mkLambdaFVars xs r` (used only by `sunfold_go_lam`,
    /// above — the other telescopes in this crate rebuild `Forall`/
    /// `Let` shapes, not `Lam`). Unlike `infer.rs`'s `rebuild_forall`,
    /// there is no unused-binder elision here (`mkLambdaFVars` has none,
    /// unlike `mkForallFVars`'s let-case): every fvar is unconditionally
    /// re-wrapped as a `Lam`, innermost first.
    fn rebuild_lambda(
        &mut self,
        fvars: &[ExprId],
        body: ExprId,
    ) -> Result<Option<ExprId>, MetaError> {
        let mut r = body;
        let mut i = fvars.len();
        while i > 0 {
            i -= 1;
            let (binder_name, ty, binder_info) = match self.node(fvars[i]) {
                Node::FVar { id: Some(id) } => {
                    let decl = self.lctx.get(id).ok_or_else(|| {
                        MetaError::Infer("sunfold_go: telescope fvar not declared".into())
                    })?;
                    (decl.binder_name, decl.ty, decl.binder_info)
                }
                _ => {
                    return Err(MetaError::Infer(
                        "sunfold_go: telescope entry is not an fvar".into(),
                    ))
                }
            };
            r = abstract_fvars(
                self.scratch,
                Some(self.view.store),
                r,
                std::slice::from_ref(&fvars[i]),
                &mut self.guard,
            )?;
            let ty2 = abstract_fvars(
                self.scratch,
                Some(self.view.store),
                ty,
                &fvars[..i],
                &mut self.guard,
            )?;
            r = self
                .scratch
                .expr_lam(Some(self.view.store), binder_name, ty2, r, binder_info)?;
        }
        Ok(Some(r))
    }

    fn sunfold_go_match(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        self.step()?;
        self.guarded(|s| s.sunfold_go_match_body(e))
    }

    /// oracle: `goMatch` (WHNF.lean:763-776).
    fn sunfold_go_match_body(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        match self.reduce_matcher(e)? {
            ReduceMatcherResult::Reduced(r) => {
                // oracle :766-769: if the REDUCED VALUE itself carries
                // the `sunfoldMatchAlt` marker, stop here and return it
                // as-is (interrupted, per the module doc above
                // `smartUnfoldingReduce?`'s own doc comment) — else keep
                // reducing (`go e`, an equation compiler leaf may itself
                // contain another nested annotated match).
                match self.annotation(r, self.sunfold_match_alt) {
                    Some(alt) => Ok(Some(alt)),
                    None => self.sunfold_go(r),
                }
            }
            ReduceMatcherResult::Stuck(e_prime) => {
                let mv = match self.get_stuck_mvar(e_prime)? {
                    Some(m) => m,
                    None => return Ok(None),
                };
                if self.synth_pending(mv)? {
                    self.sunfold_go_match(e)
                } else {
                    Ok(None)
                }
            }
            ReduceMatcherResult::NotMatcher | ReduceMatcherResult::PartialApp => Ok(None),
        }
    }

    /// Multi-binder beta step: consume as many leading `Lam` binders of
    /// `f` as `args` allows (partial application: apply what's left over
    /// once `f`'s lambdas run out, or leave a residual `Lam` if `args`
    /// runs out first). oracle: `Expr.betaRev` (`Expr.lean:1592-1617`,
    /// called with its `useZeta`/`preserveMData` defaults `false`/
    /// `false`), used by both `whnfCore`'s beta arm (WHNF.lean:678-680)
    /// and `deltaBetaDefinition` (WHNF.lean:423-430, via
    /// `unfold_definition` below). This is the SAME recurrence as
    /// `leanr_kernel::tc::TypeChecker::whnf_core`'s own inline multi-
    /// lambda beta step (tc.rs:1479-1505, the kernel's representation
    /// twin of this exact operation) — ported here rather than shared
    /// because that method is private to the kernel crate; verified
    /// against `Expr.lean`'s own worked examples (`betaRev (fun x y =>
    /// t x y) #[a] ==> fun y => t a y`, etc.).
    ///
    /// `pub(crate)`: task 9's `infer.rs::ibr_app` (the
    /// `instantiate_beta_rev` divergence fix, oracle:
    /// `instantiateBetaRevRange`'s App arm calling `head.betaRev
    /// revArgs`, InferType.lean:91) reuses this SAME function rather
    /// than duplicating it — one oracle-cited `Expr.betaRev`
    /// transcription, not two.
    pub(crate) fn beta_rev(&mut self, f: ExprId, args: &[ExprId]) -> Result<ExprId, MetaError> {
        if args.is_empty() {
            return Ok(f);
        }
        let num_args = args.len();
        let mut m = 1usize;
        let mut cur = f;
        loop {
            let deeper = match self.node(cur) {
                Node::Lam { body, .. }
                    if matches!(self.node(body), Node::Lam { .. }) && m < num_args =>
                {
                    body
                }
                _ => break,
            };
            cur = deeper;
            m += 1;
        }
        let body = match self.node(cur) {
            Node::Lam { body, .. } => body,
            // `f` was not itself a `Lam` (only reachable from
            // `unfold_definition`'s applied case, whose value need not
            // be lambda-headed) — no beta possible, apply all args.
            _ => return self.mk_app_spine(f, args),
        };
        let inst = instantiate_rev(
            self.scratch,
            Some(self.view.store),
            body,
            &args[0..m],
            &mut self.guard,
        )?;
        self.mk_app_spine(inst, &args[m..num_args])
    }

    /// oracle: `Expr.headBeta` (Expr.lean:1657-1659), via
    /// `isHeadBetaTargetFn false` (Expr.lean:1650-1654). Only the `Lam`
    /// case is modeled — same simplification `whnf_core_app`'s own beta
    /// arm (above) already makes for this file's other beta sites: an
    /// `MData`-wrapped lambda head is not exercised by any corpus this
    /// plan targets. Used by `reduce_matcher_telescope`'s `Reduced` arm
    /// (oracle :563: `result.headBeta`). `pub(crate)`, not private (task
    /// 7): `assign.rs::process_assignment_fo_approx`'s own loop (oracle:
    /// `processAssignmentFOApprox`, ExprDefEq.lean:1211, `let v :=
    /// v.headBeta`) needs the exact same primitive.
    pub(crate) fn head_beta(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let f = self.get_app_fn(e);
        if matches!(self.node(f), Node::Lam { .. }) {
            let args = self.get_app_args(e);
            self.beta_rev(f, &args)
        } else {
            Ok(e)
        }
    }

    /// oracle: `whnfCore`'s `.proj` arm (WHNF.lean:704-714).
    fn whnf_core_proj(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let (idx, structure) = match self.node(e) {
            Node::Proj { idx, structure, .. } => (idx as usize, structure),
            Node::ProjBig { idx, structure, .. } => {
                let n = self.scratch.nat_at(Some(self.view.store), idx).clone();
                match n.to_usize() {
                    Some(v) => (v, structure),
                    None => return Ok(e),
                }
            }
            _ => unreachable!("whnf_core_proj: caller already matched Proj/ProjBig"),
        };
        let reduced_c = match self.cfg.proj {
            ProjReduction::No => return Ok(e),
            ProjReduction::Yes => self.whnf_core(structure)?,
            ProjReduction::YesWithDelta => self.whnf(structure)?,
            ProjReduction::YesWithDeltaI => self.whnf_at_most_i(structure)?,
        };
        match self.project_core(reduced_c, idx)? {
            Some(v) => self.whnf_core(v),
            None => Ok(e),
        }
    }

    /// oracle: `whnfAtMostI` (Basic.lean:2124-2128) — `whnf` capped at
    /// `.instances` transparency: downgrades only when the ambient
    /// transparency is ABOVE `.instances` (`all`/`default`/`implicit`),
    /// i.e. `min(saved, .instances)` by rank; leaves `.reducible`/
    /// `.instances`/`.none` untouched.
    ///
    /// TIER-1 CORPUS EXCLUSION: this path is only reachable via
    /// `whnf_core_proj` when `cfg.proj == ProjReduction::YesWithDeltaI`,
    /// but `Config::default`'s `proj` is `YesWithDelta` and no tier-1
    /// corpus query overrides it — so no fixture replayed by `mise run
    /// meta:fast` ever sets `YesWithDeltaI`, and this path has zero
    /// coverage from the fast corpus gate. It is exercised only by this
    /// module's hand-built `whnf_at_most_i`/`YesWithDeltaI` unit
    /// test(s), which hand-insert reducibility entries the way
    /// `delta_respects_transparency` does. Plan 4's nightly should not
    /// expect this path to be reachable from the tier-1 corpus.
    fn whnf_at_most_i(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let saved = self.cfg.transparency;
        if saved > TransparencyMode::Instances {
            self.set_transparency(TransparencyMode::Instances);
        }
        let r = self.whnf(e);
        self.set_transparency(saved);
        r
    }

    /// oracle: `whnfD` (Basic.lean:2116-2118) — `whnf` forced to
    /// `.default` transparency regardless of the ambient config,
    /// restored after. Used by `to_ctor_when_structure`'s "no eta for
    /// propositions" check (WHNF.lean:194); `pub(crate)` (task 6) so
    /// `lazy_delta.rs`'s `isDefEqEta`/`isProp` (:172, `isDefEqEta`'s own
    /// `whnfD bType`, and `isProp`'s `whnfD type`) can reuse it too.
    pub(crate) fn whnf_default(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let saved = self.cfg.transparency;
        self.set_transparency(TransparencyMode::Default);
        let r = self.whnf(e);
        self.set_transparency(saved);
        r
    }

    /// oracle: `projectCore?` (WHNF.lean:564-572). `pub(crate)` (task 6):
    /// `lazy_delta.rs`'s `isDefEqProjDelta` (`tryReduceProjs`, :2126-2129)
    /// reuses this same primitive.
    pub(crate) fn project_core(
        &mut self,
        c: ExprId,
        i: usize,
    ) -> Result<Option<ExprId>, MetaError> {
        let c = self.to_ctor_if_lit(c)?;
        let head = self.get_app_fn(c);
        let ctor_val = match self.node(head) {
            Node::Const { name: Some(n), .. } => match self.view.get(n) {
                Some(ConstantInfo::Ctor(v)) => v,
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };
        let nparams = match ctor_val.num_params.to_usize() {
            Some(v) => v,
            None => return Ok(None),
        };
        let idx = nparams + i;
        let args = self.get_app_args(c);
        if idx < args.len() {
            Ok(Some(args[idx]))
        } else {
            Ok(None)
        }
    }

    /// oracle: `Expr.toCtorIfLit` (WHNF.lean:23-29). The `LitStr` arm is
    /// a SEAM (returns unchanged): building `String.ofList` over a
    /// char-list literal (:27-28) has no tier-1 corpus query needing it
    /// yet. `pub(crate)` (task 6): `lazy_delta.rs`'s `isDefEqStringLit`
    /// (:202-209) calls this directly on its productive (`LitStr` vs
    /// `String.ofList`) arm — still gated by this same seam until it is
    /// filled in (see that function's own doc comment).
    #[allow(clippy::wrong_self_convention)] // oracle name; reduces `self`
    pub(crate) fn to_ctor_if_lit(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        match self.node(e) {
            Node::LitNat { v } => {
                let n = self.scratch.nat_at(Some(self.view.store), v).clone();
                if n.is_zero() {
                    let no_levels = self.scratch.intern_level_list(Some(self.view.store), &[])?;
                    Ok(self.scratch.expr_const(
                        Some(self.view.store),
                        Some(self.nat_zero),
                        no_levels,
                    )?)
                } else {
                    let pred = n.sub(&Nat::from(1u64));
                    let pred_e = self.scratch.expr_lit_nat(Some(self.view.store), &pred)?;
                    let no_levels = self.scratch.intern_level_list(Some(self.view.store), &[])?;
                    let succ = self.scratch.expr_const(
                        Some(self.view.store),
                        Some(self.nat_succ),
                        no_levels,
                    )?;
                    Ok(self.scratch.expr_app(Some(self.view.store), succ, pred_e)?)
                }
            }
            Node::LitStr { .. } => Ok(e),
            _ => Ok(e),
        }
    }

    /// oracle: `reduceRec` (WHNF.lean:228-263). Major-premise index per
    /// `RecursorVal.getMajorIdx` (`Declaration.lean:394-395`:
    /// `numParams+numMotives+numMinors+numIndices`) — no existing helper
    /// on this crate's own `RecursorVal`, computed inline; matches
    /// `leanr_kernel::tc::TypeChecker::inductive_reduce_rec`'s own
    /// (kernel-side) computation of the same quantity (tc.rs:1784),
    /// though ORDER differs from that kernel method deliberately: this
    /// method follows WHNF.lean's rule order (whnf major → k → toCtorIfLit
    /// → cleanup → toCtorWhenStructure), not the kernel's own
    /// `type_checker.cpp` order (K first, then whnf) — the two are
    /// different oracle functions serving different checkers.
    fn reduce_rec(
        &mut self,
        rec_val: &RecursorVal,
        rec_levels: LevelsId,
        rec_args: &[ExprId],
    ) -> Result<Option<ExprId>, MetaError> {
        let nparams = match rec_val.num_params.to_usize() {
            Some(v) => v,
            None => return Ok(None),
        };
        let nmotives = match rec_val.num_motives.to_usize() {
            Some(v) => v,
            None => return Ok(None),
        };
        let nminors = match rec_val.num_minors.to_usize() {
            Some(v) => v,
            None => return Ok(None),
        };
        let nindices = match rec_val.num_indices.to_usize() {
            Some(v) => v,
            None => return Ok(None),
        };
        let major_idx = nparams + nmotives + nminors + nindices;
        if major_idx >= rec_args.len() {
            return Ok(None);
        }
        let major_induct = match self.get_major_induct(rec_val.val.ty, major_idx) {
            Some(n) => n,
            None => return Ok(None),
        };
        let mut major = rec_args[major_idx];

        // oracle :230-237 (`isWFRec`): bump transparency to `.all` for
        // this ONE whnf call when reducing `Acc.rec`/`WellFounded.rec`
        // at `.default` transparency.
        let is_wf_rec = rec_val.val.name == self.acc_rec || rec_val.val.name == self.wf_rec;
        major = if is_wf_rec && self.cfg.transparency == TransparencyMode::Default {
            let saved = self.cfg.transparency;
            self.set_transparency(TransparencyMode::All);
            let r = self.whnf(major);
            self.set_transparency(saved);
            r?
        } else {
            self.whnf(major)?
        };

        if rec_val.k {
            major = self.to_ctor_when_k(rec_val, major_induct, major)?;
        }
        major = self.to_ctor_if_lit(major)?;
        major = self.cleanup_nat_offset_major(major)?;
        major = self.to_ctor_when_structure(major_induct, major)?;

        let rule = match self.get_rec_rule_for(&rec_val.rules, major) {
            Some(r) => r.clone(),
            None => return Ok(None),
        };
        let rec_level_ids = self
            .scratch
            .level_list_at(Some(self.view.store), rec_levels)
            .to_vec();
        if rec_level_ids.len() != rec_val.val.level_params.len() {
            return Ok(None);
        }
        let mut rhs = instantiate_level_params(
            self.scratch,
            Some(self.view.store),
            rule.rhs,
            &rec_val.val.level_params,
            &rec_level_ids,
            &mut self.guard,
        )?;
        // Three `mkAppRange` calls (:253/:258/:259): params+motives+minors,
        // then the major's own trailing ctor fields, then any remaining
        // recursor args after the major.
        let pmm = nparams + nmotives + nminors;
        if pmm > rec_args.len() {
            return Ok(None);
        }
        rhs = self.mk_app_spine(rhs, &rec_args[..pmm])?;

        let major_args = self.get_app_args(major);
        let nfields = match rule.nfields.to_usize() {
            Some(v) => v,
            None => return Ok(None),
        };
        if nfields > major_args.len() {
            return Ok(None);
        }
        let nctor_params = major_args.len() - nfields;
        rhs = self.mk_app_spine(rhs, &major_args[nctor_params..])?;
        rhs = self.mk_app_spine(rhs, &rec_args[major_idx + 1..])?;

        Ok(Some(rhs))
    }

    /// oracle: `RecursorVal.getMajorInduct` (`Declaration.lean:403-407`)
    /// — walk `major_idx` `Forall` bodies of the recursor's OWN type,
    /// then take the head const name of that binder's domain. Matches
    /// `leanr_kernel::tc::TypeChecker::get_major_induct`'s own
    /// (kernel-side) identical walk (tc.rs:2381-2397).
    fn get_major_induct(&self, rec_ty: ExprId, major_idx: usize) -> Option<NameId> {
        let mut t = rec_ty;
        for _ in 0..major_idx {
            t = match self.node(t) {
                Node::Forall { body, .. } => body,
                _ => return None,
            };
        }
        match self.node(t) {
            Node::Forall { binder_type, .. } => match self.node(self.get_app_fn(binder_type)) {
                Node::Const { name, .. } => name,
                _ => None,
            },
            _ => None,
        }
    }

    /// oracle: `toCtorWhenK` (WHNF.lean:138-159). SEAM: this plan
    /// compares the K-major's inferred type against the freshly-built
    /// nullary constructor application's inferred type STRUCTURALLY
    /// (`ExprId` equality after `whnf` on both sides) rather than via
    /// `isDefEq` — `defeq.rs::is_def_eq` (this plan's own unifier) now
    /// exists, but this call site was never rewired to use it; left as
    /// a named seam for whichever later task closes the gap.
    /// `instantiateMVars` (oracle :140) is elided: no
    /// general recursive mvar-substitution utility exists yet in this
    /// crate; the structural `has_expr_mvar` bit already reflects
    /// unresolved metavariables closely enough for this bail-out check
    /// (incompleteness only, never wrong).
    #[allow(clippy::wrong_self_convention)] // oracle name; reduces `self`
    fn to_ctor_when_k(
        &mut self,
        rec_val: &RecursorVal,
        major_induct: NameId,
        major: ExprId,
    ) -> Result<ExprId, MetaError> {
        let major_type = self.infer_type(major)?;
        let major_type = self.whnf(major_type)?;
        let major_type_head = self.get_app_fn(major_type);
        let named = matches!(self.node(major_type_head), Node::Const { name: Some(n), .. } if n == major_induct);
        if !named {
            return Ok(major);
        }
        let nparams = match rec_val.num_params.to_usize() {
            Some(v) => v,
            None => return Ok(major),
        };
        if self.data(major_type).has_expr_mvar() {
            let mt_args = self.get_app_args(major_type);
            if mt_args
                .iter()
                .skip(nparams)
                .any(|&a| self.data(a).has_expr_mvar())
            {
                return Ok(major);
            }
        }
        let new_ctor = match self.mk_nullary_ctor(major_type, nparams)? {
            Some(c) => c,
            None => return Ok(major),
        };
        let new_type = self.infer_type(new_ctor)?;
        let new_type = self.whnf(new_type)?;
        if major_type == new_type {
            Ok(new_ctor)
        } else {
            Ok(major)
        }
    }

    /// oracle: `mkNullaryCtor` (WHNF.lean:127-131).
    fn mk_nullary_ctor(&mut self, ty: ExprId, nparams: usize) -> Result<Option<ExprId>, MetaError> {
        let head = self.get_app_fn(ty);
        let (d_name, d_levels) = match self.node(head) {
            Node::Const {
                name: Some(n),
                levels,
            } => (n, levels),
            _ => return Ok(None),
        };
        let ctor_name = match self.get_first_ctor(d_name) {
            Some(c) => c,
            None => return Ok(None),
        };
        let args = self.get_app_args(ty);
        if args.len() < nparams {
            return Ok(None);
        }
        let ctor_const =
            self.scratch
                .expr_const(Some(self.view.store), Some(ctor_name), d_levels)?;
        Ok(Some(self.mk_app_spine(ctor_const, &args[..nparams])?))
    }

    /// oracle: `getFirstCtor` (WHNF.lean:122-125). `pub(crate)` (task 6):
    /// `lazy_delta.rs`'s `isDefEqUnitLike`/`isDefEqSingleton` reuse this
    /// same lookup.
    pub(crate) fn get_first_ctor(&self, name: NameId) -> Option<NameId> {
        match self.view.get(name) {
            Some(ConstantInfo::Induct(v)) => v.ctors.first().copied(),
            _ => None,
        }
    }

    /// SEAM: oracle `cleanupNatOffsetMajor` (WHNF.lean:218-226). Offset
    /// constraints (`isOffset?`/`offsetCnstrs`) need a `Config.
    /// offsetCnstrs` field this plan's `Config` does not carry (same
    /// gate `isDefEqOffset` cites, `lazy_delta.rs`); returns `major`
    /// unchanged.
    fn cleanup_nat_offset_major(&mut self, major: ExprId) -> Result<ExprId, MetaError> {
        Ok(major)
    }

    /// oracle: `isConstructorApp?`, used by `toCtorWhenStructure`
    /// (WHNF.lean:184). Matches
    /// `leanr_kernel::tc::TypeChecker::is_constructor_app`'s own
    /// (kernel-side) identical check (tc.rs:2399-2405). `pub(crate)`
    /// (task 6): `lazy_delta.rs`'s `isDefEqEtaStruct` (`matchConstCtor
    /// a.getAppFn`'s success arm, :129-131) reuses this same check.
    pub(crate) fn is_constructor_app(&self, e: ExprId) -> bool {
        matches!(self.node(self.get_app_fn(e)), Node::Const { name: Some(n), .. }
            if matches!(self.view.get(n), Some(ConstantInfo::Ctor(_))))
    }

    /// oracle: `toCtorWhenStructure` (WHNF.lean:178-204 — the brief's
    /// own `:171-196` citation stops short of the function's actual end;
    /// corrected here to the real range). `useEtaStruct`'s config/
    /// attribute gate (:179-180) is elided: this plan's `Config` does
    /// not model `etaStruct` yet (see `config.rs`'s own doc on why
    /// fields arrive with the feature that consults them) — treated as
    /// always-on, matching the oracle's own default. `instantiateMVars`
    /// (:188) is elided for the same reason as `to_ctor_when_k`.
    /// `mkProjFn`'s auto-generated-projection-function lookup (:165-170)
    /// is also elided: this crate has no structure-projection-function
    /// registry, so this always falls back to raw `Expr.proj`, matching
    /// `leanr_kernel::tc::TypeChecker::expand_eta_struct`'s own
    /// (kernel-side) identical simplification (tc.rs:1959-1995).
    #[allow(clippy::wrong_self_convention)] // oracle name; reduces `self`
    fn to_ctor_when_structure(
        &mut self,
        induct_name: NameId,
        major: ExprId,
    ) -> Result<ExprId, MetaError> {
        if !self.view.is_structure_like(induct_name) {
            return Ok(major);
        }
        if self.is_constructor_app(major) {
            return Ok(major);
        }
        let major_type = self.infer_type(major)?;
        let major_type = self.whnf(major_type)?;
        let head = self.get_app_fn(major_type);
        let (d_name, d_levels) = match self.node(head) {
            Node::Const {
                name: Some(n),
                levels,
            } if n == induct_name => (n, levels),
            _ => return Ok(major),
        };
        // We do not perform eta for propositions (oracle :194-195,
        // using `whnfD` specifically — see `whnf_default`'s own doc).
        let mt_ty = self.infer_type(major_type)?;
        let mt_ty = self.whnf_default(mt_ty)?;
        let zero = self.scratch.level_zero(Some(self.view.store))?;
        if matches!(self.node(mt_ty), Node::Sort { level } if level == zero) {
            return Ok(major);
        }
        let ctor_name = match self.get_first_ctor(d_name) {
            Some(c) => c,
            None => return Ok(major),
        };
        let ctor_info = match self.view.get(ctor_name) {
            Some(ConstantInfo::Ctor(v)) => v,
            _ => return Ok(major),
        };
        let nparams = match ctor_info.num_params.to_usize() {
            Some(v) => v,
            None => return Ok(major),
        };
        let nfields = match ctor_info.num_fields.to_usize() {
            Some(v) => v,
            None => return Ok(major),
        };
        let mt_args = self.get_app_args(major_type);
        if mt_args.len() < nparams {
            return Ok(major);
        }
        let ctor_const =
            self.scratch
                .expr_const(Some(self.view.store), Some(ctor_name), d_levels)?;
        let mut result = self.mk_app_spine(ctor_const, &mt_args[..nparams])?;
        for i in 0..nfields {
            let proj = self.scratch.expr_proj(
                Some(self.view.store),
                Some(induct_name),
                &Nat::from(i as u64),
                major,
            )?;
            result = self.scratch.expr_app(Some(self.view.store), result, proj)?;
        }
        Ok(result)
    }

    /// oracle: `getRecRuleFor` (WHNF.lean:133-136).
    fn get_rec_rule_for<'a>(
        &self,
        rules: &'a [RecursorRule],
        major: ExprId,
    ) -> Option<&'a RecursorRule> {
        match self.node(self.get_app_fn(major)) {
            Node::Const { name: Some(n), .. } => rules.iter().find(|r| r.ctor == n),
            _ => None,
        }
    }

    /// oracle: `reduceQuotRec` (WHNF.lean:270-288). `Quot.lift`:
    /// majorPos 5, argPos 3; `Quot.ind`: majorPos 4, argPos 3.
    ///
    /// TIER-1 CORPUS EXCLUSION: prelude-mode fixtures (`Prelude0`/
    /// `Meta0`/`Matcher`) never contain `Quot` — it is declared by the
    /// `prelude`-but-not-core `Init.Prelude` companion the tier-1
    /// corpus does not replay — so this path has zero coverage from the
    /// fast corpus gate (`mise run meta:fast`). It is exercised only by
    /// this module's hand-built `reduce_quot_rec_*` unit test(s), which
    /// construct the `Quot`/`Quot.mk`/`Quot.lift` machinery directly as
    /// `ConstantInfo::Quot` entries (mirroring
    /// `leanr_kernel::quot::tests::quot_iota_gated_on_initialized`)
    /// rather than via any corpus fixture. Plan 4's nightly should not
    /// expect this path to be reachable from the tier-1 corpus.
    fn reduce_quot_rec(
        &mut self,
        quot_val: &QuotVal,
        rec_args: &[ExprId],
    ) -> Result<Option<ExprId>, MetaError> {
        let (major_pos, arg_pos) = match quot_val.kind {
            QuotKind::Lift => (5usize, 3usize),
            QuotKind::Ind => (4usize, 3usize),
            _ => return Ok(None),
        };
        if major_pos >= rec_args.len() {
            return Ok(None);
        }
        let major = self.whnf(rec_args[major_pos])?;
        // `major` must be `app (app (app (const majorFn _) _) _) majorArg`
        // — three nested `App`s atop a `Const` (`Quot.mk`'s shape).
        let (inner1, major_arg) = match self.node(major) {
            Node::App { f, arg } => (f, arg),
            _ => return Ok(None),
        };
        let (inner2, _) = match self.node(inner1) {
            Node::App { f, arg } => (f, arg),
            _ => return Ok(None),
        };
        let (head, _) = match self.node(inner2) {
            Node::App { f, arg } => (f, arg),
            _ => return Ok(None),
        };
        let major_fn = match self.node(head) {
            Node::Const { name: Some(n), .. } => n,
            _ => return Ok(None),
        };
        match self.view.get(major_fn) {
            Some(ConstantInfo::Quot(qv)) if qv.kind == QuotKind::Ctor => {}
            _ => return Ok(None),
        }
        if arg_pos >= rec_args.len() {
            return Ok(None);
        }
        let f = rec_args[arg_pos];
        let r = self.scratch.expr_app(Some(self.view.store), f, major_arg)?;
        let rec_arity = major_pos + 1;
        Ok(Some(self.mk_app_spine(r, &rec_args[rec_arity..])?))
    }

    /// oracle: `reduceNat?` (WHNF.lean:1054-1078), dispatching over the
    /// interned `Nat.*` names (`MetaCtx::new`'s `nat_bin_ops` map).
    /// `pub(crate)` (task 6): `lazy_delta.rs`'s `isDefEqNat` (:189-200)
    /// reuses this directly.
    pub(crate) fn reduce_nat(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        let nargs = self.get_app_num_args(e);
        if nargs == 1 {
            let (f, arg) = match self.node(e) {
                Node::App { f, arg } => (f, arg),
                _ => return Ok(None),
            };
            if !matches!(self.node(f), Node::Const { name: Some(n), .. } if n == self.nat_succ) {
                return Ok(None);
            }
            return match self.with_nat_value(arg)? {
                Some(v) => Ok(Some(self.lit(v.add(&Nat::from(1u64)))?)),
                None => Ok(None),
            };
        }
        if nargs != 2 {
            return Ok(None);
        }
        let (ff, a2) = match self.node(e) {
            Node::App { f, arg } => (f, arg),
            _ => return Ok(None),
        };
        let (head, a1) = match self.node(ff) {
            Node::App { f, arg } => (f, arg),
            _ => return Ok(None),
        };
        let op = match self.node(head) {
            Node::Const { name: Some(n), .. } => match self.nat_bin_ops.get(&n) {
                Some(&o) => o,
                None => return Ok(None),
            },
            _ => return Ok(None),
        };
        let v1 = match self.with_nat_value(a1)? {
            Some(v) => v,
            None => return Ok(None),
        };
        let v2 = match self.with_nat_value(a2)? {
            Some(v) => v,
            None => return Ok(None),
        };
        let r = match op {
            NatOp::Add => self.lit(v1.add(&v2))?,
            NatOp::Sub => self.lit(v1.sub(&v2))?,
            NatOp::Mul => self.lit(v1.mul(&v2))?,
            NatOp::Div => self.lit(v1.div(&v2))?,
            NatOp::Mod => self.lit(v1.modulo(&v2))?,
            NatOp::Gcd => self.lit(v1.gcd(&v2))?,
            NatOp::Land => self.lit(v1.land(&v2))?,
            NatOp::Lor => self.lit(v1.lor(&v2))?,
            NatOp::Xor => self.lit(v1.lxor(&v2))?,
            // Sound divergence from the oracle: `Nat.shiftLeft`'s oracle
            // (`reduceBinNatOp Nat.shiftLeft`, WHNF.lean:1075) has no
            // shift-amount guard at all (`Nat.shiftLeft` is total in
            // Lean). A shift amount that does not fit `usize` cannot be
            // materialized here without unbounded memory, so this
            // leaves the application un-reduced instead of attempting
            // it — incompleteness, never a wrong answer.
            NatOp::ShiftLeft => match v2.to_usize() {
                Some(k) => self.lit(v1.shiftl(k))?,
                None => return Ok(None),
            },
            NatOp::ShiftRight => self.lit(v1.shiftr(v2.to_usize().unwrap_or(usize::MAX)))?,
            // oracle: `checkExponent`/`exponentiation.threshold`
            // (`EXPONENTIATION_THRESHOLD`'s own doc comment above) —
            // refuse to reduce a pow whose exponent exceeds the
            // threshold.
            NatOp::Pow => match v2.to_usize() {
                Some(exp) if exp <= EXPONENTIATION_THRESHOLD => self.lit(v1.pow(exp as u32))?,
                _ => return Ok(None),
            },
            NatOp::Beq => self.bool_const(v1.beq(&v2))?,
            NatOp::Ble => self.bool_const(v1.ble(&v2))?,
        };
        Ok(Some(r))
    }

    fn lit(&mut self, n: Nat) -> Result<ExprId, MetaError> {
        Ok(self.scratch.expr_lit_nat(Some(self.view.store), &n)?)
    }

    /// `Bool.true`/`Bool.false` const.
    fn bool_const(&mut self, b: bool) -> Result<ExprId, MetaError> {
        let name = if b { self.bool_true } else { self.bool_false };
        let no_levels = self.scratch.intern_level_list(Some(self.view.store), &[])?;
        Ok(self
            .scratch
            .expr_const(Some(self.view.store), Some(name), no_levels)?)
    }

    /// oracle: `withNatValue` (WHNF.lean:1020-1030). `instantiateMVars`
    /// is elided (see this module's other such notes) — a term that
    /// structurally still carries an expr-mvar or fvar is treated as
    /// not-yet-a-value, which is conservative/incomplete, never wrong.
    fn with_nat_value(&mut self, a: ExprId) -> Result<Option<Nat>, MetaError> {
        let d = self.data(a);
        if d.has_expr_mvar() || d.has_fvar() {
            return Ok(None);
        }
        let w = self.whnf(a)?;
        match self.node(w) {
            Node::Const { name: Some(n), .. } if n == self.nat_zero => Ok(Some(Nat::from(0u64))),
            Node::LitNat { v } => Ok(Some(self.scratch.nat_at(Some(self.view.store), v).clone())),
            _ => Ok(None),
        }
    }

    /// SEAM: oracle `getStructuralRecArgPos?` (forward-declared
    /// WHNF.lean:49-56, `@[extern "lean_get_structural_rec_arg_pos"]
    /// opaque`; the real implementation is
    /// `Structural.eqnInfoExt`/`Structural/Eqns.lean`, an elaborator
    /// extension out of reach for this decode-only crate). Always
    /// `None` — per the oracle's OWN doc comment on `unfoldDefinition?`
    /// (its "Remark 4"), a `none` here takes the SAME branch the oracle
    /// itself takes for Binport-imported (Lean-3-era) `.olean`s that
    /// never recorded a rec-arg position at all: `| none => recordUnfold
    /// fInfo.name; return some r` — this is a real, named oracle branch,
    /// not merely an approximation of one. Divergence risk: a constant
    /// where the REAL oracle has recorded a position (and would run the
    /// extra constructor-application check on that argument) unifies
    /// unconditionally under this seam instead; this plan's fixture
    /// (`count`, recursing on its only argument) cannot expose that gap,
    /// so the fix for any future corpus divergence is corpus selection,
    /// not code (Task 9's job).
    fn get_structural_rec_arg_pos(
        &mut self,
        _decl_name: NameId,
    ) -> Result<Option<usize>, MetaError> {
        Ok(None)
    }

    /// oracle `unfoldProjInstWhenInstances?` (WHNF.lean:814-818), gated
    /// at `unfoldDefinition?`'s own call site (:874, `matchConstAux`'s
    /// `failK` — `unfold_definition_app`'s own TWO
    /// `self.unfold_proj_inst_when_instances(e)` call sites above are
    /// this ONE oracle `failK`, split into its two firing sub-conditions
    /// exactly as that method's own doc comment already explains) —
    /// unfolding a class-field projection (e.g. `LE.le`) one step
    /// further into its instance's own projection (e.g. `instLENat.1`)
    /// at `.instances`/`.implicit` transparency. The outer gate here
    /// reads the AMBIENT transparency (`getTransparency`, :815) BEFORE
    /// `unfold_proj_inst` (below) does any of its own transparency
    /// bumping.
    fn unfold_proj_inst_when_instances(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        if !matches!(
            self.cfg.transparency,
            TransparencyMode::Instances | TransparencyMode::Implicit
        ) {
            return Ok(None);
        }
        self.unfold_proj_inst(e)
    }

    /// oracle `unfoldProjInst?` (WHNF.lean:793-806) — transcribed in
    /// full now that `projection_fns` (task B6) decodes
    /// `getProjectionFnInfo?`'s own registry:
    ///
    /// 1. `f := e.getAppFn`; must be a bare `Const` (:794-795), else
    ///    `none`.
    /// 2. `isProjInst declName` (:782-784, inlined here rather than as
    ///    its own method — it is a two-line `getProjectionFnInfo?`
    ///    `fromClass` read with no other caller in this crate):
    ///    `projection_fns.get(&name)` with `from_class == true`, else
    ///    `none`.
    /// 3. `withDefault <| getUnfoldableConst? declName` (:797) — the
    ///    SAME `status_of`/`can_unfold`/`can_unfold_override` gate
    ///    `unfold_definition_const` (task 6/7) already uses, but with
    ///    `cfg.transparency` temporarily forced to `.default` for just
    ///    this ONE check (class fields are never marked `[reducible]`
    ///    themselves, so gating at the AMBIENT `.instances`/`.implicit`
    ///    transparency would always fail here — `withDefault` is the
    ///    whole point: confirm `declName` is unfoldable AT ALL, at the
    ///    most permissive ordinary transparency, before proceeding).
    ///    Restricted to `.defn` kind, matching `getUnfoldableConst?`'s
    ///    own `| _ => return none` non-defn arms — same restriction
    ///    `unfold_definition_const` already applies via its own
    ///    `ConstantInfo::Defn(v) => v, _ => return Ok(None)` match.
    /// 4. `deltaBetaDefinition fInfo us e.getAppRevArgs .. fun e' => ..`
    ///    (:798) — level-arity check, `instantiate_level_params`,
    ///    `beta_rev`: the SAME inline sequence `unfold_definition_const`
    ///    (task 7) already performs for its own plain-delta case, here
    ///    producing `e'` (e.g. `instLENat.1 a b`, an application headed
    ///    by a `Proj`/`ProjBig`).
    /// 5. `withReducibleAndInstances <| reduceProj? e'.getAppFn` (:804)
    ///    — `withReducibleAndInstances` sets transparency to `.instances`
    ///    (`Meta/Basic.lean:1286-1290`); `reduceProj?` (WHNF.lean:578-581)
    ///    is `project?` (:574-575, `whnf` the structure then
    ///    `project_core`) restricted to a literal `.proj`/`.projBig`
    ///    head. `none` here (a non-`Proj` head, or a stuck/non-
    ///    constructor structure term) propagates to the whole method's
    ///    own `none`.
    /// 6. `mkAppN r e'.getAppArgs |>.headBeta` (:806) — reapply the
    ///    projected field value to `e'`'s own remaining args and
    ///    `head_beta` the result (this crate's own `Expr.headBeta` port,
    ///    already `pub(crate)` for `reduce_matcher_telescope`'s sake,
    ///    above).
    ///
    /// `recordUnfold declName` (:805) is a no-op here — this crate
    /// models no unfold-diagnostics counters anywhere (same omission as
    /// every OTHER `recordUnfold*` call site in this file, e.g.
    /// `unfold_definition_const`'s own doc comment).
    fn unfold_proj_inst(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        let f = self.get_app_fn(e);
        let (name, levels) = match self.node(f) {
            Node::Const {
                name: Some(n),
                levels,
            } => (n, levels),
            _ => return Ok(None),
        };
        let is_proj_inst = matches!(
            self.projection_fns.get(&name),
            Some(info) if info.from_class
        );
        if !is_proj_inst {
            return Ok(None);
        }
        // `withDefault <| getUnfoldableConst? declName` (:797) — bump to
        // `.default` for JUST this gate check, restored immediately
        // after (this file's own `whnf_default`/`whnf_at_most_i`
        // save/restore precedent).
        let saved = self.cfg.transparency;
        self.cfg.transparency = TransparencyMode::Default;
        let status = self.status_of(name);
        let ok = if self.can_unfold_override {
            self.can_unfold_at_matcher(name, status)
        } else {
            Ok(crate::can_unfold(self.cfg.transparency, status))
        };
        self.cfg.transparency = saved;
        if !ok? {
            return Ok(None);
        }
        let defn = match self.view.get(name) {
            Some(ConstantInfo::Defn(v)) => v,
            _ => return Ok(None),
        };
        let level_ids = self
            .scratch
            .level_list_at(Some(self.view.store), levels)
            .to_vec();
        if defn.val.level_params.len() != level_ids.len() {
            return Ok(None);
        }
        let args = self.get_app_args(e);
        let value = instantiate_level_params(
            self.scratch,
            Some(self.view.store),
            defn.value,
            &defn.val.level_params,
            &level_ids,
            &mut self.guard,
        )?;
        let e2 = self.beta_rev(value, &args)?;
        let f2 = self.get_app_fn(e2);
        let proj = match self.node(f2) {
            Node::Proj { idx, structure, .. } => Some((idx as usize, structure)),
            Node::ProjBig { idx, structure, .. } => {
                let n = self.scratch.nat_at(Some(self.view.store), idx).clone();
                n.to_usize().map(|v| (v, structure))
            }
            _ => None,
        };
        let Some((idx, structure)) = proj else {
            return Ok(None);
        };
        // `withReducibleAndInstances <| reduceProj? e'.getAppFn` (:804).
        let saved2 = self.cfg.transparency;
        self.cfg.transparency = TransparencyMode::Instances;
        let field = self.reduce_proj(structure, idx);
        self.cfg.transparency = saved2;
        let Some(field_val) = field? else {
            return Ok(None);
        };
        let e2_args = self.get_app_args(e2);
        let applied = self.mk_app_spine(field_val, &e2_args)?;
        Ok(Some(self.head_beta(applied)?))
    }

    /// oracle `project?` (WHNF.lean:574-575) — `projectCore?` (this
    /// file's own `project_core`) applied to the WHNF of the structure
    /// term, not the raw term (a bare `Const` instance name, e.g.
    /// `instLENat`, must itself be delta-unfolded to expose the
    /// constructor application `project_core` needs).
    fn reduce_proj(&mut self, structure: ExprId, idx: usize) -> Result<Option<ExprId>, MetaError> {
        let w = self.whnf(structure)?;
        self.project_core(w, idx)
    }

    /// oracle: `unfoldDefinition?` (WHNF.lean:871-957), this crate's
    /// `ignoreTransparency` always `false` (its only call site,
    /// `whnf_imp`, never passes `true`). Two arms, matching the
    /// oracle's own `.app`/`.const` split exactly (a bare `Const` and an
    /// applied one are NOT simply "the same gate, then maybe beta" —
    /// see `unfold_definition_const`'s own doc for why the smart-
    /// unfolding check there is unconditional, unlike the app arm's).
    pub(crate) fn unfold_definition(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        match self.node(e) {
            Node::App { .. } => self.unfold_definition_app(e),
            Node::Const {
                name: Some(n),
                levels,
            } => self.unfold_definition_const(n, levels),
            _ => Ok(None),
        }
    }

    /// oracle: `unfoldDefinition?`'s `.app` arm (WHNF.lean:872-925),
    /// `matchConstAux`'s (:409-415) inlined `ignoreTransparency := false`
    /// gate — `getConstInfo?` there is exactly `getUnfoldableConst?`,
    /// which is this method's own `status_of`/`can_unfold`/
    /// `can_unfold_at_matcher` gate (task 5/6), restricted to `.defn`
    /// kind (`GetUnfoldableConst.lean`'s own `| .thm => none`/`| _ =>
    /// none` arms — a `Thm`/`Axiom`/etc. never even reaches the gate).
    fn unfold_definition_app(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        let f = self.get_app_fn(e);
        let (name, levels) = match self.node(f) {
            Node::Const {
                name: Some(n),
                levels,
            } => (n, levels),
            // oracle: `matchConstAux`'s `failK` when `f.getAppFn` is not
            // even a `Const` — `unfoldProjInstWhenInstances? e`.
            _ => return self.unfold_proj_inst_when_instances(e),
        };
        let status = self.status_of(name);
        let ok = if self.can_unfold_override {
            self.can_unfold_at_matcher(name, status)?
        } else {
            crate::can_unfold(self.cfg.transparency, status)
        };
        if !ok {
            // oracle: `matchConstAux`'s `failK` when the transparency
            // gate itself fails.
            return self.unfold_proj_inst_when_instances(e);
        }
        let level_ids = self
            .scratch
            .level_list_at(Some(self.view.store), levels)
            .to_vec();
        let args = self.get_app_args(e);

        if self.smart_unfolding {
            let aux_name = self.smart_unfolding_name_for(name)?;
            if let Some(ConstantInfo::Defn(aux)) = self.view.get(aux_name) {
                if aux.val.level_params.len() != level_ids.len() {
                    // oracle: `deltaBetaDefinition`'s `failK` (level-arity
                    // mismatch) — `fun _ => pure none`.
                    return Ok(None);
                }
                // oracle :880-882: `deltaBetaDefinition fAuxInfo fLvls
                // e.getAppRevArgs (preserveMData := true) ..`. This
                // crate's `beta_rev` has no separate `preserve_mdata`
                // flag: verified (subst.rs's `instantiate_go`, the
                // primitive `beta_rev` calls into for its final
                // substitution) that `Node::MData` is always rebuilt
                // through, never stripped, regardless of caller — so
                // substitution alone already preserves every mdata node
                // in the aux's body. `beta_rev`'s OWN lambda-peeling
                // loop only ever matches `Node::Lam` directly (never
                // looks THROUGH an `MData` wrapper to find a further
                // curried lambda), which is exactly `preserveMData :=
                // true`'s own "stop consuming lambdas at an mdata
                // boundary" behavior (`Expr.betaRev`, Expr.lean:1592-
                // 1613) — so this fixture's (and any single-mdata-layer)
                // shape needs no new parameter to match the oracle here.
                let value = instantiate_level_params(
                    self.scratch,
                    Some(self.view.store),
                    aux.value,
                    &aux.val.level_params,
                    &level_ids,
                    &mut self.guard,
                )?;
                let e1 = self.beta_rev(value, &args)?;
                return match self.smart_unfolding_reduce(e1)? {
                    None => Ok(None),
                    Some(r) => match self.get_structural_rec_arg_pos(name)? {
                        // oracle's own Binport-fallback branch (see
                        // `get_structural_rec_arg_pos`'s doc).
                        None => Ok(Some(r)),
                        Some(pos) => {
                            let num_args = args.len();
                            if pos >= num_args {
                                return Ok(None);
                            }
                            let rec_arg = args[pos];
                            let w = self.whnf_matcher(rec_arg)?;
                            if self.is_constructor_app(w) {
                                Ok(Some(r))
                            } else {
                                Ok(None)
                            }
                        }
                    },
                };
            }
            // oracle :922-925: no `_sunfold` aux — `whnfCore` already
            // tries matcher applications, so refuse here rather than
            // exposing the matcher's own `brecOn`-shaped internals.
            if self.matcher_of(name).is_some() {
                return Ok(None);
            }
        }
        // oracle: `unfoldDefault` (WHNF.lean:848-865), this crate's
        // `recordUnfold`/`backward.whnf.reducibleClassField`-driven
        // instance-projection refinement omitted (no diagnostics
        // counters modeled anywhere in this crate, and the class-
        // projection registry it needs is the same undecoded extension
        // `unfold_proj_inst_when_instances` elides above) — plain
        // delta-beta on an already-gated `Defn`.
        let defn = match self.view.get(name) {
            Some(ConstantInfo::Defn(v)) => v,
            _ => return Ok(None),
        };
        if defn.val.level_params.len() != level_ids.len() {
            return Ok(None);
        }
        let value = instantiate_level_params(
            self.scratch,
            Some(self.view.store),
            defn.value,
            &defn.val.level_params,
            &level_ids,
            &mut self.guard,
        )?;
        Ok(Some(self.beta_rev(value, &args)?))
    }

    /// oracle: `unfoldDefinition?`'s `.const` arm (WHNF.lean:945-957) —
    /// a BARE constant (no application at all). Deliberately NOT the
    /// same shape as the app arm: when a `_sunfold` aux exists for
    /// `name` (and smart unfolding is on), this returns `None`
    /// UNCONDITIONALLY, with no fallback to plain delta or a matcher
    /// check at all (`if .. then return none else ..`, :951-952) —
    /// there is no discriminant argument here for smart unfolding to
    /// reduce against, so exposing the bare value via plain delta would
    /// unfold straight through to the `brecOn`-shaped internals smart
    /// unfolding exists to hide (see this module's own top-of-file
    /// doc). oracle correction: the task brief's shorthand said
    /// theorems unfold "at `.all` only" — `GetUnfoldableConst.lean`
    /// shows BOTH `getUnfoldableConst?`/`getUnfoldableConstNoEx?` with
    /// `| some (.thmInfo _) => return none` UNCONDITIONALLY, at ANY
    /// transparency; the oracle file wins, and this method never
    /// unfolds a `Thm`.
    fn unfold_definition_const(
        &mut self,
        name: NameId,
        levels: LevelsId,
    ) -> Result<Option<ExprId>, MetaError> {
        let status = self.status_of(name);
        let ok = if self.can_unfold_override {
            self.can_unfold_at_matcher(name, status)?
        } else {
            crate::can_unfold(self.cfg.transparency, status)
        };
        let cinfo = if ok { self.view.get(name) } else { None };
        let cinfo = match cinfo {
            Some(c) => c,
            // `getConstInfoNoEx?`'s gate failure (or unknown name) =>
            // `pure none`.
            None => return Ok(None),
        };
        if self.smart_unfolding {
            let aux_name = self.smart_unfolding_name_for(name)?;
            if self.view.get(aux_name).is_some() {
                return Ok(None);
            }
        }
        let defn = match cinfo {
            ConstantInfo::Defn(v) => v,
            // Thm/Axiom/Ctor/Induct/Rec/Quot/Opaque never delta-unfold
            // here (Thm per this method's oracle-correction note above;
            // the rest simply have no `value`). The oracle's
            // `recordUnfoldAxiom` diagnostics side effect on the axiom
            // case is bookkeeping this crate models nowhere (same
            // omission as every other `recordUnfold*` call in this
            // file).
            _ => return Ok(None),
        };
        let level_ids = self
            .scratch
            .level_list_at(Some(self.view.store), levels)
            .to_vec();
        if defn.val.level_params.len() != level_ids.len() {
            return Ok(None);
        }
        Ok(Some(instantiate_level_params(
            self.scratch,
            Some(self.view.store),
            defn.value,
            &defn.val.level_params,
            &level_ids,
            &mut self.guard,
        )?))
    }
}

#[cfg(test)]
impl<'e> MetaCtx<'e> {
    /// Test helper (task 5): intern a possibly-dotted name (`"N"`,
    /// `"N.zero"`, `"Nat.add"`, ...) resolved through the persistent
    /// store (so it dedups against an already-replayed fixture's own
    /// interned names, same rationale as `infer.rs`'s own `dotted`/
    /// `single` test helpers) and build a no-universe-argument
    /// `Expr.const` for it.
    fn const_named(&mut self, dotted: &str) -> ExprId {
        let base = Some(self.view.store);
        let mut name = None;
        for part in dotted.split('.') {
            let s = self.scratch.intern_str(base, part).expect("intern");
            name = Some(self.scratch.name_str(base, name, s).expect("name"));
        }
        let no_levels = self.scratch.intern_level_list(base, &[]).expect("levels");
        self.scratch
            .expr_const(base, name, no_levels)
            .expect("const")
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use leanr_kernel::bank::Store;
    use leanr_kernel::{
        ConstSource, ConstantVal, ConstructorVal, DefinitionSafety, DefinitionVal, EnvView,
        ReducibilityHints,
    };
    use leanr_olean::{EntryScope, ReducibilityEntry, ReducibilityStatus};

    use crate::test_support::{with_matcher_ctx, with_prelude0_ctx};
    use crate::{MVarDecl, MVarKind};

    fn dump(ctx: &mut MetaCtx, e: ExprId) -> String {
        match ctx.node(e) {
            Node::App { f, arg } => format!("({} {})", dump(ctx, f), dump(ctx, arg)),
            Node::Const { name, .. } => {
                let nm = ctx.scratch.to_name(Some(ctx.view.store), name);
                format!("{nm}")
            }
            Node::Lam { .. } => "<lam>".to_string(),
            Node::LitNat { v } => format!("{}", ctx.scratch.nat_at(Some(ctx.view.store), v)),
            Node::MVar { .. } => "<mvar>".to_string(),
            Node::FVar { .. } => "<fvar>".to_string(),
            other => format!("{other:?}"),
        }
    }

    /// Intern a dotted name (`"Quot"`, `"Quot.mk"`, `"Pair.mk"`, ...)
    /// directly on `base`, the same idiom `MetaCtx::const_named` uses
    /// through the crate's own `Store`/`scratch` split — used below by
    /// tests that hand-build synthetic env entries (`reduce_quot_rec`'s
    /// and `ProjReduction::YesWithDeltaI`'s) the way
    /// `delta_respects_transparency` does, rather than through a
    /// fixture.
    fn dotted_name(base: &mut Store, parts: &[&str]) -> NameId {
        let mut name = None;
        for part in parts {
            let s = base.intern_str(None, part).expect("intern");
            name = Some(base.name_str(None, name, s).expect("name"));
        }
        name.expect("dotted_name: parts must be non-empty")
    }

    // Exemplar (Task 4's with_prelude0_ctx helper; the rest follow this
    // pattern — write every body in full before implementing):
    #[test]
    fn beta_reduces() {
        with_prelude0_ctx(|ctx| {
            let n_const = ctx.const_named("N"); // test helper: intern name, expr_const with no levels
            let zero = ctx.const_named("N.zero");
            // fun (x : N) => x, i.e. Lam(N, bvar 0)
            let bvar0 = ctx
                .scratch
                .expr_bvar(Some(ctx.view.store), &Nat::from(0u64))
                .expect("bvar");
            let lam = ctx
                .scratch
                .expr_lam(
                    Some(ctx.view.store),
                    None,
                    n_const,
                    bvar0,
                    leanr_kernel::BinderInfo::Default,
                )
                .expect("lam");
            let app = ctx.mk_app_spine(lam, &[zero]).expect("app");
            assert_eq!(ctx.whnf_core(app).expect("whnf_core"), zero);
        });
    }

    #[test]
    fn zeta_reduces_used_let() {
        with_prelude0_ctx(|ctx| {
            let n_const = ctx.const_named("N");
            let zero = ctx.const_named("N.zero");
            let succ = ctx.const_named("N.succ");
            let base = Some(ctx.view.store);
            let bvar0 = ctx.scratch.expr_bvar(base, &Nat::from(0u64)).expect("bvar");
            let succ_x = ctx.scratch.expr_app(base, succ, bvar0).expect("app");
            // let x := N.zero; N.succ x
            let let_e = ctx
                .scratch
                .expr_let(base, None, n_const, zero, succ_x, false)
                .expect("let");
            let expected = ctx.scratch.expr_app(base, succ, zero).expect("expected");
            assert!(ctx.cfg.zeta, "zeta defaults on");
            assert_eq!(ctx.whnf_core(let_e).expect("whnf_core"), expected);
        });
    }

    #[test]
    fn zeta_off_leaves_let() {
        with_prelude0_ctx(|ctx| {
            let n_const = ctx.const_named("N");
            let zero = ctx.const_named("N.zero");
            let succ = ctx.const_named("N.succ");
            let base = Some(ctx.view.store);
            let bvar0 = ctx.scratch.expr_bvar(base, &Nat::from(0u64)).expect("bvar");
            let succ_x = ctx.scratch.expr_app(base, succ, bvar0).expect("app");
            let let_e = ctx
                .scratch
                .expr_let(base, None, n_const, zero, succ_x, false)
                .expect("let");
            ctx.cfg.zeta = false;
            ctx.cfg.zeta_unused = false;
            assert_eq!(
                ctx.whnf_core(let_e).expect("whnf_core"),
                let_e,
                "zeta off (and zeta_unused off) must leave the let unreduced"
            );
        });
    }

    #[test]
    fn assigned_mvar_head_instantiates() {
        with_prelude0_ctx(|ctx| {
            let zero = ctx.const_named("N.zero");
            let base = Some(ctx.view.store);
            let z = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, z).expect("sort");
            let m_str = ctx.scratch.intern_str(base, "m_test").expect("intern");
            let m_name = ctx.scratch.name_str(base, None, m_str).expect("name");
            let mid = MVarId(m_name);
            ctx.mctx_mut().declare(
                mid,
                MVarDecl {
                    user_name: None,
                    ty: sort0,
                    lctx: leanr_kernel::LocalContext::default(),
                    kind: MVarKind::Natural,
                },
            );
            ctx.mctx_mut()
                .assign(mid, zero)
                .expect("assign ?m := N.zero");
            let mexpr = ctx.scratch.expr_mvar(base, Some(m_name)).expect("mvar");
            assert_eq!(ctx.whnf_core(mexpr).expect("whnf_core"), zero);
        });
    }

    #[test]
    fn iota_reduces_recursor() {
        with_prelude0_ctx(|ctx| {
            // Prelude0's `N.add a b := N.rec (motive := fun _ => N) a
            // (fun _ ih => N.succ ih) b` — a real, well-typed recursor
            // application straight from the fixture (rather than a
            // hand-built `N.rec` spine whose exact compiled rule shape
            // this test would otherwise have to predict). Exercises
            // delta (N.add unfolds) + beta + iota (N.rec's succ rule)
            // together: `N.add N.zero (N.succ N.zero)` must whnf to a
            // `N.succ`-headed term. WHNF only normalizes the HEAD, not
            // arguments — the succ rule's recursive `ih` position
            // (`N.rec motive N.zero s N.zero`, itself one more iota step
            // from `N.zero`) is correctly left unreduced inside the
            // argument, so this asserts the head shape, not deep
            // equality against a hand-built fully-reduced term.
            let add = ctx.const_named("N.add");
            let zero = ctx.const_named("N.zero");
            let succ = ctx.const_named("N.succ");
            let one = ctx.mk_app_spine(succ, &[zero]).expect("N.succ N.zero");
            let call = ctx
                .mk_app_spine(add, &[zero, one])
                .expect("N.add N.zero (N.succ N.zero)");
            let result = ctx.whnf(call).expect("whnf");
            assert_eq!(
                ctx.get_app_fn(result),
                succ,
                "N.add N.zero (N.succ N.zero) must whnf to a N.succ-headed term via delta+beta+iota, got {}",
                dump(ctx, result)
            );
            assert_eq!(
                ctx.get_app_args(result).len(),
                1,
                "N.succ takes exactly one argument"
            );
        });
    }

    #[test]
    fn delta_respects_transparency() {
        let mut base = Store::persistent();
        let z = base.level_zero(None).expect("level");
        let no_levels = base.intern_level_list(None, &[]).expect("levels");
        let sort0 = base.expr_sort(None, z).expect("sort0");
        let one_lvl = base.level_succ(None, z).expect("succ");
        // The unfolded "answer" — distinguishable from `sort0`.
        let value = base.expr_sort(None, one_lvl).expect("sort1");

        let semi_str = base.intern_str(None, "semiConst").expect("intern");
        let semi_name = base.name_str(None, None, semi_str).expect("name");
        let irred_str = base.intern_str(None, "irredConst").expect("intern");
        let irred_name = base.name_str(None, None, irred_str).expect("name");

        let semi_const = base
            .expr_const(None, Some(semi_name), no_levels)
            .expect("const");
        let irred_const = base
            .expr_const(None, Some(irred_name), no_levels)
            .expect("const");

        let mk_defn = |name: NameId| {
            ConstantInfo::Defn(DefinitionVal {
                val: ConstantVal {
                    name,
                    level_params: vec![],
                    ty: sort0,
                },
                value,
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all: vec![name],
            })
        };
        let mut extra = HashMap::new();
        extra.insert(semi_name, mk_defn(semi_name));
        extra.insert(irred_name, mk_defn(irred_name));

        let reducibility = vec![
            ReducibilityEntry {
                scope: EntryScope::Global,
                name: semi_name,
                status: ReducibilityStatus::Semireducible,
            },
            ReducibilityEntry {
                scope: EntryScope::Global,
                name: irred_name,
                status: ReducibilityStatus::Irreducible,
            },
        ];

        let empty_consts = leanr_kernel::CheckedConstants::new(HashMap::new());
        let view = EnvView {
            consts: ConstSource::Gated(&empty_consts),
            extra: Some(&extra),
            quot_initialized: false,
            store: &base,
        };
        let mut scratch = Store::scratch();
        let mut ctx = MetaCtx::new(
            view,
            &mut scratch,
            crate::Config::default(),
            &reducibility,
            &[],
            &[],
            &[],
            &[],
        );

        ctx.set_transparency(TransparencyMode::Reducible);
        assert_eq!(
            ctx.whnf(semi_const).expect("whnf"),
            semi_const,
            "Semireducible must not unfold at Reducible"
        );

        ctx.set_transparency(TransparencyMode::Default);
        assert_eq!(
            ctx.whnf(semi_const).expect("whnf"),
            value,
            "Semireducible must unfold at Default"
        );

        ctx.set_transparency(TransparencyMode::Default);
        assert_eq!(
            ctx.whnf(irred_const).expect("whnf"),
            irred_const,
            "Irreducible must not unfold at Default"
        );

        ctx.set_transparency(TransparencyMode::All);
        assert_eq!(
            ctx.whnf(irred_const).expect("whnf"),
            value,
            "Irreducible must unfold at All"
        );
    }

    #[test]
    fn nat_literals_fold() {
        with_prelude0_ctx(|ctx| {
            let add = ctx.const_named("Nat.add");
            let base = Some(ctx.view.store);
            let two = ctx
                .scratch
                .expr_lit_nat(base, &Nat::from(2u64))
                .expect("lit2");
            let three = ctx
                .scratch
                .expr_lit_nat(base, &Nat::from(3u64))
                .expect("lit3");
            let app = ctx.mk_app_spine(add, &[two, three]).expect("app");
            let five = ctx
                .scratch
                .expr_lit_nat(base, &Nat::from(5u64))
                .expect("lit5");
            assert_eq!(ctx.whnf(app).expect("whnf"), five);
        });
    }

    #[test]
    fn whnf_caches_closed_terms_per_config() {
        with_prelude0_ctx(|ctx| {
            let zero = ctx.const_named("N.zero");

            ctx.set_transparency(TransparencyMode::Default);
            ctx.whnf(zero).expect("whnf default");
            let after_first = ctx.whnf_cache.len();
            assert!(after_first > 0, "a closed term's whnf must be cached");

            ctx.set_transparency(TransparencyMode::Reducible);
            ctx.whnf(zero).expect("whnf reducible");
            let after_second = ctx.whnf_cache.len();
            assert_eq!(
                after_second,
                after_first + 1,
                "a different transparency must be a different cache key, not collide"
            );
        });
    }

    /// `isZero (N.succ N.zero)` whnf-reduces through its matcher to
    /// `N.zero` — at `.reducible` transparency specifically.
    ///
    /// Step-1 failure-mode note (recorded in the task report): at
    /// `.default` transparency, `ctx.whnf(isZero (N.succ N.zero))`
    /// already fully reduces to `N.zero` even with `reduce_matcher`
    /// stubbed to `NotMatcher` — plain delta unfolds `isZero` (a
    /// Semireducible `def`, unfoldable at `.default`), THEN plain delta
    /// unfolds the compiled `isZero.match_1` aux (also Semireducible),
    /// exposing a `N.casesOn`/`N.rec` application task 5's existing
    /// (transparency-independent) iota rule already reduces — no
    /// matcher-specific code is exercised at all, so that test would
    /// never go RED against the stub. Per the brief's instruction, the
    /// test is strengthened to isolate the matcher path: this test
    /// unfolds `isZero` exactly ONCE by hand (`unfold_definition` on
    /// the applied form — ordinary delta, at whatever transparency,
    /// exposing `isZero.match_1 <motive> (N.succ N.zero) <alt1> <alt2>`
    /// without going through the matcher machinery at all), THEN drops
    /// to `.reducible` transparency and `whnf`s THAT term. At
    /// `.reducible`, plain delta of `isZero.match_1` itself (also
    /// Semireducible) is BLOCKED (`can_unfold(Reducible,
    /// Semireducible) == false`) — the stub leaves the term completely
    /// stuck (confirmed empirically: `whnf` returns it unchanged with
    /// the stub in place), while `reduce_matcher`'s real transcription
    /// grabs the matcher's value UNCONDITIONALLY (oracle
    /// `reduceMatcher?` never gates the aux lookup itself on
    /// transparency — that is exactly the point of the whole
    /// `.reducible`/`.instances`/`.implicit` escape hatch the module doc
    /// above quotes) and reduces via iota (itself transparency-
    /// independent) regardless.
    #[test]
    fn matcher_application_reduces() {
        with_matcher_ctx(|ctx| {
            let is_zero = ctx.const_named("isZero");
            let zero = ctx.const_named("N.zero");
            let succ = ctx.const_named("N.succ");
            let one = ctx.mk_app_spine(succ, &[zero]).expect("N.succ N.zero");
            let app = ctx
                .mk_app_spine(is_zero, &[one])
                .expect("isZero (N.succ N.zero)");
            let matcher_app = ctx
                .unfold_definition(app)
                .expect("unfold_definition")
                .expect("isZero has a value to unfold");
            ctx.set_transparency(TransparencyMode::Reducible);
            let result = ctx.whnf(matcher_app).expect("whnf");
            assert_eq!(
                result,
                zero,
                "isZero.match_1 (N.succ N.zero) .. must whnf to N.zero at .reducible \
                 transparency via reduce_matcher, got {}",
                dump(ctx, result)
            );
        });
    }

    /// A matcher applied to a stuck (fvar) discriminant does not
    /// reduce: `reduce_matcher`'s `Stuck` verdict leaves `whnf_core`'s
    /// input expression completely unchanged (oracle `reduceMatcher?`'s
    /// `.stuck auxApp` arm, WHNF.lean:562, which `whnfCore`'s own caller
    /// (:686-688) turns back into "return the ORIGINAL application `e2`
    /// unchanged", not the internal (whnf'd, telescoped) `auxApp`).
    /// `whnf_core` (no delta) is exercised directly here, not `whnf`
    /// (full whnf would then ALSO plain-delta the matcher aux itself,
    /// exposing the stuck recursor application underneath and changing
    /// the head — a real but separate effect this test deliberately
    /// does not conflate with `reduce_matcher`'s own Stuck contract).
    #[test]
    fn matcher_stuck_on_free_discriminant() {
        with_matcher_ctx(|ctx| {
            let is_zero = ctx.const_named("isZero");
            let n_const = ctx.const_named("N");
            let base = Some(ctx.view.store);
            let n_str = ctx.scratch.intern_str(base, "n").expect("intern");
            let n_name = ctx.scratch.name_str(base, None, n_str).expect("name");
            let fvar = ctx
                .lctx
                .mk_local_decl(
                    ctx.scratch,
                    base,
                    &mut ctx.fvar_gen,
                    Some(n_name),
                    n_const,
                    leanr_kernel::BinderInfo::Default,
                )
                .expect("fvar");
            let app = ctx.mk_app_spine(is_zero, &[fvar]).expect("isZero n");
            let matcher_app = ctx
                .unfold_definition(app)
                .expect("unfold_definition")
                .expect("isZero has a value to unfold");
            let result = ctx.whnf_core(matcher_app).expect("whnf_core");
            assert_eq!(
                result,
                matcher_app,
                "a matcher stuck on a free discriminant must leave whnf_core's input \
                 unchanged, got {}",
                dump(ctx, result)
            );
        });
    }

    /// `count (N.succ N.zero)` unfolds via the `count._sunfold`
    /// auxiliary and reduces to `N.succ (count N.zero)` — a ctor-headed
    /// result — in a SINGLE `unfold_definition` call, not the full
    /// `whnf` loop.
    ///
    /// Step-1 failure-mode note (recorded in the task report, same
    /// class of gotcha `matcher_application_reduces`'s own doc comment
    /// already documents for `isZero`): asserting only on `ctx.whnf(..)`
    /// here would NOT go red against task 6 — `count` itself compiles
    /// to a `N.brecOn` application, and `N.brecOn` is an ordinary
    /// `Defn` (not a builtin `Recursor`), so task 5/6's plain
    /// delta+iota machinery ALREADY drives `whnf`'s outer loop through
    /// `count` → `N.brecOn` → `N.below`/`N.rec` all the way to a
    /// `N.succ`-headed term for this simple, one-layer-deep example,
    /// with no smart-unfolding awareness at all (confirmed empirically:
    /// a `whnf`-based version of this test passes unchanged with task
    /// 7's own implementation reverted). The test is strengthened to
    /// isolate the mechanism this task actually adds: a SINGLE
    /// `unfold_definition` call, which `smart_unfolding_reduce`'s
    /// one-shot match-and-substitute must land directly on
    /// `N.succ (count N.zero)` — whereas plain delta's single step
    /// only exposes the raw `N.brecOn ...` application (confirmed
    /// empirically against task 6: that call returns
    /// `((N.brecOn <lam>) (N.succ N.zero)) count._f`, not `N.succ`-headed
    /// at all).
    #[test]
    fn smart_unfolding_reduces_structural_recursion() {
        with_matcher_ctx(|ctx| {
            let count = ctx.const_named("count");
            let zero = ctx.const_named("N.zero");
            let succ = ctx.const_named("N.succ");
            let one = ctx.mk_app_spine(succ, &[zero]).expect("N.succ N.zero");
            let app = ctx
                .mk_app_spine(count, &[one])
                .expect("count (N.succ N.zero)");
            let once = ctx
                .unfold_definition(app)
                .expect("unfold_definition")
                .expect("count has a value to unfold");
            assert_eq!(
                ctx.get_app_fn(once),
                succ,
                "a SINGLE unfold_definition call on count (N.succ N.zero) must already \
                 land on a N.succ-headed term via the _sunfold aux, got {}",
                dump(ctx, once)
            );
            // Confirm the FULL `whnf` loop agrees (it must — smart
            // unfolding is one entry in that loop, not a separate path).
            let result = ctx.whnf(app).expect("whnf");
            assert_eq!(
                ctx.get_app_fn(result),
                succ,
                "count (N.succ N.zero) must also whnf to a N.succ-headed term, got {}",
                dump(ctx, result)
            );
        });
    }

    /// `count` applied to a stuck (fvar) discriminant does NOT unfold:
    /// the `_sunfold` aux's inner `sunfoldMatch` is `Stuck` on a bare
    /// fvar, `get_stuck_mvar` finds no mvar to try to unstick (this
    /// plan's `synth_pending` seam is unreachable here for exactly that
    /// reason), and `smart_unfolding_reduce` returns `None` —
    /// `unfold_definition_app`'s smart-unfolding branch then returns
    /// `None` itself rather than falling back to plain delta (an aux
    /// exists for `count`, so the plain-delta fallback arm is never
    /// reached at all), leaving `whnf`'s result exactly the original
    /// `count n` application: never exposing the `N.brecOn` internals
    /// underneath.
    #[test]
    fn smart_unfolding_blocks_on_stuck_argument() {
        with_matcher_ctx(|ctx| {
            let count = ctx.const_named("count");
            let n_const = ctx.const_named("N");
            let base = Some(ctx.view.store);
            let n_str = ctx.scratch.intern_str(base, "n").expect("intern");
            let n_name = ctx.scratch.name_str(base, None, n_str).expect("name");
            let fvar = ctx
                .lctx
                .mk_local_decl(
                    ctx.scratch,
                    base,
                    &mut ctx.fvar_gen,
                    Some(n_name),
                    n_const,
                    leanr_kernel::BinderInfo::Default,
                )
                .expect("fvar");
            let app = ctx.mk_app_spine(count, &[fvar]).expect("count n");
            let result = ctx.whnf(app).expect("whnf");
            assert_eq!(
                result,
                app,
                "count applied to a stuck fvar must not unfold, got {}",
                dump(ctx, result)
            );
        });
    }

    /// Final-review item 1: `reduce_quot_rec` (`Quot.lift` majorPos-5/
    /// argPos-3 path, WHNF.lean:270-290) had zero coverage —
    /// Meta0/Prelude0 are prelude-mode fixtures and never contain
    /// `Quot` (see that method's own "TIER-1 CORPUS EXCLUSION" doc).
    /// Built by hand, exactly like `delta_respects_transparency`: a
    /// persistent `Store` with `Quot.mk`/`Quot.lift` inserted directly
    /// as `ConstantInfo::Quot` entries — never through the kernel's
    /// real `add_quot` (`reduce_quot_rec` only ever inspects
    /// `QuotKind`/the head name, never typechecks the machinery),
    /// mirroring `leanr_kernel::quot::tests::
    /// quot_iota_gated_on_initialized`'s "AFTER add_quot" shape.
    /// Exercises the oracle's own worked example: `Quot.lift f
    /// (Quot.mk r a)` whnf-reduces to `f a`.
    #[test]
    fn reduce_quot_rec_lift_reduces_to_f_a() {
        let mut base = Store::persistent();
        let zero = base.level_zero(None).expect("level");
        let no_levels = base.intern_level_list(None, &[]).expect("levels");
        let placeholder_ty = base.expr_sort(None, zero).expect("sort0");

        let quot_mk_name = dotted_name(&mut base, &["Quot", "mk"]);
        let quot_lift_name = dotted_name(&mut base, &["Quot", "lift"]);

        let cval = |name: NameId| ConstantVal {
            name,
            level_params: vec![],
            ty: placeholder_ty,
        };

        let mut extra = HashMap::new();
        extra.insert(
            quot_mk_name,
            ConstantInfo::Quot(QuotVal {
                val: cval(quot_mk_name),
                kind: QuotKind::Ctor,
            }),
        );
        extra.insert(
            quot_lift_name,
            ConstantInfo::Quot(QuotVal {
                val: cval(quot_lift_name),
                kind: QuotKind::Lift,
            }),
        );

        // Leaves: α, r, β, f, h, a — all free-standing (no
        // `ConstantInfo` entry at all; reduction never looks them up,
        // only the two `Quot` names above).
        let alpha_name = dotted_name(&mut base, &["alpha"]);
        let r_name = dotted_name(&mut base, &["r"]);
        let beta_name = dotted_name(&mut base, &["beta"]);
        let f_name = dotted_name(&mut base, &["f"]);
        let h_name = dotted_name(&mut base, &["h"]);
        let a_name = dotted_name(&mut base, &["a"]);
        let alpha = base
            .expr_const(None, Some(alpha_name), no_levels)
            .expect("const");
        let r = base
            .expr_const(None, Some(r_name), no_levels)
            .expect("const");
        let beta = base
            .expr_const(None, Some(beta_name), no_levels)
            .expect("const");
        let f = base
            .expr_const(None, Some(f_name), no_levels)
            .expect("const");
        let h = base
            .expr_const(None, Some(h_name), no_levels)
            .expect("const");
        let a = base
            .expr_const(None, Some(a_name), no_levels)
            .expect("const");

        // `Quot.mk α r a`.
        let quot_mk_const = base
            .expr_const(None, Some(quot_mk_name), no_levels)
            .expect("const");
        let mk = base.expr_app(None, quot_mk_const, alpha).expect("app");
        let mk = base.expr_app(None, mk, r).expect("app");
        let mk = base.expr_app(None, mk, a).expect("app");

        // `Quot.lift α r β f h (Quot.mk α r a)` — majorPos 5, argPos 3.
        let quot_lift_const = base
            .expr_const(None, Some(quot_lift_name), no_levels)
            .expect("const");
        let e = base.expr_app(None, quot_lift_const, alpha).expect("app");
        let e = base.expr_app(None, e, r).expect("app");
        let e = base.expr_app(None, e, beta).expect("app");
        let e = base.expr_app(None, e, f).expect("app");
        let e = base.expr_app(None, e, h).expect("app");
        let e = base.expr_app(None, e, mk).expect("app");

        let expected = base.expr_app(None, f, a).expect("app");

        let empty_consts = leanr_kernel::CheckedConstants::new(HashMap::new());
        let view = EnvView {
            consts: ConstSource::Gated(&empty_consts),
            extra: Some(&extra),
            quot_initialized: true,
            store: &base,
        };
        let mut scratch = Store::scratch();
        let mut ctx = MetaCtx::new(
            view,
            &mut scratch,
            crate::Config::default(),
            &[],
            &[],
            &[],
            &[],
            &[],
        );

        let result = ctx.whnf(e).expect("whnf");
        assert_eq!(
            result, expected,
            "Quot.lift f (Quot.mk r a) must whnf-reduce to f a"
        );
    }

    /// Final-review item 2: the `ProjReduction::YesWithDeltaI` path
    /// (`whnf_core_proj` → `whnf_at_most_i`) had zero coverage — the
    /// tier-1 corpus never sets it (`Config::default`'s `proj` is
    /// `YesWithDelta`; see `whnf_at_most_i`'s own "TIER-1 CORPUS
    /// EXCLUSION" doc). Hand-built exactly like
    /// `delta_respects_transparency`: a persistent `Store` with a
    /// synthetic 2-field structure (`Pair.mk`, a bare
    /// `ConstantInfo::Ctor` with 0 params) and two nullary `Defn`s whose
    /// value is a `Pair.mk` application — one at `InstanceReducible`
    /// (unfolds within the `.instances` cap `YesWithDeltaI` imposes),
    /// one at `Semireducible` (unfolds at ambient `.default` but NOT at
    /// the `.instances` cap — "Default-only-unfoldable", proving the
    /// cap actually does something rather than being a no-op alias for
    /// `YesWithDelta`).
    #[test]
    fn proj_yes_with_delta_i_caps_at_instances() {
        let mut base = Store::persistent();
        let zero = base.level_zero(None).expect("level");
        let one_lvl = base.level_succ(None, zero).expect("succ");
        let no_levels = base.intern_level_list(None, &[]).expect("levels");
        let placeholder_ty = base.expr_sort(None, zero).expect("sort0");
        // Two distinguishable field values.
        let field0 = base.expr_sort(None, zero).expect("sort0 field");
        let field1 = base.expr_sort(None, one_lvl).expect("sort1 field");

        let pair_mk_name = dotted_name(&mut base, &["Pair", "mk"]);
        let pair_induct_name = dotted_name(&mut base, &["Pair"]);
        let struct_a_name = dotted_name(&mut base, &["structA"]);
        let struct_b_name = dotted_name(&mut base, &["structB"]);

        let cval = |name: NameId| ConstantVal {
            name,
            level_params: vec![],
            ty: placeholder_ty,
        };

        let mut extra = HashMap::new();
        extra.insert(
            pair_mk_name,
            ConstantInfo::Ctor(ConstructorVal {
                val: cval(pair_mk_name),
                induct: pair_induct_name,
                cidx: Nat::from(0u64),
                num_params: Nat::from(0u64),
                num_fields: Nat::from(2u64),
                is_unsafe: false,
            }),
        );

        let pair_mk_const = base
            .expr_const(None, Some(pair_mk_name), no_levels)
            .expect("const");
        let pair_value = base.expr_app(None, pair_mk_const, field0).expect("app");
        let pair_value = base.expr_app(None, pair_value, field1).expect("app");

        let mk_struct_defn = |name: NameId| {
            ConstantInfo::Defn(DefinitionVal {
                val: cval(name),
                value: pair_value,
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all: vec![name],
            })
        };
        extra.insert(struct_a_name, mk_struct_defn(struct_a_name));
        extra.insert(struct_b_name, mk_struct_defn(struct_b_name));

        let reducibility = vec![
            ReducibilityEntry {
                scope: EntryScope::Global,
                name: struct_a_name,
                status: ReducibilityStatus::InstanceReducible,
            },
            ReducibilityEntry {
                scope: EntryScope::Global,
                name: struct_b_name,
                status: ReducibilityStatus::Semireducible,
            },
        ];

        let struct_a_const = base
            .expr_const(None, Some(struct_a_name), no_levels)
            .expect("const");
        let struct_b_const = base
            .expr_const(None, Some(struct_b_name), no_levels)
            .expect("const");
        // Project field 1 (index nparams(0) + 1).
        let proj_a = base
            .expr_proj(None, None, &Nat::from(1u64), struct_a_const)
            .expect("proj");
        let proj_b = base
            .expr_proj(None, None, &Nat::from(1u64), struct_b_const)
            .expect("proj");

        let empty_consts = leanr_kernel::CheckedConstants::new(HashMap::new());
        let view = EnvView {
            consts: ConstSource::Gated(&empty_consts),
            extra: Some(&extra),
            quot_initialized: false,
            store: &base,
        };
        let mut scratch = Store::scratch();
        let cfg = crate::Config {
            proj: ProjReduction::YesWithDeltaI,
            transparency: TransparencyMode::Default, // above .instances
            ..crate::Config::default()
        };
        let mut ctx = MetaCtx::new(view, &mut scratch, cfg, &reducibility, &[], &[], &[], &[]);

        let saved = ctx.cfg.transparency;

        // (a) InstanceReducible discriminant unfolds within the cap.
        let result_a = ctx.whnf(proj_a).expect("whnf proj_a");
        assert_eq!(
            result_a, field1,
            "an InstanceReducible discriminant must reduce under \
             YesWithDeltaI's .instances cap"
        );
        assert_eq!(
            ctx.cfg.transparency, saved,
            "ambient transparency must be restored after whnf_at_most_i"
        );

        // (b) Semireducible discriminant stays stuck under the cap —
        // even though it WOULD unfold at the ambient .default
        // transparency were it not capped (can_unfold(.default,
        // Semireducible) == true; can_unfold(.instances, Semireducible)
        // == false). This is the cap actually doing its job, not a
        // no-op.
        let result_b = ctx.whnf(proj_b).expect("whnf proj_b");
        assert_eq!(
            result_b, proj_b,
            "a Semireducible (Default-only-unfoldable) discriminant must \
             stay stuck under YesWithDeltaI's .instances cap"
        );
        assert_eq!(
            ctx.cfg.transparency, saved,
            "ambient transparency must be restored after whnf_at_most_i"
        );

        // Confirm (b)'s premise directly: the SAME proj_b, uncapped
        // (YesWithDelta instead of YesWithDeltaI), DOES reduce —
        // proving structB is genuinely "Default-only-unfoldable" and
        // the YesWithDeltaI stuck result above is the cap's doing, not
        // some unrelated reason `structB` never unfolds at all.
        ctx.cfg.proj = ProjReduction::YesWithDelta;
        let result_b_uncapped = ctx.whnf(proj_b).expect("whnf proj_b uncapped");
        assert_eq!(
            result_b_uncapped, field1,
            "structB must reduce once the .instances cap is removed \
             (YesWithDelta), confirming it is Default-only-unfoldable"
        );
    }

    // -----------------------------------------------------------------
    // Task B6: `synth_pending` + the `get_stuck_mvar`/
    // `unfold_proj_inst_when_instances` class-projection seams.
    // -----------------------------------------------------------------

    /// `Mul.mul N ?inst x y` — a class-projection application stuck on
    /// an unresolved (but synthesizable, `Instances.olean` declares
    /// `instMulN : Mul N`) instance metavariable. Brief's own suggested
    /// helper name/shape (`stuck_mul_over_fresh_instance`); reused by
    /// all three of this task's seam tests below.
    fn stuck_mul_over_fresh_instance(ctx: &mut MetaCtx) -> (ExprId, MVarId) {
        use crate::test_support::{const_dotted, const_named, fresh_fvar, fresh_mvar};
        let n = const_named(ctx, "N");
        let mul = const_named(ctx, "Mul");
        let mul_n = ctx.mk_app_spine(mul, &[n]).expect("Mul N");
        let (inst_expr, inst_mvar) = fresh_mvar(ctx, mul_n);
        let mul_mul = const_dotted(ctx, "Mul", "mul");
        let x = fresh_fvar(ctx, n, "x");
        let y = fresh_fvar(ctx, n, "y");
        let goal = ctx
            .mk_app_spine(mul_mul, &[n, inst_expr, x, y])
            .expect("Mul.mul N ?inst x y");
        (goal, inst_mvar)
    }

    /// Brief's Step-1 test (verbatim shape): `synth_pending` on the
    /// blocking instance mvar now makes progress instead of the old
    /// stub's unconditional `false`.
    #[test]
    fn synth_pending_resolves_stuck_class_projection() {
        use crate::test_support::with_instances_ctx;
        with_instances_ctx(|ctx| {
            let (_goal, mvar) = stuck_mul_over_fresh_instance(ctx);
            assert!(ctx.synth_pending(mvar).unwrap(), "expected progress");
            assert!(ctx.mctx().is_assigned(mvar));
        });
    }

    /// The `get_stuck_mvar` `Const`-arm class-projection descent (oracle
    /// `getStuckMVar?`'s `getProjectionFnInfo?` branch, WHNF.lean:347-
    /// 365): over the SAME stuck goal, `get_stuck_mvar` must itself find
    /// the blocking instance mvar by descending through `Mul.mul`'s own
    /// `projection_fns`-decoded `num_params` position — this is a
    /// DIFFERENT code path from `synth_pending` above (that test never
    /// calls `get_stuck_mvar` at all), so a green `synth_pending` test
    /// does not exercise this seam.
    #[test]
    fn get_stuck_mvar_descends_class_projection_to_instance_mvar() {
        use crate::test_support::with_instances_ctx;
        with_instances_ctx(|ctx| {
            let (goal, mvar) = stuck_mul_over_fresh_instance(ctx);
            let found = ctx.get_stuck_mvar(goal).unwrap();
            assert_eq!(found, Some(mvar), "expected the instance mvar itself");
        });
    }

    /// `unfold_proj_inst_when_instances` (oracle `unfoldProjInstWhenInstances?`
    /// / `unfoldProjInst?`, WHNF.lean:793-818) reducing a FULLY RESOLVED
    /// class projection at `.instances` transparency: `Mul.mul N
    /// instMulN x y` -- delta-beta to `instMulN.1 x y`, then reduce the
    /// instance projection itself (`instMulN` is `InstanceReducible`,
    /// unfolds at `.instances`) down to `instMulN`'s own `mul` field
    /// (`fun _ b => b`) applied to `x y`, which beta-reduces to plain
    /// `y`.
    #[test]
    fn unfold_proj_inst_when_instances_reduces_class_projection() {
        use crate::test_support::{const_dotted, const_named, fresh_fvar, with_instances_ctx};
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let mul_mul = const_dotted(ctx, "Mul", "mul");
            let inst_mul_n = const_named(ctx, "instMulN");
            let x = fresh_fvar(ctx, n, "x");
            let y = fresh_fvar(ctx, n, "y");
            let e = ctx
                .mk_app_spine(mul_mul, &[n, inst_mul_n, x, y])
                .expect("Mul.mul N instMulN x y");
            ctx.set_transparency(TransparencyMode::Instances);
            let r = ctx.unfold_proj_inst_when_instances(e).unwrap();
            assert_eq!(r, Some(y), "expected Mul.mul N instMulN x y to reduce to y");
        });
    }

    /// The outer transparency gate (`unfoldProjInstWhenInstances?`'s own
    /// `matches .instances | .implicit`, WHNF.lean:815): at `.default`
    /// transparency this must stay `None` — the SAME class projection
    /// that reduces at `.instances` just above must NOT reduce here,
    /// proving the gate is load-bearing and not a no-op that happens to
    /// agree with the reduced answer.
    #[test]
    fn unfold_proj_inst_when_instances_gated_by_transparency() {
        use crate::test_support::{const_dotted, const_named, fresh_fvar, with_instances_ctx};
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let mul_mul = const_dotted(ctx, "Mul", "mul");
            let inst_mul_n = const_named(ctx, "instMulN");
            let x = fresh_fvar(ctx, n, "x");
            let y = fresh_fvar(ctx, n, "y");
            let e = ctx
                .mk_app_spine(mul_mul, &[n, inst_mul_n, x, y])
                .expect("Mul.mul N instMulN x y");
            ctx.set_transparency(TransparencyMode::Default);
            let r = ctx.unfold_proj_inst_when_instances(e).unwrap();
            assert_eq!(r, None, "must not fire outside .instances/.implicit");
        });
    }

    // -----------------------------------------------------------------
    // Task B6 fix round 1 (opus review): tests for the headline
    // SEMANTICS the four tests above never exercised — the depth guard
    // (condition 4) and the `from_class == false` gate (the whole
    // "no fixture answer changed" regression argument's real
    // mechanism, per the corrected report). Plus the two optional ones
    // (condition 2's early return, the explicit-args fallback loop)
    // since both turned out straightforward.
    // -----------------------------------------------------------------

    /// (b), REQUIRED: the depth guard itself (oracle
    /// `synthPendingDepth greater than maxSynthPendingDepth`,
    /// `SynthInstance.lean:1044-1048`, default `1`) — this task's own
    /// crux. Forcing `synth_pending_depth` past
    /// `MAX_SYNTH_PENDING_DEPTH` BEFORE the call must refuse WITHOUT
    /// assigning the mvar, distinguishing this from the general
    /// `guard_depth`/`MAX_REC_DEPTH` bound (a much larger budget that
    /// would not fire at depth 2) — this is what actually pins
    /// `MAX_SYNTH_PENDING_DEPTH`, not merely "synth_pending eventually
    /// terminates".
    #[test]
    fn synth_pending_depth_guard_refuses_without_assigning() {
        use crate::test_support::with_instances_ctx;
        with_instances_ctx(|ctx| {
            let (_goal, mvar) = stuck_mul_over_fresh_instance(ctx);
            ctx.synth_pending_depth = MAX_SYNTH_PENDING_DEPTH + 1;
            let progressed = ctx.synth_pending(mvar).unwrap();
            assert!(
                !progressed,
                "must refuse once synth_pending_depth exceeds \
                 MAX_SYNTH_PENDING_DEPTH, even though the goal is \
                 otherwise identical to the resolving test above"
            );
            assert!(
                !ctx.mctx().is_assigned(mvar),
                "a refused attempt must not assign the mvar as a side \
                 effect"
            );
        });
    }

    /// (d), REQUIRED: the `from_class == false` gate (oracle
    /// `getProjectionFnInfo?`'s own `fromClass` field, `WHNF.lean:349`;
    /// `isProjInst`, `WHNF.lean:782-784`) is what the ENTIRE "no fixture
    /// answer changed" regression argument for this task actually rests
    /// on (see the task report's corrected argument, Minor 6) — not an
    /// empty `projection_fns` registry, which this test disproves by
    /// construction. `Matcher.olean` declares a PLAIN (non-class)
    /// `structure Prod` with field `fst`; `projectionFnInfoExt` (Lean's
    /// own extension) registers a `ProjectionFnInfo` for EVERY structure
    /// field, class or not, so `projection_fns` genuinely contains a
    /// `Prod.fst` entry here with `from_class == false`. Building an
    /// application that genuinely carries an unresolved mvar in the
    /// structure-argument position and confirming BOTH class-projection
    /// seams still answer `None` proves the `from_class` check — not an
    /// absent lookup — is what stops them.
    #[test]
    fn from_class_false_gates_plain_structure_projection() {
        use crate::test_support::{const_dotted, const_named, fresh_mvar, with_matcher_ctx};
        with_matcher_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let prod = const_named(ctx, "Prod");
            let prod_n_n = ctx.mk_app_spine(prod, &[n, n]).expect("Prod N N");
            let (s_expr, _s_mvar) = fresh_mvar(ctx, prod_n_n);
            let prod_fst = const_dotted(ctx, "Prod", "fst");
            let e = ctx
                .mk_app_spine(prod_fst, &[n, n, s_expr])
                .expect("Prod.fst N N ?s");

            // Confirm the premise: `projection_fns` genuinely has an
            // entry for `Prod.fst`, and it is genuinely `from_class ==
            // false` — proving the seams below gate on that field, not
            // on an empty/missing lookup.
            let fst_name = match ctx.node(prod_fst) {
                Node::Const { name: Some(n), .. } => n,
                other => panic!("expected Prod.fst to be a bare Const, got {other:?}"),
            };
            let info = ctx.projection_fns.get(&fst_name).expect(
                "Prod.fst must have a projection_fns entry: every \
                         structure field registers one, not only classes'",
            );
            assert!(
                !info.from_class,
                "Prod is declared with plain `structure`, not `class` — \
                 from_class must be false"
            );

            let found = ctx.get_stuck_mvar(e).unwrap();
            assert_eq!(
                found, None,
                "get_stuck_mvar must stop at the from_class gate even \
                 though a real unresolved mvar sits in the structure \
                 argument position"
            );

            ctx.set_transparency(TransparencyMode::Instances);
            let unfolded = ctx.unfold_proj_inst_when_instances(e).unwrap();
            assert_eq!(
                unfolded, None,
                "unfold_proj_inst_when_instances must stop at the same \
                 from_class gate (isProjInst), independent of transparency"
            );
        });
    }

    /// (a), optional but straightforward: condition 2's early return
    /// (oracle `mvarDecl.kind matches .syntheticOpaque => return false`,
    /// `SynthInstance.lean:1035-1036`) — a synthetic-opaque mvar must be
    /// refused even when its declared type is otherwise class-headed and
    /// genuinely synthesizable (isolates condition 2 from condition 3:
    /// this reuses the SAME class-headed type `stuck_mul_over_fresh_
    /// instance` already proved synthesizable, on a mvar declared with
    /// the ONE differing field, `kind`).
    #[test]
    fn synth_pending_refuses_synthetic_opaque_mvar() {
        use crate::test_support::{const_named, fresh_mvar, with_instances_ctx};
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let mul_const = const_named(ctx, "Mul");
            let mul_n = ctx.mk_app_spine(mul_const, &[n]).expect("Mul N");
            let (_m_expr, m_id) = fresh_mvar(ctx, mul_n);
            ctx.mctx_mut().declare(
                m_id,
                MVarDecl {
                    user_name: None,
                    ty: mul_n,
                    lctx: Default::default(),
                    kind: MVarKind::SyntheticOpaque,
                },
            );
            let progressed = ctx.synth_pending(m_id).unwrap();
            assert!(
                !progressed,
                "a syntheticOpaque mvar must never be resolved by \
                 synth_pending, even over an otherwise-synthesizable type"
            );
            assert!(!ctx.mctx().is_assigned(m_id));
        });
    }

    /// (c), optional but straightforward: the explicit-args fallback
    /// loop (oracle `getStuckMVar?`'s :354-364, "recurse on the explicit
    /// arguments") — reached only when the major-instance-arg check
    /// (:350-353) does NOT find a stuck mvar because the instance itself
    /// is already resolved (`instMulN`, concrete). Puts the stuck mvar
    /// in an EXPLICIT argument position instead (`Mul.mul N instMulN ?x
    /// y`), so a green result here can only come from the fallback loop,
    /// not the major-arg check `get_stuck_mvar_descends_class_projection_
    /// to_instance_mvar` (above) already exercises.
    #[test]
    fn get_stuck_mvar_falls_back_to_explicit_arg_when_major_resolved() {
        use crate::test_support::{
            const_dotted, const_named, fresh_fvar, fresh_mvar, with_instances_ctx,
        };
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let mul_mul = const_dotted(ctx, "Mul", "mul");
            let inst_mul_n = const_named(ctx, "instMulN");
            let (x_expr, x_mvar) = fresh_mvar(ctx, n);
            let y = fresh_fvar(ctx, n, "y");
            let e = ctx
                .mk_app_spine(mul_mul, &[n, inst_mul_n, x_expr, y])
                .expect("Mul.mul N instMulN ?x y");
            let found = ctx.get_stuck_mvar(e).unwrap();
            assert_eq!(
                found,
                Some(x_mvar),
                "the major instance arg (instMulN) is already resolved, \
                 so the stuck mvar must be found via the :354-364 \
                 explicit-args fallback loop, not the :350-353 \
                 major-instance-arg check"
            );
        });
    }
}
