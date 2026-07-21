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
//! - [`MetaCtx::unfold_definition`] — plain delta plus (task 6) the
//!   `can_unfold_at_matcher` gate-swap when `whnf_matcher` sets
//!   `can_unfold_override`; task 7 additionally adds smart unfolding
//!   in place.
//! - the `Defn` arm of `whnf_core_app`'s recursor dispatch — aux-recursor
//!   (`casesOn`/`brecOn`-shaped) unfolding inside `whnf_core` itself
//!   (:696-701); lands with the extension that identifies
//!   `isAuxRecursor`-equivalent definitions.
//! - [`MetaCtx::whnf_delayed_assigned`] — delayed-mvar-assignment
//!   expansion (:587-606; plan 3, alongside the rest of unification).
//! - [`MetaCtx::to_ctor_when_k`] — compares structurally (`ExprId`
//!   equality after `whnf`) instead of via `isDefEq` (plan 3 upgrades
//!   this).
//! - [`MetaCtx::cleanup_nat_offset_major`] — offset-constraint cleanup
//!   (:218-226; plan 3, `offsetCnstrs`).
//! - [`MetaCtx::to_ctor_if_lit`]'s `LitStr` arm — string-literal
//!   `toCtorIfLit` (:27-28; no tier-1 corpus query needs it yet).
//! - the `FVar` arm of `whnf_easy_cases` — `isImplementationDetail`/
//!   `zetaDeltaSet`/`trackZetaDelta` (:399-407) are elaborator-context
//!   channels that do not exist yet; only `cfg.zeta_delta` is modeled.
//!   Arrives with the term elaborator (M4b).
//! - (task 6) `hasMatchPatternAttribute` (:504-505, inside
//!   `can_unfold_at_matcher`) — the `@[match_pattern]` attribute
//!   extension is undecoded; always `false` here.
//! - (task 6) `getProjectionFnInfo?`/`getAuxParentProjectionInfo?`
//!   (:347/:367, inside `get_stuck_mvar`) — the type-class-projection
//!   and diamond-inheritance-projection registries do not exist yet;
//!   always `None` there (same posture as `to_ctor_when_structure`'s
//!   `mkProjFn` elision, below).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelsId, NameId};
use leanr_kernel::{
    instantiate_level_params, instantiate_rev, ConstantInfo, Nat, QuotKind, QuotVal, RecursorRule,
    RecursorVal,
};
use leanr_olean::ReducibilityStatus;

use crate::metactx::NatOp;
use crate::{MVarId, MetaCtx, MetaError, ProjReduction, TransparencyMode};

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
/// `Stuck`'s own payload is legitimately unread this task: `whnf_core`'s
/// call site discards it exactly as the oracle's own does
/// (`| .stuck _ => pure e`, WHNF.lean:687) — the payload is only ever
/// consumed by `smartUnfoldingReduce?` (:764-772, via `getStuckMVar?`),
/// task 7's job, not this one's. Scoped `allow`: a genuine task-7
/// remnant, not a leftover.
#[allow(dead_code)]
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
    /// does not exist on this plan's `MetavarContext` — arrives in
    /// plan 3 alongside the rest of unification. Always `None`.
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
    /// Unused by any of this task's own code — task 7's
    /// `smartUnfoldingReduce?` port is its first real caller. Scoped
    /// `allow`: a genuine task-7 remnant, not a leftover.
    #[allow(dead_code)]
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
                            // SEAM: class-projection / diamond-inheritance
                            // registries (see this method's doc comment).
                            _ => Ok(None),
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
    fn beta_rev(&mut self, f: ExprId, args: &[ExprId]) -> Result<ExprId, MetaError> {
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
    /// (oracle :563: `result.headBeta`).
    fn head_beta(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
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
    /// restored after. Used only by `to_ctor_when_structure`'s "no eta
    /// for propositions" check (WHNF.lean:194).
    fn whnf_default(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let saved = self.cfg.transparency;
        self.set_transparency(TransparencyMode::Default);
        let r = self.whnf(e);
        self.set_transparency(saved);
        r
    }

    /// oracle: `projectCore?` (WHNF.lean:564-572).
    fn project_core(&mut self, c: ExprId, i: usize) -> Result<Option<ExprId>, MetaError> {
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
    /// yet.
    #[allow(clippy::wrong_self_convention)] // oracle name; reduces `self`
    fn to_ctor_if_lit(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
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
    /// `isDefEq` — a full unifier arrives in plan 3, which upgrades this
    /// comparison. `instantiateMVars` (oracle :140) is elided: no
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

    /// oracle: `getFirstCtor` (WHNF.lean:122-125).
    fn get_first_ctor(&self, name: NameId) -> Option<NameId> {
        match self.view.get(name) {
            Some(ConstantInfo::Induct(v)) => v.ctors.first().copied(),
            _ => None,
        }
    }

    /// SEAM: oracle `cleanupNatOffsetMajor` (WHNF.lean:218-226). Offset
    /// constraints (`isOffset?`/`offsetCnstrs`) are a plan-3 concern
    /// (alongside `to_ctor_when_k`'s `isDefEq` upgrade); returns `major`
    /// unchanged.
    fn cleanup_nat_offset_major(&mut self, major: ExprId) -> Result<ExprId, MetaError> {
        Ok(major)
    }

    /// oracle: `isConstructorApp?`, used by `toCtorWhenStructure`
    /// (WHNF.lean:184). Matches
    /// `leanr_kernel::tc::TypeChecker::is_constructor_app`'s own
    /// (kernel-side) identical check (tc.rs:2399-2405).
    fn is_constructor_app(&self, e: ExprId) -> bool {
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
    fn reduce_nat(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
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

    /// This task's plain-delta slice of `unfoldDefinition?`
    /// (WHNF.lean:871-955): `Const` head only (bare or applied),
    /// `Defn`-with-value only, gated by `can_unfold` — or, when
    /// `whnf_matcher` has set `can_unfold_override` (task 6), by
    /// `can_unfold_at_matcher` instead. No smart unfolding, no matcher
    /// suppression — task 7 wraps this in place.
    ///
    /// oracle correction: the task brief's shorthand said theorems
    /// unfold "at `.all` only". `GetUnfoldableConst.lean` (this
    /// toolchain, v4.33.0-rc1) shows BOTH `getUnfoldableConst?` and
    /// `getUnfoldableConstNoEx?` with `| some (.thmInfo _) => return none`
    /// UNCONDITIONALLY — a theorem is never delta-unfolded via `whnf`,
    /// at ANY transparency, including `.all`. The oracle file wins; this
    /// method never unfolds a `Thm`.
    pub(crate) fn unfold_definition(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        let is_app = matches!(self.node(e), Node::App { .. });
        let f = if is_app { self.get_app_fn(e) } else { e };
        let (name, levels) = match self.node(f) {
            Node::Const {
                name: Some(n),
                levels,
            } => (n, levels),
            _ => return Ok(None),
        };
        let defn = match self.view.get(name) {
            Some(ConstantInfo::Defn(v)) => v,
            // Thm/Axiom/Ctor/Induct/Rec/Quot/Opaque never delta-unfold
            // here (see this method's oracle-correction note above for
            // Thm specifically; the rest simply have no `value`).
            _ => return Ok(None),
        };
        // oracle: plain `canUnfold?` (Meta.Context.canUnfold?) except
        // when `whnf_matcher` (task 6) has set `can_unfold_override`,
        // in which case `canUnfoldAtMatcher` is the predicate instead
        // (WHNF.lean:528-529, `withCanUnfoldPred canUnfoldAtMatcher`).
        let status = self.status_of(name);
        let ok = if self.can_unfold_override {
            self.can_unfold_at_matcher(name, status)?
        } else {
            crate::can_unfold(self.cfg.transparency, status)
        };
        if !ok {
            return Ok(None);
        }
        let level_ids = self
            .scratch
            .level_list_at(Some(self.view.store), levels)
            .to_vec();
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
        if is_app {
            // oracle: `deltaBetaDefinition` (WHNF.lean:423-430).
            let args = self.get_app_args(e);
            Ok(Some(self.beta_rev(value, &args)?))
        } else {
            Ok(Some(value))
        }
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
        ConstSource, ConstantVal, DefinitionSafety, DefinitionVal, EnvView, ReducibilityHints,
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
}
