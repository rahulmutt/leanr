//! Pattern (expr-)metavariable assignment: `process_assignment`,
//! `checkAssignment`'s occurs check, `checkTypesAndAssign`,
//! `isDefEqMVarSelf`, and the `isDefEqQuickOther`/`isDefEqQuickMVarMVar`
//! dispatch `defeq.rs`'s mvar arms call into (spec plan 3, task 5).
//!
//! oracle: `Lean/Meta/ExprDefEq.lean`, toolchain
//! leanprover/lean4:v4.33.0-rc1. Every function below cites the exact
//! region read from the pinned source.
//!
//! # Scope: the PATTERN case only, approximations OFF
//!
//! A constraint `?m a₁ … aₙ =?= v` is solved here ONLY when the `aᵢ`
//! are pairwise-distinct free variables not already visible in `?m`'s
//! own declared local context (a genuine "pattern", oracle's own
//! term). Every approximation branch the real `processAssignment`
//! defines for the NON-pattern cases —
//! `processAssignmentFOApprox`/`processConstApprox` (repeated/non-fvar
//! pattern args), `ctxApprox` (out-of-scope fvars inside `v`,
//! `CheckAssignment.checkApp`'s rescue), `quasiPatternApprox` (a
//! pattern arg that IS already in `?m`'s own local context) — is a
//! named seam below returning `false`, citing task 7. `Config`'s four
//! `*_approx` fields (`config.rs`) all default `false`, matching the
//! oracle's own defaults; this task's fixtures are chosen so none of
//! these seams are ever needed to reach the oracle's own verdict.
//!
//! # The `isDefEqBinding` telescope (cross-task reconciliation)
//!
//! Task 3's `defeq.rs::is_def_eq_binding_shallow` opens exactly ONE
//! fresh fvar per Lam/Forall level (recursing one binder at a time)
//! rather than the oracle's `isDefEqBindingAux` accumulated multi-
//! binder telescope. This task's own pattern-assignment machinery
//! (`process_assignment` et al.) does NOT need a telescope-OPENING
//! mechanism of its own at all: it only ever CONSUMES fvars that are
//! already declared in `self.lctx` — the arguments of `?m a₁ … aₙ`,
//! wherever they came from (a fixture that declared them directly, or
//! `is_def_eq_binding_shallow`'s own per-level fvar, still in scope
//! for the dynamic extent of its recursive call). Tracing the concrete
//! case `fun x y => ?m x y =?= fun x y => f x y`: the OUTER
//! `is_def_eq_binding_shallow` call opens `x`, substitutes, and
//! recurses via `is_def_eq_core` into the (still Lam-headed) bodies;
//! THAT recursive call hits the `(Lam, Lam)` arm again and opens `y`
//! via a SECOND, independent `is_def_eq_binding_shallow` call — but
//! since the first call's `LocalContext::restore` only runs AFTER its
//! own recursive `is_def_eq_core` call returns, both `x` and `y` are
//! simultaneously live in `self.lctx` by the time the innermost
//! `?m x y =?= f x y` is reached, and `get_app_fs`/`get_app_args`
//! (syntactic spine walks, oblivious to which call opened which fvar)
//! see both. So two nested single-fvar calls are observationally
//! equivalent to one accumulated telescope for every consumer
//! `process_assignment` has. The genuinely divergent part of the real
//! `isDefEqBindingAux` (tracking local INSTANCES as the telescope
//! opens, `isClass?`/`withNewLocalInstance`) is elaborator-level
//! typeclass-resolution state this crate does not model at all, task
//! 6+ territory, and orthogonal to assignment either way. Conclusion:
//! the task-3 placeholder is CORRECT for this task's needs and is left
//! unchanged — see the task-5 report for this same argument restated
//! for a human reviewer.
//!
//! # Depth / read-only seam (repeats `level.rs`'s own posture)
//!
//! Every `isReadOnly`/`isMVarWithGreaterDepth`/`isSubPrefixOf`-shaped
//! oracle check below collapses to its tier-1 answer (all declared
//! mvars mutually assignable and mutually visible, single flat mctx
//! depth) — named at each site, never silently dropped. `MVarKind::
//! SyntheticOpaque` is the one REAL (non-seamed) non-assignability
//! reason this crate does track (`mvar_ctx.rs`'s own doc comment).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::{abstract_fvars, instantiate_rev, LocalContext, Nat};

use crate::{MVarDecl, MVarId, MVarKind, MetaCtx, MetaError};

impl<'e> MetaCtx<'e> {
    // ===================================================================
    // isDefEqQuickOther / isDefEqQuickMVarMVar — the mvar dispatch
    // `defeq.rs`'s `is_def_eq_quick` falls through to.
    // ===================================================================

    /// oracle: `isDefEqQuickOther` (ExprDefEq.lean:1842-1927), the mvar-
    /// headed-application dispatch `defeq.rs::is_def_eq_quick` falls
    /// through to for every pair its own leaf arms don't decide
    /// (matching the oracle's own fallthrough: `isDefEqQuick`'s `| t, s
    /// => isDefEqQuickOther t s`). Two real oracle features are elided
    /// as already-cited seams, not silently dropped: pattern-annotation
    /// consumption (`patternAnnotation?`, :1846-1849 — this crate's
    /// `MData` has no pattern-annotation kind decoded) and eta-expansion
    /// equality (`etaEq`, :1858 — `isDefEqEta`'s own citation, task 6,
    /// `defeq.rs`'s module doc). The synthetic-mvar eager-synthesis
    /// branch (:1900-1905) is commented out in the ORACLE ITSELF, so it
    /// is not transcribed either. `expandDelayedAssigned?` (:1706-1725)
    /// is permanently moot: this crate's `MetavarContext` has no
    /// delayed-assignment concept at all (not a seam — a feature never
    /// built this plan), so both its call sites are dead code here.
    pub(crate) fn is_def_eq_mvar(
        &mut self,
        t: ExprId,
        s: ExprId,
    ) -> Result<Option<bool>, MetaError> {
        let t_fn = self.get_app_fn(t);
        let s_fn = self.get_app_fn(s);
        let t_fn_is_mvar = matches!(self.node(t_fn), Node::MVar { id: Some(_) });
        let s_fn_is_mvar = matches!(self.node(s_fn), Node::MVar { id: Some(_) });
        if !t_fn_is_mvar && !s_fn_is_mvar {
            return Ok(None);
        }
        if let Node::MVar { id: Some(id) } = self.node(t_fn) {
            if self.mctx.is_assigned(MVarId(id)) {
                let t2 = self.instantiate_mvars(t)?;
                return self.is_def_eq_quick(t2, s);
            }
        }
        if let Node::MVar { id: Some(id) } = self.node(s_fn) {
            if self.mctx.is_assigned(MVarId(id)) {
                let s2 = self.instantiate_mvars(s)?;
                return self.is_def_eq_quick(t, s2);
            }
        }
        let t_fn_mvar = self.unassigned_mvar_id(t_fn);
        let s_fn_mvar = self.unassigned_mvar_id(s_fn);
        match (t_fn_mvar, s_fn_mvar) {
            (Some(a), Some(b)) if a == b => {
                let args1 = self.get_app_args(t);
                let args2 = self.get_app_args(s);
                Ok(Some(self.is_def_eq_mvar_self(t_fn, &args1, &args2)?))
            }
            (Some(_), None) => Ok(Some(self.process_assignment_prime(t, s)?)),
            (None, Some(_)) => Ok(Some(self.process_assignment_prime(s, t)?)),
            (None, None) => {
                // oracle: proof-irrelevance then `isDefEqStuckEx`
                // (:1922-1926) — both already-cited seams (task 6;
                // `level.rs`'s module doc on `isDefEqStuckEx`). Never a
                // silent `true`.
                Ok(Some(false))
            }
            (Some(_), Some(_)) => self.is_def_eq_mvar_mvar(t, s),
        }
    }

    /// `isAssignable` (ExprDefEq.lean:1731-1734), restricted to the
    /// "is this node itself an mvar" question: `mvarId.
    /// isReadOnlyOrSyntheticOpaque` collapses to `kind ==
    /// SyntheticOpaque` (the one REAL, non-seamed exclusion this crate
    /// tracks; read-only is the tier-1 seam, module doc). Callers only
    /// ever invoke this on a node already established NOT to be
    /// currently assigned (`is_def_eq_mvar`'s own early "isAssigned"
    /// branches always return before reaching here), so an assigned
    /// mvar is not re-checked here.
    fn unassigned_mvar_id(&self, e: ExprId) -> Option<MVarId> {
        match self.node(e) {
            Node::MVar { id: Some(id) } => {
                let mid = MVarId(id);
                if self.mctx.is_assigned(mid) {
                    return None;
                }
                match self.mctx.decl(mid) {
                    Some(d) if d.kind == MVarKind::SyntheticOpaque => None,
                    Some(_) => Some(mid),
                    None => None,
                }
            }
            _ => None,
        }
    }

    /// oracle: `isDefEqQuickMVarMVar` (ExprDefEq.lean:1963-1977): both
    /// `t`/`s` are `?m ...`-headed with DIFFERENT (both assignable)
    /// mvar heads (the same-head case is `is_def_eq_mvar_self`, dispatch
    /// above). Tries assigning one side first as its own mini-trial
    /// (this crate's `checkpoint`/`rollback`, `metactx.rs`, standing in
    /// for the oracle's nested `checkpointDefEq`); on failure, rolls
    /// back and tries the other side, this time uncheckpointed —
    /// exactly like the oracle's own asymmetric second call, since the
    /// ENCLOSING top-level `is_def_eq` (`defeq.rs`) will roll back
    /// everything anyway if this whole dispatch ultimately fails.
    fn is_def_eq_mvar_mvar(&mut self, t: ExprId, s: ExprId) -> Result<Option<bool>, MetaError> {
        let s_is_bare_mvar = matches!(self.node(s), Node::MVar { id: Some(_) });
        let t_is_bare_mvar = matches!(self.node(t), Node::MVar { id: Some(_) });
        let (first, second) = if s_is_bare_mvar && !t_is_bare_mvar {
            (s, t)
        } else {
            (t, s)
        };
        let snap = self.checkpoint();
        if self.process_assignment(first, second)? {
            return Ok(Some(true));
        }
        self.rollback(snap);
        Ok(Some(self.process_assignment(second, first)?))
    }

    /// oracle: `isDefEqMVarSelf` (ExprDefEq.lean:1789-1811): `?m args₁
    /// =?= ?m args₂` (same mvar both sides). Unify args pairwise first;
    /// only if THAT fails does the oracle fall back to constant-
    /// function approximation.
    fn is_def_eq_mvar_self(
        &mut self,
        mvar: ExprId,
        args1: &[ExprId],
        args2: &[ExprId],
    ) -> Result<bool, MetaError> {
        if args1.len() != args2.len() {
            return Ok(false);
        }
        if self.is_def_eq_args(mvar, args1, args2)? {
            return Ok(true);
        }
        let mvar_id = match self.unassigned_mvar_id(mvar) {
            Some(id) => id,
            None => return Ok(false),
        };
        // oracle gates the constant-function fallback
        // (`assignConst`/`mkAuxMVar`, :1243-1271) on
        // `mvarDecl.numScopeArgs == args.size || cfg.constApprox`.
        // `numScopeArgs` (delayed-assignment scope tracking) has no
        // analogue anywhere in this crate (no delayed-assignment
        // machinery at all, module doc), so the gate collapses to
        // `cfg.const_approx` alone (task 7) — which still defaults
        // `false`, matching the oracle's own default, so this branch is
        // dead on the `default` profile exactly as before.
        if !self.cfg.const_approx {
            return Ok(false);
        }
        // oracle :1799-1801: `type <- inferType (mkAppN mvar args₁);
        // auxMVar <- mkAuxMVar mvarDecl.lctx mvarDecl.localInstances
        // type; assignConst mvar args₁.size auxMVar`.
        let mvar_app = self.mk_app_spine(mvar, args1)?;
        let ty = self.infer_type(mvar_app)?;
        let aux = match self.mk_aux_mvar_for(mvar_id, ty)? {
            Some((expr, _id)) => expr,
            // SEAM: `mvar`'s own declared lctx is non-empty — see
            // `mk_aux_mvar_for`'s own doc comment (thin ctxApprox/
            // constApprox-rescue coverage, task 7: `LocalContext` has
            // no `Clone`/enumeration API to port `mkAuxMVar`'s general
            // lctx-copy faithfully without touching `leanr_kernel`).
            None => return Ok(false),
        };
        self.assign_const(mvar, args1.len(), aux)
    }

    // ===================================================================
    // isDefEqArgs — the assignment-aware(-by-delegation) arg spine.
    // ===================================================================

    /// oracle: `isDefEqArgs`/`isDefEqArgsFirstPass` (ExprDefEq.lean:
    /// 371-421, :319-349). The oracle's own logic here is almost
    /// entirely about deciding, PER ARGUMENT, whether to skip (a
    /// proof-irrelevant `Prop` arg already known equal via its shared
    /// type), postpone (implicit/instance-implicit, unified in a SECOND
    /// pass at a bumped transparency), or postpone-for-higher-order —
    /// every one of those decisions reads `ParamInfo`
    /// (`getFunInfoNArgs`), a per-declaration signature cache (explicit/
    /// implicit/instance/prop-ness of each parameter) this crate does
    /// not build at all — a distinct, much larger elaborator feature
    /// with no citation anywhere in this task's brief. Without a
    /// `ParamInfo` table to consult, EVERY argument falls through as if
    /// it were a plain, non-postponed explicit argument — the oracle's
    /// own first-pass loop, stripped of that table, degenerates exactly
    /// to "compare every argument pairwise, in order, short-circuiting
    /// on the first mismatch" (task 3's original inlined walk, extracted
    /// here as its own named function so `is_def_eq_mvar_self` can share
    /// it too, per `isDefEqMVarSelf`'s own citation of this same
    /// function, ExprDefEq.lean:1794). Each pairwise comparison goes
    /// through `is_def_eq_core` (unchanged), which is what actually
    /// makes this "assignment-aware" now that task 5 wires mvar
    /// assignment into `is_def_eq_quick`'s own ladder — the upgrade is
    /// emergent, not encoded in this function's own body.
    pub(crate) fn is_def_eq_args(
        &mut self,
        _f: ExprId,
        args1: &[ExprId],
        args2: &[ExprId],
    ) -> Result<bool, MetaError> {
        if args1.len() != args2.len() {
            return Ok(false);
        }
        for (&a, &b) in args1.iter().zip(args2.iter()) {
            if !self.is_def_eq_core(a, b)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    // ===================================================================
    // processAssignment' / processAssignment — the pattern case.
    // ===================================================================

    /// oracle: `processAssignment'` (ExprDefEq.lean:1367-1379): retry
    /// against `v`'s `whnf` on failure. `pub(crate)` (task 6):
    /// `lazy_delta.rs`'s `isDefEqSingleton` (:2153-2163) calls this
    /// directly, matching the oracle's own call there.
    pub(crate) fn process_assignment_prime(
        &mut self,
        mvar_app: ExprId,
        v: ExprId,
    ) -> Result<bool, MetaError> {
        if self.process_assignment(mvar_app, v)? {
            return Ok(true);
        }
        let v2 = self.whnf(v)?;
        if v2 == v {
            return Ok(false);
        }
        if mvar_app == v2 {
            return Ok(true);
        }
        self.process_assignment(mvar_app, v2)
    }

    /// oracle: `processAssignment` (ExprDefEq.lean:1313-1359), the
    /// PATTERN case, now with all four expr-side approximations wired
    /// in at their real call sites (task 7 — every one of these was a
    /// named seam through task 6). `mvar_app` is the full `?m a₁ … aₙ`
    /// application (peeled via `get_app_fn`/`get_app_args`, matching the
    /// oracle's own `mvarApp.getAppFn`/`.getAppArgs`). Assumes `?m` is
    /// unassigned (every real call site already established this).
    ///
    /// The oracle's own `process` is a recursive loop carrying an
    /// ACCUMULATOR: the full `args` array, with the validated PREFIX
    /// (indices `0..i`) already run through `simpAssignmentArg` and the
    /// unvalidated SUFFIX (`i..`) still raw. On ANY per-arg rejection —
    /// a repeated fvar, an fvar already visible in `?m`'s own lctx
    /// (unless `quasiPatternApprox`), or a non-fvar arg — the oracle
    /// does NOT abort outright; it falls to `useFOApprox args`
    /// (`processAssignmentFOApprox <||> processConstApprox .. i ..`),
    /// passing `i` as `patternVarPrefix` (:1319-1332). This function is
    /// transcribed as that exact same loop-with-accumulator (`i`
    /// tracked via a plain `while`, `args` mutated in place) rather than
    /// task 5/6's `for`-loop-building-a-separate-`sim_args`-Vec-and-
    /// bailing-immediately shape: with every `*_approx` flag off, every
    /// `use_fo_approx` call below immediately returns `Ok(false)` (both
    /// `process_assignment_fo_approx`/`process_const_approx` bail on
    /// their own flag check before doing anything else), so this is
    /// observably IDENTICAL to task 5/6's `Ok(false)` seams on the
    /// `default` profile — the regression task 6's own fixtures pin.
    pub(crate) fn process_assignment(
        &mut self,
        mvar_app: ExprId,
        v: ExprId,
    ) -> Result<bool, MetaError> {
        let mvar = self.get_app_fn(mvar_app);
        let mvar_id = match self.node(mvar) {
            Node::MVar { id: Some(id) } => MVarId(id),
            _ => return Ok(false), // defensive: every call site already established mvar-headedness.
        };
        let mut args = self.get_app_args(mvar_app);
        let mut i = 0usize;
        while i < args.len() {
            let arg = self.simp_assignment_arg(args[i])?;
            args[i] = arg;
            match self.node(arg) {
                Node::FVar { id: Some(fid) } => {
                    if args[..i].contains(&arg) {
                        // oracle :1320-1321: repeated pattern var.
                        return self.use_fo_approx(mvar, &args, i, v);
                    }
                    let in_own_lctx = self
                        .mctx
                        .decl(mvar_id)
                        .map(|d| d.lctx.get(fid).is_some())
                        .unwrap_or(false);
                    if in_own_lctx && !self.cfg.quasi_pattern_approx {
                        // oracle :1322-1323: ctx-local fvar, quasiPatternApprox off.
                        return self.use_fo_approx(mvar, &args, i, v);
                    }
                    i += 1;
                }
                _ => {
                    // oracle :1327-1328: non-fvar pattern argument.
                    return self.use_fo_approx(mvar, &args, i, v);
                }
            }
        }
        // oracle: `let v ← instantiateMVars v -- enforce A4` (:1336).
        let v = self.instantiate_mvars(v)?;
        if self.get_app_fn(v) == mvar {
            // oracle :1337-1339: "using A6".
            return self.use_fo_approx(mvar, &args, args.len(), v);
        }
        let checked = match self.check_assignment(mvar_id, &args, v)? {
            None => return self.use_fo_approx(mvar, &args, args.len(), v),
            Some(v2) => v2,
        };
        let lam = match self.mk_lambda_fvars_with_let_deps(&args, checked)? {
            // oracle :1345: `let some v ← mkLambdaFVarsWithLetDeps args v
            // | return false` — a bare `false`, NOT `useFOApprox`
            // (unlike every other failure exit in this function).
            None => return Ok(false),
            Some(l) => l,
        };
        // oracle :1346-1352. With `quasiPatternApprox` off this is
        // vacuously false by construction (every entry in `args` was
        // already rejected above were it ctx-local) — task 5/6's own
        // reasoning, now genuinely reachable when the flag is on.
        let has_ctx_locals = args.iter().any(|&a| match self.node(a) {
            Node::FVar { id: Some(fid) } => self
                .mctx
                .decl(mvar_id)
                .map(|d| d.lctx.get(fid).is_some())
                .unwrap_or(false),
            _ => false,
        });
        if has_ctx_locals {
            if self.is_type_correct(lam)? {
                self.check_types_and_assign(mvar, lam)
            } else {
                self.use_fo_approx(mvar, &args, args.len(), v)
            }
        } else {
            self.check_types_and_assign(mvar, lam)
        }
    }

    // ===================================================================
    // useFOApprox / processAssignmentFOApprox / processConstApprox /
    // assignConst — the four expr-side approximations (task 7).
    // ===================================================================

    /// oracle: `processAssignment`'s own local `useFOApprox` closure
    /// (:1319-1321): `processAssignmentFOApprox mvar args v <||>
    /// processConstApprox mvar args i v` — first-order approximation,
    /// then (only if that also fails) constant-function approximation.
    fn use_fo_approx(
        &mut self,
        mvar: ExprId,
        args: &[ExprId],
        pattern_var_prefix: usize,
        v: ExprId,
    ) -> Result<bool, MetaError> {
        if self.process_assignment_fo_approx(mvar, args, v)? {
            return Ok(true);
        }
        self.process_const_approx(mvar, args, pattern_var_prefix, v)
    }

    /// oracle: `processAssignmentFOApprox` (ExprDefEq.lean:1184-1210),
    /// gated on `self.cfg.fo_approx`. Loops `v.headBeta`, tries the
    /// first-order decomposition under its OWN checkpoint (oracle:
    /// `checkpointDefEq`, mirrored here by this crate's own
    /// `checkpoint`/`rollback` pair — same convention
    /// `is_def_eq_mvar_mvar`, task 5, already established for a
    /// checkpointed sub-attempt not itself worth a second postponed-
    /// queue drain, since the ENCLOSING `is_def_eq` drains it once for
    /// the whole call), and on failure unfolds `v` and retries.
    fn process_assignment_fo_approx(
        &mut self,
        mvar: ExprId,
        args: &[ExprId],
        v: ExprId,
    ) -> Result<bool, MetaError> {
        if !self.cfg.fo_approx {
            return Ok(false);
        }
        let mut v = v;
        loop {
            self.step()?;
            let vb = self.head_beta(v)?;
            let snap = self.checkpoint();
            if self.process_assignment_fo_approx_aux(mvar, args, vb)? {
                return Ok(true);
            }
            self.rollback(snap);
            match self.unfold_definition(vb)? {
                None => return Ok(false),
                Some(v2) => v = v2,
            }
        }
    }

    /// oracle: `processAssignmentFOApproxAux` (ExprDefEq.lean:1177-1183).
    /// `mkAppRange mvar 0 (args.size - 1) args` = `mvar` applied to
    /// every arg but the last (`self.mk_app_spine(mvar, &args[..n-1])`).
    /// Both nested comparisons run at `is_def_eq_core` (not the
    /// checkpoint-wrapped `is_def_eq`): the CALLER already opened one
    /// checkpoint for this whole attempt (oracle's own
    /// `checkpointDefEq`), so nesting a second one here would double-
    /// checkpoint — the same point this file's `check_types_and_assign`
    /// doc comment makes.
    fn process_assignment_fo_approx_aux(
        &mut self,
        mvar: ExprId,
        args: &[ExprId],
        v: ExprId,
    ) -> Result<bool, MetaError> {
        match self.node(v) {
            Node::MData { expr, .. } => self.process_assignment_fo_approx_aux(mvar, args, expr),
            Node::App { f, arg } => {
                let last = match args.last() {
                    Some(&l) => l,
                    None => return Ok(false),
                };
                if !self.is_def_eq_core(last, arg)? {
                    return Ok(false);
                }
                let mvar_prefix = self.mk_app_spine(mvar, &args[..args.len() - 1])?;
                self.is_def_eq_core(mvar_prefix, f)
            }
            _ => Ok(false),
        }
    }

    /// oracle: `processConstApprox` (ExprDefEq.lean:1271-1310), gated on
    /// `self.cfg.const_approx`.
    ///
    /// The `mvarDecl.numScopeArgs != numArgs && !cfg.constApprox` guard
    /// collapses to `!cfg.const_approx` alone — the SAME reasoning
    /// `is_def_eq_mvar_self`'s own doc comment gives (`numScopeArgs`
    /// tracks delayed-assignment scope, a feature this crate's
    /// `MetavarContext` has no analogue for at all).
    ///
    /// The `patternVarPrefix > 0` branch (:1284-1309) — searching for
    /// the LONGEST valid pattern prefix before falling back to a fully
    /// constant function — is a named SEAM here: this crate always goes
    /// straight to `defaultCase` (`assignConst mvar args.size v`,
    /// :1273), which is the search's OWN eventual fallback too (every
    /// `go` iteration that fails re-tries a SHORTER prefix, terminating
    /// at `defaultCase` when none work). Skipping straight to
    /// `defaultCase` can therefore only make this crate accept STRICTLY
    /// FEWER constraints than the oracle (never more): sound, just
    /// incomplete for the corner where an actual proper prefix would
    /// have let SOME of `v`'s free vars stay bound rather than escape
    /// entirely. Acknowledged-thin coverage, matching the brief's own
    /// allowance for the const-approx corner.
    fn process_const_approx(
        &mut self,
        mvar: ExprId,
        args: &[ExprId],
        _pattern_var_prefix: usize,
        v: ExprId,
    ) -> Result<bool, MetaError> {
        if !self.cfg.const_approx {
            return Ok(false);
        }
        self.assign_const(mvar, args.len(), v)
    }

    /// oracle: `assignConst` (ExprDefEq.lean:1243-1254): assign `mvar :=
    /// fun x₁ … x_numArgs => v`, where `x₁ … x_numArgs` are FRESH
    /// fvars opened from `mvar`'s OWN declared type (a
    /// `forallBoundedTelescope`, NOT the actual call-site args) — so `v`
    /// ends up closed over none of them unless it already mentioned one
    /// some other way, i.e. this really does assign a function that
    /// (up to `mkLambdaFVarsWithLetDeps`'s own let-dependency
    /// abstraction) ignores its arguments. Also `isDefEqMVarSelf`'s
    /// (:1794, "We use it at `processConstApprox` and
    /// `isDefEqMVarSelf`") own constant-function fallback, called with
    /// `v` already an aux mvar there.
    pub(crate) fn assign_const(
        &mut self,
        mvar: ExprId,
        num_args: usize,
        v: ExprId,
    ) -> Result<bool, MetaError> {
        let mvar_id = match self.node(mvar) {
            Node::MVar { id: Some(id) } => MVarId(id),
            _ => return Ok(false),
        };
        let mvar_ty = match self.mctx.decl(mvar_id) {
            Some(d) => d.ty,
            None => return Ok(false),
        };
        let checkpoint = self.lctx.save();
        let result = self.assign_const_body(mvar, mvar_id, mvar_ty, num_args, v);
        self.lctx.restore(checkpoint);
        result
    }

    fn assign_const_body(
        &mut self,
        mvar: ExprId,
        mvar_id: MVarId,
        mvar_ty: ExprId,
        num_args: usize,
        v: ExprId,
    ) -> Result<bool, MetaError> {
        let xs = self.forall_bounded_telescope(mvar_ty, num_args)?;
        if xs.len() != num_args {
            return Ok(false);
        }
        let lam = match self.mk_lambda_fvars_with_let_deps(&xs, v)? {
            None => return Ok(false),
            Some(l) => l,
        };
        let checked = match self.check_assignment(mvar_id, &[], lam)? {
            None => return Ok(false),
            Some(c) => c,
        };
        self.check_types_and_assign(mvar, checked)
    }

    /// A restricted `forallBoundedTelescope` (the general combinator
    /// this task's own callers need): peel up to `num_args` leading
    /// `Forall` binders off `ty`, `whnf`-ing when the raw syntax runs
    /// out before `num_args` binders are found (matching
    /// `forallTelescopeReducingAuxAux`'s own `reducing := true` branch —
    /// `whnf.rs::reduce_matcher_telescope`'s own citation of the exact
    /// same oracle combinator; duplicated here rather than shared since
    /// that method is tightly coupled to its own caller's checkpoint/
    /// restore bracketing). Returns FEWER than `num_args` fvars (never
    /// panics or errors) when the type's own Pi spine is too short even
    /// after `whnf` — every caller here treats `len != num_args` as the
    /// oracle's own `if xs.size != numArgs then pure false` guard.
    fn forall_bounded_telescope(
        &mut self,
        ty: ExprId,
        num_args: usize,
    ) -> Result<Vec<ExprId>, MetaError> {
        let mut xs: Vec<ExprId> = Vec::new();
        let mut cur_ty = ty;
        for _ in 0..num_args {
            let t = if matches!(self.node(cur_ty), Node::Forall { .. }) {
                cur_ty
            } else {
                self.whnf(cur_ty)?
            };
            let (binder_name, binder_type, body, binder_info) = match self.node(t) {
                Node::Forall {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => (binder_name, binder_type, body, binder_info),
                _ => break,
            };
            let d = instantiate_rev(
                self.scratch,
                Some(self.view.store),
                binder_type,
                &xs,
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
            xs.push(fvar);
            cur_ty = body;
        }
        Ok(xs)
    }

    /// oracle: `isTypeCorrect` (Check.lean:365-370): `try check e; true
    /// catch _ => false`, where `check` is `Lean.Meta.check`'s own
    /// separate elaborator-level re-typechecker (`Check.lean`, a large
    /// distinct subsystem this crate does not build at all — no
    /// citation anywhere in this task's brief). The nearest available
    /// proxy already in this crate is `infer_type`: both ultimately ask
    /// "does this term have SOME type under the current context", and
    /// `infer_type` already `Err`s on the same structural shapes (an
    /// ill-applied non-function head, etc.) that would make the real
    /// `check` throw. SEAM, task 7: only reachable via
    /// `quasiPatternApprox`'s own `hasCtxLocals` branch above, and
    /// mirrors the oracle's own blanket `catch _ => false` by folding
    /// EVERY `infer_type` error (not just "genuinely ill-typed" ones)
    /// into `false`.
    fn is_type_correct(&mut self, e: ExprId) -> Result<bool, MetaError> {
        Ok(self.infer_type(e).is_ok())
    }

    /// oracle: `mkAuxMVar` (`Lean/MetavarContext.lean`'s
    /// `mkFreshExprMVarAt`-family primitive, `@[extern]`-backed, no Lean
    /// source to transcribe line-by-line — same posture as
    /// `instantiate_mvars`'s own citation). Mints a globally-fresh
    /// `MVarId` of kind `Natural`, declared with local context
    /// `LocalContext::default()` (EMPTY) and type `ty`. This crate had
    /// no production-code fresh-EXPR-mvar-minting facility before task
    /// 7 (only `test_support::fresh_mvar`, `#[cfg(test)]`-gated); this
    /// is that facility's first production use, mirroring
    /// `level.rs::fresh_level_mvar`'s own "fixed prefix + counter"
    /// idiom (`expr_mvar_gen`, `metactx.rs`) rather than reusing
    /// `FVarIdGen` (an expr-mvar name must not collide with an fvar
    /// name).
    ///
    /// Always mints with an EMPTY lctx: see `mk_aux_mvar_for`'s own doc
    /// comment for why (this crate's only call site, `constApprox`'s
    /// `isDefEqMVarSelf` fallback, only ever invokes this after
    /// confirming the mvar being rescued already has an empty own
    /// lctx).
    pub(crate) fn mk_aux_mvar(&mut self, ty: ExprId) -> Result<(ExprId, MVarId), MetaError> {
        let idx = self.expr_mvar_gen;
        self.expr_mvar_gen += 1;
        let base = Some(self.view.store);
        let prefix_str = self.scratch.intern_str(base, "_leanr_aux_mvar")?;
        let prefix = self.scratch.name_str(base, None, prefix_str)?;
        let idx_id = self.scratch.intern_nat(base, &Nat::from(idx))?;
        let name = self.scratch.name_num(base, Some(prefix), idx_id)?;
        let id = MVarId(name);
        self.mctx.declare(
            id,
            MVarDecl {
                user_name: None,
                ty,
                lctx: LocalContext::default(),
                kind: MVarKind::Natural,
            },
        );
        let expr = self.scratch.expr_mvar(base, Some(name))?;
        Ok((expr, id))
    }

    /// `mk_aux_mvar`, restricted to the ONE case this crate can port
    /// soundly without touching `leanr_kernel`: the oracle's `mkAuxMVar`
    /// call site this function backs (`isDefEqMVarSelf` :1800) passes
    /// `mvarDecl.lctx` — the mvar BEING rescued's OWN declared local
    /// context — as the new aux mvar's lctx too. `leanr_kernel::
    /// LocalContext` has neither `Clone` nor any enumeration API
    /// (`local_ctx.rs`: `decls`/`index` are private, `get` needs an
    /// already-known fvar id) to copy an ARBITRARY such context, and
    /// porting one is out of this task's reach (never modify
    /// `leanr_kernel`, per the brief). The one case still reachable
    /// without that: `mvar_id`'s own lctx is EMPTY, where
    /// `LocalContext::default()` (`mk_aux_mvar`'s own hardcoded choice)
    /// already IS that exact copy — an empty context has nothing to
    /// lose. Every mvar this crate's own fixtures/helpers mint
    /// (`test_support::fresh_mvar`'s own `lctx: Default::default()`)
    /// falls in this case. Returns `None` (a named SEAM, not a wrong
    /// answer) when `mvar_id`'s own lctx is non-empty — narrower than
    /// the oracle, never unsound: acknowledged-thin `constApprox`-rescue
    /// coverage (spec risk 3; `checkApp`'s SEPARATE `ctxApprox` rescue
    /// does not use this helper at all any more — see
    /// `check_assignment_scope`'s own doc comment for why it is not
    /// implemented here).
    fn mk_aux_mvar_for(
        &mut self,
        mvar_id: MVarId,
        ty: ExprId,
    ) -> Result<Option<(ExprId, MVarId)>, MetaError> {
        let lctx_len = match self.mctx.decl(mvar_id) {
            Some(d) => d.lctx.save(),
            None => return Ok(None),
        };
        if lctx_len != 0 {
            return Ok(None);
        }
        Ok(Some(self.mk_aux_mvar(ty)?))
    }

    /// oracle: `simpAssignmentArg`/`simpAssignmentArgAux` (ExprDefEq.
    /// lean:1226-1242). `instantiateMVars` only when the arg's own
    /// app-head carries an expr mvar (`arg.getAppFn.hasExprMVar`),
    /// matching the oracle's own guard exactly.
    fn simp_assignment_arg(&mut self, arg: ExprId) -> Result<ExprId, MetaError> {
        let head = self.get_app_fn(arg);
        let arg = if self.data(head).has_expr_mvar() {
            self.instantiate_mvars(arg)?
        } else {
            arg
        };
        self.simp_assignment_arg_aux(arg)
    }

    fn simp_assignment_arg_aux(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        match self.node(e) {
            Node::MData { expr, .. } => self.simp_assignment_arg_aux(expr),
            Node::FVar { id: Some(id) } => match self.lctx.get(id).and_then(|d| d.value) {
                Some(v) => self.simp_assignment_arg_aux(v),
                None => Ok(e),
            },
            _ => Ok(e),
        }
    }

    // ===================================================================
    // checkTypesAndAssign
    // ===================================================================

    /// oracle: `checkTypesAndAssign` (ExprDefEq.lean:492-513),
    /// simplified: the `respectTransparencyAtTypes`/`withImplicitConfig`/
    /// `withInferTypeConfig` transparency-bump machinery (widening
    /// unfolding for the TYPE comparison specifically) is not modeled —
    /// this compares at whatever `self.cfg.transparency` already is,
    /// same posture as every other un-bumped call site in this plan
    /// (task 7 territory; the diagnostics-retry branch, :506-509, is
    /// dead code without it too). Calls `is_def_eq_core`, NOT the
    /// checkpoint-wrapped `is_def_eq`: this runs NESTED inside an
    /// enclosing `is_def_eq` call (via `process_assignment`, itself
    /// reached from `is_def_eq_mvar`), and nesting a SECOND checkpoint +
    /// postponed-drain here would double-checkpoint — the exact same
    /// point `level.rs`'s `is_level_def_eq` doc comment makes about
    /// `isLevelDefEqAux` vs. the standalone `isLevelDefEq`.
    fn check_types_and_assign(&mut self, mvar: ExprId, v: ExprId) -> Result<bool, MetaError> {
        let mvar_id = match self.node(mvar) {
            Node::MVar { id: Some(id) } => MVarId(id),
            _ => return Ok(false),
        };
        let mvar_ty = self.infer_type(mvar)?;
        let v_ty = self.infer_type(v)?;
        if self.is_def_eq_core(mvar_ty, v_ty)? {
            self.mctx.assign(mvar_id, v)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    // ===================================================================
    // mkLambdaFVarsWithLetDeps
    // ===================================================================

    /// oracle: `mkLambdaFVarsWithLetDeps` (ExprDefEq.lean:549-...). The
    /// let-DEPENDENCY collection (`addLetDeps`/`hasLetDeclsInBetween`)
    /// needs to enumerate `LocalContext` decls POSITIONALLY between two
    /// fvars — an API this crate's `LocalContext` (`leanr_kernel`,
    /// untouched per this task's own constraint) does not expose at
    /// all. Every fvar this module's own machinery ever mints
    /// (`is_def_eq_binding_shallow`'s telescope, `defeq.rs`) is a plain
    /// `mk_local_decl`, never `mk_let_decl` — the scenario
    /// `hasLetDeclsInBetween` exists to detect cannot arise via any
    /// path this task builds. Defensively (not just by construction):
    /// if any `xs` entry itself somehow carries a `value` (would only
    /// happen if that invariant were violated elsewhere), that is
    /// treated as the named seam below rather than silently
    /// mis-abstracted. SEAM: plan 4 / M4b for real let-dependency
    /// abstraction.
    fn mk_lambda_fvars_with_let_deps(
        &mut self,
        xs: &[ExprId],
        v: ExprId,
    ) -> Result<Option<ExprId>, MetaError> {
        for &x in xs {
            if let Node::FVar { id: Some(id) } = self.node(x) {
                if self.lctx.get(id).and_then(|d| d.value).is_some() {
                    return Ok(None); // SEAM (doc comment above).
                }
            }
        }
        Ok(Some(self.mk_lambda_over_fvars(xs, v)?))
    }

    /// Our own `mk_lambda`: `leanr_kernel::subst::mk_lambda` exists but
    /// is NOT re-exported from that crate's public API (`lib.rs`'s
    /// `pub use subst::{...}` list omits it) — `infer.rs`'s
    /// `rebuild_forall` hit the identical gap for `mk_pi` and wrote its
    /// own fold; this mirrors that exact idiom for `Lam` instead of
    /// `Forall`, minus the let-binder branch (unreachable here, see
    /// this function's only caller's doc comment).
    fn mk_lambda_over_fvars(&mut self, xs: &[ExprId], body: ExprId) -> Result<ExprId, MetaError> {
        let mut r = body;
        let mut i = xs.len();
        while i > 0 {
            i -= 1;
            r = abstract_fvars(
                self.scratch,
                Some(self.view.store),
                r,
                std::slice::from_ref(&xs[i]),
                &mut self.guard,
            )?;
            let (binder_name, ty, binder_info) = match self.node(xs[i]) {
                Node::FVar { id: Some(id) } => {
                    let decl = self.lctx.get(id).ok_or_else(|| {
                        MetaError::MVar("mk_lambda_over_fvars: telescope fvar not declared".into())
                    })?;
                    (decl.binder_name, decl.ty, decl.binder_info)
                }
                _ => {
                    return Err(MetaError::MVar(
                        "mk_lambda_over_fvars: pattern arg is not an fvar".into(),
                    ))
                }
            };
            let ty2 = abstract_fvars(
                self.scratch,
                Some(self.view.store),
                ty,
                &xs[..i],
                &mut self.guard,
            )?;
            r = self
                .scratch
                .expr_lam(Some(self.view.store), binder_name, ty2, r, binder_info)?;
        }
        Ok(r)
    }

    // ===================================================================
    // checkAssignment / CheckAssignmentQuick.check / typeOccursCheck
    // ===================================================================

    /// oracle: `checkAssignment` (ExprDefEq.lean:1151-1176). `hasCtxLocals`
    /// (whether some pattern arg is itself already visible in `mvar_id`'s
    /// own declared local context) is `false` on this crate's call path
    /// UNLESS `quasiPatternApprox` is on and actually let a ctx-local
    /// pattern arg through (`process_assignment`'s own loop, task 7):
    /// with the flag off, every pattern arg found in `mvarDecl.lctx` is
    /// still rejected before this function is ever reached, exactly as
    /// before. Either way, this function's own machinery
    /// (`check_assignment_scope`/`type_occurs_check`) does not itself
    /// branch on `hasCtxLocals` — the oracle's `hasCtxLocals`-gated
    /// choice between the "quick" check (`CheckAssignmentQuick.check`,
    /// what `check_assignment_scope` transcribes) and the expensive,
    /// term-REWRITING `CheckAssignment.checkAssignmentAux` (`ctxApprox`'s
    /// real home, ExprDefEq.lean:864-1030) stays a named SEAM, folded
    /// into `check_assignment_scope`'s own escalation-to-`None`/`false`
    /// case — see that function's own doc comment for why `ctxApprox`
    /// specifically cannot be soundly grafted into the quick, bool-only
    /// path instead (task 7 finding).
    pub(crate) fn check_assignment(
        &mut self,
        mvar_id: MVarId,
        fvars: &[ExprId],
        v: ExprId,
    ) -> Result<Option<ExprId>, MetaError> {
        // oracle: "check whether `mvarId` occurs in the type of `fvars`"
        // (:1153-1155). `inferType fvar` for an `FVar` is exactly
        // `self.lctx.get(fvar_id).ty` (`infer.rs::infer_fvar`), so this
        // reuses that existing entry point rather than re-deriving it.
        for &fvar in fvars {
            let ty = self.infer_type(fvar)?;
            if !self.occurs_check(mvar_id, ty)? {
                return Ok(None);
            }
        }
        if !self.data(v).has_expr_mvar() && !self.data(v).has_fvar() {
            return Ok(Some(v));
        }
        if !self.check_assignment_scope(mvar_id, fvars, v)? {
            // SEAM: this function's own doc comment.
            return Ok(None);
        }
        if !self.type_occurs_check(mvar_id, v)? {
            return Ok(None);
        }
        Ok(Some(v))
    }

    /// oracle: `CheckAssignmentQuick.check` (ExprDefEq.lean:1083-1130).
    /// The genuine content that survives: every FVAR met in `v` must be
    /// either one of the abstracted pattern `fvars`, or already visible
    /// in `mvar_id`'s own declared local context (`mvar_decl.lctx`) —
    /// anything else is a real, oracle-agreeing out-of-scope rejection
    /// (`throwOutOfScopeFVar`, :870 — not an approximation gap; the ONE
    /// rescue for a bare out-of-scope fvar, `checkFVar`'s non-dep-let
    /// value-follow, :864-870, is excluded defensively below since this
    /// crate's own machinery never mints a let-bound fvar, matching
    /// `mk_lambda_fvars_with_let_deps`'s own reasoning). `mvar_id == id`
    /// (the metavariable being assigned occurring directly in `v`) is
    /// the ONE non-approximated `MVar` case (:1113: `if mvarId' ==
    /// mvarId then return false`). Every OTHER metavariable met is
    /// SEAM: `isSubPrefixOf` (:1114) — this crate's `LocalContext`
    /// exposes no positional/enumeration API to port that lctx-subset
    /// check faithfully; at tier 1 (same posture as `level.rs`'s
    /// single-mctx-depth seam), every declared mvar is treated as
    /// mutually visible. `ctxApprox`'s rescue does NOT belong here at
    /// all (task 7 finding): this function transcribes
    /// `CheckAssignmentQuick.check`, which the oracle's own
    /// `checkAssignment` driver only ever uses to decide whether the
    /// SLOW, term-rewriting `CheckAssignment.checkAssignmentAux` path
    /// is even needed (:1160-1163) — `ctxApprox`'s rescue lives
    /// EXCLUSIVELY inside that slow path (`checkApp`/`checkMVar`,
    /// :864-1030), which rebuilds the checked term (substituting the
    /// rescued subterm) rather than returning a bare bool. Grafting the
    /// rescue's SIDE EFFECT (assigning the inner mvar) onto this
    /// function while still returning the ORIGINAL, un-rewritten `v` up
    /// through `check_assignment`'s quick-success path (`pure v`,
    /// :1162) would produce an assignment for `mvar_id` that still
    /// syntactically references a variable outside its own declared
    /// scope — ill-formed, not merely approximate. See
    /// `check_assignment_scope_body`'s `Node::App` arm for the fuller
    /// account (a first attempt at this task built exactly that grafted
    /// version and reverted it).
    fn check_assignment_scope(
        &mut self,
        mvar_id: MVarId,
        fvars: &[ExprId],
        e: ExprId,
    ) -> Result<bool, MetaError> {
        if !self.data(e).has_fvar() && !self.data(e).has_expr_mvar() {
            return Ok(true);
        }
        self.guarded(|ctx| ctx.check_assignment_scope_body(mvar_id, fvars, e))
    }

    fn check_assignment_scope_body(
        &mut self,
        mvar_id: MVarId,
        fvars: &[ExprId],
        e: ExprId,
    ) -> Result<bool, MetaError> {
        match self.node(e) {
            Node::FVar { id: Some(fid) } => {
                let in_mvar_lctx = self
                    .mctx
                    .decl(mvar_id)
                    .map(|d| d.lctx.get(fid).is_some())
                    .unwrap_or(false);
                if in_mvar_lctx {
                    return Ok(true);
                }
                let is_let = self.lctx.get(fid).and_then(|d| d.value).is_some();
                if is_let {
                    // Doc comment above: defensively unreachable.
                    return Ok(false);
                }
                Ok(fvars.contains(&e))
            }
            Node::MVar { id: Some(id) } => {
                if MVarId(id) == mvar_id {
                    return Ok(false);
                }
                // SEAM: `isSubPrefixOf` (doc comment above) — tier-1
                // always true.
                Ok(true)
            }
            // oracle: `checkApp`'s `ctxApprox` rescue (ExprDefEq.lean:
            // 952-978) lives ONLY in the SLOW path this arm does not
            // implement — see this function's own doc comment for why
            // (`CheckAssignmentQuick.check`, the function THIS ARM
            // transcribes, is a pure exception-free bool predicate,
            // :1040-1080: its OWN `.app`/`.fvar` cases have no rescue at
            // all, just `visit f <&&> visit a` and a plain out-of-scope
            // `false`; `checkAssignment`'s outer driver, :1160-1163,
            // only ever calls the SLOW, term-REWRITING
            // `CheckAssignment.checkAssignmentAux` — a different
            // function this crate does not build — when the quick check
            // here returns `false`). A first attempt at this task
            // (reverted) grafted the rescue into this bool-only
            // function anyway: it could get the VERDICT right by
            // mutating the inner mvar's assignment as a side effect,
            // but `checkAssignment`'s quick-success path uses `v`
            // UNCHANGED (`pure v`, :1162) — never the REWRITTEN term the
            // real rescue produces — so the surviving syntactic subterm
            // would still reference the rescued fvar, producing an
            // assignment that is free in a variable outside its own
            // declared scope. Left as a named SEAM instead: `ctxApprox`
            // never fires via this path (task 7, spec risk 3 —
            // acknowledged-thin, here meaning NOT reachable at all
            // rather than merely narrow; see the task report for the
            // full reasoning).
            Node::App { f, arg } => Ok(self.check_assignment_scope(mvar_id, fvars, f)?
                && self.check_assignment_scope(mvar_id, fvars, arg)?),
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => Ok(self.check_assignment_scope(mvar_id, fvars, binder_type)?
                && self.check_assignment_scope(mvar_id, fvars, body)?),
            Node::LetE {
                ty, value, body, ..
            } => Ok(self.check_assignment_scope(mvar_id, fvars, ty)?
                && self.check_assignment_scope(mvar_id, fvars, value)?
                && self.check_assignment_scope(mvar_id, fvars, body)?),
            Node::MData { expr, .. } => self.check_assignment_scope(mvar_id, fvars, expr),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                self.check_assignment_scope(mvar_id, fvars, structure)
            }
            _ => Ok(true),
        }
    }

    /// oracle: `typeOccursCheck`/`typeOccursCheckImp` (ExprDefEq.lean:
    /// 1139-1150): guards against an INDIRECT cycle through some OTHER
    /// (unassigned) metavariable `?n` found inside `v` whose own
    /// declared TYPE mentions `mvar_id` (issue #4405's `?m_1 :=
    /// (?m_2).1` where `?m_2 : Fin ?m_1`). Distinct from `occurs_check`
    /// (which finds `mvar_id` occurring DIRECTLY): this only ever runs
    /// `occurs_check` on the TYPE of an mvar node met while walking `v`,
    /// never recursing further through that mvar itself.
    fn type_occurs_check(&mut self, mvar_id: MVarId, e: ExprId) -> Result<bool, MetaError> {
        if !self.data(e).has_expr_mvar() {
            return Ok(true);
        }
        self.guarded(|ctx| ctx.type_occurs_check_body(mvar_id, e))
    }

    fn type_occurs_check_body(&mut self, mvar_id: MVarId, e: ExprId) -> Result<bool, MetaError> {
        match self.node(e) {
            // oracle: `visitMVar` (:1128-1131) — `false` (reject) when
            // the mvar's OWN decl can't even be found; a defensive,
            // conservative default the oracle itself takes, not this
            // crate's addition.
            Node::MVar { id: Some(id) } => match self.mctx.decl(MVarId(id)) {
                Some(d) => {
                    let ty = d.ty;
                    self.occurs_check(mvar_id, ty)
                }
                None => Ok(false),
            },
            Node::App { f, arg } => {
                Ok(self.type_occurs_check(mvar_id, f)? && self.type_occurs_check(mvar_id, arg)?)
            }
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => Ok(self.type_occurs_check(mvar_id, binder_type)?
                && self.type_occurs_check(mvar_id, body)?),
            Node::LetE {
                ty, value, body, ..
            } => Ok(self.type_occurs_check(mvar_id, ty)?
                && self.type_occurs_check(mvar_id, value)?
                && self.type_occurs_check(mvar_id, body)?),
            Node::MData { expr, .. } => self.type_occurs_check(mvar_id, expr),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                self.type_occurs_check(mvar_id, structure)
            }
            _ => Ok(true),
        }
    }

    /// oracle: `Lean.occursCheck` (`Lean/Util/OccursCheck.lean:18-53`):
    /// `true` iff `mvar_id` does NOT occur in `e`, following ASSIGNED
    /// mvars (an unassigned mvar node simply isn't `mvar_id` and has
    /// nothing further to recurse into — this crate's `MetavarContext`
    /// has no delayed-assignment channel to also follow, matching this
    /// module's other delayed-assignment elisions). This is THE occurs
    /// check the brief's step-1 test (`occurs_check_rejects_cycle`)
    /// exercises: `?m =?= N.succ ?m` walks into the `App`'s arg and
    /// meets `?m` itself.
    pub(crate) fn occurs_check(&mut self, mvar_id: MVarId, e: ExprId) -> Result<bool, MetaError> {
        if !self.data(e).has_expr_mvar() {
            return Ok(true);
        }
        self.guarded(|ctx| ctx.occurs_check_body(mvar_id, e))
    }

    fn occurs_check_body(&mut self, mvar_id: MVarId, e: ExprId) -> Result<bool, MetaError> {
        match self.node(e) {
            Node::MVar { id: Some(id) } => {
                if MVarId(id) == mvar_id {
                    return Ok(false);
                }
                match self.mctx.assignment(MVarId(id)) {
                    Some(v) => self.occurs_check(mvar_id, v),
                    None => Ok(true),
                }
            }
            Node::App { f, arg } => {
                Ok(self.occurs_check(mvar_id, f)? && self.occurs_check(mvar_id, arg)?)
            }
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => Ok(self.occurs_check(mvar_id, binder_type)? && self.occurs_check(mvar_id, body)?),
            Node::LetE {
                ty, value, body, ..
            } => Ok(self.occurs_check(mvar_id, ty)?
                && self.occurs_check(mvar_id, value)?
                && self.occurs_check(mvar_id, body)?),
            Node::MData { expr, .. } => self.occurs_check(mvar_id, expr),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                self.occurs_check(mvar_id, structure)
            }
            _ => Ok(true),
        }
    }

    // ===================================================================
    // instantiateMVars — the shared read-back primitive.
    // ===================================================================

    /// oracle: `instantiateMVars`/`instantiateMVarsImp`
    /// (`MetavarContext.lean`, `@[extern]` opaque — no Lean source to
    /// transcribe line-by-line, same posture as `level.rs`'s
    /// `instantiate_level_mvars`). Recursively replaces every ASSIGNED
    /// `MVar` node with its (recursively instantiated) assignment;
    /// everything else rebuilt only if a child actually changed. `pub`,
    /// not `pub(crate)`: `process_assignment`'s own "enforce A4" step
    /// needs it, and it is ALSO the harness gate's read-back primitive
    /// for the new `defeq_mvar` records (`oracle_fast.rs`) — a second,
    /// independent re-implementation there would just be this function
    /// copied across the crate boundary, so it is exposed as public API
    /// instead of duplicated.
    pub fn instantiate_mvars(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        self.step()?;
        if !self.data(e).has_expr_mvar() {
            return Ok(e);
        }
        self.guarded(|ctx| ctx.instantiate_mvars_body(e))
    }

    fn instantiate_mvars_body(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        match self.node(e) {
            Node::MVar { id: Some(id) } => match self.mctx.assignment(MVarId(id)) {
                Some(v) => self.instantiate_mvars(v),
                None => Ok(e),
            },
            Node::App { f, arg } => {
                let f2 = self.instantiate_mvars(f)?;
                let a2 = self.instantiate_mvars(arg)?;
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
                let t2 = self.instantiate_mvars(binder_type)?;
                let b2 = self.instantiate_mvars(body)?;
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
                let t2 = self.instantiate_mvars(binder_type)?;
                let b2 = self.instantiate_mvars(body)?;
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
                let t2 = self.instantiate_mvars(ty)?;
                let v2 = self.instantiate_mvars(value)?;
                let b2 = self.instantiate_mvars(body)?;
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
                let e2 = self.instantiate_mvars(expr)?;
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
                let s2 = self.instantiate_mvars(structure)?;
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
                let s2 = self.instantiate_mvars(structure)?;
                if s2 == structure {
                    Ok(e)
                } else {
                    Ok(self
                        .scratch
                        .expr_proj(Some(self.view.store), type_name, &idxn, s2)?)
                }
            }
            // BVar/BVarBig/FVar/Sort/Const/LitNat/LitStr/anonymous MVar:
            // none carry an expr mvar that could be assigned differently
            // from `e` itself.
            _ => Ok(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use leanr_kernel::bank::{ExprId, NameId, Store};
    use leanr_kernel::{
        AxiomVal, CheckedConstants, ConstSource, ConstantInfo, ConstantVal, EnvView,
    };

    use crate::test_support::{fresh_fvar, fresh_mvar};
    use crate::{Config, MetaCtx};

    /// A tiny bespoke environment (NOT `test_support::with_ctx`'s
    /// totally-empty one): `N.zero`/`N.succ` are declared as `Prop`-
    /// typed axioms (brief step 1: "use Sort 0 as the mvar type and
    /// Prop-typed constants") purely so `check_types_and_assign`'s
    /// `infer_type` calls have something to resolve — `checkTypesAndAssign`
    /// runs even for a trivial nullary assignment (`processAssignment`'s
    /// `args.any (mvarDecl.lctx.containsFVar)` guard is vacuously false
    /// on an EMPTY arg list, so its `else` branch, `checkTypesAndAssign`,
    /// always runs). Neither test below depends on what "N" MEANS —
    /// only that `N.zero : Sort 0` matches `n_type`'s own `Sort 0`.
    fn with_n_ctx<R>(f: impl FnOnce(&mut MetaCtx) -> R) -> R {
        with_n_ctx_cfg(Config::default(), f)
    }

    /// `with_n_ctx`, parameterized over `Config` (task 7: the
    /// approximation flag-gating tests below need `fo_approx`/
    /// `const_approx` on, everything else identical to `with_n_ctx`'s
    /// own env — same two `N.zero`/`N.succ` axioms, so both helpers stay
    /// interchangeable for existing tests).
    fn with_n_ctx_cfg<R>(cfg: Config, f: impl FnOnce(&mut MetaCtx) -> R) -> R {
        let mut base = Store::persistent();
        let z = base.level_zero(None).expect("level zero");
        let sort0 = base.expr_sort(None, z).expect("sort 0");
        let mut consts = HashMap::new();
        for name in ["N.zero", "N.succ"] {
            let mut id: Option<NameId> = None;
            for part in name.split('.') {
                let sid = base.intern_str(None, part).expect("intern");
                id = Some(base.name_str(None, id, sid).expect("name"));
            }
            let nid = id.expect("nonempty name");
            let info = ConstantInfo::Axiom(AxiomVal {
                val: ConstantVal {
                    name: nid,
                    level_params: vec![],
                    ty: sort0,
                },
                is_unsafe: false,
            });
            consts.insert(nid, info);
        }
        let const_names: Vec<NameId> = consts.keys().copied().collect();
        let checked = CheckedConstants::new(consts);
        // `CheckedConstants::get` (checked.rs) is admission-GATED — an
        // entry present in the map is still invisible until `admit`
        // flips its flag (the parallel-driver contract, checked.rs's
        // own module doc). This test env has no driver admitting
        // anything, so every constant must be admitted by hand here.
        for nid in const_names {
            checked.admit(nid);
        }
        let mut scratch = Store::scratch();
        let view = EnvView {
            consts: ConstSource::Gated(&checked),
            extra: None,
            quot_initialized: false,
            store: &base,
        };
        let mut ctx = MetaCtx::new(view, &mut scratch, cfg, &[], &[], &[], &[], &[]);
        f(&mut ctx)
    }

    fn n_type(ctx: &mut MetaCtx) -> ExprId {
        let base = Some(ctx.view.store);
        let z = ctx.scratch.level_zero(base).expect("level");
        ctx.scratch.expr_sort(base, z).expect("sort")
    }

    fn mk_const(ctx: &mut MetaCtx, name: &str) -> ExprId {
        let base = Some(ctx.view.store);
        let mut id: Option<NameId> = None;
        for part in name.split('.') {
            let sid = ctx.scratch.intern_str(base, part).expect("intern");
            id = Some(ctx.scratch.name_str(base, id, sid).expect("name"));
        }
        let no_levels = ctx.scratch.intern_level_list(base, &[]).expect("levels");
        ctx.scratch.expr_const(base, id, no_levels).expect("const")
    }

    fn mk_app(ctx: &mut MetaCtx, f: ExprId, a: ExprId) -> ExprId {
        ctx.scratch
            .expr_app(Some(ctx.view.store), f, a)
            .expect("app")
    }

    /// A non-dependent `dom -> cod` Pi, needed by the `const_approx`
    /// test below: `assignConst`/`assign_const` opens a
    /// `forallBoundedTelescope` over the mvar's OWN declared type, which
    /// must therefore actually BE a `Forall` (not a bare `Sort`, unlike
    /// every other test in this module) for that telescope to open
    /// anything at all.
    fn mk_forall(ctx: &mut MetaCtx, dom: ExprId, cod: ExprId) -> ExprId {
        ctx.scratch
            .expr_forall(
                Some(ctx.view.store),
                None,
                dom,
                cod,
                leanr_kernel::BinderInfo::Default,
            )
            .expect("forall")
    }

    /// oracle: `processAssignmentFOApprox` (ExprDefEq.lean:1184-1210),
    /// gated by `self.cfg.fo_approx` — `?m N.zero =?= N.succ N.zero`.
    /// `N.zero` is a non-fvar pattern argument, so `process_assignment`'s
    /// per-arg loop seams straight to `use_fo_approx` at `i = 0`
    /// regardless of the flag; only with `fo_approx` on does
    /// `processAssignmentFOApproxAux`'s first-order decomposition
    /// (`args.back! =?= a` and `?m args[..n-1] =?= f`, here trivially
    /// `N.zero =?= N.zero` and `?m =?= N.succ`) actually fire, assigning
    /// `?m := N.succ`. Flag off must reproduce task 5/6's own `Ok(false)`
    /// seam exactly (the `default`-profile regression this task's brief
    /// requires).
    #[test]
    fn fo_approx_flag_gates_first_order_unification() {
        for (fo_approx, expected) in [(false, false), (true, true)] {
            with_n_ctx_cfg(
                Config {
                    fo_approx,
                    ..Config::default()
                },
                |ctx| {
                    let ty = n_type(ctx);
                    let (m_expr, m_id) = fresh_mvar(ctx, ty);
                    let zero = mk_const(ctx, "N.zero");
                    let succ = mk_const(ctx, "N.succ");
                    let lhs = mk_app(ctx, m_expr, zero);
                    let rhs = mk_app(ctx, succ, zero);
                    assert_eq!(
                        ctx.is_def_eq(lhs, rhs).unwrap(),
                        expected,
                        "fo_approx={fo_approx}"
                    );
                    assert_eq!(ctx.mctx.is_assigned(m_id), expected);
                    if expected {
                        assert_eq!(ctx.mctx.assignment(m_id), Some(succ));
                    }
                },
            );
        }
    }

    /// oracle: `processConstApprox`/`assignConst` (ExprDefEq.lean:
    /// 1271-1310, :1243-1254), gated by `self.cfg.const_approx` —
    /// `?m N.zero =?= N.succ` where `?m : Sort 0 -> Sort 0`. `N.zero` is
    /// again a non-fvar pattern arg (same seam site as the `fo_approx`
    /// test above), but this time the RHS `N.succ` is NOT an
    /// application, so `processAssignmentFOApproxAux` can never match
    /// regardless of `fo_approx` — isolating `const_approx` cleanly.
    /// With the flag on, `processConstApprox`'s `patternVarPrefix == 0`
    /// case (`defaultCase`) opens ONE fresh fvar from `?m`'s own
    /// declared `Sort 0 -> Sort 0` telescope and assigns `?m := fun _ =>
    /// N.succ` — the exact scenario the brief's own step 1 names.
    #[test]
    fn const_approx_flag_gates_constant_function_assignment() {
        for (const_approx, expected) in [(false, false), (true, true)] {
            with_n_ctx_cfg(
                Config {
                    const_approx,
                    ..Config::default()
                },
                |ctx| {
                    let s0 = n_type(ctx);
                    let mvar_ty = mk_forall(ctx, s0, s0);
                    let (m_expr, m_id) = fresh_mvar(ctx, mvar_ty);
                    let zero = mk_const(ctx, "N.zero");
                    let succ = mk_const(ctx, "N.succ");
                    let lhs = mk_app(ctx, m_expr, zero);
                    assert_eq!(
                        ctx.is_def_eq(lhs, succ).unwrap(),
                        expected,
                        "const_approx={const_approx}"
                    );
                    assert_eq!(ctx.mctx.is_assigned(m_id), expected);
                },
            );
        }
    }

    /// oracle: `isDefEqMVarSelf`'s OWN separate `constApprox` fallback
    /// (ExprDefEq.lean:1799-1801) — a SECOND `constApprox` call site,
    /// distinct from `process_assignment`'s (the test above): `?m a =?=
    /// ?m b` (SAME mvar both sides) with `a ≠ b` DISTINCT fvars, so
    /// `is_def_eq_args`'s pairwise unification fails outright (`a` and
    /// `b` are unrelated fvars — no rule makes them def-eq) and
    /// `isDefEqMVarSelf` falls to `mkAuxMVar mvarDecl.lctx .. <;>
    /// assignConst`. `Sort 1` (not `Sort 0`/`Prop`), deliberately: `a`,
    /// `b : Sort 1` keeps proof irrelevance (`is_def_eq_proof_irrel`,
    /// task 6) from ALSO making `a =?= b` true for an unrelated reason
    /// (any two `Sort 0`-typed terms are proof-irrelevant-equal), which
    /// would make this test pass without ever reaching `constApprox` at
    /// all.
    #[test]
    fn const_approx_gates_is_def_eq_mvar_self_fallback() {
        for (const_approx, expected) in [(false, false), (true, true)] {
            with_n_ctx_cfg(
                Config {
                    const_approx,
                    ..Config::default()
                },
                |ctx| {
                    let z = ctx.scratch.level_zero(None).unwrap();
                    let one = ctx.scratch.level_succ(None, z).unwrap();
                    let sort1 = ctx.scratch.expr_sort(None, one).unwrap();
                    let mvar_ty = mk_forall(ctx, sort1, sort1);
                    let (m_expr, m_id) = fresh_mvar(ctx, mvar_ty);
                    let a = fresh_fvar(ctx, sort1, "a");
                    let b = fresh_fvar(ctx, sort1, "b");
                    let lhs = mk_app(ctx, m_expr, a);
                    let rhs = mk_app(ctx, m_expr, b);
                    assert_eq!(
                        ctx.is_def_eq(lhs, rhs).unwrap(),
                        expected,
                        "const_approx={const_approx}"
                    );
                    assert_eq!(ctx.mctx.is_assigned(m_id), expected);
                },
            );
        }
    }

    #[test]
    fn assigns_a_pattern_mvar() {
        with_n_ctx(|ctx| {
            // ?m =?= N.zero  (nullary pattern) -> ?m := N.zero
            let ty = n_type(ctx);
            let (m_expr, m_id) = fresh_mvar(ctx, ty);
            let zero = mk_const(ctx, "N.zero");
            assert!(ctx.is_def_eq(m_expr, zero).unwrap());
            assert_eq!(ctx.mctx.assignment(m_id), Some(zero));
        });
    }

    #[test]
    fn occurs_check_rejects_cycle() {
        with_n_ctx(|ctx| {
            // ?m =?= N.succ ?m  -> must NOT assign (occurs), verdict false
            let ty = n_type(ctx);
            let (m_expr, m_id) = fresh_mvar(ctx, ty);
            let succ = mk_const(ctx, "N.succ");
            let succ_m = mk_app(ctx, succ, m_expr);
            assert!(!ctx.is_def_eq(m_expr, succ_m).unwrap());
            assert!(!ctx.mctx.is_assigned(m_id));
        });
    }
}
