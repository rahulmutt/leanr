//! oracle: `Lean/Meta/Coe.lean` (v4.33.0-rc1), 1:1 — `expandCoe`
//! (`:44-70`), `coerceSimpleRecordingNames?`/`coerceSimple?` (`:78-98`),
//! `coerceToFunction?` (`:100-112`), `coerceToSort?` (`:114-126`),
//! `isTypeApp?` (`:128-132`), `coerceCollectingNames?`/`coerce?`
//! (`:259-278`). `coerceMonadLift?` (`:201-257`) is a shape GUARD, not a
//! port — design spec § Amendment 5 item 6 and `monad_lift_guard` below.
//!
//! Dropped, deliberately, because they have no term impact (§ Amendment
//! 5 item 5): the applied-instance name list (`StateT` over `List Name`,
//! consumed only by the `CoeExpansionTrace` info leaf), `pushInfoLeaf`,
//! and `recordExtraModUseFromDecl` (`recProjTarget`'s only purpose).
//!
//! What `expandCoe` actually reduces: `CoeT.coe` and its siblings are
//! class projections, kept NON-reducible by the oracle (`WHNF.lean:810-811`),
//! so under `.instances` `unfoldDefinition?`'s `matchConstAux` fails and
//! its continuation `unfoldProjInstWhenInstances?` (`:814-818`) →
//! `unfoldProjInst?` (`:793-806`) does the work: delta-beta the projection
//! at default transparency, then reduce `inst.1` against the instance's
//! constructor at `.instances`. `whnf.rs::unfold_definition_app` already
//! routes both failure sub-conditions to `unfold_proj_inst` (M4a plan 4
//! task B6), so `expand_coe` needs no `whnf.rs` change.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId};

use crate::synth::LOption;
use crate::transform::TransformStep;
use crate::{MetaCtx, MetaError, TransparencyMode};

impl<'e> MetaCtx<'e> {
    fn name_of(&mut self, parts: &[&str]) -> Result<NameId, MetaError> {
        let base = Some(self.view.store);
        let mut id: Option<NameId> = None;
        for p in parts {
            let s = self.scratch.intern_str(base, p)?;
            id = Some(self.scratch.name_str(base, id, s)?);
        }
        Ok(id.expect("name_of: non-empty"))
    }

    fn const_with_levels(
        &mut self,
        parts: &[&str],
        levels: &[LevelId],
    ) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let n = self.name_of(parts)?;
        let ls = self.scratch.intern_level_list(base, levels)?;
        Ok(self.scratch.expr_const(base, Some(n), ls)?)
    }

    fn mk_app_n(&mut self, f: ExprId, args: &[ExprId]) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let mut r = f;
        for a in args {
            r = self.scratch.expr_app(base, r, *a)?;
        }
        Ok(r)
    }

    /// oracle: `expandCoe` (`Coe.lean:44-70`) — under
    /// `withReducibleAndInstances`, `transform` with a `pre` that, on an
    /// application whose head is a `@[coe_decl]` constant, unfolds it
    /// (`unfoldDefinition?`, `:56` — see the module doc for what that
    /// actually reduces on a class projection), `headBeta`s, and
    /// `.visit`s the result so `pre` runs on it again (`:66`); every
    /// other node `.continue`s (`:67`).
    pub fn expand_coe(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        self.with_transparency(TransparencyMode::Instances, |ctx| {
            ctx.transform(e, &mut |ctx, e| {
                let f = ctx.get_app_fn(e);
                if let Node::Const {
                    name: Some(decl), ..
                } = ctx.node(f)
                {
                    if ctx.is_coe_decl(decl) {
                        if let Some(e2) = ctx.unfold_definition(e)? {
                            let e2 = ctx.head_beta(e2)?;
                            return Ok(TransformStep::Visit(e2));
                        }
                    }
                }
                Ok(TransformStep::Continue(None))
            })
        })
    }

    /// oracle: `coerceSimpleRecordingNames?` + `coerceSimple?`
    /// (`Coe.lean:78-98`) — synthesize `CoeT.{u,v} eType e expected`,
    /// build `CoeT.coe.{u,v} eType e expected inst`, `expandCoe`, and
    /// VERIFY the result's type is defeq to `expected` (`:86-87`): a
    /// mismatch is a hard error, not a silent pass.
    pub fn coerce_simple(
        &mut self,
        e: ExprId,
        expected: ExprId,
    ) -> Result<LOption<ExprId>, MetaError> {
        let e_type = self.infer_type(e)?;
        let u = self.get_level(e_type)?;
        let v = self.get_level(expected)?;
        let coe_t = self.const_with_levels(&["CoeT"], &[u, v])?;
        let goal = self.mk_app_n(coe_t, &[e_type, e, expected])?;
        match self.try_synth_instance(goal)? {
            LOption::Some(inst) => {
                let coe_t_coe = self.const_with_levels(&["CoeT", "coe"], &[u, v])?;
                let app = self.mk_app_n(coe_t_coe, &[e_type, e, expected, inst])?;
                let result = self.expand_coe(app)?;
                let r_type = self.infer_type(result)?;
                if !self.is_def_eq(r_type, expected)? {
                    return Err(MetaError::CoeExpansionMismatch(
                        "could not coerce: coerced expression has wrong type (Coe.lean:86-87)"
                            .into(),
                    ));
                }
                Ok(LOption::Some(result))
            }
            LOption::Undef => Ok(LOption::Undef),
            LOption::None => Ok(LOption::None),
        }
    }

    /// oracle: `coerceToFunction?` (`Coe.lean:100-112`) — `α ← inferType`,
    /// `u ← getLevel α`, `v` a fresh level mvar, `?γ : α → Sort v` a fresh
    /// expr mvar (the class's `outParam`, which the search assigns —
    /// P2b-i's `assignOutParams`), `trySynthInstance (CoeFun.{u,v} α ?γ)`
    /// with BOTH `.none` and `.undef` mapped to `none` (`:106`), expand
    /// `CoeFun.coe.{u,v} α ?γ inst e`, and require the result's type to
    /// `whnf` to a `forall` (`:108-110`).
    pub fn coerce_to_function(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        let base = Some(self.view.store);
        let alpha = self.infer_type(e)?;
        let u = self.get_level(alpha)?;
        let (_, v) = self.fresh_level_mvar()?;
        let sort_v = self.scratch.expr_sort(base, v)?;
        let gamma_ty = self.mk_arrow(alpha, sort_v)?;
        let (gamma, _) = self.mk_aux_mvar(gamma_ty)?;
        let coe_fun = self.const_with_levels(&["CoeFun"], &[u, v])?;
        let goal = self.mk_app_n(coe_fun, &[alpha, gamma])?;
        let LOption::Some(inst) = self.try_synth_instance(goal)? else {
            return Ok(None);
        };
        let coe = self.const_with_levels(&["CoeFun", "coe"], &[u, v])?;
        let app = self.mk_app_n(coe, &[alpha, gamma, inst, e])?;
        let expanded = self.expand_coe(app)?;
        let t = self.infer_type(expanded)?;
        let w = self.whnf(t)?;
        if !matches!(self.node(w), Node::Forall { .. }) {
            return Err(MetaError::CoeExpansionMismatch(
                "failed to coerce to a function: after applying CoeFun.coe the result is still not a function (Coe.lean:108-110)".into(),
            ));
        }
        Ok(Some(expanded))
    }

    /// oracle: `coerceToSort?` (`Coe.lean:114-126`) — the `CoeSort` twin:
    /// `?β : Sort v`, `CoeSort.{u,v} α ?β`, expand `CoeSort.coe.{u,v} α ?β
    /// inst e`, require a `Sort` (`:122-124`).
    pub fn coerce_to_sort(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        let base = Some(self.view.store);
        let alpha = self.infer_type(e)?;
        let u = self.get_level(alpha)?;
        let (_, v) = self.fresh_level_mvar()?;
        let sort_v = self.scratch.expr_sort(base, v)?;
        let (beta, _) = self.mk_aux_mvar(sort_v)?;
        let coe_sort = self.const_with_levels(&["CoeSort"], &[u, v])?;
        let goal = self.mk_app_n(coe_sort, &[alpha, beta])?;
        let LOption::Some(inst) = self.try_synth_instance(goal)? else {
            return Ok(None);
        };
        let coe = self.const_with_levels(&["CoeSort", "coe"], &[u, v])?;
        let app = self.mk_app_n(coe, &[alpha, beta, inst, e])?;
        let expanded = self.expand_coe(app)?;
        let t = self.infer_type(expanded)?;
        let w = self.whnf(t)?;
        if !matches!(self.node(w), Node::Sort { .. }) {
            return Err(MetaError::CoeExpansionMismatch(
                "failed to coerce to a type: after applying CoeSort.coe the result is still not a type (Coe.lean:122-124)".into(),
            ));
        }
        Ok(Some(expanded))
    }

    /// oracle: `isTypeApp?` (`Coe.lean:128-132`) — `withReducible whnf`,
    /// then `some (m, α)` on an `.app m α` with both halves
    /// `instantiateMVars`-ed.
    pub(crate) fn is_type_app(
        &mut self,
        ty: ExprId,
    ) -> Result<Option<(ExprId, ExprId)>, MetaError> {
        let w = self.whnf_r(ty)?;
        match self.node(w) {
            Node::App { f, arg } => {
                let f = self.instantiate_mvars(f)?;
                let a = self.instantiate_mvars(arg)?;
                Ok(Some((f, a)))
            }
            _ => Ok(None),
        }
    }

    /// The monad-lift shape guard (design spec § Amendment 5 item 6) —
    /// NOT a port of `coerceMonadLift?` (`Coe.lean:201-257`), which is
    /// the do-notation slice's.
    ///
    /// The oracle tries it FIRST (`:260`), so silently skipping it would
    /// let a term the oracle coerces via `coeM`/`liftM`/`liftCoeM` fall
    /// through to `CoeT` and emit a different term. But it can only
    /// return `some` when (a) both `expectedType` and `eType` are
    /// `isTypeApp?` (`:204-205`) AND (b) either `isMonad? n` answers
    /// `some` — `trySynthInstance (Monad n)` inside a `try … catch _ =>
    /// none` (`AppBuilder.lean:701-709`) — or `autoLift`'s `MonadLiftT m n`
    /// synthesis inside another `try … catch _ => return none`
    /// (`:214-245`) does. Without `Monad` and `MonadLiftT` in the
    /// environment both are `none` on every input, and the oracle
    /// proceeds to `coerceToFunction?`/`coerceSimpleRecordingNames?`.
    /// So the guard is exactly (a) ∧ (env contains `Monad` ∨ `MonadLiftT`),
    /// and on every other shape leanr proceeds as the oracle does.
    ///
    /// Known residual, owner do-notation slice: on the `autoLift` branch
    /// the oracle runs `isLevelDefEq` (`:224`) BEFORE the `MonadLiftT`
    /// synthesis fails, and that level assignment is not rolled back.
    /// With concrete-universe type constructors — every shape the
    /// fixtures can express — it assigns nothing.
    fn monad_lift_guard(&mut self, e: ExprId, expected: ExprId) -> Result<(), MetaError> {
        let expected = self.instantiate_mvars(expected)?;
        let e_type = self.infer_type(e)?;
        let e_type = self.instantiate_mvars(e_type)?;
        if self.is_type_app(expected)?.is_none() {
            return Ok(());
        }
        if self.is_type_app(e_type)?.is_none() {
            return Ok(());
        }
        let monad = self.name_of(&["Monad"])?;
        let lift = self.name_of(&["MonadLiftT"])?;
        if self.view.get(monad).is_some() || self.view.get(lift).is_some() {
            return Err(MetaError::Unsupported(
                "monad-lift coercion requires the do-notation slice".into(),
            ));
        }
        Ok(())
    }

    /// oracle: `coerceCollectingNames?` + `coerce?` (`Coe.lean:259-278`),
    /// preserving the dispatch order — monad lift (the guard), then
    /// `CoeFun` when `whnfR expectedType` is a `forall` and the coerced
    /// function's type is defeq to it (`:262-265`), then `CoeT`.
    pub fn coerce(&mut self, e: ExprId, expected: ExprId) -> Result<LOption<ExprId>, MetaError> {
        self.monad_lift_guard(e, expected)?;
        let w = self.whnf_r(expected)?;
        if matches!(self.node(w), Node::Forall { .. }) {
            if let Some(f) = self.coerce_to_function(e)? {
                let f_type = self.infer_type(f)?;
                if self.is_def_eq(f_type, expected)? {
                    return Ok(LOption::Some(f));
                }
            }
        }
        self.coerce_simple(e, expected)
    }
}

#[cfg(test)]
mod tests {
    use crate::synth::LOption;
    use crate::test_support::{
        const_dotted, const_named, render_expr, with_instances_ctx, with_synth0_ctx,
    };
    use crate::{MetaCtx, MetaError};
    use leanr_kernel::bank::ExprId;

    fn app(ctx: &mut MetaCtx, f: ExprId, args: &[ExprId]) -> ExprId {
        let base = Some(ctx.view.store);
        let mut r = f;
        for a in args {
            r = ctx.scratch.expr_app(base, r, *a).expect("app");
        }
        r
    }

    /// `(N.zero : M)` — one `Coe` step: the instance is found through
    /// `CoeT ← CoeHTCT ← CoeHTC ← CoeOTC ← CoeTC ← Coe`, and `expand_coe`
    /// unfolds every projection down to the instance's own function.
    #[test]
    fn coerce_simple_expands_one_step_to_the_instance_function() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let m = const_named(ctx, "M");
            let of_n = const_dotted(ctx, "M", "ofN");
            let want = app(ctx, of_n, &[zero]);
            match ctx.coerce_simple(zero, m).expect("coerce") {
                LOption::Some(got) => assert_eq!(render_expr(ctx, got), render_expr(ctx, want)),
                other => panic!("expected Some, got {other:?}"),
            }
        });
    }

    /// `(N.zero : Big)` — two steps through `CoeTC`'s transitive
    /// instance (`[Coe β γ] [CoeTC α β] : CoeTC α γ`, `β := M` found by
    /// the search). Kill: stub `expand_coe` to the identity and the
    /// result carries `CoeT.coe`.
    #[test]
    fn coerce_simple_expands_two_steps() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let big = const_named(ctx, "Big");
            let of_n = const_dotted(ctx, "M", "ofN");
            let of_m = const_dotted(ctx, "Big", "ofM");
            let inner = app(ctx, of_n, &[zero]);
            let want = app(ctx, of_m, &[inner]);
            match ctx.coerce_simple(zero, big).expect("coerce") {
                LOption::Some(got) => assert_eq!(render_expr(ctx, got), render_expr(ctx, want)),
                other => panic!("expected Some, got {other:?}"),
            }
        });
    }

    /// `(N.zero : N)` — the reflexive `instance : CoeT α a α` (declared
    /// last, tried first) whose `coe := a`; the expansion IS `N.zero`.
    #[test]
    fn coerce_simple_reflexive_expands_to_the_term_itself() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let n = const_named(ctx, "N");
            assert!(
                matches!(ctx.coerce_simple(zero, n).expect("coerce"), LOption::Some(got) if got == zero)
            );
        });
    }

    /// `(N.zero : NoBase)` — no path through the diamond; `.none`, and
    /// the search TERMINATES (the reflexive/transitive instances are
    /// what a non-tabled resolver would loop on).
    #[test]
    fn coerce_simple_answers_none_when_no_chain_exists() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let no_base = const_named(ctx, "NoBase");
            assert!(matches!(
                ctx.coerce_simple(zero, no_base).expect("coerce"),
                LOption::None
            ));
        });
    }

    /// `coerceToFunction?` on `FnN.mk N.succ : FnN` — `CoeFun FnN ?γ`
    /// assigns the outParam, and the expansion is `FnN.f (FnN.mk N.succ)`,
    /// whose type reduces to a `forall`.
    #[test]
    fn coerce_to_function_expands_the_coe_fun_instance() {
        with_synth0_ctx(|ctx| {
            let succ = const_dotted(ctx, "N", "succ");
            let mk = const_dotted(ctx, "FnN", "mk");
            let g = app(ctx, mk, &[succ]);
            let f = const_dotted(ctx, "FnN", "f");
            let want = app(ctx, f, &[g]);
            let got = ctx.coerce_to_function(g).expect("coerce").expect("some");
            assert_eq!(render_expr(ctx, got), render_expr(ctx, want));
        });
    }

    /// `coerceToFunction?` on something with no `CoeFun` instance is
    /// `none`, not an error.
    #[test]
    fn coerce_to_function_is_none_without_an_instance() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            assert!(ctx.coerce_to_function(zero).expect("coerce").is_none());
        });
    }

    /// `coerceToSort?` on `SortN.mk N : SortN` — `CoeSort SortN ?β`
    /// assigns the outParam; the expansion `SortN.ty (SortN.mk N)` has a
    /// `Sort` type.
    #[test]
    fn coerce_to_sort_expands_the_coe_sort_instance() {
        with_synth0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let mk = const_dotted(ctx, "SortN", "mk");
            let s = app(ctx, mk, &[n]);
            let ty = const_dotted(ctx, "SortN", "ty");
            let want = app(ctx, ty, &[s]);
            let got = ctx.coerce_to_sort(s).expect("coerce").expect("some");
            assert_eq!(render_expr(ctx, got), render_expr(ctx, want));
        });
    }

    /// `coerce` dispatch order (`Coe.lean:259-266`): with a `forall`
    /// expected type, `CoeFun` is tried BEFORE `CoeT`. This needs a
    /// DEPENDENT `γ` to be observable at all: `CoeOut`'s bridge instance
    /// (`instance [CoeFun α fun _ => β] : CoeOut α β`) can only unify a
    /// NON-dependent `γ` against its own `fun _ => β` pattern, so for a
    /// carrier like `FnN` (`γ := fun _ => N → N`) the general `CoeT`
    /// chase reaches the same `CoeFun` instance too and answers the
    /// identical term regardless of dispatch order (§ Amendment 5 item
    /// 10 — see `Synth0.lean`'s own doc comment on `DepFn`). `DepFn`'s
    /// `γ := fun d => d.dom → d.dom` mentions its own binder, so that
    /// unification fails, `CoeOut`/`CoeT`'s route answers `.none`, and
    /// ONLY the `coerceToFunction?`-first branch in `coerce?` produces a
    /// term — making this test a genuine discriminator of the order.
    #[test]
    fn coerce_prefers_coe_fun_under_a_forall_expected_type() {
        with_synth0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let succ = const_dotted(ctx, "N", "succ");
            let mk = const_dotted(ctx, "DepFn", "mk");
            let d = app(ctx, mk, &[n, succ]);
            let expected = ctx.infer_type(succ).expect("N -> N");
            let f = const_dotted(ctx, "DepFn", "f");
            let want = app(ctx, f, &[d]);
            match ctx.coerce(d, expected).expect("coerce") {
                LOption::Some(got) => assert_eq!(render_expr(ctx, got), render_expr(ctx, want)),
                other => panic!("expected Some, got {other:?}"),
            }
        });
    }

    /// `expand_coe` on an untagged head is the identity.
    #[test]
    fn expand_coe_leaves_untagged_heads_alone() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let succ = const_dotted(ctx, "N", "succ");
            let e = app(ctx, succ, &[zero]);
            assert_eq!(ctx.expand_coe(e).expect("expand"), e);
        });
    }

    /// The monad-lift guard (design spec § Amendment 5 item 6). Over
    /// `Instances.olean`, which declares `Monad`: two type applications
    /// (`Prod N N` vs `Prod N NoBase`) hit the seam. Over `Synth0.olean`,
    /// which does not: the same shape falls through to `coerce_simple`
    /// and answers `.none`, exactly as the oracle's `coerceMonadLift?`
    /// returns `none` in an environment without `Monad`/`MonadLiftT`.
    #[test]
    fn monad_lift_guard_fires_only_when_the_env_declares_monad() {
        fn prod_shape(ctx: &mut MetaCtx) -> (ExprId, ExprId) {
            let base = Some(ctx.view.store);
            let zero_l = ctx.scratch.level_zero(base).expect("level");
            let ls = ctx
                .scratch
                .intern_level_list(base, &[zero_l, zero_l])
                .expect("levels");
            let n = const_named(ctx, "N");
            let no_base = const_named(ctx, "NoBase");
            let zero = const_dotted(ctx, "N", "zero");
            let mk_str = ctx.scratch.intern_str(base, "Prod").expect("intern");
            let prod = ctx.scratch.name_str(base, None, mk_str).expect("name");
            let mk_s = ctx.scratch.intern_str(base, "mk").expect("intern");
            let prod_mk = ctx.scratch.name_str(base, Some(prod), mk_s).expect("name");
            let prod_c = ctx.scratch.expr_const(base, Some(prod), ls).expect("const");
            let prod_mk_c = ctx
                .scratch
                .expr_const(base, Some(prod_mk), ls)
                .expect("const");
            let e = app(ctx, prod_mk_c, &[n, n, zero, zero]);
            let expected = app(ctx, prod_c, &[n, no_base]);
            (e, expected)
        }
        with_instances_ctx(|ctx| {
            let (e, expected) = prod_shape(ctx);
            match ctx.coerce(e, expected) {
                Err(MetaError::Unsupported(m)) => assert!(m.contains("do-notation"), "{m}"),
                other => panic!("expected the monad-lift seam, got {other:?}"),
            }
        });
        with_synth0_ctx(|ctx| {
            let (e, expected) = prod_shape(ctx);
            assert!(matches!(
                ctx.coerce(e, expected).expect("coerce"),
                LOption::None
            ));
        });
    }

    /// Coercing a `fun`-bound VALUE, not a constant — the shape that
    /// blocked M4b-3 P4's elaborator tier (design spec § The finding,
    /// measured). `CoeT α a β` takes the coerced value as a class
    /// parameter, so the search must assign a candidate's telescope
    /// metavariable to a local variable; before the
    /// metavariable-local-contexts slice that assignment was rejected as
    /// out of scope and this answered `.none`.
    ///
    /// The expansion is pinned, not just the verdict: a `Some` still
    /// carrying `CoeT.coe` or a projection node would mean the search
    /// succeeded but `expand_coe` did not run.
    ///
    /// NOTE on the substring check below: `render_expr`'s `Debug` is
    /// deliberately NON-recursive (`leanr_kernel::expr::Expr`'s own doc
    /// comment — depth-safety against adversarial terms), so it prints
    /// child positions as a bare `..` and never surfaces a nested
    /// `Const`'s name. A substring check against the FULL rendered
    /// application (as the brief's literal text writes it) can never
    /// see `"CoeT"` at all — it would silently pass even against an
    /// unexpanded `CoeT.coe eType e expected inst` result, because that
    /// term's outer node is `App`, not `Const`. So this test renders
    /// the application HEAD on its own (a bare `Const` when expansion
    /// happened, which DOES print its dotted name) instead of the whole
    /// term. The full-term `assert_eq!` against `want` already pins the
    /// exact expanded value (verified below to fail hard against an
    /// identity-stubbed `expand_coe`); the head check makes the "no
    /// `CoeT.coe`" half of the acceptance wording independently
    /// reachable and readable in a failure message.
    #[test]
    fn coerce_simple_expands_a_locally_bound_value() {
        with_synth0_ctx(|ctx| {
            let n_ty = const_named(ctx, "N");
            let m = const_named(ctx, "M");
            let of_n = const_dotted(ctx, "M", "ofN");
            let cp = ctx.lctx_checkpoint();
            let x = ctx
                .push_local_decl(None, n_ty, leanr_kernel::BinderInfo::Default)
                .expect("decl");
            let want = app(ctx, of_n, &[x]);
            let got = ctx.coerce_simple(x, m).expect("coerce");
            ctx.lctx_restore(cp);
            match got {
                LOption::Some(got) => {
                    assert_eq!(render_expr(ctx, got), render_expr(ctx, want));
                    let head = ctx.get_app_fn(got);
                    let head_rendered = render_expr(ctx, head);
                    assert!(
                        !head_rendered.contains("CoeT"),
                        "unexpanded: {head_rendered}"
                    );
                    assert_eq!(head_rendered, render_expr(ctx, of_n));
                }
                other => panic!("expected Some, got {other:?}"),
            }
        });
    }

    /// `CoeFun` and `CoeSort` coercions of a `fun`-bound value worked
    /// BEFORE the metavariable-local-contexts slice and must keep
    /// working: their class parameters are types only
    /// (`CoeFun FnN ?γ`, `CoeSort SortN ?β`), so their goals never
    /// mention the local variable and the out-of-scope rejection never
    /// applied to them. This is the measurement that scoped the finding
    /// to `CoeT` alone (design spec § The finding, measured), kept as a
    /// regression guard.
    #[test]
    fn coerce_to_function_and_sort_still_accept_a_locally_bound_value() {
        with_synth0_ctx(|ctx| {
            let fnn = const_named(ctx, "FnN");
            let sortn = const_named(ctx, "SortN");
            let cp = ctx.lctx_checkpoint();
            let g = ctx
                .push_local_decl(None, fnn, leanr_kernel::BinderInfo::Default)
                .expect("decl");
            let s = ctx
                .push_local_decl(None, sortn, leanr_kernel::BinderInfo::Default)
                .expect("decl");
            let f_case = ctx.coerce_to_function(g).expect("coerce");
            let s_case = ctx.coerce_to_sort(s).expect("coerce");
            ctx.lctx_restore(cp);
            assert!(f_case.is_some(), "CoeFun on a local value");
            assert!(s_case.is_some(), "CoeSort on a local value");
        });
    }
}
