//! `Context` + `State` + `AppElab`, and the `fType` navigation helpers.
//! Oracle: `App.lean:132-300`.
//!
//! Lean's `abbrev M := ReaderT Context (StateRefT State TermElabM)`
//! (`App.lean:229`) is ONE struct here, not a transformer stack: the
//! reader half is immutable after construction, the state half is
//! `&mut`, and each `private def foo : M α` becomes a method. Rust's
//! borrow checker then enforces exactly what `StateRefT` provides.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;
use leanr_meta::MVarId;

use crate::app::expand::{Arg, NamedArg};
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `structure Context` (`App.lean:132-175`).
pub struct Context {
    /// `..` was used.
    pub ellipsis: bool,
    /// `@` was used.
    pub explicit: bool,
    /// Special support for applications whose result type is the
    /// `outParam` of a local instance (`App.lean:141-168`). The oracle
    /// computes it as `env.contains ``Lean.Internal.coeM && flag &&
    /// !explicit` (`App.lean:1355`) — coercions must be available for
    /// the feature to make sense. P1 computes it the SAME way, which
    /// makes it `false` throughout the hermetic fixture env (prelude-mode
    /// `Elab0` declares no `Lean.Internal.coeM`) with no special-casing.
    /// The consuming logic lands in P2 with the fixpoint.
    pub result_is_out_param_support: bool,
    /// oracle: `Context.numImplicitParams` — cached max over
    /// `namedArgs`; only nonzero for structure projections (M4b-4).
    pub num_implicit_params: usize,
}

/// oracle: `structure State` (`App.lean:178-227`). Every field the
/// oracle has is present, including those no P1 arm drives yet — see
/// this module's own doc and the design spec § P1.
pub struct State {
    pub f: ExprId,
    pub f_type: ExprId,
    pub f_args: Vec<ExprId>,
    pub args: Vec<Arg>,
    pub named_args: Vec<NamedArg>,
    pub expected_type: Option<ExprId>,
    /// oracle: `State.etaArgs` — `(binder name, fvar)` per eta-expanded
    /// parameter. Written by `args::add_eta_arg`, consumed by
    /// `finalize`'s `mkLambdaFVars` + `updateBinderNames` step (Task 7).
    pub eta_args: Vec<(Option<NameId>, ExprId)>,
    /// oracle: `State.toSetErrorCtx`. Driven by Task 5.
    pub to_set_error_ctx: Vec<MVarId>,
    /// oracle: `State.instMVars` — instance-implicit argument mvars
    /// awaiting synthesis. NO P1 producer: `process_inst_implicit_arg`
    /// is P2's seam. `finalize` asserts it is empty (Task 4).
    pub inst_mvars: Vec<MVarId>,
    pub propagate_expected: bool,
    /// oracle: `State.resultTypeOutParam?`. No P1 producer (P2).
    pub result_type_out_param: Option<MVarId>,
    /// oracle: `State.foundNamedArgs` — valid named-argument names seen
    /// while walking the function's type; feeds the oracle's "invalid
    /// argument name" diagnostic (`App.lean:401`), which leanr does not
    /// emit yet. Written by `args::push_found_named_arg` (Task 7); never
    /// part of the emitted `Expr`.
    pub found_named_args: Vec<String>,
}

pub struct AppElab<'a, 'e> {
    pub ctx: Context,
    pub st: State,
    pub elab: &'a mut TermElabM<'e>,
}

impl<'a, 'e> AppElab<'a, 'e> {
    /// Destructure an `ExprId`. `Store::expr_node` is already public
    /// (`leanr_kernel/src/bank/terms.rs:615`), so this needs no
    /// `leanr_meta` accessor — `mctx.store()` is the scratch store and
    /// `view.store` the persistent base, exactly the pairing every
    /// `base`-taking kernel method wants.
    pub fn node(&self, e: ExprId) -> Node {
        let base = self.elab.view.store;
        self.elab.mctx.store().expr_node(Some(base), e)
    }

    /// oracle: `State.paramIdx` (`App.lean:230`).
    pub fn param_idx(&self) -> usize {
        self.st.f_args.len()
    }

    /// oracle: `State.getFType` (`App.lean:232-237`) — `fType` with
    /// loose bvars instantiated by the arguments consumed so far.
    /// `f_args` is passed OUTERMOST-first (binder order, i.e. application
    /// order), matching `instantiate_beta_rev_range`'s documented
    /// convention that the LAST element replaces `#0`.
    pub fn get_f_type(&mut self) -> Result<ExprId, ElabError> {
        let f_type = self.st.f_type;
        let args = self.st.f_args.clone();
        let out = self.elab.mctx.instantiate_beta_rev_range(f_type, &args)?;
        self.st.f_type = out;
        Ok(out)
    }

    /// oracle: `fTypeIsForall` (`App.lean:238-249`). Returns true if
    /// `fType` is a function type, WHNF-ing and caching if needed, and
    /// guarantees the domain has no loose bvars.
    pub fn f_type_is_forall(&mut self) -> Result<bool, ElabError> {
        if let Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = self.node(self.st.f_type)
        {
            // oracle: `if d.hasLooseBVars then ..` (`App.lean:242-244`) —
            // instantiate the domain so `getParamType` is valid, and ONLY
            // then. `has_loose_bvars` below is `Expr.hasLooseBVars` read
            // off the packed per-node metadata, so this is the oracle's
            // own guard rather than a paraphrase of it.
            if !self.has_loose_bvars(binder_type) {
                return Ok(true);
            }
            let args = self.st.f_args.clone();
            let d = self
                .elab
                .mctx
                .instantiate_beta_rev_range(binder_type, &args)?;
            if d != binder_type {
                // `body` is the original Forall's child, very likely a
                // PERSISTENT-region `ExprId` (`self.node`/
                // `consume_type_annotations` both use this exact
                // `base = Some(view.store)` pairing for the same
                // reason) — `base = None` would route a persistent id
                // through the scratch store's own row space
                // (`Store::store_for`), a silent wrong-row read in
                // release builds (caught only by a `debug_assert!` in
                // debug builds).
                let base = self.elab.view.store;
                let f_type = self
                    .elab
                    .mctx
                    .store_mut()
                    .expr_forall(Some(base), binder_name, d, body, binder_info)
                    .map_err(leanr_meta::MetaError::from)?;
                self.st.f_type = f_type;
            }
            return Ok(true);
        }
        let f_type = self.get_f_type()?;
        let reduced = self.whnf_forall(f_type)?;
        self.st.f_type = reduced;
        Ok(matches!(self.node(reduced), Node::Forall { .. }))
    }

    /// oracle: `whnfForall` (`Lean/Meta/Basic.lean`) — WHNF, but keep the
    /// ORIGINAL term if the reduct is not a forall. Composed from the
    /// public `MetaCtx::whnf`; no accessor needed.
    ///
    /// `pub(crate)` for `app::propagate::get_resulting_type`, whose
    /// `main'` walk needs the SAME `whnfForall` the oracle calls at
    /// `App.lean:458`.
    pub(crate) fn whnf_forall(&mut self, e: ExprId) -> Result<ExprId, ElabError> {
        let r = self.elab.mctx.whnf(e)?;
        if matches!(self.node(r), Node::Forall { .. }) {
            Ok(r)
        } else {
            Ok(e)
        }
    }

    /// oracle: `getParamName` (`App.lean:251-255`). Valid only when
    /// `f_type_is_forall` returned true.
    pub fn get_param_name(&self) -> Option<NameId> {
        match self.node(self.st.f_type) {
            Node::Forall { binder_name, .. } => binder_name,
            _ => None,
        }
    }

    /// oracle: `getParamType` (`App.lean:257-261`).
    pub fn get_param_type(&self) -> Result<ExprId, ElabError> {
        match self.node(self.st.f_type) {
            Node::Forall { binder_type, .. } => Ok(binder_type),
            _ => Err(ElabError::IllFormedSyntax(
                "getParamType called on a non-forall fType".to_string(),
            )),
        }
    }

    /// oracle: `getParamInfo` (`App.lean:263-267`).
    pub fn get_param_info(&self) -> Result<BinderInfo, ElabError> {
        match self.node(self.st.f_type) {
            Node::Forall { binder_info, .. } => Ok(binder_info),
            _ => Err(ElabError::IllFormedSyntax(
                "getParamInfo called on a non-forall fType".to_string(),
            )),
        }
    }

    /// oracle: `getArgExpectedType` (`App.lean:269-273`) —
    /// `getParamType` with `consumeTypeAnnotations` applied, i.e. the
    /// `optParam`/`autoParam`/`outParam`/`semiOutParam` wrapper stripped.
    /// P1 has no optParam/autoParam ARM (P5) and no classes (so no
    /// `outParam`), but stripping here is not the arm: it is what makes
    /// the argument's expected type correct whenever a wrapper is present
    /// and the caller supplied the argument explicitly. Omitting it would
    /// silently elaborate the argument against `optParam α d` instead of
    /// `α`.
    pub fn get_arg_expected_type(&mut self) -> Result<ExprId, ElabError> {
        let t = self.get_param_type()?;
        self.consume_type_annotations(t)
    }

    /// oracle: `Expr.consumeTypeAnnotations` (`Lean/Expr.lean:1739-1745`)
    /// — strip ALL FOUR type-annotation gadgets from the head:
    ///
    /// ```lean
    /// partial def consumeTypeAnnotations (e : Expr) : Expr :=
    ///   if e.isOptParam || e.isAutoParam then
    ///     consumeTypeAnnotations e.appFn!.appArg!
    ///   else if e.isOutParam || e.isSemiOutParam then
    ///     consumeTypeAnnotations e.appArg!
    ///   else e
    /// ```
    ///
    /// i.e. `optParam α d` / `autoParam α tac` (arity 2, keep the FIRST
    /// argument — the annotated type) and `outParam α` / `semiOutParam α`
    /// (arity 1, keep their only argument). The arity tests are the
    /// oracle's own (`isAppOfArity`, `Expr.lean:1709-1722`): a
    /// partially-applied `optParam α` is NOT `isOptParam`, and stripping
    /// it would return `α` where the oracle keeps the whole term.
    ///
    /// The two `outParam` gadgets are INERT under P1's hermetic fixture
    /// environment — `Elab0.lean` declares no class, so no parameter type
    /// can carry one — but they are part of THIS function and go live the
    /// moment P2 brings classes. Omitting them would be a silent
    /// divergence rather than a named seam, which is why they are here
    /// now.
    ///
    /// Two callers, matching the oracle's own: `get_arg_expected_type`
    /// (`App.lean:273`'s `(← getParamType).consumeTypeAnnotations`) and
    /// `app::args::find_named_arg_depends_on` (the `cleanupAnnotations`
    /// in `App.lean:331`, whose `consumeMData` half is still unmodelled —
    /// see that call site's own note).
    ///
    /// The `isOptParam || isAutoParam` test that
    /// `app::args::has_opt_auto_params` and
    /// `app::propagate::is_opt_or_auto_param` need is a DIFFERENT
    /// predicate with its own helper, `consume_opt_auto_param` below —
    /// widening those two to see `outParam` would make them answer a
    /// question the oracle does not ask there.
    pub(crate) fn consume_type_annotations(&mut self, mut t: ExprId) -> Result<ExprId, ElabError> {
        loop {
            match self.type_annotation_at_head(t) {
                Some(stripped) => t = stripped,
                None => return Ok(t),
            }
        }
    }

    /// The `optParam`/`autoParam` HALF of `consume_type_annotations`, and
    /// only that half. `consume_opt_auto_param(x) != x` is exactly the
    /// oracle's `x.isOptParam || x.isAutoParam`, which is what all three
    /// of its call sites test for: `hasOptAutoParams`
    /// (`App.lean:121-127`, via `app::args::has_opt_auto_params`), the
    /// propagation guard at `App.lean:472` (via
    /// `app::propagate::is_opt_or_auto_param`), and the default-filling
    /// arms at `App.lean:827-854` (via `app::args`'s own seam check).
    /// Every one of those asks "does this parameter carry a DEFAULT
    /// VALUE" — which `outParam`/`semiOutParam` do not.
    ///
    /// Safe on a binder type carrying LOOSE BVARS — which the
    /// `propagate.rs` caller genuinely passes, since `main'` recurses
    /// into the binding body without instantiating: this only walks the
    /// application spine and reads the head's `Const` name, never
    /// instantiating or inferring, so an un-instantiated bvar is simply a
    /// spine node that is not a `Const` and falls through. The same is
    /// true of `consume_type_annotations` above.
    pub(crate) fn consume_opt_auto_param(&mut self, mut t: ExprId) -> Result<ExprId, ElabError> {
        while self.head_is_opt_or_auto_param(t) {
            match self.type_annotation_at_head(t) {
                Some(inner) => t = inner,
                None => break,
            }
        }
        Ok(t)
    }

    /// `true` when `t` is `optParam _ _` or `autoParam _ _` at the head,
    /// arity included. oracle: `Expr.isOptParam || Expr.isAutoParam`.
    fn head_is_opt_or_auto_param(&self, t: ExprId) -> bool {
        match self.type_annotation_head(t) {
            Some((name, arity)) => (name == "optParam" || name == "autoParam") && arity == 2,
            None => false,
        }
    }

    /// One step of `consumeTypeAnnotations`: `Some(inner)` if `t` is a
    /// well-formed application of one of the four gadgets, where `inner`
    /// is the annotated type the oracle keeps; `None` otherwise.
    fn type_annotation_at_head(&self, t: ExprId) -> Option<ExprId> {
        let (name, arity) = self.type_annotation_head(t)?;
        let args = self.app_args(t);
        match name.as_str() {
            // `e.appFn!.appArg!` — the first of two arguments.
            "optParam" | "autoParam" if arity == 2 => Some(args[0]),
            // `e.appArg!` — the only argument.
            "outParam" | "semiOutParam" if arity == 1 => Some(args[0]),
            _ => None,
        }
    }

    /// The rendered name of an application spine's head `Const` and the
    /// spine's arity, if the head is a `Const` and the spine non-empty.
    fn type_annotation_head(&self, e: ExprId) -> Option<(String, usize)> {
        let mut arity = 0usize;
        let mut cur = e;
        while let Node::App { f, .. } = self.node(cur) {
            arity += 1;
            cur = f;
        }
        if arity == 0 {
            return None;
        }
        match self.node(cur) {
            Node::Const { name: Some(n), .. } => Some((self.render_name(n), arity)),
            _ => None,
        }
    }

    /// An application spine's arguments, in APPLICATION order.
    fn app_args(&self, e: ExprId) -> Vec<ExprId> {
        let mut args = Vec::new();
        let mut cur = e;
        while let Node::App { f, arg } = self.node(cur) {
            args.push(arg);
            cur = f;
        }
        args.reverse();
        args
    }

    /// oracle: `hasArgsToProcess` (`App.lean:290-293`).
    pub fn has_args_to_process(&self) -> bool {
        !self.st.args.is_empty() || !self.st.named_args.is_empty()
    }

    /// `Expr.hasLooseBVars` — read straight off the packed per-node
    /// metadata (`ExprData::loose_bvar_range`,
    /// `leanr_kernel/src/expr.rs:246`), which `Store::expr_data` already
    /// exposes publicly. The saturation sentinel documented on
    /// `loose_bvar_range_exact` does not affect this test: a packed range
    /// of `0` is `min(actual, SAT)`, so it is exact, and any nonzero
    /// packed value (saturated or not) proves `actual > 0`.
    pub(crate) fn has_loose_bvars(&self, e: ExprId) -> bool {
        let base = self.elab.view.store;
        self.elab
            .mctx
            .store()
            .expr_data(Some(base), e)
            .loose_bvar_range()
            > 0
    }

    /// oracle: `Expr.isArrow` (`Lean/Expr.lean:1319-1322`) — a
    /// NON-DEPENDENT function type, i.e. a `forallE` whose body does not
    /// mention the binder. Anything else (including a non-forall) is
    /// `false`.
    pub(crate) fn is_arrow(&self, e: ExprId) -> bool {
        match self.node(e) {
            Node::Forall { body, .. } => !self.has_loose_bvars(body),
            _ => false,
        }
    }

    /// `NameId` -> the rendered dotted name a `NamedArg` carries as a
    /// `String` (`expand::NamedArg`'s own doc explains why named-argument
    /// names stay source text rather than becoming `NameId`s). One
    /// allocation per call, so callers render once and reuse.
    pub(crate) fn render_name(&self, n: NameId) -> String {
        let base = self.elab.view.store;
        self.elab
            .mctx
            .store()
            .to_name(Some(base), Some(n))
            .to_string()
    }

    /// oracle: `forallTelescopeReducing` (`Lean/Meta/Basic.lean:1592`,
    /// worker `forallTelescopeReducingAuxAux` at `:1453-1487`,
    /// `maxFVars? := none`, `cleanupAnnotations := false`) — WHNF `ty`,
    /// and for as long as the result is a `forall`, mint an fvar for the
    /// binder and continue on the body instantiated with it; then run
    /// `k` under the resulting local context.
    ///
    /// Two P1 callers, both matching the oracle's own
    /// (`args::has_opt_auto_params`, `args::find_named_arg_depends_on`),
    /// and neither uses the telescope's final body type — so `k` takes
    /// only the binder list, unlike the oracle's `Array Expr → Expr → _`.
    ///
    /// The oracle's `process` defers domain instantiation
    /// (`d.instantiateRevRange j fvars.size fvars`, re-based at each
    /// reduction point); instantiating the body eagerly at every step,
    /// as below, is the same substitution performed earlier — every
    /// `TelescopeBinder::ty` handed to `k` is closed with respect to the
    /// telescope, exactly as the oracle's `xDecl.type` is.
    ///
    /// `ty` itself must be closed (no loose bvars from an enclosing
    /// context); both call sites pass an already-instantiated `getFType`.
    ///
    /// The ambient `lctx` is restored on EVERY exit path (`Ok` or `Err`)
    /// — `builtin/binder.rs:217,226`'s checkpoint/restore idiom — so the
    /// telescope's fvars never outlive `k`.
    pub(crate) fn forall_telescope_reducing<R>(
        &mut self,
        ty: ExprId,
        k: impl FnOnce(&mut Self, &[TelescopeBinder]) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let checkpoint = self.elab.mctx.lctx_checkpoint();
        let result = (|| {
            let mut binders: Vec<TelescopeBinder> = Vec::new();
            let mut cur = ty;
            loop {
                // oracle: `process` recurses straight into `b` while the
                // type is already a `forall` (`Basic.lean:1460-1468`) and
                // reaches `whnf` only on the `_` arm (`:1474-1481`).
                // Reducing an already-`forall` type is a no-op, so this
                // guard is a cost decision, not a semantic one — but it
                // keeps the walk shaped like the oracle's.
                let reduced = if matches!(self.node(cur), Node::Forall { .. }) {
                    cur
                } else {
                    self.whnf_forall(cur)?
                };
                let Node::Forall {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } = self.node(reduced)
                else {
                    break;
                };
                let fvar = self
                    .elab
                    .mctx
                    .push_local_decl(binder_name, binder_type, binder_info)
                    .map_err(ElabError::from)?;
                cur = self
                    .elab
                    .mctx
                    .instantiate_beta_rev_range(body, std::slice::from_ref(&fvar))?;
                binders.push(TelescopeBinder {
                    name: binder_name,
                    fvar,
                    ty: binder_type,
                });
            }
            k(self, &binders)
        })();
        self.elab.mctx.lctx_restore(checkpoint);
        result
    }
}

/// One binder of a `AppElab::forall_telescope_reducing` walk: the
/// oracle's `xs[i]` together with the two fields its callers read off
/// `xs[i].fvarId!.getDecl` (`userName` and `type`). Carried here rather
/// than looked up afterwards because `leanr_meta` exposes no public
/// local-decl accessor — and because both are already in hand at the
/// moment the decl is pushed.
pub(crate) struct TelescopeBinder {
    /// oracle: `xDecl.userName` (`.anonymous` -> `None`).
    pub name: Option<NameId>,
    /// oracle: `xs[i]`, the `Expr.fvar` itself.
    pub fvar: ExprId,
    /// oracle: `xDecl.type` == `inferType xs[i]`, closed with respect to
    /// the telescope.
    pub ty: ExprId,
}
