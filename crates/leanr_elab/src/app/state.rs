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
    /// `f_args` is passed innermost-first, matching
    /// `instantiate_beta_rev_range`'s documented convention.
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
            // oracle: instantiate the domain so `getParamType` is valid.
            // `has_loose_bvars` is not exposed; re-interning an
            // already-closed domain is a no-op on the hash-consed bank,
            // so instantiate unconditionally rather than adding an
            // accessor for the predicate.
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
    /// `optParam`/`autoParam` wrapper stripped. P1 has no
    /// optParam/autoParam ARM (P5), but stripping here is not the arm:
    /// it is what makes the argument's expected type correct whenever a
    /// wrapper is present and the caller supplied the argument
    /// explicitly. Omitting it would silently elaborate the argument
    /// against `optParam α d` instead of `α`.
    pub fn get_arg_expected_type(&mut self) -> Result<ExprId, ElabError> {
        let t = self.get_param_type()?;
        self.consume_type_annotations(t)
    }

    /// oracle: `Expr.consumeTypeAnnotations` — strip `optParam _ _` and
    /// `autoParam _ _` wrappers from the head.
    ///
    /// `pub(crate)` for the three sites that apply it to a binder type
    /// that is not the current parameter's: `app::args::has_opt_auto_params`
    /// (every binder of the remaining telescope, `App.lean:873`'s
    /// `hasOptAutoParams (← getFType)`),
    /// `app::args::find_named_arg_depends_on` (the `cleanupAnnotations`
    /// in `App.lean:331`), and `app::propagate::is_opt_or_auto_param`
    /// (`App.lean:472`'s `paramType.isAutoParam || paramType.isOptParam`).
    ///
    /// Safe on a binder type carrying LOOSE BVARS — which the
    /// `propagate.rs` caller genuinely passes, since `main'` recurses
    /// into the binding body without instantiating: this only walks the
    /// application spine and reads the head's `Const` name, never
    /// instantiating or inferring, so an un-instantiated bvar is simply a
    /// spine node that is not a `Const` and falls through the
    /// `_ => return Ok(t)` arm.
    pub(crate) fn consume_type_annotations(&mut self, mut t: ExprId) -> Result<ExprId, ElabError> {
        loop {
            let (f, arg0) = match self.app_fn_and_first_arg(t) {
                Some(pair) => pair,
                None => return Ok(t),
            };
            match self.node(f) {
                Node::Const { name: Some(n), .. } => {
                    let base = self.elab.view.store;
                    let rendered = self
                        .elab
                        .mctx
                        .store()
                        .to_name(Some(base), Some(n))
                        .to_string();
                    if rendered == "optParam" || rendered == "autoParam" {
                        t = arg0;
                        continue;
                    }
                    return Ok(t);
                }
                _ => return Ok(t),
            }
        }
    }

    /// The head and FIRST argument of an application spine, if any.
    fn app_fn_and_first_arg(&self, e: ExprId) -> Option<(ExprId, ExprId)> {
        let mut spine = Vec::new();
        let mut cur = e;
        while let Node::App { f, arg } = self.node(cur) {
            spine.push(arg);
            cur = f;
        }
        spine.pop().map(|first| (cur, first))
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
