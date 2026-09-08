//! oracle: `Lean/Meta/Transform.lean` (v4.33.0-rc1) — the generic
//! `pre`/`post` traversal, ported for `coe.rs::expand_coe` (M4b-3 P4).
//!
//! Scope (design spec § Amendment 5 item 4): `Meta.transform`
//! (`:179-187`) over `transformWithCache` (`:97-176`) with `post` fixed at
//! its default (`fun e => .done e`) and every flag at its default
//! (`usedLetOnly := false`, `skipConstInApp := false`; `transform` does
//! not expose `skipInstances`). `betaReduce`, `zetaReduce`,
//! `unfoldDeclsFrom` and the rest of that file have no consumer in M4b-3
//! and are not ported. The cache (`checkCache` on `ExprStructEq`,
//! `:110`) is a map keyed on `ExprId`, which hash-consing makes
//! structural for free.

use std::collections::HashMap;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::{instantiate_rev, Nat};

use crate::{MetaCtx, MetaError};

/// oracle: `inductive TransformStep` (`Transform.lean:13-26`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransformStep {
    /// Return expression without visiting any subexpressions.
    Done(ExprId),
    /// Visit the given expression instead; it is passed to `pre` again.
    Visit(ExprId),
    /// Continue with the given expression (default: the current one) —
    /// for `pre`, visit its children.
    Continue(Option<ExprId>),
}

/// The `pre` callback: `Expr → m TransformStep`.
pub type Pre<'a, 'e> =
    &'a mut dyn FnMut(&mut MetaCtx<'e>, ExprId) -> Result<TransformStep, MetaError>;

type Cache = HashMap<ExprId, ExprId>;

impl<'e> MetaCtx<'e> {
    /// oracle: `Meta.transform` (`Transform.lean:179-187`) with `post`
    /// at its default and `usedLetOnly := false`, `skipConstInApp :=
    /// false` — the only configuration M4b-3 has a consumer for
    /// (`expandCoe`, `Coe.lean:46`). Terms handed to `pre` never contain
    /// loose bound variables: binders are opened with real local
    /// declarations, so any `MetaM` method is safe inside `pre`.
    pub fn transform(&mut self, input: ExprId, pre: Pre<'_, 'e>) -> Result<ExprId, MetaError> {
        let mut cache: Cache = HashMap::new();
        self.transform_visit(input, pre, &mut cache)
    }

    /// oracle: `visit` (`:109-172`) — `checkCache`, then `pre`, then
    /// the `TransformStep` dispatch. `visitPost` collapses to the
    /// identity under the default `post`.
    fn transform_visit(
        &mut self,
        e: ExprId,
        pre: Pre<'_, 'e>,
        cache: &mut Cache,
    ) -> Result<ExprId, MetaError> {
        if let Some(&r) = cache.get(&e) {
            return Ok(r);
        }
        self.step()?;
        let r = match pre(self, e)? {
            TransformStep::Done(r) => r,
            TransformStep::Visit(e2) => self.transform_visit(e2, pre, cache)?,
            TransformStep::Continue(e2) => {
                let e = e2.unwrap_or(e);
                self.transform_children(e, pre, cache)?
            }
        };
        cache.insert(e, r);
        Ok(r)
    }

    /// oracle: the `.continue` arm's `match e` (`:164-172`).
    fn transform_children(
        &mut self,
        e: ExprId,
        pre: Pre<'_, 'e>,
        cache: &mut Cache,
    ) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        match self.node(e) {
            Node::Forall { .. } => {
                let cp = self.lctx_checkpoint();
                let r = self.transform_forall(e, pre, cache);
                self.lctx_restore(cp);
                r
            }
            Node::Lam { .. } => {
                let cp = self.lctx_checkpoint();
                let r = self.transform_lambda(e, pre, cache);
                self.lctx_restore(cp);
                r
            }
            Node::LetE { .. } => {
                let cp = self.lctx_checkpoint();
                let r = self.transform_let(e, pre, cache);
                self.lctx_restore(cp);
                r
            }
            // oracle: `visitApp` (`:135-149`) without the `skipInstances`
            // branch — `e.withApp fun f args => mkAppN (← visit f) (← args.mapM visit)`.
            Node::App { .. } => {
                let f = self.get_app_fn(e);
                let args = self.get_app_args(e);
                let mut r = self.transform_visit(f, pre, cache)?;
                for a in args {
                    let a2 = self.transform_visit(a, pre, cache)?;
                    r = self.scratch.expr_app(base, r, a2)?;
                }
                Ok(r)
            }
            Node::MData { data, expr } => {
                let b = self.transform_visit(expr, pre, cache)?;
                Ok(self.scratch.expr_mdata(base, data, b)?)
            }
            Node::Proj {
                type_name,
                idx,
                structure,
            } => {
                let b = self.transform_visit(structure, pre, cache)?;
                Ok(self
                    .scratch
                    .expr_proj(base, type_name, &Nat::from(idx as u64), b)?)
            }
            Node::ProjBig {
                type_name,
                idx,
                structure,
            } => {
                let n = self.scratch.nat_at(base, idx).clone();
                let b = self.transform_visit(structure, pre, cache)?;
                Ok(self.scratch.expr_proj(base, type_name, &n, b)?)
            }
            _ => Ok(e),
        }
    }

    /// oracle: `visitLambda` (`:117-122`) — open every leading `lam`
    /// with a local decl (visiting each domain first), visit the body,
    /// `mkLambdaFVars`. The caller checkpoints/restores the lctx.
    fn transform_lambda(
        &mut self,
        e: ExprId,
        pre: Pre<'_, 'e>,
        cache: &mut Cache,
    ) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut cur = e;
        loop {
            match self.node(cur) {
                Node::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    let d =
                        instantiate_rev(self.scratch, base, binder_type, &fvars, &mut self.guard)?;
                    let d = self.transform_visit(d, pre, cache)?;
                    let x = self.push_local_decl(binder_name, d, binder_info)?;
                    fvars.push(x);
                    cur = body;
                }
                _ => {
                    let b = instantiate_rev(self.scratch, base, cur, &fvars, &mut self.guard)?;
                    let b = self.transform_visit(b, pre, cache)?;
                    return self.mk_lambda(&fvars, b);
                }
            }
        }
    }

    /// oracle: `visitForall` (`:123-128`) — same shape, `mkForallFVars`.
    fn transform_forall(
        &mut self,
        e: ExprId,
        pre: Pre<'_, 'e>,
        cache: &mut Cache,
    ) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut cur = e;
        loop {
            match self.node(cur) {
                Node::Forall {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    let d =
                        instantiate_rev(self.scratch, base, binder_type, &fvars, &mut self.guard)?;
                    let d = self.transform_visit(d, pre, cache)?;
                    let x = self.push_local_decl(binder_name, d, binder_info)?;
                    fvars.push(x);
                    cur = body;
                }
                _ => {
                    let b = instantiate_rev(self.scratch, base, cur, &fvars, &mut self.guard)?;
                    let b = self.transform_visit(b, pre, cache)?;
                    return self.mk_forall(&fvars, b);
                }
            }
        }
    }

    /// oracle: `visitLet` (`:129-134`) — open every leading `letE` with
    /// a let-decl (visiting type and value first), visit the body, then
    /// `mkLetFVars (usedLetOnly := false)`, i.e. every let is rebuilt
    /// innermost-first.
    fn transform_let(
        &mut self,
        e: ExprId,
        pre: Pre<'_, 'e>,
        cache: &mut Cache,
    ) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut lets: Vec<(ExprId, bool)> = Vec::new();
        let mut cur = e;
        loop {
            match self.node(cur) {
                Node::LetE {
                    decl_name,
                    ty,
                    value,
                    body,
                    non_dep,
                } => {
                    let t = instantiate_rev(self.scratch, base, ty, &fvars, &mut self.guard)?;
                    let t = self.transform_visit(t, pre, cache)?;
                    let v = instantiate_rev(self.scratch, base, value, &fvars, &mut self.guard)?;
                    let v = self.transform_visit(v, pre, cache)?;
                    let x = self.push_let_decl(decl_name, t, v)?;
                    fvars.push(x);
                    lets.push((x, non_dep));
                    cur = body;
                }
                _ => {
                    let b = instantiate_rev(self.scratch, base, cur, &fvars, &mut self.guard)?;
                    let mut b = self.transform_visit(b, pre, cache)?;
                    for (x, non_dep) in lets.iter().rev() {
                        b = self.mk_let_expr(*x, b, *non_dep)?;
                    }
                    return Ok(b);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::TransformStep;
    use crate::test_support::{const_dotted, render_expr, with_synth0_ctx};
    use crate::MetaCtx;
    use leanr_kernel::bank::ExprId;
    use leanr_kernel::{BinderInfo, Nat};

    fn app(ctx: &mut MetaCtx, f: ExprId, a: ExprId) -> ExprId {
        ctx.scratch
            .expr_app(Some(ctx.view.store), f, a)
            .expect("app")
    }

    /// `pre` that never rewrites returns the SAME hash-consed id, binder
    /// telescopes included — `fun (x : N) => N.succ x` is opened with a
    /// real fvar, re-abstracted, and comes back identical.
    #[test]
    fn transform_is_the_identity_when_pre_continues() {
        with_synth0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = const_dotted(ctx, "N", "zero");
            let n_ty = ctx.infer_type(n).expect("N");
            let succ = const_dotted(ctx, "N", "succ");
            let bvar0 = ctx.scratch.expr_bvar(base, &Nat::from(0u64)).expect("bvar");
            let body = app(ctx, succ, bvar0);
            let x = ctx.scratch.intern_str(base, "x").expect("intern");
            let x = ctx.scratch.name_str(base, None, x).expect("name");
            let lam = ctx
                .scratch
                .expr_lam(base, Some(x), n_ty, body, BinderInfo::Default)
                .expect("lam");
            let out = ctx
                .transform(lam, &mut |_, _| Ok(TransformStep::Continue(None)))
                .expect("transform");
            assert_eq!(out, lam, "{}", render_expr(ctx, out));
        });
    }

    /// `.done e'` replaces WITHOUT revisiting; `.visit e'` runs `pre`
    /// again on the replacement (`Transform.lean:162-163`).
    #[test]
    fn done_replaces_and_visit_reenters_pre() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let succ = const_dotted(ctx, "N", "succ");
            let one = app(ctx, succ, zero);
            let two = app(ctx, succ, one);

            let got = ctx
                .transform(zero, &mut |_, e| {
                    Ok(if e == zero {
                        TransformStep::Done(one)
                    } else if e == one {
                        TransformStep::Done(two)
                    } else {
                        TransformStep::Continue(None)
                    })
                })
                .expect("transform");
            assert_eq!(got, one, "done: no re-entry");

            let got = ctx
                .transform(zero, &mut |_, e| {
                    Ok(if e == zero {
                        TransformStep::Visit(one)
                    } else if e == one {
                        TransformStep::Done(two)
                    } else {
                        TransformStep::Continue(None)
                    })
                })
                .expect("transform");
            assert_eq!(got, two, "visit: pre runs again on the replacement");
        });
    }

    /// `.continue` descends: a rewrite inside an argument, under a
    /// binder, and inside a `let` value are all reached, and the
    /// results are rebuilt with the same constructors.
    #[test]
    fn continue_descends_into_app_lambda_and_let() {
        with_synth0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = const_dotted(ctx, "N", "zero");
            let n_ty = ctx.infer_type(zero).expect("N");
            let succ = const_dotted(ctx, "N", "succ");
            let one = app(ctx, succ, zero);
            let x = ctx.scratch.intern_str(base, "x").expect("intern");
            let x = ctx.scratch.name_str(base, None, x).expect("name");
            // fun (x : N) => let y := N.zero; N.succ y
            let bvar0 = ctx.scratch.expr_bvar(base, &Nat::from(0u64)).expect("bvar");
            let let_body = app(ctx, succ, bvar0);
            let let_e = ctx
                .scratch
                .expr_let(base, Some(x), n_ty, zero, let_body, false)
                .expect("let");
            let lam = ctx
                .scratch
                .expr_lam(base, Some(x), n_ty, let_e, BinderInfo::Default)
                .expect("lam");
            let got = ctx
                .transform(lam, &mut |_, e| {
                    Ok(if e == zero {
                        TransformStep::Done(one)
                    } else {
                        TransformStep::Continue(None)
                    })
                })
                .expect("transform");
            // expected: fun (x : N) => let y := N.succ N.zero; N.succ y
            let want_let = ctx
                .scratch
                .expr_let(base, Some(x), n_ty, one, let_body, false)
                .expect("let");
            let want = ctx
                .scratch
                .expr_lam(base, Some(x), n_ty, want_let, BinderInfo::Default)
                .expect("lam");
            assert_eq!(render_expr(ctx, got), render_expr(ctx, want));
        });
    }

    /// The cache: a shared subterm is visited ONCE (`checkCache`,
    /// `:110`). `N.succ` applied to the same `N.zero` twice — an
    /// ill-typed but structurally fine term; `transform` never infers
    /// types.
    #[test]
    fn shared_subterms_are_visited_once() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let succ = const_dotted(ctx, "N", "succ");
            let e = app(ctx, succ, zero);
            let e = app(ctx, e, zero);
            let mut visits_of_zero = 0usize;
            ctx.transform(e, &mut |_, x| {
                if x == zero {
                    visits_of_zero += 1;
                }
                Ok(TransformStep::Continue(None))
            })
            .expect("transform");
            assert_eq!(visits_of_zero, 1);
        });
    }
}
