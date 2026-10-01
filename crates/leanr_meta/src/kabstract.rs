//! oracle: `Lean/Meta/KAbstract.lean` (v4.33.0-rc1), `kabstract` with
//! `occs := .all` — the only form `ElabElim` (`App.lean:1170`, `:1186`)
//! calls. Abstract every subterm of `e` that is key-matched (same
//! `HeadIndex`, same `headNumArgs`) AND `isDefEq` to `p`, replacing it
//! with the de Bruijn index of the binder depth it sits under.
//!
//! The oracle's `getMCtx`/`setMCtx` rollback runs only when a match is
//! EXCLUDED by `occs`; under `.all` every match is included, so it is
//! dead and not ported. A failed `isDefEq` leaves the mctx as
//! `isDefEq` itself leaves it, in both implementations.

use leanr_kernel::abstract_fvars;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::Nat;

use crate::head_index::HeadIndex;
use crate::{MetaCtx, MetaError};

impl<'e> MetaCtx<'e> {
    /// oracle: `kabstract e p .all`.
    pub fn kabstract(&mut self, e: ExprId, p: ExprId) -> Result<ExprId, MetaError> {
        let e = self.instantiate_mvars(e)?;
        if matches!(self.node(p), Node::FVar { .. }) {
            // oracle: "Easy case" — plain `abstract`.
            return Ok(abstract_fvars(
                self.scratch,
                Some(self.view.store),
                e,
                std::slice::from_ref(&p),
                &mut self.guard,
            )?);
        }
        let p_head = self.to_head_index(p)?;
        let p_num_args = self.head_num_args(p);
        self.kabstract_visit(e, 0, p, p_head, p_num_args)
    }

    /// oracle: `visit`.
    fn kabstract_visit(
        &mut self,
        e: ExprId,
        offset: u32,
        p: ExprId,
        p_head: HeadIndex,
        p_num_args: usize,
    ) -> Result<ExprId, MetaError> {
        self.step()?;
        // `hasLooseBVars` is tested first, so `to_head_index` is never
        // asked about a term with loose bvars.
        if self.data(e).loose_bvar_range() > 0
            || self.to_head_index(e)? != p_head
            || self.head_num_args(e) != p_num_args
        {
            return self.kabstract_children(e, offset, p, p_head, p_num_args);
        }
        if self.is_def_eq(e, p)? {
            let base = Some(self.view.store);
            return Ok(self.scratch.expr_bvar(base, &Nat::from(offset as u64))?);
        }
        self.kabstract_children(e, offset, p, p_head, p_num_args)
    }

    /// oracle: `visitChildren`. Child order is load-bearing: `isDefEq`
    /// assigns metavariables, so the first candidate visited fixes them
    /// for the rest (`app`: `f` then `a`; `letE`: type, value, body;
    /// binders: domain, then body at `offset + 1`).
    fn kabstract_children(
        &mut self,
        e: ExprId,
        offset: u32,
        p: ExprId,
        ph: HeadIndex,
        pn: usize,
    ) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        Ok(match self.node(e) {
            Node::App { f, arg } => {
                let f2 = self.kabstract_visit(f, offset, p, ph, pn)?;
                let a2 = self.kabstract_visit(arg, offset, p, ph, pn)?;
                self.scratch.expr_app(base, f2, a2)?
            }
            Node::MData { data, expr } => {
                let b = self.kabstract_visit(expr, offset, p, ph, pn)?;
                self.scratch.expr_mdata(base, data, b)?
            }
            Node::Proj {
                type_name,
                idx,
                structure,
            } => {
                let b = self.kabstract_visit(structure, offset, p, ph, pn)?;
                self.scratch
                    .expr_proj(base, type_name, &Nat::from(idx as u64), b)?
            }
            Node::ProjBig {
                type_name,
                idx,
                structure,
            } => {
                let n = self.scratch.nat_at(base, idx).clone();
                let b = self.kabstract_visit(structure, offset, p, ph, pn)?;
                self.scratch.expr_proj(base, type_name, &n, b)?
            }
            Node::LetE {
                decl_name,
                ty,
                value,
                body,
                non_dep,
            } => {
                let t = self.kabstract_visit(ty, offset, p, ph, pn)?;
                let v = self.kabstract_visit(value, offset, p, ph, pn)?;
                let b = self.kabstract_visit(body, offset + 1, p, ph, pn)?;
                self.scratch.expr_let(base, decl_name, t, v, b, non_dep)?
            }
            Node::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let d = self.kabstract_visit(binder_type, offset, p, ph, pn)?;
                let b = self.kabstract_visit(body, offset + 1, p, ph, pn)?;
                self.scratch
                    .expr_lam(base, binder_name, d, b, binder_info)?
            }
            Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let d = self.kabstract_visit(binder_type, offset, p, ph, pn)?;
                let b = self.kabstract_visit(body, offset + 1, p, ph, pn)?;
                self.scratch
                    .expr_forall(base, binder_name, d, b, binder_info)?
            }
            _ => e,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::{app, bvar, c, fresh_fvar, fresh_mvar, with_meta0_ctx};

    /// oracle (Meta0): `kabstract (P.mk (N.succ two) one) (N.succ ?m)` =
    /// `P.mk #0 one`, `?m := two`. The FIRST candidate (left-to-right,
    /// `app` visits `f` before `a`) fixes `?m`; `one = N.succ N.zero` is
    /// then not defeq to `N.succ two`.
    #[test]
    fn kabstract_mvar_pattern_first_match_wins() {
        with_meta0_ctx(|ctx| {
            let n = c(ctx, "N");
            let (m, _) = fresh_mvar(ctx, n);
            let succ = c(ctx, "N.succ");
            let zero = c(ctx, "N.zero");
            let two = c(ctx, "two");
            let one = app(ctx, succ, zero);
            let succ_two = app(ctx, succ, two);
            let pmk = c(ctx, "P.mk");
            let e = {
                let f = app(ctx, pmk, succ_two);
                app(ctx, f, one)
            };
            let p = app(ctx, succ, m);
            let r = ctx.kabstract(e, p).unwrap();
            let b0 = bvar(ctx, 0);
            let want = {
                let f = app(ctx, pmk, b0);
                app(ctx, f, one)
            };
            assert_eq!(r, want);
            let mv = ctx.instantiate_mvars(m).unwrap();
            assert_eq!(mv, two, "?m := two");
        });
    }

    /// The fvar fast path is plain `abstract`: it abstracts EVERY
    /// occurrence, with no defeq test.
    #[test]
    fn kabstract_fvar_pattern_is_abstract() {
        with_meta0_ctx(|ctx| {
            let n = c(ctx, "N");
            let x = fresh_fvar(ctx, n, "x");
            let succ = c(ctx, "N.succ");
            let e = app(ctx, succ, x);
            let r = ctx.kabstract(e, x).unwrap();
            let b0 = bvar(ctx, 0);
            assert_eq!(r, app(ctx, succ, b0));
        });
    }
}
