//! oracle: `Expr.abstractRange` / C++ `abstract` (`src/kernel/abstract.cpp`),
//! which abstracts free AND meta variables. The kernel's port
//! (`leanr_kernel::abstract_fvars`, `subst.rs`) handles fvars only and is
//! TCB; this module is the `leanr_meta`-local twin used only when a
//! telescope contains a metavariable (`MkBinding.mkBinding` with
//! `mvarIdsToAbstract`, `MetavarContext.lean:1364`).
//!
//! `abstract_go` is a copy of the kernel's `subst.rs::abstract_go` with
//! three differences only: the skip test also lets expr-mvar-carrying
//! subterms through, an `MVar` node is matched against the `MVar`
//! entries of `xs` exactly as an `FVar` node is against the `FVar`
//! entries, and an entry only ever matches a node of its own kind.
//! Keep in sync with `leanr_kernel::subst::abstract_go` (TCB, so this
//! copy lives here; a fix to either must be mirrored in the other).

use std::collections::HashMap;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, Store};
use leanr_kernel::{KernelError, Nat, RecGuard};

use crate::{MetaCtx, MetaError};

/// The kernel's `subst.rs` `VisitCache`, restated (private there):
/// `(ExprId, offset)` keyed, `replace_fn.cpp:27-30`'s memo.
type VisitCache = HashMap<(ExprId, u32), ExprId>;

impl MetaCtx<'_> {
    /// Abstract `xs` (fvars and/or mvars) out of `e`: the entry at index
    /// `i` becomes `bvar(offset + xs.len() - i - 1)`. `xs` all fvars ⇒
    /// exactly the kernel's `abstract_fvars` (today's path, byte for
    /// byte); otherwise the mvar-aware twin below.
    pub(crate) fn abstract_vars(&mut self, e: ExprId, xs: &[ExprId]) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        if xs
            .iter()
            .all(|&x| matches!(self.node(x), Node::FVar { .. }))
        {
            return Ok(leanr_kernel::abstract_fvars(
                self.scratch,
                base,
                e,
                xs,
                &mut self.guard,
            )?);
        }
        Ok(abstract_go(
            self.scratch,
            base,
            e,
            0,
            xs,
            &mut self.guard,
            &mut VisitCache::new(),
        )?)
    }
}

/// abstract.cpp:18-19's skip test, widened to metavariables.
fn skip(st: &Store, base: Option<&Store>, e: ExprId) -> bool {
    let d = st.expr_data(base, e);
    !(d.has_fvar() || d.has_expr_mvar())
}

fn abstract_go(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    offset: u32,
    xs: &[ExprId],
    g: &mut RecGuard,
    cache: &mut VisitCache,
) -> Result<ExprId, KernelError> {
    if skip(st, base, e) {
        return Ok(e);
    }
    let key = (e, offset);
    if let Some(&r) = cache.get(&key) {
        return Ok(r);
    }
    let r = match st.expr_node(base, e) {
        node @ (Node::FVar { .. } | Node::MVar { .. }) => {
            let n = xs.len();
            let mut hit = None;
            for i in (0..n).rev() {
                // An entry matches only a node of its own kind.
                let same = match (node, st.expr_node(base, xs[i])) {
                    (Node::FVar { id }, Node::FVar { id: xid }) => id == xid,
                    (Node::MVar { id }, Node::MVar { id: xid }) => id == xid,
                    _ => false,
                };
                if same {
                    let rel = (n as u64) - (i as u64) - 1;
                    let new_idx = (offset as u64)
                        .checked_add(rel)
                        .ok_or(KernelError::LooseBVar)?;
                    hit = Some(new_idx);
                    break;
                }
            }
            match hit {
                // As in the kernel: a hit returns without `save_result`.
                Some(new_idx) => return st.expr_bvar(base, &Nat::from(new_idx)),
                None => e,
            }
        }
        Node::BVar { .. }
        | Node::BVarBig { .. }
        | Node::Sort { .. }
        | Node::Const { .. }
        | Node::LitNat { .. }
        | Node::LitStr { .. } => e,
        Node::App { f, arg } => {
            let (f2, arg2) = g.enter(|g| {
                Ok((
                    abstract_go(st, base, f, offset, xs, g, cache)?,
                    abstract_go(st, base, arg, offset, xs, g, cache)?,
                ))
            })?;
            if f2 == f && arg2 == arg {
                e
            } else {
                st.expr_app(base, f2, arg2)?
            }
        }
        Node::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    abstract_go(st, base, binder_type, offset, xs, g, cache)?,
                    abstract_go(st, base, body, offset + 1, xs, g, cache)?,
                ))
            })?;
            if bt2 == binder_type && bd2 == body {
                e
            } else {
                st.expr_lam(base, binder_name, bt2, bd2, binder_info)?
            }
        }
        Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    abstract_go(st, base, binder_type, offset, xs, g, cache)?,
                    abstract_go(st, base, body, offset + 1, xs, g, cache)?,
                ))
            })?;
            if bt2 == binder_type && bd2 == body {
                e
            } else {
                st.expr_forall(base, binder_name, bt2, bd2, binder_info)?
            }
        }
        Node::LetE {
            decl_name,
            ty,
            value,
            body,
            non_dep,
        } => {
            let (t2, v2, b2) = g.enter(|g| {
                Ok((
                    abstract_go(st, base, ty, offset, xs, g, cache)?,
                    abstract_go(st, base, value, offset, xs, g, cache)?,
                    abstract_go(st, base, body, offset + 1, xs, g, cache)?,
                ))
            })?;
            if t2 == ty && v2 == value && b2 == body {
                e
            } else {
                st.expr_let(base, decl_name, t2, v2, b2, non_dep)?
            }
        }
        Node::MData { data, expr } => {
            let expr2 = g.enter(|g| abstract_go(st, base, expr, offset, xs, g, cache))?;
            if expr2 == expr {
                e
            } else {
                st.expr_mdata(base, data, expr2)?
            }
        }
        node @ (Node::Proj { .. } | Node::ProjBig { .. }) => {
            let (type_name, structure) = match node {
                Node::Proj {
                    type_name,
                    structure,
                    ..
                }
                | Node::ProjBig {
                    type_name,
                    structure,
                    ..
                } => (type_name, structure),
                _ => unreachable!(),
            };
            let structure2 = g.enter(|g| abstract_go(st, base, structure, offset, xs, g, cache))?;
            if structure2 == structure {
                e
            } else {
                let idx_nat = match node {
                    Node::Proj { idx, .. } => Nat::from(idx as u64),
                    Node::ProjBig { idx, .. } => st.nat_at(base, idx).clone(),
                    _ => unreachable!(),
                };
                st.expr_proj(base, type_name, &idx_nat, structure2)?
            }
        }
    };
    cache.insert(key, r);
    Ok(r)
}

#[cfg(test)]
mod tests {
    use crate::test_support::{app, bvar, cu, fresh_fvar, fresh_mvar, with_ctx};

    /// A mixed telescope numbers its entries by position (`offset + n -
    /// i - 1`), under a binder too, and an mvar not in `xs` stays.
    #[test]
    fn abstract_vars_matches_by_kind_and_position() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let u = ctx.scratch.level_zero(base).expect("level");
            let sort = ctx.scratch.expr_sort(base, u).expect("sort");
            let (m, _) = fresh_mvar(ctx, sort);
            let (other, _) = fresh_mvar(ctx, sort);
            let x = fresh_fvar(ctx, m, "x");
            let f = cu(ctx, "f", &[]);
            // f ?m x ?other, under `fun (_ : Sort 0) => _`
            let inner = app(ctx, f, m);
            let inner = app(ctx, inner, x);
            let inner = app(ctx, inner, other);
            let e = ctx
                .scratch
                .expr_lam(base, None, sort, inner, leanr_kernel::BinderInfo::Default)
                .expect("lam");
            let r = ctx.abstract_vars(e, &[m, x]).expect("ok");
            let (b2, b1) = (bvar(ctx, 2), bvar(ctx, 1));
            let want = app(ctx, f, b2);
            let want = app(ctx, want, b1);
            let want = app(ctx, want, other);
            let want = ctx
                .scratch
                .expr_lam(base, None, sort, want, leanr_kernel::BinderInfo::Default)
                .expect("lam");
            assert_eq!(r, want, "fun _ => f #2 #1 ?other");
        });
    }
}
