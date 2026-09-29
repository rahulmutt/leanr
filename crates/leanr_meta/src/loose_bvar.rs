//! The exact `Expr.hasLooseBVar` test (`Lean/Expr.lean:1330`, an
//! `opaque`), which leanr otherwise lacks.
//!
//! `ExprData::loose_bvar_range` is `1 + max loose index`, saturating at
//! the kernel's `LOOSE_BVAR_SAT`, so `range > 0` answers "is ANY bvar
//! loose", not "is THIS bvar loose". The two differ exactly when every
//! loose index is `>= 1`, which is the case the oracle's
//! `mkAuxMVarType` unused-let arm turns on (`MetavarContext.lean:1138`).
//! `loose_bvar_range_exact` is `pub(crate)` to `leanr_kernel`, so the only
//! fast path available here is the public saturating accessor, sound in
//! one direction: a range of `0` proves the term closed.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;

use crate::{MetaCtx, MetaError};

// No caller until Task 8 (`mk_aux_mvar_type`'s unused-let arm); `expect`
// fails the build once it has one, forcing this line's removal.
#[cfg_attr(not(test), expect(dead_code))]
impl MetaCtx<'_> {
    /// oracle: `Expr.hasLooseBVar e bvarIdx` (`Lean/Expr.lean:1330`).
    ///
    /// Entry point: the closed fast path, one step, one guard, the
    /// shape `depends_on` (`mk_binding.rs`) uses, with the recursion
    /// re-entering here so every level steps and guards.
    pub(crate) fn has_loose_bvar(&mut self, e: ExprId, idx: u32) -> Result<bool, MetaError> {
        if self.data(e).loose_bvar_range() == 0 {
            return Ok(false);
        }
        self.step()?;
        self.guarded(|ctx| ctx.has_loose_bvar_body(e, idx))
    }

    /// `idx + 1` for descending under a binder. If it overflows `u32`
    /// no bvar (`BVar` holds a `u32`) can match, so the answer is false.
    fn under_binder(&mut self, e: ExprId, idx: u32) -> Result<bool, MetaError> {
        match idx.checked_add(1) {
            Some(i) => self.has_loose_bvar(e, i),
            None => Ok(false),
        }
    }

    fn has_loose_bvar_body(&mut self, e: ExprId, idx: u32) -> Result<bool, MetaError> {
        match self.node(e) {
            Node::BVar { idx: i } => Ok(i == idx),
            // `BVarBig` holds an index that did NOT fit a `u32`, and
            // `idx` is a `u32`, so it can never be the one asked about.
            Node::BVarBig { .. } => Ok(false),
            Node::FVar { .. }
            | Node::MVar { .. }
            | Node::Sort { .. }
            | Node::Const { .. }
            | Node::LitNat { .. }
            | Node::LitStr { .. } => Ok(false),
            Node::App { f, arg } => {
                Ok(self.has_loose_bvar(f, idx)? || self.has_loose_bvar(arg, idx)?)
            }
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => Ok(self.has_loose_bvar(binder_type, idx)? || self.under_binder(body, idx)?),
            Node::LetE {
                ty, value, body, ..
            } => Ok(self.has_loose_bvar(ty, idx)?
                || self.has_loose_bvar(value, idx)?
                || self.under_binder(body, idx)?),
            Node::MData { expr, .. } => self.has_loose_bvar(expr, idx),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                self.has_loose_bvar(structure, idx)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::test_support::with_ctx;
    use leanr_kernel::Nat;

    /// The case that makes this function necessary: a term whose only
    /// loose bvar is `#1`. `loose_bvar_range()` is 2 (greater than
    /// zero) but `hasLooseBVar 0` is FALSE. Using the range as a proxy
    /// gets this backwards. This singular test is what `mkAuxMVarType`'s
    /// unused-let arm needs (`MetavarContext.lean:1138`,
    /// `e.hasLooseBVar 0`).
    #[test]
    fn has_loose_bvar_distinguishes_index_one_from_index_zero() {
        with_ctx(|ctx| {
            let b1 = ctx
                .scratch
                .expr_bvar(None, &Nat::from(1u64))
                .expect("bvar 1");
            assert!(
                ctx.data(b1).loose_bvar_range() > 0,
                "precondition: the packed range is nonzero for `#1`"
            );
            assert!(!ctx.has_loose_bvar(b1, 0).expect("has_loose_bvar"));
            assert!(ctx.has_loose_bvar(b1, 1).expect("has_loose_bvar"));
        });
    }

    /// A binder closes one level: inside `fun _ => #1`, the body's `#1`
    /// is the caller's `#0`.
    #[test]
    fn has_loose_bvar_shifts_under_a_binder() {
        with_ctx(|ctx| {
            let zero = ctx.scratch.level_zero(None).expect("level");
            let sort0 = ctx.scratch.expr_sort(None, zero).expect("Sort 0");
            let b1 = ctx
                .scratch
                .expr_bvar(None, &Nat::from(1u64))
                .expect("bvar 1");
            let lam = ctx
                .scratch
                .expr_lam(None, None, sort0, b1, leanr_kernel::BinderInfo::Default)
                .expect("lam");
            assert!(ctx.has_loose_bvar(lam, 0).expect("has_loose_bvar"));
            assert!(!ctx.has_loose_bvar(lam, 1).expect("has_loose_bvar"));
        });
    }

    /// The fast path: a closed term is `false` for every index.
    #[test]
    fn has_loose_bvar_is_false_for_a_closed_term() {
        with_ctx(|ctx| {
            let zero = ctx.scratch.level_zero(None).expect("level");
            let sort0 = ctx.scratch.expr_sort(None, zero).expect("Sort 0");
            assert!(!ctx.has_loose_bvar(sort0, 0).expect("has_loose_bvar"));
        });
    }
}
