//! oracle: `elabBinRelCore` (`Extra.lean:497-562`). `binrel% R a b`
//! elaborates `R a b` through the `binop%` tree machinery, but WITHOUT the
//! expected type in the analysis (`:534`), and under `withSynthesizeLight`
//! (`:499`; no default instances, for the reason the oracle's comment at
//! `:500-528` gives).
//!
//! Each operand is its own `toTree` (`:531-532`), so a relation operand of
//! a relation (`(a < b) = (b < a)`) is a LEAF: `tree::go` recognises only
//! the five non-rel kinds.

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;

use super::analyze::analyze;
use super::to_expr::{apply_coe, to_expr_core};
use super::tree::{to_tree, BinOpKind, Tree};
use super::{mk_const_named, resolve_head, OpView};
use crate::app::expand::Arg;
use crate::app::{elab_app_args, AppCall};
use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;

pub(crate) fn elab_bin_rel_core(
    elab: &mut TermElabM,
    view: &OpView,
    no_prop: bool,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    // `resolveId? stx[1]` FIRST, outside `withSynthesizeLight` (`:498`,
    // `:554`).
    let f = resolve_head(elab, &view.head)?;
    let (lhs_stx, rhs_stx) = match view.args.as_slice() {
        [l, r] => (l.clone(), r.clone()),
        _ => {
            return Err(ElabError::Internal(
                "binrel: an op view without two operands".into(),
            ))
        }
    };
    elab.with_synthesize_light(kinds, |elab| {
        let lhs = to_tree(elab, &lhs_stx, kinds)?;
        let rhs = to_tree(elab, &rhs_stx, kinds)?;
        let tree = Tree::BinOp {
            r#ref: view.r#ref.clone(),
            kind: BinOpKind::Regular,
            f,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        };
        let r = analyze(elab, &tree, None)?;
        match r.max {
            Some(max) if !r.has_uncomparable => {
                // `:546-551`: `noProp` turns a `Prop` max type into `Bool`.
                let max = if no_prop && is_prop(elab, max)? {
                    bool_type(elab)?
                } else {
                    max
                };
                let coerced = apply_coe(elab, &tree, max, true, kinds)?;
                to_expr_core(elab, &coerced, kinds)
            }
            _ => {
                // `:536-544`: the default strategy + `toBoolIfNecessary`.
                // Borrow the operands back out of `tree` (moved into it above).
                let Tree::BinOp { lhs, rhs, .. } = &tree else {
                    return Err(ElabError::Internal(
                        "binrel: the tree built above is not a BinOp".into(),
                    ));
                };
                let l = to_expr_core(elab, lhs, kinds)?;
                let r = to_expr_core(elab, rhs, kinds)?;
                let l = to_bool_if_necessary(elab, no_prop, &lhs_stx, l)?;
                let r = to_bool_if_necessary(elab, no_prop, &rhs_stx, r)?;
                let l_ty = elab.mctx.infer_type(l)?;
                let r = elab.ensure_has_type(&rhs_stx, Some(l_ty), r)?;
                elab_app_args(
                    elab,
                    f,
                    AppCall {
                        named_args: Vec::new(),
                        args: vec![Arg::Expr(l), Arg::Expr(r)],
                        expected,
                        explicit: false,
                        ellipsis: false,
                        stx: view.r#ref.clone(),
                        result_is_out_param_support: false,
                    },
                    kinds,
                )
            }
        }
    })
}

/// `withNewMCtxDepth <| isDefEq e (mkSort Level.zero)` (`:549`, `:560`).
/// Unguarded: the oracle uses `isDefEq` here, not `isDefEqGuarded`, so an
/// error propagates.
fn is_prop(elab: &mut TermElabM, e: ExprId) -> Result<bool, ElabError> {
    let prop = crate::builtin::sort::mk_prop(elab)?;
    Ok(elab
        .mctx
        .with_new_mctx_depth(false, |m| m.is_def_eq(e, prop))?)
}

/// `Lean.mkConst ``Bool` (`:550`, `:561`): `Bool` has no level params.
fn bool_type(elab: &mut TermElabM) -> Result<ExprId, ElabError> {
    mk_const_named(elab, "Bool")
}

/// oracle: `toBoolIfNecessary` (`:557-562`).
fn to_bool_if_necessary(
    elab: &mut TermElabM,
    no_prop: bool,
    stx: &SynElem,
    e: ExprId,
) -> Result<ExprId, ElabError> {
    if no_prop {
        let ty = elab.mctx.infer_type(e)?;
        if is_prop(elab, ty)? {
            let b = bool_type(elab)?;
            return elab.ensure_has_type(stx, Some(b), e);
        }
    }
    Ok(e)
}
