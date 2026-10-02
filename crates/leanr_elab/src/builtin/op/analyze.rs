//! oracle: `hasCoe`, `AnalyzeResult`, `isUnknown`, `analyze`
//! (`Extra.lean:231-314`).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::BinderInfo;
use leanr_meta::LOption;

use super::grow;
use super::tree::{BinOpKind, Tree};
use crate::app::lval::node;
use crate::builtin::binder::fun::cleanup_annotations;
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `hasCoe` (`:232-240`): `coerceSimple?` on a fresh local of type
/// `from` (`withLocalDeclD`). `.undef` counts as `false` (the oracle's own
/// TODO). Assignments made by the attempt are NOT rolled back, as in the
/// oracle. The local context is restored on every path.
#[doc(hidden)]
pub fn has_coe(elab: &mut TermElabM, from: ExprId, to: ExprId) -> Result<bool, ElabError> {
    let coe_t = crate::app::head::intern_dotted(elab, "CoeT")?;
    if elab.view.get(coe_t).is_none() {
        return Ok(false);
    }
    let cp = elab.mctx.lctx_checkpoint();
    let r = match elab.mctx.push_local_decl(None, from, BinderInfo::Default) {
        Ok(x) => elab.mctx.coerce_simple(x, to),
        Err(e) => Err(e),
    };
    elab.mctx.lctx_restore(cp);
    Ok(matches!(r?, LOption::Some(_)))
}

/// oracle: `AnalyzeResult` (`:242-247`).
#[derive(Debug, Default)]
pub(crate) struct AnalyzeResult {
    pub max: Option<ExprId>,
    pub has_uncomparable: bool,
    pub has_unknown: bool,
}

/// oracle: `isUnknown` (`:249-254`).
#[doc(hidden)]
pub fn is_unknown(elab: &TermElabM, mut e: ExprId) -> bool {
    loop {
        match node(elab, e) {
            Node::MVar { .. } => return true,
            Node::App { f, .. } => e = f,
            Node::LetE { body, .. } => e = body,
            Node::MData { expr, .. } => e = expr,
            _ => return false,
        }
    }
}

/// `(← instantiateMVars (← inferType e)).cleanupAnnotations`
/// (`:274`, `:441`).
pub(crate) fn leaf_type(elab: &mut TermElabM, e: ExprId) -> Result<ExprId, ElabError> {
    let ty = elab.mctx.infer_type(e)?;
    let ty = elab.mctx.instantiate_mvars(ty)?;
    Ok(cleanup_annotations(elab, ty))
}

/// oracle: `analyze` (`:256-314`).
pub(crate) fn analyze(
    elab: &mut TermElabM,
    t: &Tree,
    expected: Option<ExprId>,
) -> Result<AnalyzeResult, ElabError> {
    let max = match expected {
        None => None,
        Some(ty) => {
            let ty = elab.mctx.instantiate_mvars(ty)?;
            let ty = cleanup_annotations(elab, ty);
            (!is_unknown(elab, ty)).then_some(ty)
        }
    };
    let mut r = AnalyzeResult {
        max,
        ..Default::default()
    };
    go(elab, t, &mut r)?;
    Ok(r)
}

/// oracle: `analyze.go` (`:265-314`).
fn go(elab: &mut TermElabM, t: &Tree, r: &mut AnalyzeResult) -> Result<(), ElabError> {
    if r.has_uncomparable {
        return Ok(());
    }
    grow(|| match t {
        Tree::MacroExpansion { nested, .. } => go(elab, nested, r),
        Tree::BinOp {
            kind: BinOpKind::LeftAct,
            rhs,
            ..
        } => go(elab, rhs, r),
        Tree::BinOp {
            kind: BinOpKind::RightAct,
            lhs,
            ..
        } => go(elab, lhs, r),
        Tree::BinOp { lhs, rhs, .. } => {
            go(elab, lhs, r)?;
            go(elab, rhs, r)
        }
        Tree::UnOp { arg, .. } => go(elab, arg, r),
        Tree::Term { val, .. } => {
            let ty = leaf_type(elab, *val)?;
            if is_unknown(elab, ty) {
                r.has_unknown = true;
                return Ok(());
            }
            let Some(max) = r.max else {
                r.max = Some(ty);
                return Ok(());
            };
            // `:307`: `withNewMCtxDepth <| withConfig (isDefEqStuckEx :=
            // true) <| isDefEqGuarded max type`, the P1 dependency.
            let same = elab.mctx.with_new_mctx_depth(false, |m| {
                m.with_def_eq_stuck_ex(|m| m.is_def_eq_guarded(max, ty))
            })?;
            if !same {
                if has_coe(elab, ty, max)? {
                    // `max` stays.
                } else if has_coe(elab, max, ty)? {
                    r.max = Some(ty);
                } else {
                    r.has_uncomparable = true;
                }
            }
            Ok(())
        }
    })
}
