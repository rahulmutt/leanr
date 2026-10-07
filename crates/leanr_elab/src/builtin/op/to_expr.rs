//! oracle: `mkBinOp`, `mkUnOp`, `toExprCore`, `hasHeterogeneousDefaultInstances`,
//! `hasHomogeneousInstance`, `applyCoe`, `toExpr` (`Extra.lean:316-473`),
//! plus `mkFunUnit` (`Meta/Basic.lean:1157-1158`) and a restricted
//! `mkAppM` (`Meta/AppBuilder.lean:364-367`, `mkAppMArgs` at `:303-334`).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;
use leanr_meta::{LOption, MetaError};
use leanr_syntax::kind::KindInterner;

use super::analyze::{analyze, is_unknown, leaf_type};
use super::grow;
use super::tree::{BinOpKind, Tree};
use crate::app::expand::Arg;
use crate::app::lval::{app_fn, node};
use crate::app::{elab_app_args, AppCall};
use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `mkFunUnit`: `fun (_ : Unit) => a`. The binder name is a fresh
/// user name in the oracle; leanr's canonical encoder erases binder names.
#[doc(hidden)]
pub fn mk_fun_unit(elab: &mut TermElabM, a: ExprId) -> Result<ExprId, ElabError> {
    let base = elab.view.store;
    let unit = crate::app::head::intern_dotted(elab, "Unit")?;
    let store = elab.mctx.store_mut();
    let no_levels = store
        .intern_level_list(Some(base), &[])
        .map_err(MetaError::from)?;
    let unit = store
        .expr_const(Some(base), Some(unit), no_levels)
        .map_err(MetaError::from)?;
    Ok(store
        .expr_lam(Some(base), None, unit, a, BinderInfo::Default)
        .map_err(MetaError::from)?)
}

/// `elabAppArgs f #[] args (expectedType? := none) (explicit := false)
/// (ellipsis := false) (resultIsOutParamSupport := false)` (`:320`, `:323`).
fn apply_op(
    elab: &mut TermElabM,
    f: ExprId,
    args: Vec<ExprId>,
    r#ref: &SynElem,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    elab_app_args(
        elab,
        f,
        AppCall {
            named_args: Vec::new(),
            args: args.into_iter().map(Arg::Expr).collect(),
            expected: None,
            explicit: false,
            ellipsis: false,
            stx: r#ref.clone(),
            result_is_out_param_support: false,
        },
        kinds,
    )
}

/// oracle: `mkBinOp` (`:316-320`).
fn mk_bin_op(
    elab: &mut TermElabM,
    lazy: bool,
    f: ExprId,
    lhs: ExprId,
    rhs: ExprId,
    r#ref: &SynElem,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let rhs = if lazy { mk_fun_unit(elab, rhs)? } else { rhs };
    apply_op(elab, f, vec![lhs, rhs], r#ref, kinds)
}

/// oracle: `toExprCore` (`:325-341`).
pub(crate) fn to_expr_core(
    elab: &mut TermElabM,
    t: &Tree,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    grow(|| match t {
        Tree::Term { val, .. } => Ok(*val),
        Tree::BinOp {
            r#ref,
            kind,
            f,
            lhs,
            rhs,
        } => {
            let l = to_expr_core(elab, lhs, kinds)?;
            let r = to_expr_core(elab, rhs, kinds)?;
            mk_bin_op(elab, *kind == BinOpKind::Lazy, *f, l, r, r#ref, kinds)
        }
        // `mkUnOp` (`:322-323`).
        Tree::UnOp { r#ref, f, arg } => {
            let a = to_expr_core(elab, arg, kinds)?;
            apply_op(elab, *f, vec![a], r#ref, kinds)
        }
        Tree::MacroExpansion { nested, .. } => to_expr_core(elab, nested, kinds),
    })
}

fn const_name(elab: &TermElabM, e: ExprId) -> Option<NameId> {
    match node(elab, e) {
        Node::Const { name, .. } => name,
        _ => None,
    }
}

/// `Name.getPrefix`; `None` (the anonymous name) for a root name.
fn name_prefix(elab: &TermElabM, n: NameId) -> Option<NameId> {
    use leanr_kernel::bank::names::NameRow;
    match *elab.mctx.store().name_row(Some(elab.view.store), n) {
        NameRow::Str { parent, .. } | NameRow::Num { parent, .. } => parent,
    }
}

/// oracle: `hasHeterogeneousDefaultInstances` (`:367-378`).
#[doc(hidden)]
pub fn has_heterogeneous_default_instances(
    elab: &mut TermElabM,
    f: ExprId,
    max: ExprId,
    lhs: bool,
) -> Result<bool, ElabError> {
    let Some(f_name) = const_name(elab, f) else {
        return Ok(false);
    };
    let Some(type_name) = const_name(elab, app_fn(elab, max)) else {
        return Ok(false);
    };
    // `getDefaultInstances .anonymous` is empty: no class has that name.
    let Some(class) = name_prefix(elab, f_name) else {
        return Ok(false);
    };
    let insts = elab.mctx.default_instances_of(class);
    if insts.len() <= 1 {
        return Ok(false);
    }
    for (inst, _) in insts {
        // `getConstInfo` throws on a missing name; a default instance is
        // always declared, so a miss is skipped rather than invented.
        let Some(info) = elab.view.get(inst) else {
            continue;
        };
        // `getForallBody`: strip binders WITHOUT instantiating (loose
        // bvars are fine for the `isAppOf` tests below).
        let mut ty = info.constant_val().ty;
        while let Node::Forall { body, .. } = node(elab, ty) {
            ty = body;
        }
        // `.app (.app (.app _heteroClass lhsType) rhsType) _resultType`
        let Node::App { f: f1, .. } = node(elab, ty) else {
            continue;
        };
        let Node::App { f: f2, arg: rhs_ty } = node(elab, f1) else {
            continue;
        };
        let Node::App { arg: lhs_ty, .. } = node(elab, f2) else {
            continue;
        };
        let is_app_of = |e: ExprId| const_name(elab, app_fn(elab, e)) == Some(type_name);
        if lhs && is_app_of(rhs_ty) {
            return Ok(true);
        }
        if !lhs && is_app_of(lhs_ty) {
            return Ok(true);
        }
    }
    Ok(false)
}

/// oracle: `mkAppM` (`AppBuilder.lean:364-367`) over `mkAppMArgs`
/// (`:303-334`) and `mkAppMFinal` (`:294-301`), restricted to a telescope
/// of EXPLICIT binders: every `binop%` class (`HAdd α β γ` …) has one. An
/// implicit or instance binder (the oracle would mint an mvar or
/// synthesize) is a named seam (`Unsupported`), never a silent `None`.
///
/// `Ok(None)` is each of the oracle's catchable throws: an undeclared
/// `cname` (`getConstVal`), an argument whose type does not match
/// (`throwAppTypeMismatch`, `:326`), too many arguments (`:333`), or a
/// level mvar of `f` left unassigned (`mkAppMFinal`'s `hasAssignableMVar`,
/// `:300`). Runs under `withNewMCtxDepth`, as the oracle does, and
/// instantiates INSIDE the scope, because the scope's exit discards inner
/// assignments.
#[doc(hidden)]
pub fn mk_app_m(
    elab: &mut TermElabM,
    cname: NameId,
    args: &[ExprId],
) -> Result<Option<ExprId>, ElabError> {
    if elab.view.get(cname).is_none() {
        return Ok(None);
    }
    let base = elab.view.store;
    let raw = elab.mk_const_with_level_params(cname)?;
    let r = elab
        .mctx
        .with_new_mctx_depth(false, |m| -> Result<Option<ExprId>, MetaError> {
            // `mkFun` (`:336-341`): fresh level mvars, minted at the inner
            // depth, so this scope may assign them -- in FORWARD order
            // (`levelParams.mapM`, `AppBuilder.lean:338`).
            let f = m.update_const_with_fresh_level_mvars(raw)?;
            let mut acc = f;
            let mut f_ty = m.infer_type(f)?;
            for &a in args {
                let mut ty_node = m.store().expr_node(Some(base), f_ty);
                if !matches!(ty_node, Node::Forall { .. }) {
                    // `:327-331`: `whnfD`, then a forall or too many args.
                    f_ty = m.whnf(f_ty)?;
                    ty_node = m.store().expr_node(Some(base), f_ty);
                }
                let Node::Forall {
                    binder_type,
                    body,
                    binder_info,
                    ..
                } = ty_node
                else {
                    return Ok(None);
                };
                if binder_info != BinderInfo::Default {
                    return Err(MetaError::Unsupported(
                        "mk_app_m: a non-explicit binder (owner: the slice that \
                         needs the full mkAppM)"
                            .into(),
                    ));
                }
                // `:322-323`: `isDefEq d xType`.
                let a_ty = m.infer_type(a)?;
                if !m.is_def_eq(binder_type, a_ty)? {
                    return Ok(None);
                }
                acc = m.store_mut().expr_app(Some(base), acc, a)?;
                f_ty = m.instantiate1(body, a)?;
            }
            let r = m.instantiate_mvars(acc)?;
            // `hasAssignableMVar`: the only mvars minted in this scope are
            // `f`'s fresh level mvars (explicit binders mint no expr mvar),
            // so a level mvar the inputs do not already carry is an
            // unassigned inner one. Inputs that carry level mvars are
            // outer-depth, hence not assignable; the check is skipped for
            // them, which is conservative only if an inner one ALSO stays
            // unassigned (no `binop%` class reaches that: every level of
            // `Cls max max max` is fixed by `max`'s sort).
            let has_lmvar = |m: &leanr_meta::MetaCtx, e: ExprId| {
                m.store().expr_data(Some(base), e).has_level_mvar()
            };
            let inputs_have_lmvar = args.iter().any(|&a| has_lmvar(m, a));
            if has_lmvar(m, r) && !inputs_have_lmvar {
                return Ok(None);
            }
            Ok(Some(r))
        });
    match r {
        Ok(r) => Ok(r),
        Err(e) if e.is_oracle_catchable() => Ok(None),
        Err(e) => Err(e.into()),
    }
}

/// oracle: `hasHomogeneousInstance` (`:387-394`):
/// `try … trySynthInstance (Cls max max max) matches .some _ catch _ => false`.
#[doc(hidden)]
pub fn has_homogeneous_instance(
    elab: &mut TermElabM,
    f: ExprId,
    max: ExprId,
) -> Result<bool, ElabError> {
    let Some(f_name) = const_name(elab, f) else {
        return Ok(false);
    };
    // `mkAppM .anonymous` throws "unknown constant": `false`.
    let Some(class) = name_prefix(elab, f_name) else {
        return Ok(false);
    };
    let Some(inst) = mk_app_m(elab, class, &[max, max, max])? else {
        return Ok(false);
    };
    match elab.mctx.try_synth_instance(inst) {
        Ok(r) => Ok(matches!(r, LOption::Some(_))),
        Err(e) if e.is_oracle_catchable() => Ok(false),
        Err(e) => Err(e.into()),
    }
}

/// oracle: `applyCoe` (`:415-455`). `rel.rs` calls it with `is_pred = true`.
pub(crate) fn apply_coe(
    elab: &mut TermElabM,
    t: &Tree,
    max: ExprId,
    is_pred: bool,
    kinds: &KindInterner,
) -> Result<Tree, ElabError> {
    apply_coe_go(elab, t, None, false, is_pred, max, kinds)
}

/// oracle: `applyCoe.go` (`:418-455`).
#[allow(clippy::too_many_arguments)]
fn apply_coe_go(
    elab: &mut TermElabM,
    t: &Tree,
    f: Option<ExprId>,
    lhs: bool,
    is_pred: bool,
    max: ExprId,
    kinds: &KindInterner,
) -> Result<Tree, ElabError> {
    grow(|| match t {
        Tree::BinOp {
            r#ref,
            kind: BinOpKind::LeftAct,
            f: op,
            lhs: l,
            rhs: r,
        } => Ok(Tree::BinOp {
            r#ref: r#ref.clone(),
            kind: BinOpKind::LeftAct,
            f: *op,
            lhs: l.clone(),
            rhs: Box::new(apply_coe_go(elab, r, None, false, false, max, kinds)?),
        }),
        Tree::BinOp {
            r#ref,
            kind: BinOpKind::RightAct,
            f: op,
            lhs: l,
            rhs: r,
        } => Ok(Tree::BinOp {
            r#ref: r#ref.clone(),
            kind: BinOpKind::RightAct,
            f: *op,
            lhs: Box::new(apply_coe_go(elab, l, None, false, false, max, kinds)?),
            rhs: r.clone(),
        }),
        Tree::BinOp {
            r#ref,
            kind,
            f: op,
            lhs: l,
            rhs: r,
        } => {
            // `:431`: `pure isPred <||> hasHomogeneousInstance f maxType`.
            if is_pred || has_homogeneous_instance(elab, *op, max)? {
                Ok(Tree::BinOp {
                    r#ref: r#ref.clone(),
                    kind: *kind,
                    f: *op,
                    lhs: Box::new(apply_coe_go(elab, l, Some(*op), true, false, max, kinds)?),
                    rhs: Box::new(apply_coe_go(elab, r, Some(*op), false, false, max, kinds)?),
                })
            } else {
                // `:434-437`: each side is its own `toExpr` problem.
                let le = to_expr(elab, l, None, kinds)?;
                let re = to_expr(elab, r, None, kinds)?;
                let val = mk_bin_op(elab, *kind == BinOpKind::Lazy, *op, le, re, r#ref, kinds)?;
                Ok(Tree::Term {
                    r#ref: r#ref.clone(),
                    val,
                })
            }
        }
        Tree::UnOp { r#ref, f: op, arg } => Ok(Tree::UnOp {
            r#ref: r#ref.clone(),
            f: *op,
            arg: Box::new(apply_coe_go(elab, arg, None, false, false, max, kinds)?),
        }),
        Tree::Term { r#ref, val } => {
            let ty = leaf_type(elab, *val)?;
            if is_unknown(elab, ty) {
                if let Some(f) = f {
                    if has_heterogeneous_default_instances(elab, f, max, lhs)? {
                        return Ok(t.clone());
                    }
                }
            }
            if elab.mctx.is_def_eq_guarded(max, ty)? {
                Ok(t.clone())
            } else {
                let val = elab.mk_coe(r#ref, max, *val)?;
                Ok(Tree::Term {
                    r#ref: r#ref.clone(),
                    val,
                })
            }
        }
        Tree::MacroExpansion { stx, nested } => Ok(Tree::MacroExpansion {
            stx: stx.clone(),
            nested: Box::new(apply_coe_go(elab, nested, f, lhs, is_pred, max, kinds)?),
        }),
    })
}

/// oracle: `toExpr` (`:457-471`).
pub(crate) fn to_expr(
    elab: &mut TermElabM,
    t: &Tree,
    expected: Option<ExprId>,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let r = analyze(elab, t, expected)?;
    let result = match r.max {
        Some(max) if !r.has_uncomparable => {
            let coerced = apply_coe(elab, t, max, false, kinds)?;
            let result = to_expr_core(elab, &coerced, kinds)?;
            if !r.has_unknown {
                // `:465-469`: record the max-type calculation.
                let ty = elab.mctx.infer_type(result)?;
                elab.mctx.is_def_eq_guarded(ty, max)?;
            }
            result
        }
        _ => to_expr_core(elab, t, kinds)?,
    };
    elab.ensure_has_type(t.ref_elem(), expected, result)
}
