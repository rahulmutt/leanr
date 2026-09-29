//! M4b-4a: the LVal machinery — dot notation's field and index
//! projections. Oracle: `Lean/Elab/App.lean:1435-1897` (pinned
//! v4.33.0-rc1). Design: docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_kernel::{BinderInfo, ConstantInfo, Nat};
use leanr_meta::{MVarId, MVarKind, MetaError};
use leanr_syntax::kind::KindInterner;

use crate::app::expand::{Arg, NamedArg};
use crate::app::AppCall;
use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::{ElabError, InvalidFieldReason, InvalidProjectionReason};

/// oracle: `inductive LVal` (`TermElabM.lean:662-666`). The
/// `suffix?`/`fullRef` fields of `fieldName` only feed the
/// unknown-name error of an identifier-embedded field, which is P4's
/// (`resolveName`'s field split); they are added there.
#[derive(Debug, Clone)]
pub enum LVal {
    FieldName {
        r#ref: SynElem,
        name: String,
        levels: Vec<LevelId>,
    },
    FieldIdx {
        r#ref: SynElem,
        idx: usize,
        levels: Vec<LevelId>,
    },
}

impl LVal {
    /// oracle: `LVal.getRef` (`TermElabM.lean:668-670`).
    fn get_ref(&self) -> &SynElem {
        match self {
            LVal::FieldName { r#ref, .. } | LVal::FieldIdx { r#ref, .. } => r#ref,
        }
    }
}

/// oracle: `LValResolution` (`App.lean:1435-1447`). P1 ports the two
/// arms that need no namespace search; `const` is P3's and `localRec`
/// needs `auxDeclToFullName`, which has no leanr producer (the
/// `let rec` slice).
enum LValResolution {
    ProjFn {
        base: NameId,
        struct_name: NameId,
        field: NameId,
        levels: Vec<LevelId>,
    },
    ProjIdx {
        struct_name: NameId,
        idx: usize,
    },
}

fn node(elab: &TermElabM, e: ExprId) -> Node {
    elab.mctx.store().expr_node(Some(elab.view.store), e)
}

/// oracle: `Expr.getAppFn`.
fn app_fn(elab: &TermElabM, mut e: ExprId) -> ExprId {
    while let Node::App { f, .. } = node(elab, e) {
        e = f;
    }
    e
}

/// oracle: `Expr.getAppArgs`, application order.
fn app_args(elab: &TermElabM, mut e: ExprId) -> Vec<ExprId> {
    let mut out = Vec::new();
    while let Node::App { f, arg } = node(elab, e) {
        out.push(arg);
        e = f;
    }
    out.reverse();
    out
}

fn render(elab: &TermElabM, n: NameId) -> String {
    elab.mctx
        .store()
        .to_name(Some(elab.view.store), Some(n))
        .to_string()
}

fn mk_app(elab: &mut TermElabM, f: ExprId, a: ExprId) -> Result<ExprId, ElabError> {
    let base = elab.view.store;
    Ok(elab
        .mctx
        .store_mut()
        .expr_app(Some(base), f, a)
        .map_err(MetaError::from)?)
}

/// oracle: `Expr.getOptParamDefault?` (`Expr.lean:1695-1699`) —
/// `optParam α default`, arity 2.
fn opt_param_default(elab: &TermElabM, ty: ExprId) -> Option<ExprId> {
    let args = app_args(elab, ty);
    match node(elab, app_fn(elab, ty)) {
        Node::Const { name: Some(n), .. } if args.len() == 2 && render(elab, n) == "optParam" => {
            Some(args[1])
        }
        _ => None,
    }
}

/// oracle: `consumeImplicits` (`App.lean:1659-1676`) — `whnfCore`, then
/// fill leading implicit / (with args) strict-implicit / inst-implicit
/// binders and `optParam` defaults. `autoParam` is left alone, as in the
/// oracle ("TODO: we do not handle autoParams here").
fn consume_implicits(
    elab: &mut TermElabM,
    stx: &SynElem,
    mut e: ExprId,
    e_type: ExprId,
    has_args: bool,
) -> Result<(ExprId, ExprId), ElabError> {
    let mut e_type = elab.mctx.whnf_core(e_type)?;
    loop {
        let Node::Forall {
            binder_type: d,
            body: b,
            binder_info: bi,
            ..
        } = node(elab, e_type)
        else {
            return Ok((e, e_type));
        };
        let arg = match bi {
            BinderInfo::Implicit => natural_hole(elab, d, stx)?,
            BinderInfo::StrictImplicit if has_args => natural_hole(elab, d, stx)?,
            // `Term.mkInstMVar` (`TermElabM.lean:1925-1930`): the EAGER
            // one, synthesizing on the spot — not `ElabAppArgs`' deferred
            // `where`-binding.
            BinderInfo::InstImplicit => {
                let mvar = elab.mk_inst_mvar(d, stx.clone())?;
                let r = mk_app(elab, e, mvar)?;
                // `registerMVarErrorImplicitArgInfo mvar.mvarId! stx r`
                // (`App.lean:1670`).
                if let Node::MVar { id: Some(n) } = node(elab, mvar) {
                    elab.register_mvar_error_implicit_arg_info(MVarId(n), stx.clone(), r);
                }
                let next = elab.mctx.instantiate1(b, mvar)?;
                e = r;
                e_type = elab.mctx.whnf_core(next)?;
                continue;
            }
            _ => match opt_param_default(elab, d) {
                Some(def_val) => def_val,
                None => return Ok((e, e_type)),
            },
        };
        e = mk_app(elab, e, arg)?;
        let next = elab.mctx.instantiate1(b, arg)?;
        e_type = elab.mctx.whnf_core(next)?;
    }
}

/// `mkFreshExprMVar d` + `registerMVarErrorHoleInfo` (`App.lean:1664-1665`).
fn natural_hole(elab: &mut TermElabM, d: ExprId, stx: &SynElem) -> Result<ExprId, ElabError> {
    let (m, id) = elab.mk_fresh_expr_mvar_of_kind(d, MVarKind::Natural)?;
    elab.register_mvar_error_hole_info(id, stx.clone());
    Ok(m)
}

/// oracle: `matchConstStructure` (`MonadEnv.lean:153-160`): a constant
/// naming an inductive with exactly one constructor. Returns its
/// `numFields`.
fn match_const_structure(elab: &TermElabM, s: NameId) -> Option<usize> {
    let ConstantInfo::Induct(ind) = elab.view.get(s)? else {
        return None;
    };
    let [ctor] = ind.ctors.as_slice() else {
        return None;
    };
    let ConstantInfo::Ctor(c) = elab.view.get(*ctor)? else {
        return None;
    };
    c.num_fields.to_usize()
}

/// oracle: `resolveLValAux` (`App.lean:1517-1616`), P1's arms.
fn resolve_lval_aux(
    elab: &mut TermElabM,
    e: ExprId,
    e_type: ExprId,
    lval: &LVal,
) -> Result<LValResolution, ElabError> {
    let head = node(elab, app_fn(elab, e_type));
    let proj_err = |reason| ElabError::InvalidProjection { e, e_type, reason };
    let field_err = |field: &str, reason| ElabError::InvalidField {
        e,
        e_type,
        field: field.to_string(),
        reason,
    };
    match (head, lval) {
        // `:1519-1551`.
        (Node::Const { name: Some(s), .. }, LVal::FieldIdx { idx, levels, .. }) => {
            if *idx == 0 {
                return Err(proj_err(InvalidProjectionReason::IndexZero));
            }
            let Some(num_fields) = match_const_structure(elab, s) else {
                return Err(proj_err(InvalidProjectionReason::NotOneCtor));
            };
            if idx - 1 < num_fields {
                if elab.mctx.is_structure(s) {
                    // `fieldNames[idx - 1]!` (`:1532`): a panic in the
                    // oracle when `structureExt` disagrees with the
                    // constructor, which untrusted `.olean` input can make
                    // happen.
                    let Some(&field) = elab.mctx.get_structure_fields(s).get(idx - 1) else {
                        return Err(ElabError::Internal(format!(
                            "structure `{}` has fewer fields than its constructor",
                            render(elab, s)
                        )));
                    };
                    Ok(LValResolution::ProjFn {
                        base: s,
                        struct_name: s,
                        field,
                        levels: levels.clone(),
                    })
                } else if !levels.is_empty() {
                    Err(proj_err(InvalidProjectionReason::ExplicitUnivsOnInductive))
                } else {
                    Ok(LValResolution::ProjIdx {
                        struct_name: s,
                        idx: idx - 1,
                    })
                }
            } else if num_fields == 0 {
                Err(proj_err(InvalidProjectionReason::NoFields))
            } else {
                Err(proj_err(InvalidProjectionReason::IndexOutOfRange {
                    idx: *idx,
                    num_fields,
                }))
            }
        }
        // `:1552-1578`.
        (Node::Const { name: Some(s), .. }, LVal::FieldName { name, levels, .. }) => {
            // `Name.mkSimple fieldName`: `name` is one component.
            let field = crate::app::head::intern_components(elab, &[name])?;
            if elab.mctx.is_structure(s) {
                if let Some(base) = elab.mctx.find_field(s, field) {
                    return Ok(LValResolution::ProjFn {
                        base,
                        struct_name: s,
                        field,
                        levels: levels.clone(),
                    });
                }
            }
            // `:1557-1566`: the local-context search for an aux decl
            // (`LValResolution.localRec`). leanr's local context never
            // holds an aux decl (no `let rec` / `where` producer), so
            // the oracle's loop finds nothing here too — nothing to port.
            Err(ElabError::UnsupportedSyntax(format!(
                "`.{name}` on `{}` needs generalized field notation \
                 (`findMethod?`, App.lean:1453-1477 / :1568-1569) — M4b-4a P3",
                render(elab, s)
            )))
        }
        // `:1580-1588`.
        (Node::Forall { .. }, LVal::FieldName { name, .. }) => {
            let full = format!("Function.{name}");
            let full_id = crate::app::head::intern_components(elab, &["Function", name])?;
            if elab.view.get(full_id).is_some() {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "`.{name}` on a function resolves to `{full}` (App.lean:1581-1583) — M4b-4a P3"
                )));
            }
            // `:1584-1586`'s `c ++ suffix` sub-arm needs `suffix?`, which
            // only P4 produces; with `suffix? = none` it is `:1588`.
            Err(field_err(
                name,
                InvalidFieldReason::NotFound { full_name: full },
            ))
        }
        // `:1589-1591`.
        (Node::Forall { .. }, LVal::FieldIdx { .. }) => {
            Err(proj_err(InvalidProjectionReason::OnFunction))
        }
        // `:1593-1600`; the `reverseFieldLookup` hint is prose.
        (Node::MVar { .. }, LVal::FieldName { name, .. }) => {
            Err(field_err(name, InvalidFieldReason::TypeUnknown))
        }
        // `:1601-1603`.
        (Node::MVar { .. }, LVal::FieldIdx { .. }) => {
            Err(proj_err(InvalidProjectionReason::TypeUnknown))
        }
        // `:1605-1616`. The `c ++ suffix` sub-arm (`:1607-1608`) needs
        // `suffix?`, which only P4 produces.
        (_, LVal::FieldName { name, .. }) => Err(field_err(name, InvalidFieldReason::NotConstApp)),
        (_, LVal::FieldIdx { .. }) => Err(proj_err(InvalidProjectionReason::NotConstApp)),
    }
}

/// Which errors `resolveLValLoop`'s `catch` retries (`App.lean:1688-1694`:
/// `.error` retries, `.internal` rethrows). Named seams are NOT oracle
/// errors — retrying one would report an error for a path leanr never
/// ran (plan § Review Focus 2) — and `Meta` errors are leanr's
/// internal/budget failures. `Postpone` is the oracle's internal
/// `postponeExceptionId`, which the `.internal` arm rethrows.
fn is_retryable(e: &ElabError) -> bool {
    !matches!(
        e,
        ElabError::UnsupportedSyntax(_)
            | ElabError::Meta(_)
            | ElabError::Internal(_)
            | ElabError::Postpone
    )
}

/// oracle: `resolveLValLoop` (`App.lean:1678-1694`).
fn resolve_lval_loop(
    elab: &mut TermElabM,
    lval: &LVal,
    e: ExprId,
    e_type: ExprId,
    has_args: bool,
    kinds: &KindInterner,
) -> Result<(ExprId, LValResolution), ElabError> {
    let (e, e_type) = consume_implicits(elab, lval.get_ref(), e, e_type, has_args)?;
    // oracle: `tryPostponeIfMVar eType` (`App.lean:1680`), then, when
    // postponement is off (ladder rungs 2 and 4, or a resume below
    // them), `if (← isMVarApp eType) then
    // synthesizeSyntheticMVarsUsingDefault` (`:1681-1683`) — try default
    // instances to unblock the type before resolving.
    elab.try_postpone_if_mvar(e_type)?;
    if elab.is_mvar_app(e_type)? {
        elab.synthesize_synthetic_mvars_using_default(kinds)?;
    }
    let e_type = elab.mctx.instantiate_mvars(e_type)?;
    match resolve_lval_aux(elab, e, e_type, lval) {
        Ok(r) => Ok((e, r)),
        Err(err) if is_retryable(&err) => match elab.mctx.unfold_definition_pub(e_type)? {
            Some(t) => resolve_lval_loop(elab, lval, e, t, has_args, kinds),
            None => Err(err),
        },
        Err(err) => Err(err),
    }
}

/// oracle: `resolveLVal` (`App.lean:1696-1698`).
fn resolve_lval(
    elab: &mut TermElabM,
    e: ExprId,
    lval: &LVal,
    has_args: bool,
    kinds: &KindInterner,
) -> Result<(ExprId, LValResolution), ElabError> {
    let e_type = elab.mctx.infer_type(e)?;
    resolve_lval_loop(elab, lval, e, e_type, has_args, kinds)
}

/// oracle: `mkProjAndCheck` (`App.lean:65-73`).
fn mk_proj_and_check(
    elab: &mut TermElabM,
    s: NameId,
    idx: usize,
    e: ExprId,
) -> Result<ExprId, ElabError> {
    let base = elab.view.store;
    let r = elab
        .mctx
        .store_mut()
        .expr_proj(Some(base), Some(s), &Nat::from(idx as u64), e)
        .map_err(MetaError::from)?;
    let e_type = elab.mctx.infer_type(e)?;
    if elab.mctx.is_prop(e_type)? {
        let r_type = elab.mctx.infer_type(r)?;
        if !elab.mctx.is_prop(r_type)? {
            return Err(ElabError::InvalidProjection {
                e,
                e_type,
                reason: InvalidProjectionReason::NonPropFromProp,
            });
        }
    }
    Ok(r)
}

/// oracle: `mkBaseProjections` (`App.lean:1700-1710`): walk
/// `getPathToBaseStructure?`, applying each parent projection to the
/// structure value's own type arguments — with the universe levels of
/// that TYPE's head constant, reused as is (no fresh level mvars, no
/// `mkConst`). The oracle `panic!`s on both failure paths; untrusted
/// `.olean` input can reach them here, so they are `Internal` errors.
fn mk_base_projections(
    elab: &mut TermElabM,
    base_struct: NameId,
    struct_name: NameId,
    mut e: ExprId,
) -> Result<ExprId, ElabError> {
    let Some(path) = elab
        .mctx
        .get_path_to_base_structure(base_struct, struct_name)
    else {
        return Err(ElabError::Internal(
            "Failed to access field in parent structure (App.lean:1703)".to_string(),
        ));
    };
    let base = elab.view.store;
    for proj_fn in path {
        let ty = elab.mctx.infer_type(e)?;
        let ty = elab.mctx.whnf(ty)?;
        let Node::Const { levels, .. } = node(elab, app_fn(elab, ty)) else {
            return Err(ElabError::Internal(
                "Type of structure value cannot be reduced to a constant application \
                 (App.lean:1708)"
                    .to_string(),
            ));
        };
        let mut f = elab
            .mctx
            .store_mut()
            .expr_const(Some(base), Some(proj_fn), levels)
            .map_err(MetaError::from)?;
        for p in app_args(elab, ty) {
            f = mk_app(elab, f, p)?;
        }
        e = mk_app(elab, f, e)?;
    }
    Ok(e)
}

/// oracle: `elabAppLVals` / `elabAppLValsAux` (`App.lean:1843-1897`).
/// Matches the oracle's control flow: `projIdx` and a non-final
/// `projFn` do `loop f lvals`; a FINAL `projFn` ends in `elabAppArgs
/// projFn (namedArgs + self) args …` (`:1867-1869`), consuming the
/// outer call; the empty list ends in `elabAppArgs f namedArgs args …`.
pub fn elab_app_lvals(
    elab: &mut TermElabM,
    mut f: ExprId,
    lvals: Vec<LVal>,
    mut call: AppCall,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    // `hasArgs` reads the OUTER application's arguments on every
    // iteration (`:1850`), not the ones a non-final step passes on.
    let has_args = !call.named_args.is_empty() || !call.args.is_empty();
    let n = lvals.len();
    for (i, lval) in lvals.into_iter().enumerate() {
        let last = i + 1 == n;
        let (e, res) = resolve_lval(elab, f, &lval, has_args, kinds)?;
        match res {
            LValResolution::ProjIdx { struct_name, idx } => {
                f = mk_proj_and_check(elab, struct_name, idx, e)?;
            }
            LValResolution::ProjFn {
                base,
                struct_name,
                field,
                levels,
            } => {
                let e = mk_base_projections(elab, base, struct_name, e)?;
                // `getFieldInfo?` after `findField?` (`:1859`,
                // `unreachable!`): only malformed `structureExt` data can
                // make it miss.
                let Some(proj_fn_name) = elab.mctx.get_field_info(base, field).map(|i| i.proj_fn)
                else {
                    return Err(ElabError::Internal(format!(
                        "structure `{}` has no field info for `{}` (App.lean:1859)",
                        render(elab, base),
                        render(elab, field)
                    )));
                };
                let proj_name = render(elab, proj_fn_name);
                // `isInaccessiblePrivateName` (`:1860-1861`). leanr does
                // not model private-name accessibility (module scoping of
                // `_private` names), so a private projection is a seam,
                // not a guess.
                if proj_name.starts_with("_private.") {
                    return Err(ElabError::UnsupportedSyntax(format!(
                        "private field projection `{proj_name}` (`isInaccessiblePrivateName`, \
                         App.lean:1860-1861) — the slice that models private names"
                    )));
                }
                // `mkConst info.projFn levels` (`:1862`). `projFn` is
                // decoded from `structureExt` and never checked against
                // the environment, so a missing constant is the oracle's
                // "unknown constant" — not `mk_const`'s `expect`.
                if elab.view.get(proj_fn_name).is_none() {
                    return Err(ElabError::Internal(format!(
                        "unknown constant `{proj_name}`, the projection function \
                         `structureExt` names for this field (App.lean:1862)"
                    )));
                }
                let proj_fn = crate::app::head::mk_const(elab, proj_fn_name, &levels, &proj_name)?;
                // `getConstInfoInduct baseStructName` (`:1864`).
                let num_params = match elab.view.get(base) {
                    Some(ConstantInfo::Induct(ind)) => ind.num_params.to_usize(),
                    _ => None,
                };
                let Some(num_params) = num_params else {
                    return Err(ElabError::Internal(format!(
                        "structure `{}` is not an inductive (App.lean:1864)",
                        render(elab, base)
                    )));
                };
                // `:1865-1866`: the structure's own parameters are
                // implicit for `self` (`processExplicitArg`'s
                // `numImplicitParams` branch, `App.lean:767-802`).
                let self_arg = NamedArg {
                    name: "self".to_string(),
                    val: Arg::Expr(e),
                    num_implicit_params: num_params,
                };
                if last {
                    // `addNamedArg namedArgs namedArg` (`:1868`,
                    // `Arg.lean:56-59`): a user-written `(self := …)` is
                    // a duplicate (plan § Review Focus 3).
                    if call.named_args.iter().any(|na| na.name == "self") {
                        return Err(ElabError::DuplicateNamedArg("self".to_string()));
                    }
                    call.named_args.push(self_arg);
                    return crate::app::elab_app_args(elab, proj_fn, call, kinds);
                }
                // Non-final (`:1871-1872`): `self` alone, no expected
                // type, `explicit := false`, `ellipsis := false`.
                let step = AppCall {
                    named_args: vec![self_arg],
                    args: Vec::new(),
                    expected: None,
                    explicit: false,
                    ellipsis: false,
                    stx: call.stx.clone(),
                };
                f = crate::app::elab_app_args(elab, proj_fn, step, kinds)?;
            }
        }
    }
    crate::app::elab_app_args(elab, f, call, kinds)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `resolveLValLoop` retries on `.error` only and rethrows internal
    /// exceptions (`App.lean:1688-1694`). A postponement is internal.
    #[test]
    fn postpone_is_not_retryable() {
        assert!(!is_retryable(&ElabError::Postpone));
        assert!(is_retryable(&ElabError::PlaceholderAsFunction));
    }
}
