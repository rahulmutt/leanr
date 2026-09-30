//! M4b-4a: the LVal machinery — dot notation's field and index
//! projections. Oracle: `Lean/Elab/App.lean:1435-1897` (pinned
//! v4.33.0-rc1). Design: docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md.
//!
//! P4 added `LVal::FieldName::suffix` and the two `c ++ suffix`
//! unknown-constant arms of `resolve_lval_aux`.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_kernel::{BinderInfo, ConstantInfo, Nat};
use leanr_meta::{MVarId, MVarKind, MetaError, TransparencyMode};
use leanr_syntax::kind::KindInterner;

use crate::app::expand::{Arg, NamedArg};
use crate::app::AppCall;
use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::{ElabError, InvalidFieldReason, InvalidProjectionReason};

/// oracle: `inductive LVal` (`TermElabM.lean:662-666`).
#[derive(Debug, Clone)]
pub enum LVal {
    FieldName {
        r#ref: SynElem,
        name: String,
        levels: Vec<LevelId>,
        /// oracle: `suffix?` — `some` only on the FIRST field split off an
        /// identifier (`elabAppFnResolutions`, `App.lean:1936`), holding
        /// ALL the split-off fields rejoined (`toName fields`, `:1946-1950`).
        /// Read only by the `c ++ suffix` unknown-constant arms of
        /// `resolve_lval_aux`. `fullRef` (the error position) is not ported.
        suffix: Option<String>,
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

/// oracle: `LValResolution` (`App.lean:1435-1447`). `projFn`/`projIdx`
/// since P1, `const` since P3; `localRec` is the only unported arm: it
/// needs `auxDeclToFullName`, which has no leanr producer (the `let rec`
/// slice).
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
    /// `App.lean:1441-1444`.
    Const {
        base: NameId,
        struct_name: NameId,
        const_name: NameId,
        levels: Vec<LevelId>,
    },
}

pub(super) fn node(elab: &TermElabM, e: ExprId) -> Node {
    elab.mctx.store().expr_node(Some(elab.view.store), e)
}

/// oracle: `Expr.getAppFn`.
pub(super) fn app_fn(elab: &TermElabM, mut e: ExprId) -> ExprId {
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

pub(super) fn render(elab: &TermElabM, n: NameId) -> String {
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

/// oracle: `findMethod?` (`App.lean:1453-1477`): try `S.f`, then each
/// namespace after `S` in `S`'s resolution order (a non-structure's is
/// `[S]`). `resolveGlobalName` with `currNamespace := .anonymous` is
/// exact-name lookup in leanr (spec § Seams after P4: `open`/aliases are
/// the `open`/alias slice's), so a candidate list is empty or a
/// singleton and the ambiguity throw (`:1466-1468`) cannot arise; see
/// plan § Spec deviations 1.
fn find_method(
    elab: &mut TermElabM,
    struct_name: NameId,
    field: &str,
) -> Result<Option<(NameId, NameId)>, ElabError> {
    if let Some(r) = find_method_in(elab, struct_name, field)? {
        return Ok(Some(r));
    }
    // `:1473`.
    let order = if elab.mctx.is_structure(struct_name) {
        elab.mctx
            .get_structure_resolution_order(struct_name)
            .ok_or_else(|| {
                ElabError::Internal(format!(
                    "structure `{}` has cyclic parents in `structureExt` \
                     (getStructureResolutionOrder, Structure.lean:512)",
                    render(elab, struct_name)
                ))
            })?
    } else {
        vec![struct_name]
    };
    // `resolutionOrder[1...resolutionOrder.size]` (`:1474`).
    for &ns in order.iter().skip(1) {
        if let Some(r) = find_method_in(elab, ns, field)? {
            return Ok(Some(r));
        }
    }
    Ok(None)
}

/// `findMethod?`'s local `find?` (`App.lean:1455-1468`).
fn find_method_in(
    elab: &mut TermElabM,
    s: NameId,
    field: &str,
) -> Result<Option<(NameId, NameId)>, ElabError> {
    let s_str = render(elab, s);
    // `privateToUserName structName'` (`:1456`): leanr models no private
    // names (plan § Spec deviations 4).
    if s_str.starts_with("_private.") {
        return Err(ElabError::UnsupportedSyntax(format!(
            "`.{field}` on the private structure `{s_str}` (`privateToUserName`, \
             App.lean:1456) — the slice that models private names"
        )));
    }
    // `structName' ++ fieldName`: one string component under `s`'s own
    // `NameId`, no render/parse round trip. `base = Some(view store)` so
    // a declared name dedups to its persistent id (as in
    // `head::intern_components`).
    let base = elab.view.store;
    let store = elab.mctx.store_mut();
    let f = store
        .intern_str(Some(base), field)
        .map_err(MetaError::from)?;
    let full = store
        .name_str(Some(base), Some(s), f)
        .map_err(MetaError::from)?;
    Ok(elab.view.get(full).is_some().then_some((s, full)))
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
            // `:1568-1569`.
            if let Some((base, const_name)) = find_method(elab, s, name)? {
                return Ok(LValResolution::Const {
                    base,
                    struct_name: s,
                    const_name,
                    levels: levels.clone(),
                });
            }
            // `throwInvalidFieldAt ref fieldName fullName` (`:1578`); the
            // exporting-scope `declHint` retry (`:1570-1577`) is prose.
            let full_name = format!("{}.{name}", render(elab, s));
            Err(field_err(name, InvalidFieldReason::NotFound { full_name }))
        }
        // `:1580-1588`.
        (
            Node::Forall { .. },
            LVal::FieldName {
                name,
                levels,
                suffix,
                ..
            },
        ) => {
            let full = format!("Function.{name}");
            let full_id = crate::app::head::intern_components(elab, &["Function", name])?;
            if elab.view.get(full_id).is_some() {
                // `LValResolution.const `Function `Function fullName
                // levels` (`:1583`).
                let function = crate::app::head::intern_components(elab, &["Function"])?;
                return Ok(LValResolution::Const {
                    base: function,
                    struct_name: function,
                    const_name: full_id,
                    levels: levels.clone(),
                });
            }
            // `:1584-1586`: a field split off an identifier whose base is a
            // constant names the constant `c ++ suffix`.
            if let (Node::Const { name: Some(c), .. }, Some(suffix)) =
                (node(elab, app_fn(elab, e)), suffix)
            {
                return Err(ElabError::UnknownIdent(format!(
                    "{}.{suffix}",
                    render(elab, c)
                )));
            }
            // `:1588`.
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
        // `:1605-1615`: `c ++ suffix` (`:1607-1608`) first, as above.
        (_, LVal::FieldName { name, suffix, .. }) => {
            if let (Node::Const { name: Some(c), .. }, Some(suffix)) =
                (node(elab, app_fn(elab, e)), suffix)
            {
                return Err(ElabError::UnknownIdent(format!(
                    "{}.{suffix}",
                    render(elab, c)
                )));
            }
            Err(field_err(name, InvalidFieldReason::NotConstApp))
        }
        (_, LVal::FieldIdx { .. }) => Err(proj_err(InvalidProjectionReason::NotConstApp)),
    }
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
        // oracle: the `catch` retries `.error` only and rethrows `.internal`
        // (`App.lean:1688-1694`); see `ElabError::is_oracle_error`.
        Err(err) if err.is_oracle_error() => match elab.mctx.unfold_definition_pub(e_type)? {
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

/// oracle: `typeMatchesBaseName` (`App.lean:1712-1725`), under
/// `withReducibleAndInstances` (`TransparencyMode::Instances`). The
/// oracle's recursion on `type'` (`:1724`) is the loop: each round
/// re-runs the whole body, `cleanupAnnotations` (`:1716`) included.
fn type_matches_base_name(
    elab: &mut TermElabM,
    ty: ExprId,
    base_name: NameId,
) -> Result<bool, ElabError> {
    let store = elab.view.store;
    // `Expr.isAppOf baseName` (`Expr.lean:1138-1141`).
    let is_app_of = |m: &leanr_meta::MetaCtx, e: ExprId| {
        let mut e = e;
        while let Node::App { f, .. } = m.store().expr_node(Some(store), e) {
            e = f;
        }
        matches!(
            m.store().expr_node(Some(store), e),
            Node::Const { name: Some(n), .. } if n == base_name
        )
    };
    // `:1714-1715`.
    if render(elab, base_name) == "Function" {
        let w = elab
            .mctx
            .with_transparency(TransparencyMode::Instances, |m| m.whnf(ty))?;
        return Ok(matches!(node(elab, w), Node::Forall { .. }));
    }
    let mut cur = ty;
    loop {
        // `:1716`.
        let cleaned = crate::builtin::binder::fun::cleanup_annotations(elab, cur);
        if is_app_of(&elab.mctx, cleaned) {
            return Ok(true);
        }
        // `:1719-1725`: `Err(true)` = matched after `whnfCore`,
        // `Ok(None)` = no unfolding (false), `Ok(Some(t'))` = recurse.
        let step = elab.mctx.with_transparency(
            TransparencyMode::Instances,
            |m| -> Result<Result<Option<ExprId>, bool>, MetaError> {
                let t = m.whnf_core(cur)?;
                if is_app_of(m, t) {
                    return Ok(Err(true));
                }
                Ok(Ok(m.unfold_definition_pub(t)?))
            },
        )?;
        match step {
            Err(matched) => return Ok(matched),
            Ok(None) => return Ok(false),
            Ok(Some(t)) => cur = t,
        }
    }
}

/// Where `add_lval_arg_go` decided `e` goes. The oracle returns the
/// updated arrays from inside `go`; deciding inside the rollback scope
/// and editing outside it is the same (`e` and the args predate the
/// checkpoint).
enum LValInsert {
    Positional(usize),
    Named(String),
}

/// `addLValArg`'s fixed parameters, threaded through `go`.
struct AddLValArg<'a> {
    base_name: NameId,
    explicit: bool,
    args: &'a [Arg],
}

/// oracle: `addLValArg` (`App.lean:1735-1737`): find the first
/// parameter whose type is `base_name …` and insert `e` there —
/// positionally when the parameter is explicit (or `explicit`) and
/// `args` is long enough, else as `(x := e)` unless a parameter of the
/// same name came earlier. Runs under `withoutModifyingState` (`:1737`):
/// the telescope's mvars and any assignment made while matching are
/// rolled back (`MetaCtx::checkpoint`/`rollback`; declarations stay, as
/// the snapshot's doc says, and nothing refers to them).
fn add_lval_arg(
    elab: &mut TermElabM,
    base_name: NameId,
    e: ExprId,
    args: Vec<Arg>,
    named_args: Vec<NamedArg>,
    f: ExprId,
    explicit: bool,
) -> Result<(Vec<Arg>, Vec<NamedArg>), ElabError> {
    let snap = elab.mctx.checkpoint();
    let r = elab
        .mctx
        .infer_type(f)
        .map_err(ElabError::from)
        .and_then(|f_type| {
            // `go none f (← inferType f) 0 namedArgs (namedArgs.map
            // (·.name)) true` (`:1737`).
            let names: Vec<String> = named_args.iter().map(|na| na.name.clone()).collect();
            let st = AddLValArg {
                base_name,
                explicit,
                args: &args,
            };
            add_lval_arg_go(elab, &st, None, f, f_type, 0, names.clone(), names, true, 0)
        });
    elab.mctx.rollback(snap);
    let mut args = args;
    let mut named_args = named_args;
    match r? {
        // `args.insertIdx argIdx (Arg.expr e)` (`:1767`).
        LValInsert::Positional(idx) => args.insert(idx, Arg::Expr(e)),
        // `namedArgs.push { name := xDecl.userName, val := Arg.expr e }`
        // (`:1774`): `numImplicitParams` keeps its default, 0.
        LValInsert::Named(name) => named_args.push(NamedArg {
            name,
            val: Arg::Expr(e),
            num_implicit_params: 0,
        }),
    }
    Ok((args, named_args))
}

/// oracle: `addLValArg.go` (`App.lean:1749-1794`), the telescope walk.
/// `remaining` / `unusable` are the oracle's `remainingNamedArgs` (by
/// name: only names are read) and `unusableNamedArgs`. The oracle
/// compares `Name`s, leanr rendered strings: an anonymous binder renders
/// as `""`, which no user-written named argument can equal, as no user
/// can write `.anonymous`.
///
/// Both of the oracle's recursive calls (`:1783`, `:1785`) are tail
/// calls, so each is one more round of the outer loop here, with
/// `depth` counting the rounds `withIncRecDepth` (`:1749`) would. A
/// Rust recursion would spend ~2.8 KiB of stack per round in a debug
/// build, and a self-reproducing `CoeFun` (the `Loop` fixture)
/// overflows a 2 MiB test thread at round ~385, before the cap.
#[allow(clippy::too_many_arguments)]
fn add_lval_arg_go(
    elab: &mut TermElabM,
    st: &AddLValArg<'_>,
    mut f_pre_coercion: Option<ExprId>,
    mut f: ExprId,
    mut f_type: ExprId,
    mut arg_idx: usize,
    mut remaining: Vec<String>,
    mut unusable: Vec<String>,
    mut allow_named: bool,
    mut depth: usize,
) -> Result<LValInsert, ElabError> {
    // `withIncRecDepth` (`:1749`) against `defaultMaxRecDepth`
    // (`Init/Prelude.lean:4836`); see `ElabError::MaxRecDepth`.
    const MAX_REC_DEPTH: usize = 512;
    loop {
        // `:1751`.
        let (xs, bis, f_type2) = elab.mctx.forall_meta_telescope(f_type)?;
        for (&x, &bi) in xs.iter().zip(bis.iter()) {
            // `x.mvarId!.getDecl` (`:1756`).
            let Node::MVar { id: Some(xid) } = node(elab, x) else {
                return Err(ElabError::Internal(
                    "forall_meta_telescope minted a non-mvar".into(),
                ));
            };
            let Some((user_name, x_ty)) = elab
                .mctx
                .mctx()
                .decl(MVarId(xid))
                .map(|d| (d.user_name, d.ty))
            else {
                return Err(ElabError::Internal(
                    "forall_meta_telescope mvar is undeclared".into(),
                ));
            };
            let user_name = user_name.map(|n| render(elab, n)).unwrap_or_default();
            // `explicit || bInfo.isExplicit` (`:1765`, `:1776`);
            // `BinderInfo.isExplicit` is `.default` only (`Expr.lean:92-96`).
            let is_explicit = st.explicit || bi == BinderInfo::Default;
            // `:1757-1759`: a user-written named argument accounts for this
            // parameter — no type test, no `argIdx` advance, no push.
            if let Some(i) = remaining.iter().position(|n| *n == user_name) {
                remaining.remove(i);
                continue;
            }
            // `:1761`.
            if type_matches_base_name(elab, x_ty, st.base_name)? {
                // `:1765-1767`.
                if arg_idx <= st.args.len() && is_explicit {
                    return Ok(LValInsert::Positional(arg_idx));
                }
                // `:1771-1774`.
                if !allow_named || unusable.contains(&user_name) {
                    return Err(ElabError::UnusableLValParameter {
                        f: f_pre_coercion.unwrap_or(f),
                        param: user_name,
                        allow_named,
                    });
                }
                return Ok(LValInsert::Named(user_name));
            }
            // `:1776-1778`.
            if is_explicit {
                arg_idx += 1;
            }
            unusable.push(user_name);
        }
        // `if allowNamed || argIdx ≤ args.size then` (`:1781`): without
        // named insertion the value must still fit positionally.
        if allow_named || arg_idx <= st.args.len() {
            let f_app = xs.iter().try_fold(f, |acc, &x| mk_app(elab, acc, x))?;
            // Ambient transparency, as `:1782` (no `withReducible…` here).
            let w = elab.mctx.whnf(f_type2)?;
            if matches!(node(elab, w), Node::Forall { .. }) {
                if depth + 1 >= MAX_REC_DEPTH {
                    return Err(ElabError::MaxRecDepth);
                }
                // `:1782-1783`: `go fPreCoercion? (mkAppN f xs) fType' …
                // allowNamed`.
                f = f_app;
                f_type = w;
                depth += 1;
                continue;
            }
            if let Some(f2) = elab.mctx.coerce_to_function(f_app)? {
                if depth + 1 >= MAX_REC_DEPTH {
                    return Err(ElabError::MaxRecDepth);
                }
                // `:1784-1785`: `go (fPreCoercion?.getD f) f' (← inferType
                // f') … false` — named insertion off from here on.
                f_pre_coercion = Some(f_pre_coercion.unwrap_or(f));
                f_type = elab.mctx.infer_type(f2)?;
                f = f2;
                allow_named = false;
                depth += 1;
                continue;
            }
        }
        // `:1792-1794`.
        return Err(ElabError::NoLValParameter {
            f: f_pre_coercion.unwrap_or(f),
            base: render(elab, st.base_name),
        });
    }
}

/// oracle: `elabAppLVals` / `elabAppLValsAux` (`App.lean:1843-1897`).
/// Matches the oracle's control flow: `projIdx` and a non-final
/// `projFn` / `const` do `loop f lvals`; a FINAL `projFn` ends in
/// `elabAppArgs projFn (namedArgs + self) args …` (`:1867-1869`) and a
/// final `const` in `elabAppArgs constFn` over `addLValArg`'s arrays
/// (`:1877-1879`), consuming the outer call; the empty list ends in
/// `elabAppArgs f namedArgs args …`.
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
            // `App.lean:1873-1883`.
            LValResolution::Const {
                base,
                struct_name,
                const_name,
                levels,
            } => {
                let e = if base != struct_name {
                    mk_base_projections(elab, base, struct_name, e)?
                } else {
                    e
                };
                let display = render(elab, const_name);
                // `mkConst constName levels` (`:1875`). `find_method` and
                // the `Function` arm only return declared constants.
                let const_fn = crate::app::head::mk_const(elab, const_name, &levels, &display)?;
                if last {
                    // `:1878-1879`.
                    let args = std::mem::take(&mut call.args);
                    let named = std::mem::take(&mut call.named_args);
                    let (args, named) =
                        add_lval_arg(elab, base, e, args, named, const_fn, call.explicit)?;
                    call.args = args;
                    call.named_args = named;
                    return crate::app::elab_app_args(elab, const_fn, call, kinds);
                }
                // Non-final (`:1881-1883`): no outer arguments, `explicit
                // := false`, no expected type.
                let (args, named_args) =
                    add_lval_arg(elab, base, e, Vec::new(), Vec::new(), const_fn, false)?;
                let step = AppCall {
                    named_args,
                    args,
                    expected: None,
                    explicit: false,
                    ellipsis: false,
                    stx: call.stx.clone(),
                };
                f = crate::app::elab_app_args(elab, const_fn, step, kinds)?;
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
        assert!(!ElabError::Postpone.is_oracle_error());
        assert!(ElabError::PlaceholderAsFunction.is_oracle_error());
    }

    /// `MaxRecDepth` is a runtime exception (`Exception.isRuntime`,
    /// `CoreM.lean:783-784`): `Core.tryCatch` (`:792-799`) rethrows it
    /// past `resolveLValLoop`'s retry and `postponeOnError`.
    #[test]
    fn max_rec_depth_is_not_catchable() {
        assert!(!ElabError::MaxRecDepth.is_oracle_error());
    }
}
