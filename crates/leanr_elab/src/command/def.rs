//! The `def`/`abbrev`/`opaque`/`example` pipeline: oracle `finishElab`
//! (`Elab/MutualDef.lean:1343-1442`) → `addPreDefinitions`
//! (`PreDefinition/Main.lean:288-356`; the non-recursive branch at `:307-309`) → `addNonRecAux`
//! (`PreDefinition/Basic.lean:179-210`), restricted to one non-recursive
//! declaration (spec § The oracle model, steps 5-8).
//!
//! Not modelled, none observable in M4c-1: `withFunLocalDecls`'s auxDecl
//! (self-reference is a `view.rs` seam), `shareCommonPreDefs`
//! (hash-consing), `fixLevelParams`' self-`const` rewrite (same reason),
//! `ensureEqnReservedNamesAvailable` (root names only), `cleanupOfNat`
//! (instances only), attributes, compilation, docs and info trees (spec
//! seams).
//!
//! Non-theorem values go through `abstractNestedProofs`; the `_proof_N` aux
//! theorems it mints are committed BEFORE the main declaration.

use std::collections::HashSet;

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_kernel::{
    ConstantVal, Declaration, DefinitionSafety, DefinitionVal, OpaqueVal, ReducibilityHints,
    TheoremVal,
};
use leanr_meta::{
    sort_decl_level_params, AuxLemmas, CollectLevelParams, MetaError, TransparencyMode,
};
use leanr_syntax::kind::KindInterner;

use super::header::{self, Header};
use super::view::{DefKind, DefView};
use super::Built;
use crate::builtin::binder::fun::cleanup_annotations;
use crate::elab::TermElabM;
use crate::error::ElabError;

pub(super) fn elab_def(
    elab: &mut TermElabM,
    view: &DefView,
    kinds: &KindInterner,
) -> Result<Built, ElabError> {
    let id = header::expand_decl_id(elab, view)?;
    let header = header::elab_header(elab, view, &id, kinds)?;
    let header = level_mvar_to_param_headers(elab, view.kind, header)?;
    // `Elab.async` is on, as on the `lean` command line
    // (`Elab/Frontend.lean:291-292`): a theorem whose header has no mvars
    // takes `elabAsync` (`MutualDef.lean:1236-1242`). The test runs after
    // the header conversion, so only expression mvars can block it.
    let base = Some(elab.view.store);
    let d = elab.mctx.store().expr_data(base, header.ty);
    if view.kind == DefKind::Theorem && !d.has_expr_mvar() && !d.has_level_mvar() {
        check_async_signature(elab, &header)?;
    }
    let value = elab_value(elab, view, &header, kinds)?;
    // `finishElab` (`MutualDef.lean:1394-1401`): synthesize once more, then
    // instantiate the values and the headers.
    elab.synthesize_synthetic_mvars_no_postponing(kinds)?;
    let value = elab.mctx.instantiate_mvars(value)?;
    let ty = elab.mctx.instantiate_mvars(header.ty)?;
    // `MutualClosure.pushMain` (`MutualDef.lean:1051-1053`).
    if view.kind == DefKind::Theorem && !is_prop_full(elab, ty)? {
        return Err(ElabError::TheoremTypeNotProp(id.short.clone()));
    }
    // `levelMVarToParamTypesPreDecls` under `withLevelNames allUserLevelNames`
    // (`MutualDef.lean:1434`; `PreDefinition/Basic.lean:56-58`): TYPES only.
    let ty = elab.with_level_names(header.level_names.clone(), |elab| {
        elab.level_mvar_to_param(ty)
    })?;
    // `instantiateMVarsAtPreDecls` (`:1435`).
    let ty = elab.mctx.instantiate_mvars(ty)?;
    let value = elab.mctx.instantiate_mvars(value)?;
    // `fixLevelParams preDefs scopeLevelNames allUserLevelNames` (`:1437-1438`).
    let level_params = fix_level_params(elab, &[ty, value], &header.level_names)?;
    // `addPreDefinitions` → `ensureNoUnassignedMVarsAtPreDef` (`Main.lean:294`).
    ensure_no_unassigned_mvars_at_pre_def(elab, &id.short, ty, value)?;
    // `addNonRecAux` → `letToHaveType`/`letToHaveValue` (`Basic.lean:183-184`):
    // a seam (spec decision 5). Checked before `abstractNestedProofs` (oracle
    // order: after it); both orders end in a seam.
    reject_let(elab, ty)?;
    reject_let(elab, value)?;
    // `addNonRecAux` → `abstractNestedProofs` (`PreDefinition/Basic.lean:
    // 120-127`, `:180`): not for theorems or examples. The aux theorems are
    // committed BEFORE the main declaration, as the oracle's `mkAuxLemma`
    // has already `addDecl`'d them (`Meta/Tactic/AuxLemma.lean:43-73`).
    let mut aux = AuxLemmas::new(id.name);
    let value = if matches!(view.kind, DefKind::Theorem | DefKind::Example) {
        value
    } else {
        elab.mctx
            .abstract_nested_proofs(&mut aux, value)
            .map_err(|e| match e {
                // P1's named seams (Amendment 1 item 4), e.g. the pending-aux lookup.
                MetaError::Unsupported(m) => ElabError::UnsupportedSyntax(m),
                e => ElabError::Meta(e),
            })?
    };
    // `getMaxHeight` sees the abstracted value: aux theorems add nothing.
    let decl = build_decl(elab, view.kind, id.name, level_params, ty, value)?;
    if view.kind == DefKind::Example {
        return Ok(Built::Check(decl));
    }
    let mut decls = aux.into_pending();
    decls.push(decl);
    Ok(Built::Add(decls))
}

/// oracle: `levelMVarToParamHeaders` (`MutualDef.lean:1148-1160`): a
/// theorem's, or a Prop-typed declaration's, header universe mvars become
/// `u_N` params eagerly, and the new names join the header's `levelNames`
/// (so they order as user names in `sortDeclLevelParams`). Then every
/// header type is instantiated.
fn level_mvar_to_param_headers(
    elab: &mut TermElabM,
    kind: DefKind,
    mut header: Header,
) -> Result<Header, ElabError> {
    if kind == DefKind::Theorem || is_prop_full(elab, header.ty)? {
        let ty0 = header.ty;
        let (ty, names) = elab.with_level_names(header.level_names.clone(), |elab| {
            let ty = elab.level_mvar_to_param(ty0)?;
            Ok((ty, elab.level_names.clone()))
        })?;
        header.ty = ty;
        header.level_names = names;
    }
    header.ty = elab.mctx.instantiate_mvars(header.ty)?;
    Ok(header)
}

/// oracle: `elabAsync`'s committed signature (`MutualDef.lean:1278-1298`):
/// the level params come from the header TYPE alone, so a universe used
/// only in the proof is "unused" (probe: `theorem ta.{u} : True :=
/// (fun (_ : Sort u) => True.intro) PUnit.{u}`). The body then runs
/// `finishElab` as for a definition.
fn check_async_signature(elab: &mut TermElabM, header: &Header) -> Result<(), ElabError> {
    let ty0 = header.ty;
    // `withLevelNames allUserLevelNames <| levelMVarToParam type`
    // (`:1281-1282`): a no-op after `level_mvar_to_param_headers`, kept for
    // fidelity.
    let ty = elab.with_level_names(header.level_names.clone(), |elab| {
        elab.level_mvar_to_param(ty0)
    })?;
    let ty = elab.mctx.instantiate_mvars(ty)?;
    // `collectLevelParams` over the type, `sortDeclLevelParams [] allUser used` (`:1288-1291`).
    fix_level_params(elab, &[ty], &header.level_names)?;
    // `Meta.letToHave type` (`:1293-1296`): the letToHave seam.
    reject_let(elab, ty)
}

/// oracle: `Meta.isProp` (`Meta/InferType.lean:323-332`): `inferType`, then
/// `whnfD`, then `isAlwaysZero` of the instantiated sort level. The
/// `isPropQuick` pre-pass (`:302-314`) is skipped: it answers `true`/`false`
/// only where this path gives the same answer. Unlike `MetaCtx::is_prop`
/// (literal `zero` only), this uses the full `isAlwaysZero`, which accepts
/// an unnormalized `imax u 0` or `max 0 0` (e.g. a declared `Sort` level;
/// `infer_type`'s own `∀` sorts are already folded by `mkLevelIMax'`).
fn is_prop_full(elab: &mut TermElabM, e: ExprId) -> Result<bool, ElabError> {
    let ty = elab.mctx.infer_type(e)?;
    let ty = elab
        .mctx
        .with_transparency(TransparencyMode::Default, |m| m.whnf(ty))?;
    let ty = elab.mctx.instantiate_mvars(ty)?;
    let base = Some(elab.view.store);
    let Node::Sort { level } = elab.mctx.store().expr_node(base, ty) else {
        return Ok(false);
    };
    Ok(is_always_zero(elab, level))
}

/// oracle: `isAlwaysZero` (`Meta/InferType.lean:261-267`; the same as
/// `Level.isAlwaysZero`, `Level.lean:212-218`).
fn is_always_zero(elab: &TermElabM, l: LevelId) -> bool {
    match *elab.mctx.store().level_row(Some(elab.view.store), l) {
        LevelRow::Zero => true,
        LevelRow::Max(a, b) => is_always_zero(elab, a) && is_always_zero(elab, b),
        LevelRow::IMax(_, b) => is_always_zero(elab, b),
        LevelRow::Succ(_) | LevelRow::Param(_) | LevelRow::MVar(_) => false,
    }
}

/// oracle: `elabFunValues`' per-header body (`MutualDef.lean:529-556`).
fn elab_value(
    elab: &mut TermElabM,
    view: &DefView,
    header: &Header,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let value_stx = view
        .value
        .clone()
        .ok_or_else(|| ElabError::Internal("a definition without a value".into()))?;
    elab.with_level_names(header.level_names.clone(), |elab| {
        let cp = elab.mctx.lctx_checkpoint();
        let out = (|| {
            // `forallBoundedTelescope header.type header.numParams
            // (cleanupAnnotations := true)` (`:536`): fresh locals whose
            // types drop `optParam`/`autoParam`/`outParam` wrappers.
            let base = Some(elab.view.store);
            let mut xs = Vec::with_capacity(header.num_params);
            let mut cur = header.ty;
            for _ in 0..header.num_params {
                let Node::Forall {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } = elab.mctx.store().expr_node(base, cur)
                else {
                    return Err(ElabError::Internal(
                        "header type has fewer binders than the header".into(),
                    ));
                };
                let dom = cleanup_annotations(elab, binder_type);
                let x = elab.mctx.push_local_decl(binder_name, dom, binder_info)?;
                xs.push(x);
                cur = elab.mctx.instantiate1(body, x)?;
            }
            // `:552-555`.
            let val = elab.elab_term_ensuring_type(&value_stx, kinds, Some(cur))?;
            elab.synthesize_synthetic_mvars_no_postponing(kinds)?;
            let val = elab.mctx.instantiate_mvars(val)?;
            // `:556`.
            Ok(elab.mctx.mk_lambda(&xs, val)?)
        })();
        elab.mctx.lctx_restore(cp);
        out
    })
}

/// oracle: `getLevelParamsPreDecls` (`PreDefinition/Basic.lean:66-73`):
/// collect from each expression, then `sortDeclLevelParams [] allUser used`.
pub(super) fn fix_level_params(
    elab: &mut TermElabM,
    exprs: &[ExprId],
    all_user: &[NameId],
) -> Result<Vec<NameId>, ElabError> {
    let mut s = CollectLevelParams::default();
    for &e in exprs {
        elab.mctx.collect_level_params(&mut s, e)?;
    }
    let base = Some(elab.view.store);
    sort_decl_level_params(elab.mctx.store(), base, &[], all_user, &s.params).map_err(|u| {
        ElabError::UnusedUniverseParam(elab.mctx.store().to_name(base, Some(u)).to_string())
    })
}

/// oracle: `ensureNoUnassignedMVarsAtPreDef` (`PreDefinition/Main.lean:99-108`)
/// and `ensureNoUnassignedLevelMVarsAtPreDef` (`:76-97`, value only).
pub(super) fn ensure_no_unassigned_mvars_at_pre_def(
    elab: &mut TermElabM,
    decl: &str,
    ty: ExprId,
    value: ExprId,
) -> Result<(), ElabError> {
    // `getMVarsAtPreDef`: the type's mvars, then the value's.
    let mut pending = elab.get_mvars(ty)?;
    for m in elab.get_mvars(value)? {
        if !pending.contains(&m) {
            pending.push(m);
        }
    }
    if let Some(e) = elab.log_unassigned_using_error_infos(&pending)? {
        return Err(e);
    }
    let base = Some(elab.view.store);
    if !elab.mctx.store().expr_data(base, value).has_level_mvar() {
        return Ok(());
    }
    let lpending = elab.get_level_mvars(value)?;
    if let Some(e) = elab.log_unassigned_level_mvars_using_error_infos(&lpending)? {
        return Err(e);
    }
    // The fallback when no level error info covers them (`:84-93`).
    Err(ElabError::UnassignedLevelMVars(format!(
        "declaration `{decl}` contains universe level metavariables at the expression"
    )))
}

/// The `letToHave` seam (spec decision 5): any `let`/`have` left in the
/// final type or value.
pub(super) fn reject_let(elab: &TermElabM, e: ExprId) -> Result<(), ElabError> {
    let base = Some(elab.view.store);
    let mut seen: HashSet<ExprId> = HashSet::new();
    let mut stack = vec![e];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match elab.mctx.store().expr_node(base, t) {
            Node::LetE { .. } => {
                return Err(ElabError::UnsupportedSyntax(
                    "`let`/`have` in a declaration's type or value (letToHave) — later M4".into(),
                ))
            }
            Node::App { f, arg } => {
                stack.push(f);
                stack.push(arg);
            }
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => {
                stack.push(binder_type);
                stack.push(body);
            }
            Node::MData { expr, .. } => stack.push(expr),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => stack.push(structure),
            _ => {}
        }
    }
    Ok(())
}

/// `addNonRecAux`'s declaration (`PreDefinition/Basic.lean:185-208`).
fn build_decl(
    elab: &mut TermElabM,
    kind: DefKind,
    name: NameId,
    level_params: Vec<NameId>,
    ty: ExprId,
    value: ExprId,
) -> Result<Declaration, ElabError> {
    let val = ConstantVal {
        name,
        level_params,
        ty,
    };
    Ok(match kind {
        // `mkDefDecl` (`:185-190`): `regular (getMaxHeight env value + 1)`, safe.
        DefKind::Def | DefKind::Example => {
            let h = elab.mctx.get_max_height(value)?;
            Declaration::Defn(DefinitionVal {
                val,
                value,
                hints: ReducibilityHints::Regular(h + 1),
                safety: DefinitionSafety::Safe,
                all: vec![name],
            })
        }
        DefKind::Abbrev => Declaration::Defn(DefinitionVal {
            val,
            value,
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![name],
        }),
        DefKind::Opaque => Declaration::Opaque(OpaqueVal {
            val,
            value,
            is_unsafe: false,
            all: vec![name],
        }),
        // `mkThmDecl` (`PreDefinition/Basic.lean:192-197`).
        DefKind::Theorem => Declaration::Thm(TheoremVal {
            val,
            value,
            all: vec![name],
        }),
        DefKind::Axiom => return Err(ElabError::Internal("build_decl: axiom".into())),
    })
}

#[cfg(test)]
mod tests {
    use leanr_kernel::bank::Store;
    use leanr_kernel::{BinderInfo, Environment};
    use leanr_meta::{Config, EnvExtensions, MetaCtx};

    use crate::elab::TermElabM;

    /// `is_prop_full` uses the full `isAlwaysZero`
    /// (`Meta/InferType.lean:261-267`), not `MetaCtx::is_prop`'s literal
    /// `zero` test. `oracle_decl_gate` cannot see the difference: both
    /// `infer_type`s fold `imax u 0` to `0` (`mkLevelIMax'`), so this pins
    /// it on an unnormalized declared type (Task 7 mutation 5). The oracle
    /// agrees: `isPropQuick` on an fvar runs `isArrowProp` → `isAlwaysZero`
    /// on the declared `Sort` (`:312`, `:276`).
    #[test]
    fn is_prop_full_uses_the_full_is_always_zero() {
        let env = Environment::default();
        let view = env.view();
        let mut scratch = Store::scratch();
        let mctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            EnvExtensions::default(),
        );
        let mut elab = TermElabM::new(mctx, view);
        let u = super::super::header::intern_atomic(&mut elab, "u").unwrap();
        let st = elab.mctx.store_mut();
        let z = st.level_zero(None).unwrap();
        let p = st.level_param(None, Some(u)).unwrap();
        let imax_u_0 = st.level_imax(None, p, z).unwrap();
        let max_0_imax = st.level_max(None, z, imax_u_0).unwrap();
        let imax_0_u = st.level_imax(None, z, p).unwrap();
        let local = |elab: &mut TermElabM, l| {
            let s = elab.mctx.store_mut().expr_sort(None, l).unwrap();
            elab.mctx
                .push_local_decl(None, s, BinderInfo::Default)
                .unwrap()
        };
        let a = local(&mut elab, imax_u_0);
        let b = local(&mut elab, max_0_imax);
        let c = local(&mut elab, imax_0_u);
        assert!(super::is_prop_full(&mut elab, a).unwrap(), "imax u 0");
        assert!(
            super::is_prop_full(&mut elab, b).unwrap(),
            "max 0 (imax u 0)"
        );
        assert!(!super::is_prop_full(&mut elab, c).unwrap(), "imax 0 u");
    }
}
