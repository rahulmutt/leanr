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

use std::collections::HashSet;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::{
    ConstantVal, Declaration, DefinitionSafety, DefinitionVal, OpaqueVal, ReducibilityHints,
};
use leanr_meta::{sort_decl_level_params, CollectLevelParams};
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
    let value = elab_value(elab, view, &header, kinds)?;
    // `finishElab` (`MutualDef.lean:1394-1401`): synthesize once more, then
    // instantiate the values and the headers.
    elab.synthesize_synthetic_mvars_no_postponing(kinds)?;
    let value = elab.mctx.instantiate_mvars(value)?;
    let ty = elab.mctx.instantiate_mvars(header.ty)?;
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
    let decl = build_decl(elab, view.kind, id.name, level_params, ty, value)?;
    Ok(if view.kind == DefKind::Example {
        Built::Check(decl)
    } else {
        Built::Add(vec![decl])
    })
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
        DefKind::Theorem | DefKind::Axiom => {
            return Err(ElabError::Internal(format!("build_decl: {kind:?}")))
        }
    })
}
