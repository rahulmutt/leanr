//! `axiom`: oracle `elabAxiom` (`Elab/Declaration.lean:101-133`, the
//! `addDecl` at `:133`). No `letToHave`, no abstraction, and no
//! `registerFailedToInferDefTypeInfo`, so `axiom ahole : _` reports the plain
//! hole error.

use leanr_kernel::bank::ExprId;
use leanr_kernel::{AxiomVal, ConstantVal, Declaration};
use leanr_syntax::kind::KindInterner;

use super::def::fix_level_params;
use super::header::{expand_decl_id, unknown_ident_to_auto_bound_seam};
use super::view::DefView;
use super::Built;
use crate::builtin::binder::{elab_type, extract_binder_group, push_binder_group};
use crate::elab::TermElabM;
use crate::error::ElabError;

pub(super) fn elab_axiom(
    elab: &mut TermElabM,
    view: &DefView,
    kinds: &KindInterner,
) -> Result<Built, ElabError> {
    let id = expand_decl_id(elab, view)?;
    let ty_stx = view
        .ty
        .clone()
        .ok_or_else(|| ElabError::Internal("axiom without a type".into()))?;
    let ty: ExprId = elab
        .with_level_names(id.level_names.clone(), |elab| {
            let cp = elab.mctx.lctx_checkpoint();
            let out = (|| {
                let mut xs = Vec::new();
                for b in &view.binders {
                    let g = extract_binder_group(elab, b, kinds)?;
                    xs.extend(push_binder_group(elab, &g, kinds)?);
                }
                let ty = elab_type(elab, &ty_stx, kinds)?;
                elab.synthesize_synthetic_mvars_no_postponing(kinds)?;
                let ty = elab.mctx.instantiate_mvars(ty)?;
                let ty = elab.mctx.mk_forall(&xs, ty)?;
                // `Term.levelMVarToParam type` (`Declaration.lean:119`); the
                // new names extend only this scope's level names.
                elab.level_mvar_to_param(ty)
            })();
            elab.mctx.lctx_restore(cp);
            out
        })
        .map_err(unknown_ident_to_auto_bound_seam)?;
    // `sortDeclLevelParams scopeLevelNames allUserLevelNames usedParams`
    // (`:120-122`) against the ORIGINAL user names: leftovers sort
    // lexicographically.
    let level_params = fix_level_params(elab, &[ty], &id.level_names)?;
    let ty = elab.mctx.instantiate_mvars(ty)?;
    // `Term.ensureNoUnassignedMVars decl` (`:132`; `TermElabM.lean:1041-1044`).
    let pending = elab.get_mvars(ty)?;
    if let Some(e) = elab.log_unassigned_using_error_infos(&pending)? {
        return Err(e);
    }
    Ok(Built::Add(vec![Declaration::Axiom(AxiomVal {
        val: ConstantVal {
            name: id.name,
            level_params,
            ty,
        },
        is_unsafe: false,
    })]))
}
