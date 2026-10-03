//! Declaration headers: oracle `expandDeclId` (`Elab/DeclModifiers.lean:
//! 326-343`) and `elabHeaders`' per-view body (`Elab/MutualDef.lean:257-291`).

use leanr_kernel::bank::{ExprId, NameId};
use leanr_meta::{MVarKind, MetaError};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::NodeOrToken;

use super::view::{DefKind, DefView};
use crate::builtin::binder::{elab_type, extract_binder_group, push_binder_group};
use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;

pub(super) struct DeclId {
    pub name: NameId,
    pub short: String,
    /// oracle order: head = last declared (`.{u, v}` → `[v, u]`).
    pub level_names: Vec<NameId>,
}

pub(super) struct Header {
    /// `∀ binders, type`, instantiated.
    pub ty: ExprId,
    /// `levelNames` after the header (`DefViewElabHeaderData.levelNames`).
    pub level_names: Vec<NameId>,
    pub num_params: usize,
}

pub(super) fn intern_atomic(elab: &mut TermElabM, s: &str) -> Result<NameId, ElabError> {
    let base = elab.view.store;
    let st = elab.mctx.store_mut();
    let sid = st.intern_str(Some(base), s).map_err(MetaError::from)?;
    Ok(st
        .name_str(Some(base), None, sid)
        .map_err(MetaError::from)?)
}

/// oracle: `expandDeclId` (`DeclModifiers.lean:326-343`). The `.{…}` fold
/// conses onto the scope's level names (`[]` in M4c-1) and rejects a
/// repeat. Then `mkDeclName` (`:263-286`) → `applyVisibility` (`:244-251`)
/// → `checkNotAlreadyDeclared` (`:29-55`). The reserved-name and private
/// checks cannot fire for the atomic, unmodified names `view.rs` admits.
pub(super) fn expand_decl_id(elab: &mut TermElabM, view: &DefView) -> Result<DeclId, ElabError> {
    let mut level_names: Vec<NameId> = Vec::new();
    for u in &view.univ_names {
        let id = intern_atomic(elab, u)?;
        if level_names.contains(&id) {
            return Err(ElabError::UniverseAlreadyDeclared(u.clone()));
        }
        level_names.insert(0, id);
    }
    // `example`'s name is `_example` (`DefView.lean:204`).
    let short = view.name.clone().unwrap_or_else(|| "_example".to_string());
    let name = intern_atomic(elab, &short)?;
    if elab.view.get(name).is_some() {
        return Err(ElabError::AlreadyDeclared(short));
    }
    Ok(DeclId {
        name,
        short,
        level_names,
    })
}

/// oracle: `elabHeaders` runs under `withAutoBoundImplicit`
/// (`MutualDef.lean:257`; `elabAxiom` too, `Declaration.lean:109`): an
/// unbound identifier or universe in a header is auto-bound, not an error.
/// Auto-bound implicits are M4c-2.
pub(super) fn unknown_ident_to_auto_bound_seam(e: ElabError) -> ElabError {
    match e {
        ElabError::UnknownIdent(s) => ElabError::UnsupportedSyntax(format!(
            "unbound `{s}` in a declaration header (auto-bound implicit) — M4c-2"
        )),
        e => e,
    }
}

/// oracle: `elabHeaders`' per-view body (`MutualDef.lean:257-291`), under
/// `withLevelNames levelNames`.
pub(super) fn elab_header(
    elab: &mut TermElabM,
    view: &DefView,
    id: &DeclId,
    kinds: &KindInterner,
) -> Result<Header, ElabError> {
    elab.with_level_names(id.level_names.clone(), |elab| {
        let cp = elab.mctx.lctx_checkpoint();
        let out = header_in_scope(elab, view, kinds);
        elab.mctx.lctx_restore(cp);
        out
    })
    .map_err(unknown_ident_to_auto_bound_seam)
}

fn header_in_scope(
    elab: &mut TermElabM,
    view: &DefView,
    kinds: &KindInterner,
) -> Result<Header, ElabError> {
    // `elabBindersEx` (`:258`): per-name, via `elabBinderViews`.
    let mut xs = Vec::new();
    for b in &view.binders {
        let g = extract_binder_group(elab, b, kinds)?;
        xs.extend(push_binder_group(elab, &g, kinds)?);
    }
    let ty = match &view.ty {
        Some(t) => {
            let ty = elab_type(elab, t, kinds)?;
            register_failed_to_infer_def_type_info(elab, view, ty, t.clone());
            ty
        }
        None => {
            // oracle: `elabType (mkHole refForElabFunType)` (`MutualDef.lean:
            // 266-270`): `elabHole` against `Sort ?u` mints a natural mvar
            // and registers its hole info (`BuiltinTerm.lean:63-67`); the
            // ref is the value syntax.
            let r = view.value.clone().ok_or_else(|| {
                ElabError::Internal("a header without a type needs a value".into())
            })?;
            let u = elab.mk_fresh_level_mvar()?;
            let sort = elab
                .mctx
                .store_mut()
                .expr_sort(None, u)
                .map_err(MetaError::from)?;
            let (ty, mid) = elab.mk_fresh_expr_mvar_of_kind(sort, MVarKind::Natural)?;
            elab.register_mvar_error_hole_info(mid, r.clone());
            register_failed_to_infer_def_type_info(elab, view, ty, r);
            ty
        }
    };
    elab.synthesize_synthetic_mvars_no_postponing(kinds)?;
    // `mkForallFVars' xs type` (`:277`) only sets mvar user names for
    // messages.
    let ty = elab.mctx.mk_forall(&xs, ty)?;
    let ty = elab.mctx.instantiate_mvars(ty)?;
    // `:280-283`. The oracle logs and continues; the first error line is
    // what M4c-1 reports.
    if view.ty.is_some() {
        let pending = elab.get_mvars(ty)?;
        if let Some(e) = elab.log_unassigned_using_error_infos(&pending)? {
            return Err(e);
        }
    }
    Ok(Header {
        ty,
        level_names: elab.level_names.clone(),
        num_params: xs.len(),
    })
}

/// oracle: `registerFailedToInferDefTypeInfo` (`MutualDef.lean:123-137`).
fn register_failed_to_infer_def_type_info(
    elab: &mut TermElabM,
    view: &DefView,
    ty: ExprId,
    stx: SynElem,
) {
    let what = match view.kind {
        DefKind::Example => "example".to_string(),
        DefKind::Theorem => format!("theorem `{}`", decl_id_text(view)),
        _ => format!("definition `{}`", decl_id_text(view)),
    };
    elab.register_custom_error_if_mvar(ty, stx, format!("Failed to infer type of {what}"));
}

/// `{view.declId}` in a message: the oracle pretty-prints the `declId`
/// syntax. For the atomic names M4c-1 admits, the source text agrees with
/// that (at most whitespace inside `.{…}` could differ).
fn decl_id_text(view: &DefView) -> String {
    match &view.decl_id {
        Some(NodeOrToken::Node(n)) => n.text().to_string().trim().to_string(),
        Some(NodeOrToken::Token(t)) => t.text().to_string(),
        None => String::new(),
    }
}
