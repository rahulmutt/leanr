//! Declaration headers: oracle `expandDeclId` (`Elab/DeclModifiers.lean:
//! 326-343`) and `elabHeaders`' per-view body (`Elab/MutualDef.lean:257-291`).

use leanr_kernel::bank::{ExprId, NameId};
use leanr_meta::{MVarKind, MetaError};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::NodeOrToken;

use super::view::{DefKind, DefView};
use crate::app::head::intern_components;
use crate::builtin::binder::{elab_type, extract_binder_group, push_binder_group};
use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::names;

pub(super) struct DeclId {
    /// The full declaration name (`mkDeclName`'s `declName`).
    pub name: NameId,
    /// `mkDeclName`'s `shortName`: the name the declaration's aux local
    /// carries (`withAuxDecl shortDeclName`, `MutualDef.lean:359-366`).
    pub short_name: NameId,
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
/// conses onto the scope's level names and rejects a
/// repeat. Then `mkDeclName` (`:263-286`) over `elab.resolve.ns`.
pub(super) fn expand_decl_id(elab: &mut TermElabM, view: &DefView) -> Result<DeclId, ElabError> {
    let mut level_names: Vec<NameId> = elab.level_names.clone();
    for u in &view.univ_names {
        let id = intern_atomic(elab, u)?;
        if level_names.contains(&id) {
            return Err(ElabError::UniverseAlreadyDeclared(u.clone()));
        }
        level_names.insert(0, id);
    }
    // `example`'s name is `_example` (`DefView.lean:204`).
    let comps = view
        .name
        .clone()
        .unwrap_or_else(|| vec!["_example".to_string()]);
    let (name, short_name) = mk_decl_name(elab, view, &comps)?;
    Ok(DeclId {
        name,
        short_name,
        level_names,
    })
}

/// oracle: `mkDeclName` (`DeclModifiers.lean:263-286`), after
/// `expandNamespacedDeclaration` has made `comps` atomic or
/// `_root_`-prefixed. Returns `(declName, shortName)`. `applyVisibility`'s
/// `addProtected` is `CommandElab`'s, once the declaration is admitted.
fn mk_decl_name(
    elab: &mut TermElabM,
    view: &DefView,
    comps: &[String],
) -> Result<(NameId, NameId), ElabError> {
    let base = Some(elab.view.store);
    // `:269-270`.
    if comps == ["_root_"] {
        return Err(ElabError::InvalidRootDeclName);
    }
    let parts: Vec<&str> = comps.iter().map(String::as_str).collect();
    // `:271-275`: a `_root_` prefix is dropped from the declaration name;
    // the short name is the last component and the namespace the rest.
    let (decl, short, ns) = if parts[0] == "_root_" {
        let decl = intern_components(elab, &parts[1..])?;
        let short = intern_atomic(elab, parts[parts.len() - 1])?;
        let ns = names::parent(elab.mctx.store(), base, decl);
        (decl, short, ns)
    } else {
        let short = intern_components(elab, &parts)?;
        let ns = elab.resolve.ns;
        let decl = names::append(elab.mctx.store_mut(), base, ns, Some(short))
            .map_err(MetaError::from)?
            .ok_or_else(|| ElabError::Internal("empty declaration name".into()))?;
        (decl, short, ns)
    };
    check_if_shadowing_structure_field(elab, decl)?;
    // `applyVisibility` (`:244-251`) → `checkNotAlreadyDeclared`
    // (`:29-55`): no `private` (seamed), so only the first two checks.
    let st = elab.mctx.store();
    if elab.view.get(decl).is_some() {
        return Err(ElabError::AlreadyDeclared(names::render(
            st,
            base,
            Some(decl),
        )));
    }
    if is_possibly_reserved(elab, decl) {
        return Err(ElabError::UnsupportedSyntax(format!(
            "possibly reserved name `{}` (isReservedName) — later M4",
            names::render(st, base, Some(decl))
        )));
    }
    // `:278-284`.
    if !view.protected {
        return Ok((decl, short));
    }
    let st = elab.mctx.store();
    match ns.and_then(|n| names::last_str(st, base, n)) {
        Some(s) => {
            let s = s.to_string();
            let pre = intern_atomic(elab, &s)?;
            let short = names::append(elab.mctx.store_mut(), base, Some(pre), Some(short))
                .map_err(MetaError::from)?
                .ok_or_else(|| ElabError::Internal("empty short name".into()))?;
            Ok((decl, short))
        }
        None if names::is_atomic(st, base, Some(short)) => Err(ElabError::ProtectedNotInNamespace),
        None => Ok((decl, short)),
    }
}

/// oracle: `checkIfShadowingStructureField` (`DeclModifiers.lean:253-261`)
/// over `getStructureFieldsFlattened` (`Structure.lean:239-261`, subobject
/// fields included). The oracle's message prints the name with
/// `.ofConstName`, which shortens it against the open namespaces: a seam.
/// `visited` guards a parent cycle (`structureExt` rows are untrusted).
fn check_if_shadowing_structure_field(elab: &TermElabM, decl: NameId) -> Result<(), ElabError> {
    let base = Some(elab.view.store);
    let st = elab.mctx.store();
    let (Some(pre), Some(s)) = (
        names::parent(st, base, decl),
        names::last_str(st, base, decl),
    ) else {
        return Ok(());
    };
    if !elab.mctx.is_structure(pre) {
        return Ok(());
    }
    let mut stack = vec![pre];
    let mut visited = Vec::new();
    while let Some(sn) = stack.pop() {
        if visited.contains(&sn) {
            continue;
        }
        visited.push(sn);
        for &f in elab.mctx.get_structure_fields(sn) {
            if names::last_str(st, base, f) == Some(s) && names::is_atomic(st, base, Some(f)) {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "declaration name `{}` shadows a structure field (the oracle's message \
                     needs name shortening) — later M4",
                    names::render(st, base, Some(decl))
                )));
            }
            if let Some(p) = elab.mctx.get_field_info(sn, f).and_then(|i| i.subobject) {
                stack.push(p);
            }
        }
    }
    Ok(())
}

/// Suffixes the pinned toolchain's reserved-name predicates
/// (`registerReservedNamePredicate`) reserve under a declared parent
/// `p`: `Meta/Eqns.lean:99-106` (`eq_def`, `eq_unfold`, `eq_<n>`),
/// `Meta/Tactic/FunInd.lean:1533-1534`,
/// `Elab/PreDefinition/PartialFixpoint/Induction.lean:306, 426`,
/// `Meta/CtorIdxHInj.lean:58-61`, `Meta/Injective.lean:290-293`,
/// `Meta/Constructions/SparseCasesOnEq.lean:86-92`,
/// `Meta/CongrTheorems.lean:405-408` (`hcongr_<n>`, `congr_simp`),
/// `Meta/Match/MatchEqs.lean:334-355` (`eq_<n>`, `splitter`,
/// `congr_eq_<n>`) and `BVDecide/Normalize/Enums.lean:347-350`.
const RESERVED_UNDER_DECLARED: [&str; 16] = [
    "eq_def",
    "eq_unfold",
    "induct",
    "induct_unfolding",
    "mutual_induct",
    "fun_cases",
    "fun_cases_unfolding",
    "hinj",
    "else_eq",
    "congr_simp",
    "splitter",
    "eq_cond_enumToBitVec",
    "fixpoint_induct",
    "coinduct",
    "partial_correctness",
    "mutual_partial_correctness",
];

/// `BVDecide/Normalize/Enums.lean:35-37, 347-350`: reserved whatever the
/// parent (atomic names included); the predicate is `isEnumType`-free.
const RESERVED_ANYWHERE: [&str; 3] = ["enumToBitVec", "eq_iff_enumToBitVec_eq", "enumToBitVec_le"];

/// `isReservedName` (`checkNotAlreadyDeclared`, `DeclModifiers.lean:45-46`),
/// conservatively: every predicate's suffix test, with the parent's
/// precise condition (a safe definition, a matcher, a constructor, …)
/// widened to "declared". The one narrowing: an axiom parent reserves no
/// equation name (`Meta/Eqns.lean:71-78`: `isSafeDefinition`), and no
/// other predicate takes `eq_def`/`eq_unfold`/`eq_<n>` under an axiom
/// (the matcher one needs a definition).
fn is_possibly_reserved(elab: &TermElabM, decl: NameId) -> bool {
    let base = Some(elab.view.store);
    let st = elab.mctx.store();
    let Some(s) = names::last_str(st, base, decl) else {
        return false;
    };
    if RESERVED_ANYWHERE.contains(&s) {
        return true;
    }
    let Some(p) = names::parent(st, base, decl) else {
        return false;
    };
    let Some(info) = elab.view.get(p) else {
        return false;
    };
    // `isEqnLikeSuffix` (`Meta/Eqns.lean:64-65`).
    let eqn_like = s == "eq_def" || s == "eq_unfold" || numbered(s, "eq_");
    if eqn_like && matches!(info, leanr_kernel::ConstantInfo::Axiom(_)) {
        return false;
    }
    RESERVED_UNDER_DECLARED.contains(&s)
        || numbered(s, "eq_")
        || numbered(s, "hcongr_")
        || numbered(s, "congr_eq_")
}

/// `s` is `prefix` followed by `String.isNat` (`Init/Data/String/
/// Slice.lean:976-989`): digits, `_` only between digits.
fn numbered(s: &str, prefix: &str) -> bool {
    let Some(rest) = s.strip_prefix(prefix) else {
        return false;
    };
    let mut last_was_digit = false;
    for c in rest.chars() {
        if c == '_' {
            if !last_was_digit {
                return false;
            }
            last_was_digit = false;
        } else if c.is_ascii_digit() {
            last_was_digit = true;
        } else {
            return false;
        }
    }
    last_was_digit
}

/// oracle: `elabHeaders` runs under `withAutoBoundImplicit`
/// (`MutualDef.lean:257`; `elabAxiom` too, `Declaration.lean:109`): an
/// unbound identifier or universe in a header is auto-bound, not an error.
/// Auto-bound implicits are M4c-2c-ii.
pub(super) fn unknown_ident_to_auto_bound_seam(e: ElabError) -> ElabError {
    match e {
        ElabError::UnknownIdent(s) => ElabError::UnsupportedSyntax(format!(
            "unbound `{s}` in a declaration header (auto-bound implicit) — M4c-2c-ii"
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
/// syntax, whose identifier `expandNamespacedDeclaration` has replaced by
/// the short name (`setDeclIdName`, `Declaration.lean:27-35`) when it
/// opened the namespace. For an atomic name the source text agrees with
/// that (at most whitespace inside `.{…}` could differ); an expanded one
/// prints its short name, `«»`-quoted when it contains a `.` (`mkIdent`).
fn decl_id_text(view: &DefView) -> String {
    let n = match &view.decl_id {
        Some(NodeOrToken::Node(n)) => n,
        Some(NodeOrToken::Token(t)) => return t.text().to_string(),
        None => return String::new(),
    };
    let text = n.text().to_string();
    let ident = n.children_with_tokens().find_map(|el| {
        el.into_token()
            .filter(|t| !leanr_syntax::kind::is_trivia(t.kind()) && !t.text().is_empty())
    });
    let (Some(ident), Some([short])) = (ident, view.name.as_deref()) else {
        return text.trim().to_string();
    };
    let written = ident.text().to_string();
    let as_written = crate::app::head::ident_components(&written)
        .is_ok_and(|c| c.as_slice() == std::slice::from_ref(short));
    if as_written {
        return text.trim().to_string();
    }
    let shown = if short.contains('.') {
        format!("«{short}»")
    } else {
        short.clone()
    };
    text.replacen(&written, &shown, 1).trim().to_string()
}
