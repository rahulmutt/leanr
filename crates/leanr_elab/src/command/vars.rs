//! Section variables: oracle `runTermElabM` (`Elab/Command.lean:774-797`),
//! `variable` / `include` / `omit` (`Elab/BuiltinCommand.lean:415-430,
//! 551-607`) and the inclusion regimes (`MutualDef.lean:455-490,
//! 595-611`; `Declaration.lean:118`).
//!
//! Not modelled: the `unusedSectionVars` lint (a warning; the gate keeps
//! errors only), `deprecated.oldSectionVars`, auto-bound implicits
//! (`— M4c-2c-ii`), the mvar-rebuild branch of `runTermElabM` (auto-bound
//! only), `variable {α}` binder-annotation updates (`— later M4`).

use std::collections::HashSet;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::BinderInfo;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::{NodeOrToken, SyntaxNode};

use crate::app::elim_info::{any_subterm, has_no_fvar};
use crate::app::head::ident_components;
use crate::builtin::binder::{extract_binder_group, push_binder_group};
use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;

/// The head scope's section variables, elaborated for one run
/// (`runTermElabM`'s `xs` and `sectionFVars`, `Command.lean:777-783`).
pub(super) struct SecVars {
    /// One fvar per binder id of `Scope::var_decls`, in order.
    pub fvars: Vec<ExprId>,
    /// `Scope::var_uids`, parallel to `fvars`. Read by the theorem
    /// regime ([`header_sec_vars`]).
    pub uids: Vec<u32>,
    /// `Scope::included_vars` / `omitted_vars`.
    pub included: Vec<u32>,
    pub omitted: Vec<u32>,
}

fn ill(what: &str) -> ElabError {
    ElabError::IllFormedSyntax(format!("bracketed binder: {what}"))
}

/// A binder identifier (`binderIdent`): `Some` for an `<ident>` token,
/// `None` for the `_` hole.
fn binder_ident(el: &SynElem, kinds: &KindInterner) -> Result<Option<Vec<String>>, ElabError> {
    match el {
        NodeOrToken::Token(t) if kinds.name(t.kind()) == "<ident>" => {
            Ok(Some(ident_components(t.text())?))
        }
        NodeOrToken::Node(n) if kinds.name(n.kind()) == "Lean.Parser.Term.hole" => Ok(None),
        _ => Err(ill("expected a binder identifier")),
    }
}

/// oracle `getBracketedBinderIds` (`Command.lean:686-693`): the ids of
/// one binder, `None` for `_` and for an anonymous `[C α]`. The layouts
/// are `extract_binder_group`'s (`builtin/binder/mod.rs`): child `[1]` is
/// the names node (an `instBinder`'s optional `x :`).
pub(super) fn bracketed_binder_ids(
    binder: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<Vec<Option<Vec<String>>>, ElabError> {
    let ch = non_trivia_children(binder);
    let names = ch
        .get(1)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ill("names slot"))?;
    let names = non_trivia_children(names);
    match kinds.name(binder.kind()) {
        "Lean.Parser.Term.explicitBinder"
        | "Lean.Parser.Term.implicitBinder"
        | "Lean.Parser.Term.strictImplicitBinder" => {
            names.iter().map(|el| binder_ident(el, kinds)).collect()
        }
        // `[$id : $_]` / `[$_]` (`Name.anonymous`).
        "Lean.Parser.Term.instBinder" => Ok(vec![match names.first() {
            Some(el) => binder_ident(el, kinds)?,
            None => None,
        }]),
        other => Err(ElabError::UnsupportedSyntax(format!(
            "bracketed binder: {other}"
        ))),
    }
}

/// oracle `typelessBinder?` (`BuiltinCommand.lean:319-324`), the
/// explicit/implicit/strict-implicit arms: a binder whose type slot (the
/// node holding `[":", T]`) is empty. The `[x]` arm is
/// [`inst_binder_ident`].
pub(super) fn typeless_binder(binder: &SyntaxNode, kinds: &KindInterner) -> bool {
    match kinds.name(binder.kind()) {
        "Lean.Parser.Term.explicitBinder"
        | "Lean.Parser.Term.implicitBinder"
        | "Lean.Parser.Term.strictImplicitBinder" => {
            match non_trivia_children(binder)
                .get(2)
                .and_then(|el| el.as_node())
            {
                Some(slot) => non_trivia_children(slot).is_empty(),
                None => true,
            }
        }
        _ => false,
    }
}

/// `typelessBinder?`'s `[$id:ident]` arm: an anonymous `instBinder` whose
/// type is a bare identifier, decoded. It is an annotation update only
/// when that id names a section variable (`replaceBinderAnnotation`,
/// `BuiltinCommand.lean:343-413`); otherwise an ordinary instance binder.
pub(super) fn inst_binder_ident(
    binder: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<Option<Vec<String>>, ElabError> {
    if kinds.name(binder.kind()) != "Lean.Parser.Term.instBinder" {
        return Ok(None);
    }
    let ch = non_trivia_children(binder);
    let named = ch
        .get(1)
        .and_then(|el| el.as_node())
        .is_some_and(|n| !non_trivia_children(n).is_empty());
    match ch.get(2) {
        Some(NodeOrToken::Token(t)) if !named && kinds.name(t.kind()) == "<ident>" => {
            Ok(Some(ident_components(t.text())?))
        }
        _ => Ok(None),
    }
}

/// oracle `runTermElabM`'s `elabBinders scope.varDecls` +
/// `synthesizeSyntheticMVarsNoPostponing` (`Command.lean:777-780`): one
/// fvar per binder id, local instances registered.
pub(super) fn elab_section_vars(
    elab: &mut TermElabM,
    var_decls: &[SyntaxNode],
    kinds: &KindInterner,
) -> Result<Vec<ExprId>, ElabError> {
    let mut xs = Vec::new();
    for b in var_decls {
        let g = extract_binder_group(elab, b, kinds).map_err(variable_auto_bound_seam)?;
        xs.extend(push_binder_group(elab, &g, kinds).map_err(variable_auto_bound_seam)?);
    }
    elab.synthesize_synthetic_mvars_no_postponing(kinds)
        .map_err(variable_auto_bound_seam)?;
    Ok(xs)
}

/// The variable-binder twin of `header::unknown_ident_to_auto_bound_seam`:
/// `runTermElabM` and `elabVariable` run under `withAutoBoundImplicit`
/// (`Command.lean:777`, `BuiltinCommand.lean:419`).
fn variable_auto_bound_seam(e: ElabError) -> ElabError {
    match e {
        ElabError::UnknownIdent(s) => ElabError::UnsupportedSyntax(format!(
            "unbound `{s}` in a `variable` binder (auto-bound implicit) — M4c-2c-ii"
        )),
        e => e,
    }
}

/// oracle `removeUnused` (`Meta/CollectFVars.lean:53-65`): scan `vars`
/// newest first; a used var is kept and its (instantiated) type's fvars
/// join `used`.
pub(super) fn remove_unused(
    elab: &mut TermElabM,
    vars: &[ExprId],
    used: &mut HashSet<ExprId>,
) -> Result<Vec<ExprId>, ElabError> {
    let mut kept = Vec::new();
    for &x in vars.iter().rev() {
        if used.contains(&x) {
            let ty = elab.mctx.infer_type(x)?;
            let ty = elab.mctx.instantiate_mvars(ty)?;
            collect_fvars(elab, ty, used);
            kept.push(x);
        }
    }
    kept.reverse();
    Ok(kept)
}

/// oracle `withUsed` (`MutualDef.lean:595-611`; `Expr.collectFVars`
/// instantiates first, `Meta/CollectFVars.lean:17-19`), also the axiom's
/// `mkForallFVars vars type (usedOnly := true)` (`Declaration.lean:118`).
pub(super) fn used_vars(
    elab: &mut TermElabM,
    vars: &[ExprId],
    exprs: &[ExprId],
) -> Result<Vec<ExprId>, ElabError> {
    let mut used = HashSet::new();
    for &e in exprs {
        let e = elab.mctx.instantiate_mvars(e)?;
        collect_fvars(elab, e, &mut used);
    }
    remove_unused(elab, vars, &mut used)
}

/// oracle `withHeaderSecVars` (`Elab/MutualDef.lean:455-490`): the
/// section variables a theorem keeps — those its headers reference, the
/// `include`d ones, their transitive dependencies, then every
/// non-`omit`ted instance variable whose type mentions only kept fvars
/// (scanned in variable order, so an instance can only be covered by
/// what precedes it in the scan). With `check`, a kept variable the
/// scope `omit`s is an error. Returns the kept variables in order; the
/// caller erases the rest from the body's context (`removeUnused` +
/// `withLCtx`, `:461-462`).
pub(super) fn header_sec_vars(
    elab: &mut TermElabM,
    sv: &SecVars,
    header_tys: &[ExprId],
    check: bool,
) -> Result<Vec<ExprId>, ElabError> {
    let mut used = HashSet::new();
    // directly referenced in headers (`Expr.collectFVars` instantiates).
    for &t in header_tys {
        let t = elab.mctx.instantiate_mvars(t)?;
        collect_fvars(elab, t, &mut used);
    }
    // included by `include`
    for (&x, uid) in sv.fvars.iter().zip(&sv.uids) {
        if sv.included.contains(uid) {
            used.insert(x);
        }
    }
    // transitively referenced
    add_dependencies(elab, &mut used)?;
    // The oracle scans `used` in insertion order and reports the first
    // omitted one; this scans in variable order. They differ only in
    // WHICH name is reported when two omitted variables are referenced.
    if check {
        for (&x, uid) in sv.fvars.iter().zip(&sv.uids) {
            if used.contains(&x) && sv.omitted.contains(uid) {
                let name = local_decl(elab, x)?.binder_name;
                return Err(ElabError::OmitReferenced(crate::names::render(
                    elab.mctx.store(),
                    Some(elab.view.store),
                    name,
                )));
            }
        }
    }
    // instances whose type's fvars are all kept, in variable order
    for (&x, uid) in sv.fvars.iter().zip(&sv.uids) {
        if sv.omitted.contains(uid) {
            continue;
        }
        let d = local_decl(elab, x)?;
        if d.binder_info == BinderInfo::InstImplicit {
            let ty = elab.mctx.instantiate_mvars(d.ty)?;
            let mut fs = HashSet::new();
            collect_fvars(elab, ty, &mut fs);
            if fs.iter().all(|f| used.contains(f)) {
                used.insert(x);
            }
        }
    }
    remove_unused(elab, &sv.fvars, &mut used)
}

/// oracle `CollectFVars.State.addDependencies` (`Meta/CollectFVars.lean:
/// 27-49`): close `used` over the (instantiated) types — and let values —
/// of its members' declarations. An fvar the current context does not
/// declare is skipped (the oracle's `find?` → `return ()`). The oracle's
/// worklist runs in insertion order; the fixpoint is the same set.
fn add_dependencies(elab: &mut TermElabM, used: &mut HashSet<ExprId>) -> Result<(), ElabError> {
    let mut work: Vec<ExprId> = used.iter().copied().collect();
    while let Some(x) = work.pop() {
        let Some(d) = lookup_local_decl(elab, x) else {
            continue;
        };
        let mut fs = HashSet::new();
        for e in std::iter::once(d.ty).chain(d.value) {
            let e = elab.mctx.instantiate_mvars(e)?;
            collect_fvars(elab, e, &mut fs);
        }
        for f in fs {
            if used.insert(f) {
                work.push(f);
            }
        }
    }
    Ok(())
}

/// The current context's declaration of fvar `x`, if it declares one.
fn lookup_local_decl(elab: &mut TermElabM, x: ExprId) -> Option<leanr_kernel::LocalDecl> {
    let Node::FVar { id: Some(id) } = elab.mctx.store().expr_node(Some(elab.view.store), x) else {
        return None;
    };
    elab.mctx.current_lctx().lctx().get(id).cloned()
}

/// oracle `getFVarLocalDecl`: a section variable's declaration.
fn local_decl(elab: &mut TermElabM, x: ExprId) -> Result<leanr_kernel::LocalDecl, ElabError> {
    lookup_local_decl(elab, x)
        .ok_or_else(|| ElabError::Internal("section variable not in the local context".into()))
}

/// oracle: `collectFVars` (`Lean/Util/CollectFVars.lean`) — add every
/// `fvar` subterm of `e` to `set`. Hash-consing makes the fvar's
/// `ExprId` its identity.
pub(crate) fn collect_fvars(elab: &TermElabM<'_>, e: ExprId, set: &mut HashSet<ExprId>) {
    let mut found = Vec::new();
    any_subterm(elab, e, has_no_fvar, |_, e, n| {
        if matches!(n, Node::FVar { .. }) {
            found.push(e);
        }
        false
    });
    set.extend(found);
}
