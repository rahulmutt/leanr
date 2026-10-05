//! Section variables: oracle `runTermElabM` (`Elab/Command.lean:774-797`),
//! `variable` / `include` / `omit` (`Elab/BuiltinCommand.lean:415-430,
//! 551-607`) and the inclusion regimes (`MutualDef.lean:455-490,
//! 595-611`; `Declaration.lean:118`).
//!
//! Not modelled: the `unusedSectionVars` lint (a warning; the gate keeps
//! errors only), `deprecated.oldSectionVars`, auto-bound implicits
//! (`— M4c-2c-ii`), the mvar-rebuild branch of `runTermElabM` (auto-bound
//! only), `variable {α}` binder-annotation updates (`— later M4`).
//! An unmatched `omit` item is reported by its source text with
//! whitespace runs collapsed, standing in for the oracle's syntax
//! formatter (`{o}`).

use std::collections::HashSet;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::{BinderInfo, Name};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::{NodeOrToken, SyntaxNode};

use crate::app::elim_info::{any_subterm, has_no_fvar};
use crate::app::head::ident_components;
use crate::builtin::binder::{extract_binder_group, push_binder_group};
use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;

use super::CommandElab;

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
/// After [`header_sec_vars`]' `addDependencies` the type step adds
/// nothing new (`used` is already closed), so only [`used_vars`]' callers
/// (def/axiom) can observe it.
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
    let mut used = FVarState::default();
    // directly referenced in headers (`Expr.collectFVars` instantiates).
    for &t in header_tys {
        let t = elab.mctx.instantiate_mvars(t)?;
        collect_fvars_ordered(elab, t, &mut used);
    }
    // included by `include`
    for (&x, uid) in sv.fvars.iter().zip(&sv.uids) {
        if sv.included.contains(uid) {
            used.add(x);
        }
    }
    // transitively referenced
    add_dependencies(elab, &mut used)?;
    // `for var in (← get).fvarIds`: the FIRST omitted one in insertion
    // order is reported.
    if check {
        for &x in &used.ids {
            if let Some(i) = sv.fvars.iter().position(|&f| f == x) {
                if sv.omitted.contains(&sv.uids[i]) {
                    let d = local_decl(elab, x)?;
                    return Err(ElabError::OmitReferenced(fvar_message_name(elab, &d)));
                }
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
            if fs.iter().all(|f| used.set.contains(f)) {
                used.add(x);
            }
        }
    }
    remove_unused(elab, &sv.fvars, &mut used.set)
}

/// `{Expr.fvar x}` as a message prints it: the user name, or — for the
/// anonymous `[C α]` binder, which the oracle names with a macro-scoped
/// `inst` (`expandOptIdent`'s `mkFreshIdent`) — `inst✝` (row
/// `omit/referencedAnonInst`). Any other
/// anonymous binder (`(_ : T)`) cannot be referenced by a header.
fn fvar_message_name(elab: &TermElabM, d: &leanr_kernel::LocalDecl) -> String {
    match d.binder_name {
        None if d.binder_info == BinderInfo::InstImplicit => "inst✝".to_string(),
        n => crate::names::render(elab.mctx.store(), Some(elab.view.store), n),
    }
}

/// oracle `CollectFVars.State` (`Util/CollectFVars.lean:15-22`): the set
/// plus its insertion order (`fvarIds`), which `withHeaderSecVars`'
/// omit check and `addDependencies`' worklist iterate.
#[derive(Default)]
struct FVarState {
    set: HashSet<ExprId>,
    ids: Vec<ExprId>,
}

impl FVarState {
    /// `State.add`; a duplicate is not re-pushed (only first-insertion
    /// order is ever observed).
    fn add(&mut self, x: ExprId) {
        if self.set.insert(x) {
            self.ids.push(x);
        }
    }
}

/// oracle `CollectFVars.State.addDependencies` (`Meta/CollectFVars.lean:
/// 27-49`): close `used` over the (instantiated) types — and let values —
/// of its members' declarations, walking `fvarIds` by index (so new
/// members are appended and visited in turn). An fvar the current
/// context does not declare is skipped (the oracle's `find?` →
/// `return ()`).
fn add_dependencies(elab: &mut TermElabM, used: &mut FVarState) -> Result<(), ElabError> {
    let mut i = 0;
    while let Some(&x) = used.ids.get(i) {
        i += 1;
        let Some(d) = lookup_local_decl(elab, x) else {
            continue;
        };
        for e in std::iter::once(d.ty).chain(d.value) {
            let e = elab.mctx.instantiate_mvars(e)?;
            collect_fvars_ordered(elab, e, used);
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
    set.extend(fvars_in_order(elab, e));
}

/// [`collect_fvars`] keeping the oracle's discovery order (`main`'s
/// left-to-right pre-order: `f` before `a`, domain before body).
fn collect_fvars_ordered(elab: &TermElabM<'_>, e: ExprId, st: &mut FVarState) {
    for x in fvars_in_order(elab, e) {
        st.add(x);
    }
}

/// The distinct `fvar` subterms of `e`, in first-visit pre-order
/// (`any_subterm`'s order).
fn fvars_in_order(elab: &TermElabM<'_>, e: ExprId) -> Vec<ExprId> {
    let mut found = Vec::new();
    any_subterm(elab, e, has_no_fvar, |_, e, n| {
        if matches!(n, Node::FVar { .. }) {
            found.push(e);
        }
        false
    });
    found
}

/// One `omit` item, resolved (`elabOmit`'s `Sum Name Expr`).
enum OmitItem {
    /// `x` or `[x : T]`: matched by user name.
    Name(Vec<String>),
    /// `[T]`: the syntax, elaborated per run before matching.
    Type(SynElem),
}

/// Whether binder name `n` is the hierarchical name `comps` (oracle
/// `ldecl.userName == id`).
fn name_is(elab: &TermElabM, n: Option<NameId>, comps: &[String]) -> bool {
    let name = elab.mctx.store().to_name(Some(elab.view.store), n);
    let mut parts = Vec::new();
    let mut cur: &Name = &name;
    loop {
        match cur {
            Name::Anonymous => break,
            Name::Str { parent, part } => {
                parts.push(part.as_str());
                cur = parent;
            }
            Name::Num { .. } => return false,
        }
    }
    parts.reverse();
    parts.len() == comps.len() && parts.iter().zip(comps).all(|(a, b)| *a == b)
}

/// `{o}` for a syntax item: its source text, whitespace runs collapsed.
fn item_text(el: &SynElem) -> String {
    let raw = match el {
        NodeOrToken::Node(n) => n.text().to_string(),
        NodeOrToken::Token(t) => t.text().to_string(),
    };
    raw.split_whitespace().collect::<Vec<_>>().join(" ")
}

impl CommandElab<'_> {
    /// oracle `elabInclude` (`BuiltinCommand.lean:551-564`):
    /// `[<atom> "include", null(<ident>+)]`.
    pub(crate) fn elab_include(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<(), ElabError> {
        let ids: Vec<Vec<String>> = match non_trivia_children(cmd).get(1) {
            Some(NodeOrToken::Node(n)) => non_trivia_children(n)
                .into_iter()
                .map(|el| match el {
                    NodeOrToken::Token(t) if kinds.name(t.kind()) == "<ident>" => {
                        ident_components(t.text())
                    }
                    _ => Err(ElabError::IllFormedSyntax(
                        "include: expected an identifier".into(),
                    )),
                })
                .collect::<Result<_, _>>()?,
            _ => {
                return Err(ElabError::IllFormedSyntax(
                    "include: expected an identifier list".into(),
                ))
            }
        };
        let head = self.scopes.last().expect("the root scope is never popped");
        let mut names = Vec::new();
        for b in &head.var_decls {
            names.extend(bracketed_binder_ids(b, kinds)?);
        }
        let mut uids = Vec::new();
        for id in ids {
            // `findIdx?`: the FIRST binder id with this name.
            match names.iter().position(|n| n.as_ref() == Some(&id)) {
                Some(i) => uids.push(head.var_uids[i]),
                None => return Err(ElabError::IncludeUndeclared(id.join("."))),
            }
        }
        let head = self
            .scopes
            .last_mut()
            .expect("the root scope is never popped");
        head.included_vars.extend(&uids);
        head.omitted_vars.retain(|u| !uids.contains(u));
        Ok(())
    }

    /// oracle `elabOmit` (`BuiltinCommand.lean:566-607`):
    /// `[<atom> "omit", null((<ident> | instBinder)+)]`.
    pub(crate) fn elab_omit(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<(), ElabError> {
        let els = match non_trivia_children(cmd).get(1) {
            Some(NodeOrToken::Node(n)) => non_trivia_children(n),
            _ => {
                return Err(ElabError::IllFormedSyntax(
                    "omit: expected an item list".into(),
                ))
            }
        };
        let mut items = Vec::new();
        for el in &els {
            let item = match el {
                NodeOrToken::Token(t) if kinds.name(t.kind()) == "<ident>" => {
                    OmitItem::Name(ident_components(t.text())?)
                }
                NodeOrToken::Node(n) if kinds.name(n.kind()) == "Lean.Parser.Term.instBinder" => {
                    // `[$id : $_]` / `[$ty]`: child [1] the optional
                    // `id :`, child [2] the type.
                    let ch = non_trivia_children(n);
                    let named = ch
                        .get(1)
                        .and_then(|o| o.as_node())
                        .and_then(|o| non_trivia_children(o).into_iter().next());
                    match named {
                        Some(NodeOrToken::Token(t)) if kinds.name(t.kind()) == "<ident>" => {
                            OmitItem::Name(ident_components(t.text())?)
                        }
                        Some(_) => {
                            return Err(ElabError::IllFormedSyntax(
                                "omit: instance binder name".into(),
                            ))
                        }
                        None => OmitItem::Type(ch.get(2).cloned().ok_or_else(|| {
                            ElabError::IllFormedSyntax("omit: instance binder type".into())
                        })?),
                    }
                }
                _ => {
                    return Err(ElabError::IllFormedSyntax(
                        "omit: expected an identifier or instance binder".into(),
                    ))
                }
            };
            items.push((item, item_text(el)));
        }
        let (omitted, _) = self.with_term_elab(kinds, |elab, sv| {
            elab.synthesize_synthetic_mvars_no_postponing(kinds)?;
            // `withoutErrToSorry (elabTermAndSynthesize ty none)`, in item
            // order, before any matching.
            let mut tys = Vec::with_capacity(items.len());
            for (item, _) in &items {
                tys.push(match item {
                    OmitItem::Type(t) => Some(elab.elab_term_and_synthesize(t, kinds, None)?),
                    OmitItem::Name(_) => None,
                });
            }
            let mut used = vec![false; items.len()];
            let mut omitted = Vec::new();
            for (&x, &uid) in sv.fvars.iter().zip(&sv.uids) {
                let d = local_decl(elab, x)?;
                // `findIdxM?`: the FIRST item that matches this variable.
                let mut hit = None;
                for (i, (item, _)) in items.iter().enumerate() {
                    let ok = match (item, tys[i]) {
                        (OmitItem::Name(n), _) => name_is(elab, d.binder_name, n),
                        (OmitItem::Type(_), Some(t)) => {
                            // `isDefEq ty ldecl.type <* setMCtx mctx`.
                            let cp = elab.mctx.checkpoint();
                            let ok = elab.mctx.is_def_eq(t, d.ty);
                            elab.mctx.rollback(cp);
                            ok?
                        }
                        (OmitItem::Type(_), None) => unreachable!("elaborated above"),
                    };
                    if ok {
                        hit = Some(i);
                        break;
                    }
                }
                // Every run variable is a section variable, so the
                // oracle's `revSectionFVars` miss (`:599`) cannot happen.
                if let Some(i) = hit {
                    omitted.push(uid);
                    used[i] = true;
                }
            }
            if let Some(i) = used.iter().position(|u| !u) {
                return Err(ElabError::OmitUnmatched(items[i].1.clone()));
            }
            Ok(omitted)
        })?;
        let head = self
            .scopes
            .last_mut()
            .expect("the root scope is never popped");
        head.omitted_vars.extend(&omitted);
        head.included_vars.retain(|u| !omitted.contains(u));
        Ok(())
    }
}
