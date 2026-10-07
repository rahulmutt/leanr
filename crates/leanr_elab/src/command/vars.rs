//! Section variables: oracle `runTermElabM` (`Elab/Command.lean:774-798`),
//! `variable` / `include` / `omit` (`Elab/BuiltinCommand.lean:415-430,
//! 551-607`) and the inclusion regimes (`MutualDef.lean:455-490,
//! 595-611`; `Declaration.lean:118`).
//!
//! Binder-annotation updates (`variable {x}`, `replaceBinderAnnotation`,
//! `BuiltinCommand.lean:343-413`) are modelled for typed variables
//! ([`VarDecl`], [`plan_annotation_update`]); a typeless binder that
//! declares a NEW variable (`variable {z}`, or the residue of an update)
//! needs the `expandBinderType` hole (`— later M4`).
//!
//! Not modelled: the `unusedSectionVars` lint (a warning; the gate keeps
//! errors only), `deprecated.oldSectionVars`;
//! `withUsed`'s local-context erasure (`removeUnused` erases the unused
//! variables from the lctx and local instances, `Meta/CollectFVars.lean:
//! 63`), as nothing elaborates under that context after the closure
//! (the theorem regime's erasure IS modelled: its body runs there); and
//! `elabFunValues`' `cleanupAnnotations` on every local declaration's
//! type (`MutualDef.lean:535`), as `elab_section_vars` stores no
//! annotations a section-variable type could carry. Neither is
//! observable today.
//! Auto-bound implicits and the mvar-rebuild branch (M4c-2c-ii P2) are
//! modelled; `SecVars::section_fvars` is the oracle's pre-rebuild
//! `sectionFVars`.
//! An unmatched `omit` item is reported by its source text with
//! whitespace runs collapsed, standing in for the oracle's syntax
//! formatter (`{o}`).

use std::collections::HashSet;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::{BinderInfo, Name};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::{NodeOrToken, SyntaxNode};

use crate::app::elim_info::{collect_fvars, fvars_in_order};
use crate::app::head::ident_components;
use crate::builtin::binder::{
    binder_info_of, extract_binder_group, push_binder_group, BinderGroup,
};
use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;

use super::CommandElab;

/// The decoded ids of a bracketed binder, in order; `None` for `_` and
/// for an anonymous `[C α]`.
pub(super) type BinderIds = Vec<Option<Vec<String>>>;

/// oracle `sectionFVars`: binder-id uid ↦ fvar, in binder order.
pub(super) type SectionFVars = Vec<(u32, ExprId)>;

/// One run of the head scope's section variables (oracle `runTermElabM`,
/// `Command.lean:774-798`): what `elabFn` receives plus `sectionFVars`.
pub(super) struct SecVars {
    /// `elabFn`'s `xs`: the auto-bound implicits (each preceded by the
    /// unassigned mvars of its type, `addAutoBoundImplicits`), then one
    /// fvar per binder id. On the rebuild branch these are the fresh
    /// telescope's fvars.
    pub fvars: Vec<ExprId>,
    /// oracle `sectionFVars` (`Command.lean:782-784`): binder-id uid ↦
    /// the fvar elaborated for it, built BEFORE `addAutoBoundImplicits`
    /// and the rebuild. Autos never have a uid, and on the rebuild branch
    /// no member of `fvars` has one (the oracle's stale map, observable:
    /// `varAuto/rebuildInclude`, spec Amendment 2).
    pub section_fvars: SectionFVars,
    /// `Scope::included_vars` / `omitted_vars`.
    pub included: Vec<u32>,
    pub omitted: Vec<u32>,
}

impl SecVars {
    /// `revSectionFVars[x]?` (`MutualDef.lean:457-459`,
    /// `BuiltinCommand.lean:585-587`).
    pub fn uid_of(&self, x: ExprId) -> Option<u32> {
        self.section_fvars
            .iter()
            .find(|&&(_, f)| f == x)
            .map(|&(u, _)| u)
    }
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

/// oracle `elabBinders` over bracketed binder syntax: one fvar per binder
/// id, in order, left in the local context.
pub(super) fn elab_binders(
    elab: &mut TermElabM,
    binders: &[SyntaxNode],
    kinds: &KindInterner,
) -> Result<Vec<ExprId>, ElabError> {
    let mut xs = Vec::new();
    for b in binders {
        let g = extract_binder_group(elab, b, kinds)?;
        xs.extend(push_binder_group(elab, &g, kinds)?);
    }
    Ok(xs)
}

/// One entry of oracle `Scope.varDecls` (`Command/Scope.lean:52`). A
/// `variable` binder is stored as written (`only: None`, `bi` its own
/// annotation). A binder-annotation update replaces a matched binder by
/// one `mkBinder` per id (`BuiltinCommand.lean:377-386`, `($id : ty)` with
/// the new or the old annotation): leanr keeps the ORIGINAL node, the
/// index of the kept id in it, and the annotation, which is all
/// `mkBinder`'s syntax carries.
#[derive(Clone, Debug)]
pub(crate) struct VarDecl {
    pub node: SyntaxNode,
    /// `Some(i)`: only the node's `i`-th binder id.
    pub only: Option<usize>,
    pub bi: BinderInfo,
}

impl VarDecl {
    /// A `variable` binder as written.
    pub(super) fn new(node: SyntaxNode, kinds: &KindInterner) -> Result<VarDecl, ElabError> {
        let kind = kinds.name(node.kind());
        let bi = binder_info_of(kind)
            .ok_or_else(|| ElabError::UnsupportedSyntax(format!("bracketed binder: {kind}")))?;
        Ok(VarDecl {
            node,
            only: None,
            bi,
        })
    }

    /// `getBracketedBinderIds` of the binder this entry stands for.
    pub(super) fn ids(&self, kinds: &KindInterner) -> Result<BinderIds, ElabError> {
        let ids = bracketed_binder_ids(&self.node, kinds)?;
        match self.only {
            None => Ok(ids),
            Some(i) => ids
                .get(i)
                .cloned()
                .map(|id| vec![id])
                .ok_or_else(|| ElabError::Internal("variable: binder id index".into())),
        }
    }

    /// The binder group `elabBinders` elaborates for this entry.
    fn group(&self, elab: &mut TermElabM, kinds: &KindInterner) -> Result<BinderGroup, ElabError> {
        let mut g = extract_binder_group(elab, &self.node, kinds)?;
        if let Some(i) = self.only {
            let name = *g
                .names
                .get(i)
                .ok_or_else(|| ElabError::Internal("variable: binder id index".into()))?;
            g.names = vec![name];
        }
        g.bi = self.bi;
        Ok(g)
    }

    /// `ty?`: whether the binder carries `: T` (an `instBinder` always does).
    fn has_type(&self, kinds: &KindInterner) -> bool {
        !typeless_binder(&self.node, kinds)
    }
}

/// oracle `elabBinder` over one [`VarDecl`]: its fvars, left in the local
/// context.
pub(super) fn elab_var_decl(
    elab: &mut TermElabM,
    d: &VarDecl,
    kinds: &KindInterner,
) -> Result<Vec<ExprId>, ElabError> {
    let g = d.group(elab, kinds)?;
    push_binder_group(elab, &g, kinds)
}

/// [`elab_binders`] over the scope's [`VarDecl`]s.
fn elab_var_decls(
    elab: &mut TermElabM,
    var_decls: &[VarDecl],
    kinds: &KindInterner,
) -> Result<Vec<ExprId>, ElabError> {
    let mut xs = Vec::new();
    for d in var_decls {
        xs.extend(elab_var_decl(elab, d, kinds)?);
    }
    Ok(xs)
}

/// oracle `typelessBinder?` (`BuiltinCommand.lean:320-325`): the ids (a
/// `_` hole is `None`) and annotation of `(ids*)`/`{ids*}`/`⦃ids*⦄`, or of
/// an anonymous `[id]` whose type is a bare identifier.
pub(super) fn typeless_binder_ids(
    binder: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<Option<(BinderIds, BinderInfo)>, ElabError> {
    if typeless_binder(binder, kinds) {
        let bi = binder_info_of(kinds.name(binder.kind()))
            .ok_or_else(|| ElabError::Internal("typeless binder kind".into()))?;
        return Ok(Some((bracketed_binder_ids(binder, kinds)?, bi)));
    }
    Ok(inst_binder_ident(binder, kinds)?.map(|id| (vec![Some(id)], BinderInfo::InstImplicit)))
}

/// What `replaceBinderAnnotation` (`BuiltinCommand.lean:343-413`) decided
/// for one typeless binder.
#[derive(Debug)]
pub(super) struct AnnotationUpdate {
    /// `modifiedVarDecls`: the scope's new `varDecls`, in order.
    pub new_decls: Option<Vec<VarDecl>>,
    /// The new instance-implicit binders `:392-399` elaborates, with the id
    /// text for the error.
    pub inst_checks: Vec<(VarDecl, String)>,
    /// `None`: no id matched, the binder itself is returned (`:413`).
    /// `Some(ids)`: the unmatched ids, returned as typeless binders
    /// (`:405-411`); empty when every id matched.
    pub residue: Option<BinderIds>,
}

/// `:397-399`'s `catch e => throwErrorAt binder m!"cannot update …"`:
/// an oracle error from the `[x : T]` check becomes the update failure; a
/// seam, a runtime or an internal failure is not an oracle `.error`, and
/// is rethrown as itself. Known first-line divergence (not a wrong-Ok):
/// the oracle's `Command.tryCatch` (`Command.lean:85-93`) re-throws only
/// interrupts, so it wraps runtime errors such as maxRecDepth too, where
/// leanr rethrows `MaxRecDepth` unwrapped.
pub(super) fn inst_update_error(e: ElabError, id: &str) -> ElabError {
    if e.is_oracle_error() {
        ElabError::CannotUpdateToInstImplicit(id.to_string())
    } else {
        e
    }
}

/// oracle `containsId` (`:328-329`): a `_` never matches.
fn contains_id(ids: &[Option<Vec<String>>], id: &Option<Vec<String>>) -> bool {
    id.is_some() && ids.contains(id)
}

/// The scan of `replaceBinderAnnotation` (`BuiltinCommand.lean:343-413`)
/// for one typeless binder with ids `binder_ids` and annotation `bi`, over
/// the scope's `var_decls`. Newest first, to respect shadowing (`:351`): a
/// matched id is erased, so an older declaration of the same name is never
/// looked at again. The default-value arm (`:354-357`) is unreachable
/// while the parser rejects binder defaults.
pub(super) fn plan_annotation_update(
    var_decls: &[VarDecl],
    mut binder_ids: BinderIds,
    bi: BinderInfo,
    kinds: &KindInterner,
) -> Result<AnnotationUpdate, ElabError> {
    let ini = binder_ids.len();
    let mut new_decls = Vec::with_capacity(var_decls.len());
    let mut inst_checks = Vec::new();
    let mut modified = false;
    for d in var_decls.iter().rev() {
        // The anonymous `[C α]` (`:365-366`'s `_` arm, kept as is) needs no
        // arm of its own: its only id is `None`, which `contains_id` never
        // matches, so it is never redundant and never split.
        let ids = d.ids(kinds)?;
        if d.bi == bi {
            // no update: a redundant annotation is an error (`:367-372`).
            if binder_ids.iter().any(|b| contains_id(&ids, b)) {
                return Err(ElabError::RedundantBinderUpdate);
            }
            new_decls.push(d.clone());
        } else if binder_ids.iter().all(|b| !contains_id(&ids, b)) {
            new_decls.push(d.clone());
        } else {
            // split: one binder per id, the matched ones re-annotated
            // (`:387-402`; pushed in reverse, `new_decls` is reversed below).
            for (j, id) in ids.iter().enumerate().rev() {
                let only = Some(d.only.unwrap_or(j));
                let hit = id
                    .as_ref()
                    .and_then(|id| binder_ids.iter().position(|b| b.as_ref() == Some(id)));
                match hit {
                    Some(p) => {
                        binder_ids.remove(p);
                        modified = true;
                        let text = id.as_ref().map(|c| c.join(".")).unwrap_or_default();
                        // `mkBinder`'s `.instImplicit` arm (`:382-385`).
                        if bi == BinderInfo::InstImplicit && !d.has_type(kinds) {
                            return Err(ElabError::CannotUpdateToInstImplicit(text));
                        }
                        let nb = VarDecl {
                            node: d.node.clone(),
                            only,
                            bi,
                        };
                        if bi == BinderInfo::InstImplicit {
                            inst_checks.push((nb.clone(), text));
                        }
                        new_decls.push(nb);
                    }
                    None => new_decls.push(VarDecl {
                        node: d.node.clone(),
                        only,
                        bi: d.bi,
                    }),
                }
            }
        }
    }
    new_decls.reverse();
    Ok(AnnotationUpdate {
        new_decls: modified.then_some(new_decls),
        inst_checks,
        residue: (binder_ids.len() != ini).then_some(binder_ids),
    })
}

/// oracle `runTermElabM` up to `elabFn` (`Command.lean:776-798`):
/// `withAutoBoundImplicit (elabBinders varDecls …)`,
/// `synthesizeSyntheticMVarsNoPostponing`, `sectionFVars` from the
/// binders' fvars, then `addAutoBoundImplicits`. The loop leaves the
/// autos in the local context and resets the auto-bound context on exit,
/// which is the oracle's `withoutAutoBoundImplicit (elabFn xs)` for the
/// caller. When an auto-bound mvar survives in `xs`, the rebuild branch
/// re-opens them as fresh fvars in an empty context (the caller's scratch
/// run continues there). Returns (`elabFn`'s xs, `sectionFVars`).
pub(super) fn elab_section_vars(
    elab: &mut TermElabM,
    var_decls: &[VarDecl],
    var_uids: &[u32],
    kinds: &KindInterner,
) -> Result<(Vec<ExprId>, SectionFVars), ElabError> {
    let (xs, section_fvars) = elab.with_auto_bound_implicit(|elab| {
        let xs = elab_var_decls(elab, var_decls, kinds)?;
        elab.synthesize_synthetic_mvars_no_postponing(kinds)?;
        if xs.len() != var_uids.len() {
            return Err(ElabError::Internal(
                "section variables: one uid per binder id".into(),
            ));
        }
        let section_fvars: SectionFVars =
            var_uids.iter().copied().zip(xs.iter().copied()).collect();
        let xs = elab.add_auto_bound_implicits(&xs)?;
        Ok((xs, section_fvars))
    })?;
    let all_fvars = xs.iter().all(|&x| {
        matches!(
            elab.mctx.store().expr_node(Some(elab.view.store), x),
            Node::FVar { .. }
        )
    });
    if all_fvars {
        return Ok((xs, section_fvars));
    }
    // `:792-798`, the rebuild branch: abstract the mvars (and fvars) of
    // `xs` over a placeholder `Sort 0` (`mkForallFVars'`; leanr's mvar arm
    // names mvar binders inaccessibly, spec Amendment 1), then reopen the
    // telescope in an EMPTY context (`withLCtx {} {}`), so the old fvars
    // cannot be reached. `section_fvars` keeps the OLD fvars: the oracle's
    // stale map (spec Amendment 2). The replaced context is never
    // reinstalled: `elabFn` runs to the end of this scratch run inside
    // it, as the oracle's `withLCtx` scope does.
    let prop = crate::builtin::sort::mk_prop(elab)?;
    let ctx_ty = elab.mctx.mk_forall(&xs, prop)?;
    let _outer = elab.mctx.install_empty_lctx();
    let ys = elab.mctx.forall_bounded_telescope(ctx_ty, xs.len())?;
    if ys.len() != xs.len() {
        return Err(ElabError::Internal(
            "runTermElabM rebuild: telescope shorter than xs".into(),
        ));
    }
    Ok((ys, section_fvars))
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
/// instantiates first, `Meta/CollectFVars.lean:18-20`), also the axiom's
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
    for &x in &sv.fvars {
        if sv.uid_of(x).is_some_and(|u| sv.included.contains(&u)) {
            used.add(x);
        }
    }
    // transitively referenced
    add_dependencies(elab, &mut used)?;
    // `for var in (← get).fvarIds`: the FIRST omitted one in insertion
    // order is reported.
    if check {
        for &x in &used.ids {
            if sv.uid_of(x).is_some_and(|u| sv.omitted.contains(&u)) {
                let d = local_decl(elab, x)?;
                return Err(ElabError::OmitReferenced(fvar_message_name(elab, &d)));
            }
        }
    }
    // instances whose type's fvars are all kept, in variable order
    for &x in &sv.fvars {
        if sv.uid_of(x).is_some_and(|u| sv.omitted.contains(&u)) {
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

/// [`collect_fvars`] keeping the oracle's discovery order (`main`'s
/// left-to-right pre-order: `f` before `a`, domain before body).
fn collect_fvars_ordered(elab: &TermElabM<'_>, e: ExprId, st: &mut FVarState) {
    for x in fvars_in_order(elab, e) {
        st.add(x);
    }
}

/// One `omit` item, resolved (`elabOmit`'s `Sum Name Expr`).
enum OmitItem {
    /// `x` or `[x : T]`: matched by user name.
    Name(Vec<String>),
    /// `[T]`: the syntax, elaborated per run before matching.
    Type(SynElem),
}

/// An [`OmitItem`] ready to match: a `[T]` item's type elaborated.
enum OmitMatch<'a> {
    Name(&'a [String]),
    Type(ExprId),
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
        for d in &head.var_decls {
            names.extend(d.ids(kinds)?);
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
            let mut matchers = Vec::with_capacity(items.len());
            for (item, _) in &items {
                matchers.push(match item {
                    OmitItem::Name(n) => OmitMatch::Name(n),
                    OmitItem::Type(t) => {
                        OmitMatch::Type(elab.elab_term_and_synthesize(t, kinds, None)?)
                    }
                });
            }
            let mut used = vec![false; items.len()];
            let mut omitted = Vec::new();
            for &x in &sv.fvars {
                let d = local_decl(elab, x)?;
                // `findIdxM?`: the FIRST item that matches this variable.
                let mut hit = None;
                for (i, m) in matchers.iter().enumerate() {
                    let ok = match *m {
                        OmitMatch::Name(n) => name_is(elab, d.binder_name, n),
                        OmitMatch::Type(t) => {
                            // `isDefEq ty ldecl.type <* setMCtx mctx`.
                            let cp = elab.mctx.checkpoint();
                            let ok = elab.mctx.is_def_eq(t, d.ty);
                            elab.mctx.rollback(cp);
                            ok?
                        }
                    };
                    if ok {
                        hit = Some(i);
                        break;
                    }
                }
                if let Some(i) = hit {
                    match sv.uid_of(x) {
                        Some(uid) => {
                            omitted.push(uid);
                            used[i] = true;
                        }
                        // `:598-599`: an auto, or any variable after a
                        // rebuild (stale `sectionFVars`).
                        None => return Err(ElabError::OmitUndeclared(fvar_message_name(elab, &d))),
                    }
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The bracketed binders of every `variable` command in `src`, in order,
    /// as [`VarDecl`]s (bypassing elaboration).
    fn var_decls(src: &str) -> (Vec<VarDecl>, std::sync::Arc<KindInterner>) {
        let parsed = leanr_syntax::parse_module(src, &leanr_syntax::builtin::snapshot());
        assert!(parsed.errors.is_empty(), "{src:?}: {:?}", parsed.errors);
        let kinds = parsed.tree.kinds.clone();
        let mut out = Vec::new();
        for cmd in parsed.tree.root().children() {
            if kinds.name(cmd.kind()) != "Lean.Parser.Command.variable" {
                continue;
            }
            let Some(NodeOrToken::Node(list)) = non_trivia_children(&cmd).get(1).cloned() else {
                panic!("variable: binder list");
            };
            for el in non_trivia_children(&list) {
                let NodeOrToken::Node(b) = el else {
                    panic!("variable: binder")
                };
                out.push(VarDecl::new(b, &kinds).expect("binder kind"));
            }
        }
        (out, kinds)
    }

    fn id(s: &str) -> Option<Vec<String>> {
        Some(vec![s.to_string()])
    }

    #[test]
    fn an_inst_update_of_a_typeless_variable_needs_a_type() {
        // `mkBinder`'s `.instImplicit` arm (`BuiltinCommand.lean:382-385`).
        // Unreachable from source while a typeless variable seams on the
        // `expandBinderType` hole (oracle row `vu/instNoType`: `variable
        // (x)` then `variable [x]`), so the scan is driven directly.
        let (decls, kinds) = var_decls("variable (x)");
        let e = plan_annotation_update(&decls, vec![id("x")], BinderInfo::InstImplicit, &kinds)
            .expect_err("no type to annotate");
        assert_eq!(
            e.oracle_first_line().as_deref(),
            Some("cannot update binder annotation of variable `x` to instance implicit:")
        );
        // A typeless variable re-annotated to anything else is fine.
        let plan = plan_annotation_update(&decls, vec![id("x")], BinderInfo::Implicit, &kinds)
            .expect("typeless implicit update");
        assert_eq!(plan.new_decls.map(|d| d[0].bi), Some(BinderInfo::Implicit));
    }

    #[test]
    fn a_split_keeps_the_other_ids_in_place() {
        // `:387-402`: `(x y z : Nat)` + `{y}` → `(x)`, `{y}`, `(z)`.
        let (decls, kinds) = var_decls("variable (x y z : Nat)");
        let plan = plan_annotation_update(&decls, vec![id("y")], BinderInfo::Implicit, &kinds)
            .expect("update");
        let new = plan.new_decls.expect("modified");
        let got: Vec<_> = new.iter().map(|d| (d.only, d.bi)).collect();
        assert_eq!(
            got,
            vec![
                (Some(0), BinderInfo::Default),
                (Some(1), BinderInfo::Implicit),
                (Some(2), BinderInfo::Default),
            ]
        );
        assert_eq!(plan.residue, Some(Vec::new()));
        assert!(plan.inst_checks.is_empty());
    }

    #[test]
    fn unmatched_ids_are_the_residue() {
        // `:405-411`: some id matched, the rest come back.
        let (decls, kinds) = var_decls("variable (x : Nat)");
        let plan =
            plan_annotation_update(&decls, vec![id("x"), id("z")], BinderInfo::Implicit, &kinds)
                .expect("update");
        assert_eq!(plan.residue, Some(vec![id("z")]));
        // `:413`: nothing matched — the binder itself, scope untouched.
        let plan = plan_annotation_update(&decls, vec![id("z")], BinderInfo::Implicit, &kinds)
            .expect("no update");
        assert_eq!(plan.residue, None);
        assert!(plan.new_decls.is_none());
    }

    #[test]
    fn only_oracle_errors_become_the_inst_update_failure() {
        let wrapped = inst_update_error(
            ElabError::InvalidBinderAnnotation {
                ty: ExprId::from_index(0, false).expect("index 0"),
            },
            "x",
        );
        assert!(matches!(wrapped, ElabError::CannotUpdateToInstImplicit(ref s) if s == "x"));
        for e in [
            ElabError::UnsupportedSyntax("seam — later M4".into()),
            ElabError::Internal("boom".into()),
            ElabError::MaxRecDepth,
        ] {
            let want = format!("{e:?}");
            assert_eq!(format!("{:?}", inst_update_error(e, "x")), want);
        }
    }
}
