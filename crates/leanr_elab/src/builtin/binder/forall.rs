//! The universal-quantifier type formers: `arrow` (non-dependent, no
//! fvar), `forall` and `depArrow` (a binder telescope abstracted with
//! `MetaCtx::mk_forall`). Oracle: `elabArrow`/`elabForall`/`elabDepArrow`
//! (`Lean/Elab/Binders.lean:293/278/310`).

use leanr_kernel::bank::ExprId;
use leanr_kernel::BinderInfo;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

use super::{elab_type, extract_binder_group, push_binder_group, BinderGroup};
use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `elabArrow` (Binders.lean:293). `A -> B`: elaborate `A` and
/// `B` independently as types, build the NON-dependent `forallE` — the
/// body `B` refers to no binder, so no fvar/abstraction is needed. The
/// binder name is anonymous (`None`); it is erased by the encoder anyway.
/// Trailing-node children (parse.rs:3 — "Pratt trailing wrap inserts
/// Start at the lhs event index", so the LHS is wrapped in): `[A, ->, B]`.
pub fn elab_arrow(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let children = non_trivia_children(node);
    let dom_elem = children
        .first()
        .ok_or_else(|| ElabError::UnsupportedSyntax("arrow: missing domain".into()))?;
    let rng_elem = children
        .get(2)
        .ok_or_else(|| ElabError::UnsupportedSyntax("arrow: missing range".into()))?;
    let dom = elab_type(elab, dom_elem, kinds)?;
    let rng = elab_type(elab, rng_elem, kinds)?;
    // `base = Some(elab.view.store)`, bound before `store_mut()` — the
    // same convention as `ident.rs:74` (disjoint-field borrow, and the
    // persistent store is the dedup base for anything a child may
    // reference). Binder name `None`: erased by the encoder.
    let base = elab.view.store;
    let e = elab
        .mctx
        .store_mut()
        .expr_forall(Some(base), None, dom, rng, BinderInfo::Default)
        .map_err(leanr_meta::MetaError::from)?;
    Ok(e)
}

/// Shared telescope driver: push every group's binders via
/// `push_binder_group`, elaborate `body_elem` as a type under the full
/// telescope, and `mk_forall` over all collected fvars. Reused by both
/// `elab_forall` and `elab_dep_arrow` (Task 4). oracle: `elabBinders …
/// fun xs => mkForallFVars xs (← elabType body)`.
pub(crate) fn elab_binders_and_forall(
    elab: &mut TermElabM,
    groups: &[BinderGroup],
    body_elem: &SynElem,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    // Bracket the whole telescope: restore `lctx` on EVERY exit path (Ok
    // or Err) — a failed body elaboration must not leak fvars into the
    // ambient context. `MetaCtx::lctx_restore` (Task 3 addition, see
    // `leanr_meta`'s own `local_names` field doc) also truncates the
    // by-user-name index in lockstep, so this single checkpoint now
    // covers both id-based (`lctx`) and name-based (`lctx_lookup_by_name`,
    // consulted by `app::head::elab_ident_head`) lookups — no second
    // checkpoint needed.
    let checkpoint = elab.mctx.lctx_checkpoint();
    let result = (|| {
        let mut fvars: Vec<ExprId> = Vec::new();
        for g in groups {
            fvars.extend(push_binder_group(elab, g, kinds)?);
        }
        let body = elab_type(elab, body_elem, kinds)?;
        elab.mctx.mk_forall(&fvars, body).map_err(ElabError::from)
    })();
    elab.mctx.lctx_restore(checkpoint);
    result
}

/// oracle: `elabForall` (Binders.lean:278), bracketed-binder path (no
/// `expandForall` macro — that fires only on the trailing `: ty` form).
/// forall children (term.rs:410): `[∀atom, binderList(KIND_NULL), optType,
/// ",", body]`. Plan 1 handles bracketed binder items only.
pub fn elab_forall(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let ch = non_trivia_children(node);
    let binder_list = ch
        .get(1)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("forall: binder list".into()))?;
    // Plan 1: reject the trailing construct-level `optType` (bare-ident
    // form via `expandForall`) — child [2], non-empty → deferred.
    if let Some(opt) = ch.get(2).and_then(|el| el.as_node()) {
        if !non_trivia_children(opt).is_empty() {
            return Err(ElabError::UnsupportedSyntax(
                "forall: trailing `: ty` (expandForall macro)".into(),
            ));
        }
    }
    let body_elem = ch
        .last()
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("forall: body".into()))?;

    let mut groups = Vec::new();
    for item in non_trivia_children(binder_list) {
        match item.as_node() {
            Some(item_node) => groups.push(extract_binder_group(elab, item_node, kinds)?),
            // A bare ident/hole binder item (no brackets) → expandForall
            // territory, deferred.
            None => {
                return Err(ElabError::UnsupportedSyntax(
                    "forall: bare-ident binder (expandForall macro)".into(),
                ))
            }
        }
    }
    elab_binders_and_forall(elab, &groups, &body_elem, kinds)
}

/// oracle: `elabDepArrow` (Binders.lean:310). depArrow children
/// (term.rs:1103): `[bracketedBinder, "->", body]` — always exactly one
/// bracketed binder with a mandatory type (`require_type = true`).
/// Dependent: the body may reference the binder, so it goes through the
/// full `push_binder_group` → `push_user_binder` (carrying the
/// `.ofBinderName` kind) + `mk_forall` telescope, unlike `arrow`.
pub fn elab_dep_arrow(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let ch = non_trivia_children(node);
    let binder_node = ch
        .first()
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("depArrow: binder".into()))?;
    let body_elem = ch
        .get(2)
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("depArrow: body".into()))?;
    let group = extract_binder_group(elab, binder_node, kinds)?;
    elab_binders_and_forall(elab, &[group], &body_elem, kinds)
}
