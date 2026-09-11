//! Binder elaborators, split by construct: `forall.rs` (`arrow`,
//! `forall`, `depArrow`), `fun.rs` (`fun`), `let_like.rs` (`let`/`have`).
//! This file holds what more than one of them shares: type elaboration,
//! bracketed-binder-group extraction and pushing, and binder-name
//! interning. Oracle: `Lean/Elab/Binders.lean`.

use leanr_kernel::bank::ExprId;
use leanr_kernel::bank::NameId;
use leanr_kernel::BinderInfo;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::NodeOrToken;
use leanr_syntax::tree::SyntaxNode;

use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;

mod forall;
mod fun;
mod let_like;

pub use forall::{elab_arrow, elab_dep_arrow, elab_forall};
pub use fun::elab_fun;
pub use let_like::elab_let_like;

/// oracle: `elabType t` = `elabTerm t (mkSort (mkLevelMVar u))` then
/// ensure-is-type. Here: a fresh level mvar `?u`, a `Sort ?u` expected
/// type, `elab_term`, and `ensure_type`. Returns the elaborated type expr.
pub(crate) fn elab_type(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let u = elab.mk_fresh_level_mvar()?;
    let sort = elab
        .mctx
        .store_mut()
        .expr_sort(None, u)
        .map_err(leanr_meta::MetaError::from)?;
    // oracle: `elabType stx = elabTerm stx (mkSort ?u)` then `ensureType`
    // (`TermElabM.lean:1951-1954`) — the second half is real since M4b-3
    // P4 task 9; before that `elab_term_ensuring_type`'s `isDefEq` stood
    // in for it, which is exact only while no domain can be coerced.
    let e = elab.elab_term(elem, kinds, Some(sort))?;
    elab.ensure_type(elem, e)
}

/// One bracketed binder group `(x y : T)` — its names, the shared type
/// syntax, and its binder-info. Plan 1: type is always present
/// (`extract_binder_group` errors on an empty binder-type).
pub(crate) struct BinderGroup {
    pub names: Vec<Option<NameId>>,
    pub ty: SynElem,
    pub bi: BinderInfo,
}

/// Map a bracketed-binder kind name to its `BinderInfo`. `instBinder`
/// (`[…]`) has a different child layout — optional name + bare type,
/// handled by `extract_binder_group`'s own `instBinder` branch (Task 3;
/// it calls the shared `extract_inst_binder_layout` helper rather than
/// walking that layout again here).
fn binder_info_of(kind: &str) -> Option<BinderInfo> {
    match kind {
        "Lean.Parser.Term.explicitBinder" => Some(BinderInfo::Default),
        "Lean.Parser.Term.implicitBinder" => Some(BinderInfo::Implicit),
        "Lean.Parser.Term.strictImplicitBinder" => Some(BinderInfo::StrictImplicit),
        "Lean.Parser.Term.instBinder" => Some(BinderInfo::InstImplicit),
        _ => None,
    }
}

/// Extract `(names, type-syntax, binder-info)` from a bracketed binder
/// group. Layout for explicit/implicit/strict (term.rs:134/152/160):
/// child `[1]` is the names `KIND_NULL` (each item a bare ident token or
/// a `_` hole node), child `[2]` is the binder-type `KIND_NULL`
/// (`[":", T]` when present). Names are interned best-effort from token
/// text (erased by the encoder, so exact form does not affect the gate).
pub(crate) fn extract_binder_group(
    elab: &mut TermElabM,
    group: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<BinderGroup, ElabError> {
    let kind = kinds.name(group.kind());
    let bi = binder_info_of(kind)
        .ok_or_else(|| ElabError::UnsupportedSyntax(format!("binder group: {kind}")))?;

    // `instBinder` (`[inst : C α]` / `[C α]`) has a layout of its own —
    // optional name + BARE type, not the `KIND_NULL`-wrapped names list
    // and `[":", T]` type slot the explicit/implicit/strict groups below
    // share. `extract_fun_binder_views` already walks this same spine for
    // `fun`'s own `instBinder` arm (Task 1); call that shared helper
    // rather than carrying a second copy of the walk here.
    if kind == "Lean.Parser.Term.instBinder" {
        let (name, ty) = extract_inst_binder_layout(elab, group, kinds)?;
        return Ok(BinderGroup {
            names: vec![name],
            ty,
            bi,
        });
    }

    let ch = non_trivia_children(group);
    let names_node = ch
        .get(1)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("binder group: names slot".into()))?;
    let type_node = ch
        .get(2)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("binder group: type slot".into()))?;
    let type_children = non_trivia_children(type_node);
    // `[":", T]`; an empty type slot is the untyped-bracketed form we defer.
    let ty = type_children
        .get(1)
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("binder group: missing `: T`".into()))?;

    // Collect the raw name texts first, then intern (avoids overlapping
    // borrows of the store while walking the tree).
    let name_texts: Vec<Option<String>> = non_trivia_children(names_node)
        .iter()
        .map(|el| match el {
            NodeOrToken::Token(tok) if kinds.name(tok.kind()) == "<ident>" => {
                Some(tok.text().to_string())
            }
            // `_` hole binder → anonymous
            _ => None,
        })
        .collect();

    // `base = Some(elab.view.store)`, NOT the brief's literal `None`
    // (Task 3 reconciliation): a binder name must intern to the exact
    // same `NameId` a later bare-identifier occurrence of the same text
    // resolves to (`app::head::intern_dotted`'s own convention, which
    // this mirrors) — the local-scope lookup `app::head::elab_ident_head`
    // performs (Task 3 addition, `elab.rs`) is a plain `NameId` equality check,
    // so a base mismatch here would silently make `(a : Type), a` fail
    // to find its own binder whenever `a`'s string already happens to
    // be interned in the persistent store under a different base path.
    // Binder names are still erased by the differential encoder, so
    // this has no effect on the oracle gate either way — but the code
    // must resolve correctly regardless.
    let base = elab.view.store;
    let mut names = Vec::with_capacity(name_texts.len());
    for t in name_texts {
        let id = match t {
            None => None,
            Some(text) => {
                let store = elab.mctx.store_mut();
                let s = store
                    .intern_str(Some(base), &text)
                    .map_err(leanr_meta::MetaError::from)?;
                let n = store
                    .name_str(Some(base), None, s)
                    .map_err(leanr_meta::MetaError::from)?;
                Some(n)
            }
        };
        names.push(id);
    }
    if names.is_empty() {
        return Err(ElabError::UnsupportedSyntax(
            "binder group: no names".into(),
        ));
    }
    Ok(BinderGroup { names, ty, bi })
}

/// Push one bracketed binder group's names into the local context,
/// returning their fvars in declaration order. The group's shared type
/// elaborates ONCE, before its own names enter scope (so `(x y : T)`
/// elaborates `T` in the context that excludes x and y) — the rule
/// `elabBinders` follows for a single `bracketedBinder` item. Shared by
/// `elab_binders_and_forall` (the `forall`/`depArrow` telescope) and
/// `push_let_binders` (the `let`/`have` telescope), which differ only in
/// what they do with the returned fvars (`mk_forall` vs. also
/// `mk_lambda`-ing a value).
fn push_binder_group(
    elab: &mut TermElabM,
    g: &BinderGroup,
    kinds: &KindInterner,
) -> Result<Vec<ExprId>, ElabError> {
    let dom = elab_type(elab, &g.ty, kinds)?;
    let mut fvars = Vec::with_capacity(g.names.len());
    for &name in &g.names {
        fvars.push(
            elab.mctx
                .push_local_decl(name, dom, g.bi)
                .map_err(ElabError::from)?,
        );
    }
    Ok(fvars)
}

/// A fresh type metavariable `?α : Sort ?u` — the elided-binder domain
/// (oracle: `mkFreshTypeMVar`). Mirrors `elab_type`'s `Sort ?u`
/// construction (fresh level mvar, `expr_sort(None, u)`), then mints a
/// fresh expr mvar of that sort. The mvar is never assigned unless a
/// later `is_def_eq` unifies it (e.g. an enclosing ascription), in which
/// case `instantiate_mvars` fills it in; otherwise it surfaces as a bare
/// `mvar`, exactly like an M4b-1 `_` hole.
fn fresh_type_mvar(elab: &mut TermElabM) -> Result<ExprId, ElabError> {
    let u = elab.mk_fresh_level_mvar()?;
    let sort = elab
        .mctx
        .store_mut()
        .expr_sort(None, u)
        .map_err(leanr_meta::MetaError::from)?;
    elab.mk_fresh_expr_mvar(sort)
}

/// Intern a binder name from token text, `base = Some(view.store)` — the
/// same convention `extract_binder_group` uses, so a body occurrence of
/// the name resolves to this binder via `lctx_lookup_by_name` (a plain
/// `NameId` equality check). Binder names are erased by the differential
/// encoder, so this never affects the gate, but the code must resolve.
fn intern_binder_name(elab: &mut TermElabM, text: &str) -> Result<NameId, ElabError> {
    let base = elab.view.store;
    let store = elab.mctx.store_mut();
    let s = store
        .intern_str(Some(base), text)
        .map_err(leanr_meta::MetaError::from)?;
    let n = store
        .name_str(Some(base), None, s)
        .map_err(leanr_meta::MetaError::from)?;
    Ok(n)
}

/// The `instBinder` child layout `["[", optIdent(null), T, "]"]`: an
/// OPTIONAL name at child `[1]` (null-wrapped) and a BARE type at child
/// `[2]` — unlike the explicit/implicit/strict groups, whose type slot
/// is a `KIND_NULL` wrapper holding `[":", T]`. Shared by
/// `extract_fun_binder_views`'s `instBinder` arm and `extract_binder_group`
/// (Task 3), so named without a `fun`-specific reading. oracle:
/// `toBinderViews`'s `instBinder` arm, `Binders.lean:161-165` (verified
/// against the pinned toolchain — a plan-inherited citation once pointed
/// at `:450-453`, which is inside the unrelated `elabFunBinderViews`).
fn extract_inst_binder_layout(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<(Option<NameId>, SynElem), ElabError> {
    let ch = non_trivia_children(node);
    let name = match ch.get(1).and_then(|el| el.as_node()) {
        Some(opt) => match non_trivia_children(opt).first() {
            Some(el) => intern_fun_binder_ident(elab, el, kinds)?,
            None => None,
        },
        None => None,
    };
    let ty = ch
        .get(2)
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("inst binder: type slot".into()))?;
    Ok((name, ty))
}

/// A binder identifier is either an `<ident>` token or a `_` hole node
/// (`binderIdent`). A hole binds an anonymous local. oracle:
/// `expandBinderIdent` (`Binders.lean:32-36`).
fn intern_fun_binder_ident(
    elab: &mut TermElabM,
    el: &SynElem,
    kinds: &KindInterner,
) -> Result<Option<NameId>, ElabError> {
    match el {
        NodeOrToken::Token(tok) if kinds.name(tok.kind()) == "<ident>" => {
            Ok(Some(intern_binder_name(elab, tok.text())?))
        }
        NodeOrToken::Node(n) if kinds.name(n.kind()) == "Lean.Parser.Term.hole" => Ok(None),
        // Named without a `fun`-specific reading: `extract_binder_group`
        // (Task 3) reaches this through `extract_inst_binder_layout` for
        // `forall`/`let`/`have` too, so a message hardcoding "fun" would
        // misreport the owning construct on failure.
        _ => Err(ElabError::UnsupportedSyntax(format!(
            "binder identifier: {}",
            kinds.name(el.kind())
        ))),
    }
}
