//! Binder elaborators. M4b-2 plan 1: the three universal-quantifier
//! type-former kinds — `forall`, `arrow`, `depArrow`. `arrow` is
//! non-dependent (no fvar); `forall`/`depArrow` introduce fvars via
//! `MetaCtx::push_local_decl` and abstract via `MetaCtx::mk_forall`
//! (Task 1). Oracle: `elabForall`/`elabArrow`/`elabDepArrow`
//! (Lean/Elab/Binders.lean:278/293/310).

use leanr_kernel::bank::ExprId;
use leanr_kernel::bank::NameId;
use leanr_kernel::BinderInfo;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::NodeOrToken;
use leanr_syntax::tree::SyntaxNode;

use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `elabType t` = `elabTerm t (mkSort (mkLevelMVar u))` then
/// ensure-is-type. Here: a fresh level mvar `?u`, a `Sort ?u` expected
/// type, and `elab_term_ensuring_type` (which drives `is_def_eq` between
/// the inferred type and `Sort ?u`). Returns the elaborated type expr.
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
    elab.elab_term_ensuring_type(elem, kinds, Some(sort))
}

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

/// One bracketed binder group `(x y : T)` — its names, the shared type
/// syntax, and its binder-info. Plan 1: type is always present
/// (`extract_binder_group` errors on an empty binder-type).
pub(crate) struct BinderGroup {
    pub names: Vec<Option<NameId>>,
    pub ty: SynElem,
    pub bi: BinderInfo,
}

/// Map a bracketed-binder kind name to its `BinderInfo`. `instBinder`
/// (`[…]`, a different child layout — optional name + bare type) is not
/// used by any Plan-1 corpus term and is deferred to M4b-3 (instance
/// args); it returns `None` here so the caller names the seam.
fn binder_info_of(kind: &str) -> Option<BinderInfo> {
    match kind {
        "Lean.Parser.Term.explicitBinder" => Some(BinderInfo::Default),
        "Lean.Parser.Term.implicitBinder" => Some(BinderInfo::Implicit),
        "Lean.Parser.Term.strictImplicitBinder" => Some(BinderInfo::StrictImplicit),
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
    // resolves to (`ident.rs::intern_dotted`'s own convention, which
    // this mirrors) — the local-scope lookup `elab_ident` performs
    // (Task 3 addition, `elab.rs`) is a plain `NameId` equality check,
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

/// Shared telescope driver: elaborate each group's type once (in the
/// context BEFORE that group's names), introduce one fvar per name via
/// `push_local_decl`, elaborate `body_elem` as a type under the full
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
    // consulted by `elab_ident`) lookups — no second checkpoint needed.
    let checkpoint = elab.mctx.lctx_checkpoint();
    let result = (|| {
        let mut fvars: Vec<ExprId> = Vec::new();
        for g in groups {
            // Elaborate the group's shared type ONCE, before its own
            // names enter scope (so `(x y : T)` elaborates `T` in the
            // context that excludes x and y).
            let dom = elab_type(elab, &g.ty, kinds)?;
            for &name in &g.names {
                let fvar = elab
                    .mctx
                    .push_local_decl(name, dom, g.bi)
                    .map_err(ElabError::from)?;
                fvars.push(fvar);
            }
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
/// full `push_local_decl` + `mk_forall` telescope, unlike `arrow`.
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

/// Extract `(binder_name, optional-type-syntax)` from one `funBinder`.
/// M4b-2 handles a bare ident token (elided type → `None`) and a
/// single-name parenthesised binder `(x : T)`, which the grammar parses
/// as a `Term.typeAscription` node (probe-confirmed), NOT an
/// `explicitBinder`. Named seams (→ `UnsupportedSyntax`): implicit /
/// strict / instance binder nodes, a paren binder whose leading child is
/// not a lone ident (`(x y : T)` / `(f a : T)`), and a paren binder with
/// no type slot.
fn extract_fun_binder(
    elab: &mut TermElabM,
    item: &SynElem,
    kinds: &KindInterner,
) -> Result<(Option<NameId>, Option<SynElem>), ElabError> {
    match item {
        // Bare ident binder: `fun x => …` — elided type.
        NodeOrToken::Token(tok) if kinds.name(tok.kind()) == "<ident>" => {
            let name = intern_binder_name(elab, tok.text())?;
            Ok((Some(name), None))
        }
        // Parenthesised binder `(x : T)` — a typeAscription node with
        // children [hygienicLParen, name, ":", null[T], ")"].
        NodeOrToken::Node(n) if kinds.name(n.kind()) == "Lean.Parser.Term.typeAscription" => {
            let tch = non_trivia_children(n);
            let name_tok = tch
                .get(1)
                .and_then(|el| el.as_token())
                .filter(|t| kinds.name(t.kind()) == "<ident>")
                .ok_or_else(|| {
                    ElabError::UnsupportedSyntax(
                        "fun: paren binder is not a single ident (M4b-3)".into(),
                    )
                })?;
            let name = intern_binder_name(elab, name_tok.text())?;
            let ty_null = tch
                .get(3)
                .and_then(|el| el.as_node())
                .ok_or_else(|| ElabError::UnsupportedSyntax("fun: binder type slot".into()))?;
            let ty_elem = non_trivia_children(ty_null)
                .into_iter()
                .next()
                .ok_or_else(|| {
                    ElabError::UnsupportedSyntax("fun: paren binder without a type (M4b-3)".into())
                })?;
            Ok((Some(name), Some(ty_elem)))
        }
        _ => Err(ElabError::UnsupportedSyntax(format!(
            "fun: unsupported binder kind {}",
            kinds.name(item.kind())
        ))),
    }
}

/// oracle: `elabFun` (Binders.lean:678) → `elabFunBinders`, `basicFun`
/// arm only. M4b-2: no scheduler, and the expected type is NOT consumed
/// here (see the plan's § Task 2 design note) — an elided binder's domain
/// is a fresh type mvar unified by the outer `elab_term_ensuring_type`.
/// Named seams: the `matchAlts` (pattern) arm, `optType`
/// (`fun x : T => e`), and the funBinder forms `extract_fun_binder`
/// rejects.
///
/// `Term.fun` children: `[("λ"|"fun"), (basicFun | matchAlts)]`.
/// `Term.basicFun` children: `[binderList(null), optType(null),
/// ("↦"|"=>"), body]`.
pub fn elab_fun(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let ch = non_trivia_children(node);
    let basic = ch
        .get(1)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("fun: body node".into()))?;
    let basic_kind = kinds.name(basic.kind());
    if basic_kind != "Lean.Parser.Term.basicFun" {
        // The `matchAlts` (pattern-matching `fun`) arm → match slice (M4b-4).
        return Err(ElabError::UnsupportedSyntax(format!("fun: {basic_kind}")));
    }
    let bch = non_trivia_children(basic);
    let binder_list = bch
        .first()
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("fun: binder list".into()))?;
    // `optType` (`fun x : T => e`) → named seam (M4b-3). Child [1] is the
    // null-wrapped optional; a non-empty wrapper means a return type was
    // written.
    if let Some(opt) = bch.get(1).and_then(|el| el.as_node()) {
        if !non_trivia_children(opt).is_empty() {
            return Err(ElabError::UnsupportedSyntax(
                "fun: return-type optType (M4b-3)".into(),
            ));
        }
    }
    let body_elem = bch
        .get(3)
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("fun: body".into()))?;

    let items = non_trivia_children(binder_list);
    if items.is_empty() {
        return Err(ElabError::UnsupportedSyntax("fun: no binders".into()));
    }

    // Bracket the telescope: restore `lctx` on EVERY exit path (Ok or
    // Err), exactly as `elab_binders_and_forall` does.
    let checkpoint = elab.mctx.lctx_checkpoint();
    let result = (|| {
        let mut fvars: Vec<ExprId> = Vec::new();
        for item in &items {
            let (name, ty_syntax) = extract_fun_binder(elab, item, kinds)?;
            let dom = match ty_syntax {
                Some(ty_elem) => elab_type(elab, &ty_elem, kinds)?,
                None => fresh_type_mvar(elab)?,
            };
            let fvar = elab
                .mctx
                .push_local_decl(name, dom, BinderInfo::Default)
                .map_err(ElabError::from)?;
            fvars.push(fvar);
        }
        // Body with expected `None` (see § Task 2 design note).
        let body = elab.elab_term(&body_elem, kinds, None)?;
        elab.mctx.mk_lambda(&fvars, body).map_err(ElabError::from)
    })();
    elab.mctx.lctx_restore(checkpoint);
    result
}
