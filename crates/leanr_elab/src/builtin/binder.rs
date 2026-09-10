//! Binder elaborators. M4b-2 plan 1: the three universal-quantifier
//! type-former kinds — `forall`, `arrow`, `depArrow`. `arrow` is
//! non-dependent (no fvar); `forall`/`depArrow` introduce fvars via
//! `MetaCtx::push_local_decl` and abstract via `MetaCtx::mk_forall`
//! (Task 1). Oracle: `elabForall`/`elabArrow`/`elabDepArrow`
//! (Lean/Elab/Binders.lean:278/293/310).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::bank::NameId;
use leanr_kernel::BinderInfo;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::NodeOrToken;
use leanr_syntax::tree::SyntaxNode;

use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::synthetic::PostponeBehavior;

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

/// oracle: `Expr.cleanupAnnotations` (`Lean/Expr.lean:1748-1756`) —
/// `e.consumeMData.consumeTypeAnnotations`, looped to a fixpoint:
///
/// ```lean
/// partial def cleanupAnnotations (e : Expr) : Expr :=
///   let e' := e.consumeMData.consumeTypeAnnotations
///   if e' == e then e else cleanupAnnotations e'
/// ```
///
/// Ported directly here rather than reused: `AppElab::consume_type_annotations`
/// (`app/state.rs`) is the closest in-repo equivalent, but it only
/// covers the `consumeTypeAnnotations` half (its own doc already names
/// the `consumeMData` half as unmodelled), and it is an inherent method
/// on `AppElab`, which bundles a `Context`/`State` this telescope has no
/// use for and would be wrong to construct just to reach one helper. No
/// `MetaCtx` accessor for either half exists (checked before adding
/// this), and none is needed: `Node::MData`/`Node::App`/`Node::Const`
/// are already public kernel API, so this stays self-contained in
/// `leanr_elab` — no `leanr_meta` addition, and so no ledger amendment.
fn cleanup_annotations(elab: &TermElabM, e: ExprId) -> ExprId {
    let base = Some(elab.view.store);
    let mut cur = e;
    loop {
        let start = cur;
        while let Node::MData { expr, .. } = elab.mctx.store().expr_node(base, cur) {
            cur = expr;
        }
        if let Some(inner) = strip_one_type_annotation(elab, cur) {
            cur = inner;
        }
        if cur == start {
            return cur;
        }
    }
}

/// One step of `Expr.consumeTypeAnnotations` (`Lean/Expr.lean:1739-1745`)
/// — all FOUR gadgets: `optParam`/`autoParam` (arity 2, keep the first
/// argument) and `outParam`/`semiOutParam` (arity 1, keep the only
/// argument). Mirrors `AppElab::type_annotation_at_head`'s idiom
/// (`app/state.rs`) — walk the application spine to the head `Const`,
/// render its name, and match on `(name, arity)`.
fn strip_one_type_annotation(elab: &TermElabM, e: ExprId) -> Option<ExprId> {
    let base = Some(elab.view.store);
    let mut args = Vec::new();
    let mut cur = e;
    while let Node::App { f, arg } = elab.mctx.store().expr_node(base, cur) {
        args.push(arg);
        cur = f;
    }
    args.reverse();
    let Node::Const { name: Some(n), .. } = elab.mctx.store().expr_node(base, cur) else {
        return None;
    };
    let name = elab.mctx.store().to_name(base, Some(n)).to_string();
    match (name.as_str(), args.len()) {
        ("optParam" | "autoParam", 2) => Some(args[0]),
        ("outParam" | "semiOutParam", 1) => Some(args[0]),
        _ => None,
    }
}

/// oracle: `FunBinders.propagateExpectedType` (`Binders.lean:410-421`).
///
/// Runs once per binder, inside the telescope loop, AFTER the binder's
/// fvar exists and BEFORE the next binder's type elaborates. Returns the
/// residual expected type for the next iteration (and, at the end, for
/// the body).
///
/// Three details the oracle pins and this port keeps:
///   * `discard <| isDefEq` — a FAILED unification is not an error and
///     does not stop the walk. Only a `MetaError` propagates; a `false`
///     result is silently dropped, leaving `fvar_type` unassigned.
///   * the non-`forallE` arm returns `none`, dropping the expected type
///     rather than keeping the previous one.
///   * `whnfForall` keeps the ORIGINAL term when the reduct is not a
///     forall; only the `forallE` test reads it, so reducing into a
///     local (`whnf`, not `whnf_forall`) is enough — the non-forall arm
///     never reads `expected` again either way.
fn propagate_expected_type(
    elab: &mut TermElabM,
    fvar: ExprId,
    fvar_type: ExprId,
    expected: Option<ExprId>,
) -> Result<Option<ExprId>, ElabError> {
    let Some(expected) = expected else {
        return Ok(None);
    };
    let reduced = elab.mctx.whnf(expected)?;
    let base = elab.view.store;
    let Node::Forall {
        binder_type, body, ..
    } = elab.mctx.store().expr_node(Some(base), reduced)
    else {
        return Ok(None);
    };
    // oracle: `discard <| isDefEq fvarType d.cleanupAnnotations`. The
    // BOOL is discarded; a MetaError still propagates.
    let domain = cleanup_annotations(elab, binder_type);
    let _ = elab.mctx.is_def_eq(fvar_type, domain)?;
    let rest = elab.mctx.instantiate_beta_rev_range(body, &[fvar])?;
    Ok(Some(rest))
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

/// One elaborated-binder view: the oracle's `BinderView`
/// (`Lean/Elab/Binders.lean`, `toBinderViews` at `:436`). A single
/// `funBinder` item can expand to SEVERAL views — `{a b : Type}` binds
/// two names sharing one type syntax.
struct FunBinderView {
    name: Option<NameId>,
    ty: Option<SynElem>,
    bi: BinderInfo,
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

/// Move of the old `extract_fun_binder`'s `typeAscription` arm: a
/// parenthesised single-name binder `(x : T)`, which the grammar parses
/// as a `Term.typeAscription` node (probe-confirmed), NOT an
/// `explicitBinder`. Named seams (→ `UnsupportedSyntax`): a leading
/// child that is not a lone ident (`(x y : T)` / `(f a : T)`), and a
/// paren binder with no type slot.
fn extract_paren_fun_binder(
    elab: &mut TermElabM,
    n: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<(NameId, SynElem), ElabError> {
    let tch = non_trivia_children(n);
    let name_tok = tch
        .get(1)
        .and_then(|el| el.as_token())
        .filter(|t| kinds.name(t.kind()) == "<ident>")
        .ok_or_else(|| {
            ElabError::UnsupportedSyntax("fun: paren binder is not a single ident (M4b-3)".into())
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
    Ok((name, ty_elem))
}

/// oracle: `toBinderViews` (`Binders.lean:140-166`), restricted to the
/// four `funBinder` alternatives (`Parser/Term.lean:379-381`). (Verified
/// against the pinned toolchain — a plan-inherited citation once pointed
/// at `:436-455`, which is inside the unrelated `elabFunBinderViews`.)
///
/// Unlike the `forall`/`let` telescope, a `fun` binder's type may be
/// ABSENT (`fun {a} => …`), so this tolerates an empty binder-type slot
/// where `extract_binder_group` errors.
fn extract_fun_binder_views(
    elab: &mut TermElabM,
    item: &SynElem,
    kinds: &KindInterner,
) -> Result<Vec<FunBinderView>, ElabError> {
    match item {
        // Bare ident binder: `fun x => …` — elided type.
        NodeOrToken::Token(tok) if kinds.name(tok.kind()) == "<ident>" => {
            let name = intern_binder_name(elab, tok.text())?;
            Ok(vec![FunBinderView {
                name: Some(name),
                ty: None,
                bi: BinderInfo::Default,
            }])
        }
        NodeOrToken::Node(n) => {
            let kind = kinds.name(n.kind());
            match kind {
                // Parenthesised binder `(x : T)` — the `termParser
                // maxPrec` alternative, parsed as a typeAscription.
                "Lean.Parser.Term.typeAscription" => {
                    let (name, ty) = extract_paren_fun_binder(elab, n, kinds)?;
                    Ok(vec![FunBinderView {
                        name: Some(name),
                        ty: Some(ty),
                        bi: BinderInfo::Default,
                    }])
                }
                // `{a b : T}` / `{a b}` and `⦃a b : T⦄` / `⦃a b⦄`.
                "Lean.Parser.Term.implicitBinder" | "Lean.Parser.Term.strictImplicitBinder" => {
                    let bi = if kind == "Lean.Parser.Term.implicitBinder" {
                        BinderInfo::Implicit
                    } else {
                        BinderInfo::StrictImplicit
                    };
                    let ch = non_trivia_children(n);
                    let names_null = ch.get(1).and_then(|el| el.as_node()).ok_or_else(|| {
                        ElabError::UnsupportedSyntax("fun binder group: names slot".into())
                    })?;
                    let ty_null = ch.get(2).and_then(|el| el.as_node()).ok_or_else(|| {
                        ElabError::UnsupportedSyntax("fun binder group: type slot".into())
                    })?;
                    // `[":", T]` when a type was written; empty otherwise.
                    let ty = non_trivia_children(ty_null).into_iter().nth(1);
                    let mut views = Vec::new();
                    for name_el in non_trivia_children(names_null) {
                        let name = intern_fun_binder_ident(elab, &name_el, kinds)?;
                        views.push(FunBinderView {
                            name,
                            ty: ty.clone(),
                            bi,
                        });
                    }
                    if views.is_empty() {
                        return Err(ElabError::UnsupportedSyntax(
                            "fun binder group: no names".into(),
                        ));
                    }
                    Ok(views)
                }
                // `[inst : C α]` / `[C α]` — optional name, BARE type at
                // child [2] (no `KIND_NULL` wrapper, unlike the groups
                // above). oracle: `Binders.lean:450-453`.
                "Lean.Parser.Term.instBinder" => {
                    let (name, ty) = extract_inst_binder_layout(elab, n, kinds)?;
                    Ok(vec![FunBinderView {
                        name,
                        ty: Some(ty),
                        bi: BinderInfo::InstImplicit,
                    }])
                }
                _ => Err(ElabError::UnsupportedSyntax(format!(
                    "fun: unsupported binder kind {kind}"
                ))),
            }
        }
        _ => Err(ElabError::UnsupportedSyntax(format!(
            "fun: unsupported binder kind {}",
            kinds.name(item.kind())
        ))),
    }
}

/// oracle: `elabFun` (Binders.lean:678) → `elabFunBinders`, `basicFun`
/// arm only. `optType` (`fun x : T => e`) ascribes the BODY under the
/// telescope (M4b-3 P5 task 2 — the `expandFun` macro rewrites
/// `fun bs : T => e` to `fun bs => (e : T)`). `expected` (M4b-3 P5 task
/// 4) threads `FunBinders.propagateExpectedType` per binder: each
/// elided binder's fresh domain mvar gets unified against the running
/// residual's forall domain, and `optType`, when present, WINS over the
/// final residual for the body (the oracle's `expandFun` rewrite makes
/// the ascription the body's own expected type; `expected` only ever
/// reaches the binders here). Named seams: the `matchAlts` (pattern) arm
/// and the funBinder forms `extract_fun_binder_views` rejects.
///
/// `Term.fun` children: `[("λ"|"fun"), (basicFun | matchAlts)]`.
/// `Term.basicFun` children: `[binderList(null), optType(null),
/// ("↦"|"=>"), body]`.
pub fn elab_fun(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
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
    // `optType` (`fun x : T => e`, `basicFun`, `Parser/Term.lean:384`).
    // Child [1] is the null-wrapped optional. oracle: `optType :=
    // optional typeSpec` (`Lean/Parser/Term/Basic.lean:265`) where
    // `typeSpec := " : " >> termParser` (`:262`) — a NAMED sub-parser, not
    // an inline `":" >> term` pair, so a non-empty wrapper holds ONE
    // `Lean.Parser.Term.typeSpec` node whose OWN children are `[":", T]`
    // — the same layout `push_let_binders`' `optType` unwrap already
    // accounts for (`binder.rs`, around `let: optType slot`). Verified
    // against the pinned toolchain source after a flat `nth(1)` read
    // directly off the wrapper silently produced `None` for every
    // `fun x : T => e` here — no error, no wrong term, just the
    // ascription dropped (`fun_opt_type_actually_ascribes_not_just_parses`
    // in `binder_smoke.rs` pins the regression).
    // oracle: the `expandFun` macro rewrites `fun bs : T => e` to
    // `fun bs => (e : T)`, so `T` ascribes the BODY, under the binders.
    let opt_type_null = bch
        .get(1)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("fun: optType slot".into()))?;
    let opt_type = match non_trivia_children(opt_type_null)
        .first()
        .and_then(|el| el.as_node())
    {
        Some(spec) => {
            let spec_kind = kinds.name(spec.kind());
            if spec_kind != "Lean.Parser.Term.typeSpec" {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "fun: optType {spec_kind}"
                )));
            }
            Some(
                non_trivia_children(spec)
                    .get(1)
                    .cloned()
                    .ok_or_else(|| ElabError::UnsupportedSyntax("fun: typeSpec type".into()))?,
            )
        }
        None => None,
    };
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
        // oracle: `FunBinders.propagateExpectedType` runs once per
        // binder, threading the RESIDUAL expected type from one to the
        // next (M4b-3 P5 task 4).
        let mut residual = expected;
        for item in &items {
            for view in extract_fun_binder_views(elab, item, kinds)? {
                let dom = match &view.ty {
                    Some(ty_elem) => elab_type(elab, ty_elem, kinds)?,
                    None => fresh_type_mvar(elab)?,
                };
                // `push_local_decl` installs a local instance when `dom`
                // is class-typed — keyed on the TYPE, not on `view.bi`,
                // exactly as the oracle's `isClass? type` test is
                // (`Binders.lean:445`). Nothing further is needed here.
                let fvar = elab
                    .mctx
                    .push_local_decl(view.name, dom, view.bi)
                    .map_err(ElabError::from)?;
                residual = propagate_expected_type(elab, fvar, dom, residual)?;
                fvars.push(fvar);
            }
        }
        // The optType elaborates INSIDE the telescope: it may mention
        // the binders (`fun (a : Type) (x : a) : a => x`). It WINS over
        // the propagated residual when both are present — the oracle's
        // `expandFun` macro turns `fun bs : T => e` into `fun bs => (e :
        // T)`, so an explicit ascription is what `elabTermEnsuringType`
        // sees for the body, not whatever `expected` propagated down to.
        let expected_body = match &opt_type {
            Some(ty_elem) => Some(elab_type(elab, ty_elem, kinds)?),
            None => residual,
        };
        let body = match expected_body {
            Some(t) => elab.elab_term_ensuring_type(&body_elem, kinds, Some(t))?,
            None => elab.elab_term(&body_elem, kinds, None)?,
        };
        elab.mctx.mk_lambda(&fvars, body).map_err(ElabError::from)
    })();
    elab.mctx.lctx_restore(checkpoint);
    result
}

/// Extract the binder name from a `Term.letId` node. Three
/// probe-confirmed shapes: a bare `<ident>` token (`let x := …`); a
/// `Term.hole` node (`let _ := …`) → anonymous; a `hygieneInfo` node
/// (`have : T := v; …`), which the oracle names `this`
/// (`mkLetIdDeclView`: `HygieneInfo.mkIdent letId[0] `this`).
///
/// leanr has no macro-scope hygiene, so the `this` minted here resolves
/// to a body occurrence of `this` by plain `NameId` equality — correct
/// for every non-shadowing term, a stated simplification of the design
/// spec (§ Plan 3 — canonical, "Stated simplification: hygiene").
fn extract_let_id_name(
    elab: &mut TermElabM,
    let_id: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<Option<NameId>, ElabError> {
    let ch = non_trivia_children(let_id);
    let first = ch
        .first()
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: empty letId".into()))?;
    match first {
        NodeOrToken::Token(tok) if kinds.name(tok.kind()) == "<ident>" => {
            Ok(Some(intern_binder_name(elab, tok.text())?))
        }
        NodeOrToken::Node(n) => match kinds.name(n.kind()) {
            "Lean.Parser.Term.hole" => Ok(None),
            "hygieneInfo" => Ok(Some(intern_binder_name(elab, "this")?)),
            other => Err(ElabError::UnsupportedSyntax(format!("let: letId {other}"))),
        },
        _ => Err(ElabError::UnsupportedSyntax("let: letId shape".into())),
    }
}

/// Push the `letIdBinders` telescope (`let f (y : Nat) : Nat := …`) into
/// the local context, returning its fvars in declaration order. Each
/// item is either a bracketed binder group (plan 1's
/// `extract_binder_group`, pushed via the shared `push_binder_group`), a
/// bare ident (`let f y := …`), or a `_` hole (`let f _ : Nat := …`)
/// whose domain is a fresh type mvar unified at the value's use site —
/// exactly plan 2's elided-`fun`-binder treatment, with the hole arm the
/// anonymous twin of the bare-ident arm (`letIdBinder := binderIdent <|>
/// bracketedBinder`, `binderIdent = Ident <|> hole`).
///
/// Named seams (→ `UnsupportedSyntax`): implicit / strict-implicit /
/// instance bracketed binders (M4b-3, which brings implicit and
/// instance arguments), and any other item shape.
///
/// The CALLER owns the `lctx_checkpoint`/`lctx_restore` bracket.
fn push_let_binders(
    elab: &mut TermElabM,
    items: &[SynElem],
    kinds: &KindInterner,
) -> Result<Vec<ExprId>, ElabError> {
    let mut fvars: Vec<ExprId> = Vec::new();
    for item in items {
        match item {
            // `_` hole binder (`let f _ : Nat := …`) → anonymous, a
            // fresh type mvar domain. Must come before the general
            // `Node` arm below, which would otherwise hand it to
            // `extract_binder_group` and misreport it as an unsupported
            // bracketed-binder kind.
            NodeOrToken::Node(n) if kinds.name(n.kind()) == "Lean.Parser.Term.hole" => {
                let dom = fresh_type_mvar(elab)?;
                let fvar = elab
                    .mctx
                    .push_local_decl(None, dom, BinderInfo::Default)
                    .map_err(ElabError::from)?;
                fvars.push(fvar);
            }
            NodeOrToken::Node(n) => {
                let g = extract_binder_group(elab, n, kinds)?;
                if !matches!(g.bi, BinderInfo::Default) {
                    return Err(ElabError::UnsupportedSyntax(
                        "let: implicit/strict/instance binder (M4b-3)".into(),
                    ));
                }
                fvars.extend(push_binder_group(elab, &g, kinds)?);
            }
            NodeOrToken::Token(tok) if kinds.name(tok.kind()) == "<ident>" => {
                let name = intern_binder_name(elab, tok.text())?;
                let dom = fresh_type_mvar(elab)?;
                let fvar = elab
                    .mctx
                    .push_local_decl(Some(name), dom, BinderInfo::Default)
                    .map_err(ElabError::from)?;
                fvars.push(fvar);
            }
            _ => {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "let: unsupported binder kind {}",
                    kinds.name(item.kind())
                )))
            }
        }
    }
    Ok(fvars)
}

/// oracle: `elabLetDeclCore` (Binders.lean:891) → `elabLetDeclAux`
/// (:745), the `letIdDecl` alternative. ONE elaborator for both forms:
/// `Lean.Parser.Term.let` passes `non_dep = false` (`elabLetDecl`, :939)
/// and `Lean.Parser.Term.have` passes `non_dep = true` (`elabHaveDecl`,
/// :942, i.e. `elabLetDeclCore … { nondep := true }`). The two outputs
/// differ by exactly that bit — probe-pinned, design spec § Amendment 2.
///
/// Elaboration order mirrors the oracle: binders → type → value →
/// (declare) → body. The value is checked against the declared type, and
/// the BODY is what receives `expected` (the oracle's
/// `elabTermEnsuringType body expectedType?`); this is plain
/// propagation, not the deferred postponement machinery.
///
/// `Term.let`/`Term.have` children: `[("let"|"have"), letConfig,
/// letDecl, ";", body]`. `Term.letIdDecl` children: `[letId,
/// null(binders), null(optType), ":=", value]`.
///
/// Named seams: a `letDecl` alternative other than `letIdDecl`
/// (`letPatDecl`/`letEqnsDecl` — leanr's parser does not emit them, so
/// the guard is defensive), a non-empty `letConfig` (leanr's parser
/// models the item list as always-empty), and the binder forms
/// `push_let_binders` rejects.
pub fn elab_let_like(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
    non_dep: bool,
) -> Result<ExprId, ElabError> {
    let ch = non_trivia_children(node);

    // [1] letConfig: `+nondep` / `(eq := h)` / … are not ported by
    // leanr's parser (always-empty `many(never())`), so a non-empty
    // item list is unreachable today — guarded as a named seam anyway.
    let cfg = ch
        .get(1)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: letConfig slot".into()))?;
    // The `many(never())` wrapper node, not the items themselves — its
    // own children (checked below) are the actual `letConfig` item list.
    if let Some(cfg_items_wrapper) = non_trivia_children(cfg).first().and_then(|el| el.as_node()) {
        if !non_trivia_children(cfg_items_wrapper).is_empty() {
            return Err(ElabError::UnsupportedSyntax("let: letConfig items".into()));
        }
    }

    // [2] letDecl → its single alternative.
    let let_decl = ch
        .get(2)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: letDecl slot".into()))?;
    let id_decl = non_trivia_children(let_decl)
        .first()
        .and_then(|el| el.as_node())
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: empty letDecl".into()))?;
    let id_kind = kinds.name(id_decl.kind());
    if id_kind != "Lean.Parser.Term.letIdDecl" {
        // letPatDecl / letEqnsDecl → not ported by leanr's parser.
        return Err(ElabError::UnsupportedSyntax(format!("let: {id_kind}")));
    }

    // letIdDecl: [letId, null(binders), null(optType), ":=", value].
    let dch = non_trivia_children(&id_decl);
    let let_id = dch
        .first()
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: letId slot".into()))?;
    let binders_null = dch
        .get(1)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: binders slot".into()))?;
    let opt_type = dch
        .get(2)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: optType slot".into()))?;
    let value_elem = dch
        .get(4)
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: value".into()))?;
    // [4] the body, after the `;`. Safe only because leanr's parser
    // ports the explicit-`";"` form of `optSemicolon`, not the
    // `checkLinebreakBefore` alternative (term.rs:786-790) — with `;`
    // absent the node would have 4 children, so `ch.get(4)` degrades to
    // `None` and this returns `UnsupportedSyntax("let: body")` rather
    // than picking a wrong child.
    let body_elem = ch
        .get(4)
        .cloned()
        .ok_or_else(|| ElabError::UnsupportedSyntax("let: body".into()))?;

    // optType: empty (elided) or one `typeSpec` whose children are
    // `[":", T]`.
    let ty_syntax: Option<SynElem> = match non_trivia_children(opt_type)
        .first()
        .and_then(|el| el.as_node())
    {
        Some(spec) => {
            let spec_kind = kinds.name(spec.kind());
            if spec_kind != "Lean.Parser.Term.typeSpec" {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "let: optType {spec_kind}"
                )));
            }
            Some(
                non_trivia_children(spec)
                    .get(1)
                    .cloned()
                    .ok_or_else(|| ElabError::UnsupportedSyntax("let: typeSpec type".into()))?,
            )
        }
        None => None,
    };

    let name = extract_let_id_name(elab, let_id, kinds)?;
    let binder_items = non_trivia_children(binders_null);

    // Bracket 1 — the `letIdBinders` telescope. Type and value are
    // elaborated UNDER the binders (oracle: `elabBindersEx binders fun
    // xs => …`), then abstracted back out with `mk_forall`/`mk_lambda`.
    // With no binders both abstractions are no-ops. Restores `lctx` on
    // EVERY exit path (Ok or Err), exactly as `elab_binders_and_forall`
    // does.
    let cp_binders = elab.mctx.lctx_checkpoint();
    let built = (|| {
        let fvars = push_let_binders(elab, &binder_items, kinds)?;
        let ty = match &ty_syntax {
            // oracle: `withSynthesize (postpone := .partial) <|
            // elabType typeStx` (`Binders.lean:775`) — `.partial` lets
            // a typeclass-resolution mvar the type creates be
            // postponed (nothing else may be), and the ladder drains
            // it before the value below is checked against the type.
            // Only the type is wrapped: `config.postponeValue` is
            // false for every form leanr parses, so the value and body
            // keep their direct, un-postponed shape below, matching
            // the oracle's own `postponeValue`-false branch
            // (`Binders.lean:779-798`). The oracle's own rationale
            // (issue #4051, cited at `Binders.lean:754-773`): without
            // this, unresolved synthetic-opaque mvars left in `type`
            // make the value's defeq check waste enormous time
            // unfolding declarations before failing, then insert a
            // postponed coercion.
            Some(t) => elab.with_synthesize(PostponeBehavior::Partial, kinds, |elab| {
                elab_type(elab, t, kinds)
            })?,
            // Elided type: a fresh mvar, the observable twin of the
            // oracle's `expandOptType`-to-`_` hole; the value's
            // `elab_term_ensuring_type` assigns it. No type syntax is
            // elaborated here, so there is nothing for
            // `with_synthesize` to scope.
            None => fresh_type_mvar(elab)?,
        };
        let value = elab.elab_term_ensuring_type(&value_elem, kinds, Some(ty))?;
        // oracle: `mkLambdaFVars fvars val (usedLetOnly := false)` and
        // `mkForallFVars fvars type`.
        let value = elab
            .mctx
            .mk_lambda(&fvars, value)
            .map_err(ElabError::from)?;
        let ty = elab.mctx.mk_forall(&fvars, ty).map_err(ElabError::from)?;
        Ok::<(ExprId, ExprId), ElabError>((ty, value))
    })();
    elab.mctx.lctx_restore(cp_binders);
    let (ty, value) = built?;

    // Bracket 2 — the let-bound decl itself (oracle: `withLetDecl …
    // (nondep := config.nondep) fun x => …`), same restore-on-every-path
    // discipline.
    let cp_let = elab.mctx.lctx_checkpoint();
    let result = (|| {
        let fvar = elab
            .mctx
            .push_let_decl(name, ty, value)
            .map_err(ElabError::from)?;
        let body = elab.elab_term_ensuring_type(&body_elem, kinds, expected)?;
        elab.mctx
            .mk_let_expr(fvar, body, non_dep)
            .map_err(ElabError::from)
    })();
    elab.mctx.lctx_restore(cp_let);
    result
}

#[cfg(test)]
mod tests {
    use leanr_kernel::bank::Store;
    use leanr_kernel::{BinderInfo, Environment, Nat};
    use leanr_meta::{Config, EnvExtensions, MetaCtx};

    use super::{fresh_type_mvar, propagate_expected_type};
    use crate::elab::TermElabM;

    // White-box coverage for `propagate_expected_type` in isolation —
    // the integration tests in `binder_smoke.rs`/`seam_audit.rs` can
    // only observe this function's effect THROUGH `elab_fun`'s
    // telescope and (for anything but the exact-arity case) through
    // the OUTER `ensure_has_type` recheck the ascription that supplies
    // `expected` always performs afterward — which, on an arity
    // mismatch, produces a genuinely different oracle-matching error
    // (`StuckCoercion`) no matter which of the two non-forall
    // behaviors this function chose (both are non-reducible-further
    // once WHNF has already answered "not a forall", so "keep the
    // stale value" and "drop it" are indistinguishable from THAT
    // vantage point — measured, not assumed, while writing
    // `fun_propagation_stops_at_a_non_forall_expected_type`). Calling
    // the function directly is the only way to pin oracle detail 3
    // (non-forallE returns `none`, not the old value) precisely.
    //
    // No persistent declarations are needed — `propagate_expected_type`
    // reads only `mctx`'s own mvar/local-context state, never `view`'s
    // environment — so each test below builds a bare
    // `Environment::default()` inline (mirroring
    // `app::head::tests::env_with_foo`'s harness shape, minus the
    // axiom neither test here needs; not factored into a shared helper
    // because an `EnvView` borrows its `Environment` and a helper
    // cannot hand both back without a self-referential struct).

    /// oracle: `propagateExpectedType`'s `forallE` arm. Two things a
    /// non-discriminating test could miss, both checked here:
    ///   * `discard <| isDefEq fvarType d.cleanupAnnotations` — the
    ///     BOOL is discarded, but the ASSIGNMENT it performs is not:
    ///     `fvar_type` (an unassigned mvar going in) must come out
    ///     assigned to `domain`.
    ///   * `let b := b.instantiate1 fvar` — with `body = bvar 0`, a
    ///     correct `instantiate1` hands back `fvar` itself (checked by
    ///     `ExprId` equality, no `render_expr` needed).
    #[test]
    fn forall_arm_assigns_the_domain_and_instantiates_the_body() {
        let env = Environment::default();
        let view = env.view();
        let mut scratch = Store::scratch();
        let mctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            EnvExtensions::default(),
        );
        let mut elab = TermElabM::new(mctx, view);

        let z = elab.mctx.store_mut().level_zero(None).unwrap();
        let domain = elab.mctx.store_mut().expr_sort(None, z).unwrap();
        let bvar0 = elab
            .mctx
            .store_mut()
            .expr_bvar(None, &Nat::from(0u64))
            .unwrap();
        let expected = elab
            .mctx
            .store_mut()
            .expr_forall(None, None, domain, bvar0, BinderInfo::Default)
            .unwrap();

        // Exactly what an elided `fun` binder's domain starts as
        // (`fresh_type_mvar`): unassigned going in.
        let fvar_type = fresh_type_mvar(&mut elab).unwrap();
        let fvar = elab
            .mctx
            .push_local_decl(None, fvar_type, BinderInfo::Default)
            .map_err(crate::error::ElabError::from)
            .unwrap();

        let residual = propagate_expected_type(&mut elab, fvar, fvar_type, Some(expected)).unwrap();
        assert_eq!(
            residual,
            Some(fvar),
            "body was `bvar 0`; instantiate1 must hand back `fvar` itself"
        );

        let resolved = elab.mctx.instantiate_mvars(fvar_type).unwrap();
        assert_eq!(
            resolved, domain,
            "the discarded isDefEq bool must still ASSIGN fvar_type := domain"
        );
    }

    /// oracle: `propagateExpectedType`'s non-`forallE` arm returns
    /// `none`, not the (necessarily non-reducible-further) value it
    /// just WHNF'd — and a `None` `expected` going in is a no-op,
    /// touching neither `fvar` nor `fvar_type` (both get an
    /// intentionally-invalid `ExprId` here to prove that).
    #[test]
    fn non_forall_arm_drops_the_expected_type_and_none_input_is_a_no_op() {
        let env = Environment::default();
        let view = env.view();
        let mut scratch = Store::scratch();
        let mctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            EnvExtensions::default(),
        );
        let mut elab = TermElabM::new(mctx, view);

        let z = elab.mctx.store_mut().level_zero(None).unwrap();
        let not_a_forall = elab.mctx.store_mut().expr_sort(None, z).unwrap();

        let residual =
            propagate_expected_type(&mut elab, not_a_forall, not_a_forall, Some(not_a_forall))
                .unwrap();
        assert_eq!(residual, None);

        let residual = propagate_expected_type(&mut elab, not_a_forall, not_a_forall, None)
            .expect("`expected = None` never touches fvar/fvar_type");
        assert_eq!(residual, None);
    }
}
