//! `let` and `have`: one elaborator, differing only in the emitted
//! `letE`'s `nonDep` bit. Oracle: `elabLetDeclCore` → `elabLetDeclAux`
//! (`Lean/Elab/Binders.lean:891`, `:745`).

use leanr_kernel::bank::ExprId;
use leanr_kernel::bank::NameId;
use leanr_kernel::BinderInfo;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::NodeOrToken;
use leanr_syntax::tree::SyntaxNode;

use super::{
    elab_type, extract_binder_group, fresh_type_mvar, intern_binder_name, push_binder_group,
    push_user_binder, push_user_let_decl,
};
use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::synthetic::PostponeBehavior;

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
/// Implicit, strict-implicit and instance bracketed binders are accepted
/// (opened by the M4b-3 close-out): `push_binder_group` pushes each with
/// its own `BinderInfo` and runs the instance-binder check, exactly as
/// the `forall` telescope does. Named seam (→ `UnsupportedSyntax`): any
/// other item shape.
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
                let fvar = push_user_binder(elab, None, dom, BinderInfo::Default)?;
                fvars.push(fvar);
            }
            // Any binder info: `push_binder_group` is the `elabBinderViews`
            // port, so it pushes the group's own `BinderInfo` and runs the
            // instance-binder check (`Binders.lean:216-219`).
            NodeOrToken::Node(n) => {
                let g = extract_binder_group(elab, n, kinds)?;
                fvars.extend(push_binder_group(elab, &g, kinds)?);
            }
            NodeOrToken::Token(tok) if kinds.name(tok.kind()) == "<ident>" => {
                let name = intern_binder_name(elab, tok.text())?;
                let dom = fresh_type_mvar(elab)?;
                let fvar = push_user_binder(elab, Some(name), dom, BinderInfo::Default)?;
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
        let fvar = push_user_let_decl(elab, name, ty, value)?;
        // oracle: `elabTermEnsuringType body expectedType? >>=
        // instantiateMVars` (`Binders.lean:824`). An instance solved
        // eagerly in the body is an ASSIGNED mvar here, and `mk_let_expr`'s
        // bare `abstract_fvars` cannot see through one: without this, the
        // let-bound local instance leaks as an fvar once the assignment is
        // instantiated later (`seam_audit.rs`'s
        // `a_let_bound_local_instance_consumed_by_an_application_abstracts_to_bvar_0`).
        let body = elab.elab_term_ensuring_type(&body_elem, kinds, expected)?;
        let body = elab.mctx.instantiate_mvars(body)?;
        elab.mctx
            .mk_let_expr(fvar, body, non_dep)
            .map_err(ElabError::from)
    })();
    elab.mctx.lctx_restore(cp_let);
    result
}
