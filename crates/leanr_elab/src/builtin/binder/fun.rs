//! `fun`: the binder-view telescope with per-binder expected-type
//! propagation. Oracle: `elabFun` → `elabFunBinders` →
//! `elabFunBinderViews` (`Lean/Elab/Binders.lean:678`, `:423`).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::bank::NameId;
use leanr_kernel::BinderInfo;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::NodeOrToken;
use leanr_syntax::tree::SyntaxNode;

use super::{
    elab_type, extract_inst_binder_layout, fresh_type_mvar, intern_binder_name,
    intern_fun_binder_ident,
};
use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `Expr.cleanupAnnotations` (`Lean/Expr.lean:1754-1756`; the
/// definition itself — `:1748` is inside its docstring) —
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

/// One elaborated-binder view: the oracle's `BinderView`
/// (`Lean/Elab/Binders.lean`, `toBinderViews` at `:140-166`). A single
/// `funBinder` item can expand to SEVERAL views — `{a b : Type}` binds
/// two names sharing one type syntax.
struct FunBinderView {
    name: Option<NameId>,
    ty: Option<SynElem>,
    bi: BinderInfo,
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
                // above). oracle: `toBinderViews`'s `instBinder` arm,
                // `Binders.lean:161-165`.
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
/// arm only. `optType` (`fun x : T => e`) is `expandFun`'s FIRST macro
/// arm (`Lean/Elab/Binders.lean:648-651`):
///
/// ```lean
/// | `(fun $binders* : $ty => $body) => do
///     let binders ← binders.mapM (expandSimpleBinderWithType ty)
///     `(fun $binders* => $body)
/// ```
///
/// — `T` distributes over the BINDERS, not the body: EVERY item in
/// `$binders*` is rewritten via `expandSimpleBinderWithType`
/// (`:265-270`) into `(binder : $ty)`, requiring each to be a bare
/// ident or `_` hole; anything else is a macro-time error,
/// `"unexpected type ascription"`. (An EARLIER version of this comment
/// claimed the opposite — that `T` ascribes the body via a `(e : T)`
/// rewrite — which is wrong: `expandSimpleBinderWithType`'s `else`
/// branch throws exactly the two terms that claim tested as
/// successes. Corrected after checking the pinned binary directly:
/// `fun x y : Nat => Nat.zero` elaborates fine, `fun (x : Nat) : Nat =>
/// x` is a real error.) leanr has no macro-expansion phase (module
/// doc), so this models the same restriction directly in the
/// telescope loop below rather than rewriting syntax first.
///
/// `expected` (M4b-3 P5 task 4) threads `FunBinders.propagateExpectedType`
/// per binder: each binder's domain (elided or, per the above,
/// `optType`-supplied) gets unified against the running residual's
/// forall domain, and the FINAL residual — never an `optType`, which
/// leaves nothing for the body per the macro above — is the body's own
/// expected type. Named seams: the `matchAlts` (pattern) arm and the
/// funBinder forms `extract_fun_binder_views` rejects.
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
    // accounts for (`binder/let_like.rs`, around `let: optType slot`). Verified
    // against the pinned toolchain source after a flat `nth(1)` read
    // directly off the wrapper silently produced `None` for every
    // `fun x : T => e` here — no error, no wrong term, just the
    // ascription dropped (`fun_opt_type_distributes_to_a_single_binder`
    // in `binder_smoke.rs` pins the regression). `T` itself DISTRIBUTES
    // over the binders, not the body — see this function's own doc
    // comment above for the corrected model and its citations.
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
            // oracle: `expandFun`'s `optType` macro arm
            // (`Binders.lean:648-651`, `expandSimpleBinderWithType`
            // `:265-270`) — when `optType` is present, EVERY item must
            // be a bare ident or `_` hole; each becomes its OWN
            // `Default` binder with `optType`'s term as its domain.
            // Anything else is the macro's own error, ported as a real
            // elaboration error (not a deferred seam — this shape is
            // rejected by every future slice too, never just "not
            // landed yet").
            let views: Vec<FunBinderView> = match &opt_type {
                Some(ty_elem) => {
                    let name = match item {
                        NodeOrToken::Token(tok) if kinds.name(tok.kind()) == "<ident>" => {
                            Some(intern_binder_name(elab, tok.text())?)
                        }
                        NodeOrToken::Node(n) if kinds.name(n.kind()) == "Lean.Parser.Term.hole" => {
                            None
                        }
                        _ => {
                            return Err(ElabError::IllFormedSyntax(
                                "unexpected type ascription".into(),
                            ));
                        }
                    };
                    vec![FunBinderView {
                        name,
                        ty: Some(ty_elem.clone()),
                        bi: BinderInfo::Default,
                    }]
                }
                None => extract_fun_binder_views(elab, item, kinds)?,
            };
            for view in views {
                let dom = match &view.ty {
                    Some(ty_elem) => elab_type(elab, ty_elem, kinds)?,
                    None => fresh_type_mvar(elab)?,
                };
                // oracle: `elabFunBinderViews` mints the fvar
                // (`Binders.lean:430-432`), runs `propagateExpectedType`
                // (`:442`), and only THEN tests `isClass? type` (`:444`
                // — the test itself, not `:445`, its FIRST match arm).
                // An ELIDED binder's domain mvar may only become
                // class-typed via that propagation step, so the
                // local-instance install has to happen AFTER it, not as
                // part of the push (fix round 1, Finding 2:
                // `push_local_decl`'s own inline install ran BEFORE
                // propagation and silently missed exactly this case).
                // NOT reproduced: the oracle runs `propagateExpectedType`
                // under `withLCtx s.lctx s.localInsts` where `s.lctx`
                // does NOT yet hold the new binder — `lctx` with the
                // binder is a local value at `:440`, only folded into
                // `s` at `:443`, AFTER `:442`'s propagation call —
                // whereas this pushes `fvar` into the ambient `lctx`
                // first and propagates second, so an aux mvar MINTED
                // DURING this propagation call captures a wider ambient
                // context than the oracle's equivalent step would (the
                // `is_def_eq` assignment on the domain mvar itself is
                // unaffected: that mvar's own recorded lctx predates
                // this push, and scope-checking keys on that recorded
                // lctx, not on whatever is ambient when the assignment
                // happens).
                let fvar = elab
                    .mctx
                    .push_local_decl_without_instance(view.name, dom, view.bi)
                    .map_err(ElabError::from)?;
                residual = propagate_expected_type(elab, fvar, dom, residual)?;
                elab.mctx
                    .install_local_instance_for_last_pushed(fvar, dom)
                    .map_err(ElabError::from)?;
                fvars.push(fvar);
            }
        }
        // oracle: `expandFun`'s `optType` arm leaves the body with NO
        // ascription at all — `T` was already distributed over the
        // binders above, so the body's expected type is whatever
        // `propagateExpectedType` threaded through, exactly like every
        // other binder telescope.
        let body = match residual {
            Some(t) => elab.elab_term_ensuring_type(&body_elem, kinds, Some(t))?,
            None => elab.elab_term(&body_elem, kinds, None)?,
        };
        elab.mctx.mk_lambda(&fvars, body).map_err(ElabError::from)
    })();
    elab.mctx.lctx_restore(checkpoint);
    result
}

#[cfg(test)]
mod tests {
    use leanr_kernel::bank::Store;
    use leanr_kernel::{BinderInfo, Environment, Nat};
    use leanr_meta::{Config, EnvExtensions, MetaCtx};

    use super::propagate_expected_type;
    use crate::builtin::binder::fresh_type_mvar;
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
    // `fun_more_binders_than_expected_pi_levels_is_a_stuck_coercion`
    // (`tests/binder_smoke.rs`, renamed in fix round 1 from
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

    /// Fix round 1, Finding 4: `cleanup_annotations`/
    /// `strip_one_type_annotation` (~45 lines) had NO covering test —
    /// every test above would pass unchanged if `cleanup_annotations`
    /// simply returned its input. Pins the actual oracle detail:
    /// `discard <| isDefEq fvarType d.cleanupAnnotations` unifies
    /// against the STRIPPED domain, not the `optParam`-wrapped one.
    /// Builds `expected = ∀ (_ : optParam Sort0 Sort0), bvar 0` by hand
    /// (`optParam`'s own arity-2 shape — `Lean/Expr.lean:1709-1722`) and
    /// checks `fvar_type` resolves to the UNWRAPPED domain: if
    /// `cleanup_annotations` were a no-op, `fvar_type` would resolve to
    /// the wrapper application instead (`is_def_eq` assigns a fresh mvar
    /// to whatever it is asked to unify against, wrapped or not).
    #[test]
    fn forall_arm_strips_opt_param_before_unifying() {
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
        let base = elab.view.store;

        let z = elab.mctx.store_mut().level_zero(None).unwrap();
        // `D`, the domain `cleanupAnnotations` must uncover.
        let domain = elab.mctx.store_mut().expr_sort(None, z).unwrap();
        // `optParam`'s second argument (the default value) — any expr;
        // its content is never inspected, only its POSITION as arg 2.
        let default_val = elab.mctx.store_mut().expr_sort(None, z).unwrap();

        let opt_param_name = {
            let store = elab.mctx.store_mut();
            let s = store.intern_str(Some(base), "optParam").unwrap();
            store.name_str(Some(base), None, s).unwrap()
        };
        let no_levels = elab
            .mctx
            .store_mut()
            .intern_level_list(Some(base), &[])
            .unwrap();
        let head = elab
            .mctx
            .store_mut()
            .expr_const(Some(base), Some(opt_param_name), no_levels)
            .unwrap();
        let applied1 = elab
            .mctx
            .store_mut()
            .expr_app(Some(base), head, domain)
            .unwrap();
        // `wrapped` = `optParam D default_val` — the oracle's own
        // `optParam`-arity-2 shape.
        let wrapped = elab
            .mctx
            .store_mut()
            .expr_app(Some(base), applied1, default_val)
            .unwrap();

        let bvar0 = elab
            .mctx
            .store_mut()
            .expr_bvar(None, &Nat::from(0u64))
            .unwrap();
        let expected = elab
            .mctx
            .store_mut()
            .expr_forall(None, None, wrapped, bvar0, BinderInfo::Default)
            .unwrap();

        let fvar_type = fresh_type_mvar(&mut elab).unwrap();
        let fvar = elab
            .mctx
            .push_local_decl(None, fvar_type, BinderInfo::Default)
            .map_err(crate::error::ElabError::from)
            .unwrap();

        let residual = propagate_expected_type(&mut elab, fvar, fvar_type, Some(expected)).unwrap();
        assert_eq!(residual, Some(fvar));

        let resolved = elab.mctx.instantiate_mvars(fvar_type).unwrap();
        assert_eq!(
            resolved, domain,
            "fvar_type must resolve to the UNWRAPPED domain D, not `optParam D default_val` \
             — cleanup_annotations must strip the wrapper before isDefEq runs"
        );
    }

    /// Fix round 1, Finding 4: the other half with no covering test — a
    /// FAILED `isDefEq` (oracle: `discard <|`, a `false` result, not a
    /// `MetaError`) must not stop the walk or surface as an error.
    /// `fvar_type` here is a CONCRETE `Sort 0` (not a fresh mvar), which
    /// cannot unify with the forall's `Sort 1` domain — a genuine,
    /// cleanly-decidable `false`, not `IsDefEqStuck` (both sides are
    /// fully concrete levels, no metavariable blocks the decision).
    #[test]
    fn forall_arm_survives_a_failed_unification() {
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

        let zero = elab.mctx.store_mut().level_zero(None).unwrap();
        let one = elab.mctx.store_mut().level_succ(None, zero).unwrap();
        let sort0 = elab.mctx.store_mut().expr_sort(None, zero).unwrap();
        let sort1 = elab.mctx.store_mut().expr_sort(None, one).unwrap();
        let bvar0 = elab
            .mctx
            .store_mut()
            .expr_bvar(None, &Nat::from(0u64))
            .unwrap();
        // ∀ (_ : Sort 1), bvar 0
        let expected = elab
            .mctx
            .store_mut()
            .expr_forall(None, None, sort1, bvar0, BinderInfo::Default)
            .unwrap();

        // `fvar_type` is concretely `Sort 0` — NOT a fresh mvar, so
        // `isDefEq (Sort 0) (Sort 1)` genuinely fails rather than
        // assigning anything.
        let fvar = elab
            .mctx
            .push_local_decl(None, sort0, BinderInfo::Default)
            .map_err(crate::error::ElabError::from)
            .unwrap();

        let residual = propagate_expected_type(&mut elab, fvar, sort0, Some(expected))
            .expect("a FAILED isDefEq must not surface as an Err — only a MetaError may");
        assert_eq!(
            residual,
            Some(fvar),
            "the walk must stay intact (Ok(Some(_))) even though the domains do not unify"
        );

        // `fvar_type` (`sort0`) was never a metavariable here, so there
        // is nothing to assign either way — the discriminating claim is
        // the `Ok` verdict and the intact residual above, not this.
        let resolved = elab.mctx.instantiate_mvars(sort0).unwrap();
        assert_eq!(resolved, sort0);
    }
}
