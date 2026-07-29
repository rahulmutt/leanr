//! `TermElabM`: the leaf-term elaborator's own state, layered directly
//! over `leanr_meta::MetaCtx`. Independent of any single parse — the
//! `KindInterner` is passed to `elab_term`, never stored, so one
//! `TermElabM` can elaborate nodes drawn from different snapshots.

use std::collections::HashMap;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_kernel::{BinderInfo, EnvView, LocalContext, Nat};
use leanr_meta::{LMVarId, MVarDecl, MVarId, MVarKind, MetaCtx};
use leanr_syntax::kind::KindInterner;

use crate::dispatch::{self, SynElem};
use crate::error::ElabError;

pub struct TermElabM<'e> {
    pub mctx: MetaCtx<'e>,
    /// The environment view `mctx` was itself built over, held a second
    /// time here: `MetaCtx::view` is `pub(crate)` to `leanr_meta` (no
    /// accessor — `grep -rn "pub fn " crates/leanr_meta/src/metactx.rs`
    /// confirms it), so `resolve_global` (design spec's named-seam
    /// global-constant resolution, `resolve.rs`) has no way to reach a
    /// `&EnvView` through `mctx` at all. `EnvView<'e>` is `Copy`
    /// (`tc.rs`'s own derive), so the caller's `view` local — already
    /// constructed one line before `MetaCtx::new(view, ..)` in every
    /// call site (`oracle_elab.rs`'s own shape) — is still valid to pass
    /// here too; storing an independent copy costs nothing and needs no
    /// `leanr_meta` change (the "do not modify leanr_meta/src" scope
    /// boundary this task was given).
    pub view: EnvView<'e>,
    /// Universe parameters in scope, for `Sort u`. Empty for closed leaf
    /// terms; the field exists because `sort` reads it.
    pub level_names: Vec<NameId>,
    /// Monotone counter backing `mk_fresh_level_mvar`, this crate's own
    /// "fixed prefix + counter" name generator (mirroring
    /// `leanr_meta::MetaCtx`'s own `level_mvar_gen`, which this crate
    /// cannot reach — it is `pub(crate)` to `leanr_meta`). A distinct
    /// prefix (`_leanr_elab_lvl_fresh`, below) keeps this counter's
    /// names from ever colliding with `leanr_meta`'s internal fresh
    /// mvars, even though both mint into the same scratch `Store`.
    level_mvar_gen: u64,
    /// Monotone counter backing `mk_fresh_expr_mvar` (Task 6) — the
    /// same "fixed prefix + counter" idiom as `level_mvar_gen`, but a
    /// SEPARATE counter and a DISTINCT prefix
    /// (`_leanr_elab_expr_fresh`, below) so an expr-mvar name can never
    /// collide with a level-mvar name even at the same counter value.
    expr_mvar_gen: u64,
    /// Monotone counter backing `mk_fresh_binder_name` (M4b-3 P1 task
    /// 7) — the same "fixed prefix + counter" idiom as the two counters
    /// above, with its own counter and its own DISTINCT prefix
    /// (`_leanr_elab_binder_fresh`, below) so a fresh binder name can
    /// never collide with either mvar-name family.
    binder_name_gen: u64,
    /// oracle: `Term.State.pendingMVars` (`TermElabM.lean:183`). **Head
    /// is the most recent** — the oracle conses. Every ordering in
    /// `synthetic/` depends on that invariant.
    pub pending_mvars: Vec<MVarId>,
    /// oracle: `Term.State.syntheticMVars` (`TermElabM.lean:182`).
    pub synthetic_mvars: HashMap<MVarId, crate::synthetic::SyntheticMVarDecl>,
    /// oracle: `Term.State.mvarErrorInfos` (`TermElabM.lean:185`).
    /// Registered by P2a, rendered by whichever slice grows a
    /// diagnostics layer (design spec § Amendment, item 2).
    pub mvar_error_infos: Vec<crate::synthetic::MVarErrorInfo>,
    /// oracle: `Term.Context.mayPostpone` — a READER field there, a
    /// plain field here, saved/restored by `without_postponing` only:
    /// `with_saved_context` deliberately does NOT touch it (that
    /// field's own doc, `synthetic/state.rs`, and Task 2's fix round). Defaults
    /// to `true`, matching `Context.mayPostpone : Bool := true`'s own
    /// default (`TermElabM.lean:303`).
    pub may_postpone: bool,
}

impl<'e> TermElabM<'e> {
    pub fn new(mctx: MetaCtx<'e>, view: EnvView<'e>) -> Self {
        TermElabM {
            mctx,
            view,
            level_names: Vec::new(),
            level_mvar_gen: 0,
            expr_mvar_gen: 0,
            binder_name_gen: 0,
            pending_mvars: Vec::new(),
            synthetic_mvars: HashMap::new(),
            mvar_error_infos: Vec::new(),
            may_postpone: true,
        }
    }

    /// oracle: `Core.mkFreshUserName` (`Lean/CoreM.lean`) — a name the
    /// user could not have written, used where a binder must be
    /// introduced without letting later syntax capture it. The oracle
    /// builds it by appending a macro scope to a hint; leanr's names
    /// carry no macro scopes, so this uses the crate's own fresh-name
    /// idiom instead — the very "fixed prefix + counter" generator
    /// `mk_fresh_level_mvar`/`mk_fresh_expr_mvar` above already use,
    /// with a third distinct prefix.
    ///
    /// The hint the oracle takes (`Core.mkFreshUserName argName`) is
    /// deliberately NOT a parameter: the hint exists only to make the
    /// generated name legible in traces, and every leanr caller
    /// (`app::args::add_eta_arg`) restores the user-facing name on the
    /// emitted binder anyway (`finalize`'s `update_binder_names`,
    /// oracle `Expr.updateBinderNames`, `App.lean:623`).
    ///
    /// `base = Some(self.view.store)`, matching `mk_fresh_level_mvar`:
    /// the minted `NameId` is handed straight to
    /// `MetaCtx::push_local_decl`, which itself builds the decl's fvar
    /// with `Some(view.store)` (`metactx.rs:464-471`), and lands in
    /// `Expr.lam` rows this crate builds with the same base — so every
    /// id involved must come from the same persistent-backed intern
    /// space.
    pub fn mk_fresh_binder_name(&mut self) -> Result<NameId, ElabError> {
        let idx = self.binder_name_gen;
        self.binder_name_gen += 1;
        let base = self.view.store;
        let store = self.mctx.store_mut();
        let prefix_str = store
            .intern_str(Some(base), "_leanr_elab_binder_fresh")
            .map_err(leanr_meta::MetaError::from)?;
        let prefix = store
            .name_str(Some(base), None, prefix_str)
            .map_err(leanr_meta::MetaError::from)?;
        let idx_id = store
            .intern_nat(Some(base), &Nat::from(idx))
            .map_err(leanr_meta::MetaError::from)?;
        let name = store
            .name_num(Some(base), Some(prefix), idx_id)
            .map_err(leanr_meta::MetaError::from)?;
        Ok(name)
    }

    /// oracle: `mkFreshLevelMVar` (`Lean/Meta/Basic.lean:861-863`) —
    /// mints a globally-fresh `LMVarId`, declares it in the `mctx`, and
    /// returns the `LevelId` of `Level.mvar` referencing it. One fresh
    /// mvar per universe parameter is exactly what
    /// `app::head::elab_ident_head` needs
    /// for `mkConst` (design spec's "Universe metavariables in the
    /// output"). Reachable capability surface is entirely public
    /// (`MetaCtx::store_mut`/`mctx_mut`, `MetavarContext::declare_level`,
    /// `Store::level_mvar`) — no `leanr_meta` change needed; this is a
    /// standalone transcription of `leanr_meta::level::fresh_level_mvar`
    /// (which is `pub(crate)` there, so unreachable from here), not a
    /// call to it.
    ///
    /// `base = Some(self.view.store)` throughout (M4b-2 task 2 fix,
    /// bound before `store_mut()` — the same disjoint-field-borrow
    /// convention `ident.rs` uses): NOT the self-contained-scratch
    /// `base = None` `mk_fresh_expr_mvar` uses below. A fresh level
    /// mvar's `Sort ?u` is fed into `elab_term_ensuring_type`
    /// (`binder::elab_type`, M4b-2), whose `is_def_eq` — on a Sort-vs-Sort
    /// compare — round-trips the mvar's `LevelId` through
    /// `level.rs::level_normalize` (`to_level` then `intern_level`),
    /// ALWAYS with `base = Some(view.store)` (that module's own fixed
    /// convention, never `None`). `intern_nat`'s `base`-first dedup
    /// lookup means interning the SAME small index (e.g. `0`) once
    /// under `base = None` and once under `base = Some(persistent)` can
    /// resolve to two DIFFERENT `NatId`s — the persistent store already
    /// has small `Nat`s interned, so the `base = Some` call finds
    /// persistent's row while a `base = None` call would have kept the
    /// original scratch row — which in turn mints a genuinely different
    /// `NameId` for the "same" mvar name on the round trip, so the
    /// later `assign_level` targets an id that was never `declare_level`-d
    /// (confirmed empirically: this was `elab_arrow`'s exact RED-phase
    /// failure, `assign_level: level metavariable .. was never
    /// declared`, traced to this mismatch, not to `binder.rs` itself).
    /// Minting under `base = Some(view.store)` from the start — matching
    /// `level.rs::fresh_level_mvar`'s own convention exactly — makes the
    /// mint and every later re-intern agree on the same persistent-backed
    /// ids, closing the gap.
    pub fn mk_fresh_level_mvar(&mut self) -> Result<LevelId, ElabError> {
        let idx = self.level_mvar_gen;
        self.level_mvar_gen += 1;
        // `Store`'s own methods return `KernelError`, which has no
        // direct `ElabError` conversion (only `MetaError` does, via
        // `ElabError::from(MetaError)`) — route each through
        // `MetaError::from` so `?` reuses that existing impl rather
        // than adding a second `From<KernelError>` to `error.rs`
        // (outside this task's file scope).
        let base = self.view.store;
        let store = self.mctx.store_mut();
        let prefix_str = store
            .intern_str(Some(base), "_leanr_elab_lvl_fresh")
            .map_err(leanr_meta::MetaError::from)?;
        let prefix = store
            .name_str(Some(base), None, prefix_str)
            .map_err(leanr_meta::MetaError::from)?;
        let idx_id = store
            .intern_nat(Some(base), &Nat::from(idx))
            .map_err(leanr_meta::MetaError::from)?;
        let name = store
            .name_num(Some(base), Some(prefix), idx_id)
            .map_err(leanr_meta::MetaError::from)?;
        let id = LMVarId(name);
        self.mctx.mctx_mut().declare_level(id);
        let level_id = self
            .mctx
            .store_mut()
            .level_mvar(Some(base), Some(name))
            .map_err(leanr_meta::MetaError::from)?;
        Ok(level_id)
    }

    /// oracle: `mkFreshExprMVar ty (kind := .natural)` — the `Natural` +
    /// `ExprId`-only path P1's ten call sites use. Delegates to
    /// `mk_fresh_expr_mvar_of_kind` (below), which carries the actual
    /// minting mechanics, discarding the `MVarId` it also returns: P1's
    /// callers never needed it.
    pub fn mk_fresh_expr_mvar(&mut self, ty: ExprId) -> Result<ExprId, ElabError> {
        self.mk_fresh_expr_mvar_of_kind(ty, MVarKind::Natural)
            .map(|(e, _)| e)
    }

    /// oracle: `mkFreshExprMVarCore`/`mkFreshMVarId`
    /// (`Lean/Meta/Basic.lean:864-877`) — mints a globally-fresh
    /// `MVarId` (own `expr_mvar_gen` counter, mirroring
    /// `mk_fresh_level_mvar`'s `level_mvar_gen` exactly), `declare`s it
    /// in `mctx` with an EMPTY `LocalContext` — slice 1 elaborates no
    /// binder/lambda/pi, so no leaf elaborator ever runs under a
    /// nonempty local context; `LocalContext::default()` is the correct
    /// context here, not a placeholder — and the caller-chosen
    /// `MVarKind` (see `builtin::hole`'s own doc for why every hole is
    /// minted `Natural` rather than replicating `elabHole`'s
    /// `Natural`/`SyntheticOpaque` branch), and returns the `ExprId` of
    /// `Expr.mvar` referencing it alongside the `MVarId` itself.
    /// `base = None` throughout — unlike `mk_fresh_level_mvar` (M4b-2
    /// task 2 fix, see its own doc comment for why THAT one now needs
    /// `base = Some(view.store)`): every id minted here (prefix string,
    /// the mvar's own synthetic name, the `Expr.mvar` row) is
    /// self-contained fresh scratch data with nothing in the PERSISTENT
    /// store to dedup against, and — the part that actually matters —
    /// nothing in this crate re-interns an expr mvar's own synthetic
    /// name through a `base = Some(persistent)` path the way
    /// `level.rs::level_normalize` does for level mvars, so there is no
    /// analogous round-trip mismatch to guard against here. `ty` itself
    /// (the caller-supplied type, possibly persistent-region) is stored
    /// VERBATIM in `MVarDecl::ty`, never re-interned, so it needs no
    /// `base` here either.
    ///
    /// P2a needs both the `MVarId` and the caller-chosen `MVarKind`: an
    /// instance-implicit argument is minted `MetavarKind.synthetic`
    /// (`App.lean:919`, so `isDefEq` may assign it — unlike
    /// `syntheticOpaque`), and the caller must keep its `MVarId` to push
    /// onto `instMVars`.
    pub fn mk_fresh_expr_mvar_of_kind(
        &mut self,
        ty: ExprId,
        kind: MVarKind,
    ) -> Result<(ExprId, MVarId), ElabError> {
        let idx = self.expr_mvar_gen;
        self.expr_mvar_gen += 1;
        let store = self.mctx.store_mut();
        let prefix_str = store
            .intern_str(None, "_leanr_elab_expr_fresh")
            .map_err(leanr_meta::MetaError::from)?;
        let prefix = store
            .name_str(None, None, prefix_str)
            .map_err(leanr_meta::MetaError::from)?;
        let idx_id = store
            .intern_nat(None, &Nat::from(idx))
            .map_err(leanr_meta::MetaError::from)?;
        let name = store
            .name_num(None, Some(prefix), idx_id)
            .map_err(leanr_meta::MetaError::from)?;
        let id = MVarId(name);
        self.mctx.mctx_mut().declare(
            id,
            MVarDecl {
                user_name: None,
                ty,
                lctx: LocalContext::default(),
                kind,
            },
        );
        let mvar_id = self
            .mctx
            .store_mut()
            .expr_mvar(None, Some(name))
            .map_err(leanr_meta::MetaError::from)?;
        Ok((mvar_id, id))
    }

    pub fn elab_term(
        &mut self,
        elem: &SynElem,
        kinds: &KindInterner,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        check_implicit_lambda(self, elem, kinds, expected)?;
        dispatch::dispatch(self, elem, kinds, expected)
    }

    pub fn elab_term_ensuring_type(
        &mut self,
        elem: &SynElem,
        kinds: &KindInterner,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        let e = self.elab_term(elem, kinds, expected)?;
        if let Some(t) = expected {
            let inferred = self.mctx.infer_type(e)?;
            if !self.mctx.is_def_eq(inferred, t)? {
                return Err(ElabError::TypeMismatch {
                    expected: t,
                    got: inferred,
                });
            }
        }
        Ok(e)
    }

    /// oracle: `elabTermAndSynthesize` (`SyntheticMVars.lean:696-698`) —
    /// `withRef stx do instantiateMVars (← withSynthesize <| elabTerm
    /// stx expectedType?)`, where `withSynthesize`'s default `postpone`
    /// is `.no` (`:678`, `PostponeBehavior.no` — confirmed against the
    /// pinned source; the brief's own citation of `:694-696` pointed at
    /// the doc comment one line high, corrected here to the `def`
    /// itself plus its two-line body).
    ///
    /// `withSynthesizeImp` (`:662-672`) saves `pendingMVars`, clears it,
    /// runs `k`, synthesizes, then restores by APPENDING the saved list
    /// back onto whatever `k`'s own synthesis left behind. At the
    /// OUTERMOST call — this one — nothing is pending before `elab_term`
    /// runs, so the saved list is always empty and that save/restore
    /// dance is a no-op: this method is exactly `elab_term` ->
    /// `synthesize_synthetic_mvars(.no)` -> `instantiate_mvars`, the
    /// pipeline the design spec pins (§ The entry-point pipeline).
    ///
    /// `elab_term_ensuring_type` (above) is UNCHANGED and remains the
    /// INNER entry point every elaborator uses (ascription, `let`,
    /// `have`, application argument elaboration); this is the
    /// OUTERMOST one, called once per top-level term the way
    /// `dump_elab.lean`'s dumper and any future top-level driver call
    /// it — never from inside another elaborator.
    pub fn elab_term_and_synthesize(
        &mut self,
        elem: &SynElem,
        kinds: &KindInterner,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        let e = self.elab_term(elem, kinds, expected)?;
        self.synthesize_synthetic_mvars_no_postponing(kinds)?;
        self.mctx.instantiate_mvars(e).map_err(ElabError::from)
    }
}

/// oracle: `useImplicitLambda` (`TermElabM.lean:1737-1779`), consulted by
/// `elabTermAux` at `TermElabM.lean:1839` — BEFORE `elabUsingElabFns`,
/// i.e. before any leaf/app elaborator runs. That is why this lives in
/// `elab_term` rather than inside a leaf: the oracle wraps the WHOLE
/// term in implicit lambdas and never dispatches on its kind at all
/// when the feature fires.
///
/// M4b-3 P5 owns the wrapping itself (`elabImplicitLambda`,
/// `TermElabM.lean:1806-1820`). This is the named seam that keeps the
/// path from being silently skipped now that Task 6's source ascription
/// can supply an expected type: without it, `(f : {α : Type} → α → α)`-
/// shaped input would elaborate `f` with NO lambda wrap and emit a
/// different term than the oracle's, with no error.
///
/// Transliterated from the pinned source, not the plan's paraphrase —
/// two places where they differ:
///   * the binder-info test is `c.isImplicit || c.isInstImplicit`
///     (`:1751`), NOT strict-implicit. `useImplicitLambda`'s own doc
///     comment says so in as many words: "implicit lambdas are not
///     triggered by the strict implicit binder annotation
///     `{{a : α}} → β`".
///   * `blockImplicitLambda` (`:1716-1720`) runs FIRST, before the
///     expected type is even looked at, and its exclusion list is what
///     keeps this from firing on the ascribed corpus records.
///
/// `useImplicitLambda`'s third result, `.postpone` (`:1753-1778`, a
/// local identifier whose type is still an mvar application), is not
/// modelled: it is only reachable AFTER the implicit-forall test above
/// has already succeeded, and both of its continuations —
/// `postponeElabTerm` when `mayPostpone`, `elabUsingElabFns` otherwise —
/// need the postponement ladder P1 deliberately does not have
/// (`elab.rs`'s own module doc). Distinguishing it here would only
/// change which unimplemented path is named.
///
/// `hasNoImplicitLambdaAnnotation` (`:1706-1707`, an `annotation?
/// \`noImplicitLambda` on the expected type) is likewise not modelled:
/// the annotation is minted only by `mkNoImplicitLambdaAnnotation`, and
/// nothing in leanr builds one — no `MData` node this crate emits
/// carries that key — so the test is vacuously false here.
fn check_implicit_lambda(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<(), ElabError> {
    if block_implicit_lambda(elem, kinds) {
        return Ok(());
    }
    let Some(expected) = expected else {
        return Ok(());
    };
    // oracle: `whnfForall expectedType` then `let .forallE _ _ _ c :=
    // expectedType | return .no`. `whnfForall` keeps the ORIGINAL term
    // when the reduct is not a forall; only the `forallE` test below
    // reads it, so reducing into a local is enough.
    let reduced = elab.mctx.whnf(expected)?;
    let base = elab.view.store;
    let Node::Forall { binder_info, .. } = elab.mctx.store().expr_node(Some(base), reduced) else {
        return Ok(());
    };
    // oracle: `unless c.isImplicit || c.isInstImplicit do return .no`.
    if !matches!(binder_info, BinderInfo::Implicit | BinderInfo::InstImplicit) {
        return Ok(());
    }
    Err(ElabError::UnsupportedSyntax(
        "implicit lambda insertion — M4b-3 P5".to_string(),
    ))
}

/// oracle: `blockImplicitLambda` (`TermElabM.lean:1715-1720`) —
/// "Block usage of implicit lambdas if `stx` is `@f` or `@f arg1 ...`
/// or `fun` with an implicit binder annotation":
///
/// ```text
/// let stx := Parser.Term.dropParens stx
/// isExplicit stx || isExplicitApp stx || isLambdaWithImplicit stx || isHole stx
///   || isTacticBlock stx || isNoImplicitLambda stx || isTypeAscription stx
/// ```
///
/// `isNoImplicitLambda` (`no_implicit_lambda% e`, `:1698-1701`) is the
/// one member with no leanr counterpart: that syntax is not registered
/// in `leanr_syntax`'s grammar at all, so no tree can carry it and the
/// disjunct is vacuously false. Every other member is transcribed.
fn block_implicit_lambda(elem: &SynElem, kinds: &KindInterner) -> bool {
    // oracle: `Parser.Term.dropParens` (`Lean/Parser/Term.lean:205-208`)
    // — strip LEADING `paren` wrappers (`(e)`), recursively. Note it
    // does NOT strip `typeAscription`, which is a distinct node kind in
    // both the oracle's grammar and leanr's, and is its own disjunct
    // below anyway.
    let mut cur = elem.clone();
    while kinds.name(cur.kind()) == "Lean.Parser.Term.paren" {
        // `paren`'s inner term is non-trivia child 1
        // (`builtin::ascription::elab_paren`'s own navigation).
        let Some(inner) = cur
            .as_node()
            .and_then(|n| dispatch::non_trivia_children(n).into_iter().nth(1))
        else {
            break;
        };
        cur = inner;
    }
    match kinds.name(cur.kind()) {
        // oracle: `isExplicit` (`:1674-1677`) — `` `(@$_) ``.
        "Lean.Parser.Term.explicit" => true,
        // oracle: `isHole` (`:1690-1691`).
        "Lean.Parser.Term.hole" | "Lean.Parser.Term.syntheticHole" => true,
        // oracle: `isTacticBlock` (`:1693-1696`) — `` `(by $_:tacticSeq) ``,
        // which is the `byTactic` kind. `byTactic'` (`show .. by ..`'s own
        // RHS parser) is a DIFFERENT kind and the oracle's quotation
        // pattern does not match it either.
        "Lean.Parser.Term.byTactic" => true,
        // oracle: `isTypeAscription` (`:1703-1704`).
        "Lean.Parser.Term.typeAscription" => true,
        // oracle: `isExplicitApp` (`:1679-1680`) — an application whose
        // FUNCTION (`stx[0]`) is itself `@..`.
        "Lean.Parser.Term.app" => cur
            .as_node()
            .and_then(|n| dispatch::non_trivia_children(n).into_iter().next())
            .is_some_and(|f| kinds.name(f.kind()) == "Lean.Parser.Term.explicit"),
        // oracle: `isLambdaWithImplicit` (`:1682-1688`).
        "Lean.Parser.Term.fun" => is_lambda_with_implicit(&cur, kinds),
        _ => false,
    }
}

/// oracle: `isLambdaWithImplicit` (`TermElabM.lean:1682-1688`) — "Return
/// true if `stx` is a lambda abstraction containing a `{}` or `[]`
/// binder annotation":
///
/// ```text
/// | `(fun $binders* => $_) =>
///     binders.raw.any fun b => b.isOfKind ``Lean.Parser.Term.implicitBinder
///                          || b.isOfKind `Lean.Parser.Term.instBinder
/// | _ => false
/// ```
///
/// `strictImplicitBinder` is deliberately absent from the oracle's list
/// (same remark as `useImplicitLambda`'s: strict-implicit never triggers
/// implicit lambdas), so it is absent here.
///
/// The `` `(fun $binders* => $_) `` quotation only matches the
/// `basicFun` shape, not `matchAlts` (`fun | .. => ..`), so a
/// non-`basicFun` body is `false` — not an error: this predicate runs
/// before dispatch and must never fail on syntax a later arm will name.
fn is_lambda_with_implicit(elem: &SynElem, kinds: &KindInterner) -> bool {
    let Some(node) = elem.as_node() else {
        return false;
    };
    // `fun`'s non-trivia child 1 is `basicFun` (or `matchAlts`);
    // `basicFun`'s child 0 is the binder-list wrapper
    // (`builtin::binder::elab_fun`'s own navigation).
    let Some(basic) = dispatch::non_trivia_children(node).into_iter().nth(1) else {
        return false;
    };
    let Some(basic) = basic.as_node() else {
        return false;
    };
    if kinds.name(basic.kind()) != "Lean.Parser.Term.basicFun" {
        return false;
    }
    let Some(binders) = dispatch::non_trivia_children(basic)
        .into_iter()
        .next()
        .and_then(|el| el.as_node().cloned())
    else {
        return false;
    };
    dispatch::non_trivia_children(&binders).iter().any(|b| {
        matches!(
            kinds.name(b.kind()),
            "Lean.Parser.Term.implicitBinder" | "Lean.Parser.Term.instBinder"
        )
    })
}
