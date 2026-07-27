//! Expected-type propagation. Oracle: `getResultingTypeCore?`
//! (`App.lean:445-509`), `getResultingType?` (`App.lean:509-514`),
//! `shouldPropagateExpectedTypeFor` (`App.lean:516-523`) and
//! `propagateExpectedType` (`App.lean:563-609`).
//!
//! The heuristic runs as soon as the FIRST explicit argument is about to
//! be elaborated: it computes what the application's result type will be
//! (simulating `main` without elaborating anything) and unifies the
//! expected type against it, so the argument is then elaborated against
//! an already-informed parameter type. `App.lean:526-561`'s own doc
//! comment is the canonical motivation (`List.cons x []` against an
//! expected `List Int`).

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::BinderInfo;
use leanr_syntax::kind::KindInterner;

use crate::app::expand::Arg;
use crate::app::state::AppElab;
use crate::error::ElabError;

/// oracle: `shouldPropagateExpectedTypeFor` (`App.lean:516-523`).
/// `Arg.expr` is already elaborated, so there is nothing left to inform;
/// the three excluded kinds are the ones whose elaboration is DEFERRED
/// (a hole becomes an mvar, a `by` block a tactic mvar), so propagating
/// into them would over-commit the expected type before the deferred
/// elaboration ever runs.
pub fn should_propagate_expected_type_for(arg: &Arg, kinds: &KindInterner) -> bool {
    match arg {
        Arg::Expr(_) => false,
        Arg::Stx(elem) => {
            let k = kinds.name(elem.kind());
            k != "Lean.Parser.Term.hole"
                && k != "Lean.Parser.Term.syntheticHole"
                && k != "Lean.Parser.Term.byTactic"
        }
    }
}

/// oracle: `propagateExpectedType` (`App.lean:563-609`).
///
/// Called from `process_explicit_arg` immediately BEFORE
/// `elab_and_add_new_arg`, and — critically — before the argument is
/// removed from `st.args`, exactly as `App.lean:803-806` orders it
/// (`propagateExpectedType arg` runs before `modify fun s => { s with
/// args }`). The count `get_resulting_type` walks with therefore still
/// INCLUDES the argument about to be elaborated.
pub fn propagate_expected_type(
    app: &mut AppElab,
    kinds: &KindInterner,
    arg: &Arg,
) -> Result<(), ElabError> {
    if !should_propagate_expected_type_for(arg, kinds) {
        return Ok(());
    }
    // oracle: `unless !s.etaArgs.isEmpty || !s.propagateExpected`. The
    // `etaArgs` half is the oracle's own `TODO: handle s.etaArgs.size > 0`.
    if !app.st.eta_args.is_empty() || !app.st.propagate_expected {
        return Ok(());
    }
    let Some(expected) = app.st.expected_type else {
        // oracle: `| none => pure ()`.
        return Ok(());
    };
    // oracle: `let expectedType ← instantiateMVars expectedType` — a
    // LOCAL shadow; `s.expectedType?` itself is not rewritten.
    let expected = app.elab.mctx.instantiate_mvars(expected)?;
    if is_prop(app, expected) {
        // oracle: `App.lean:594-597`. `Prop` is often used as a more
        // general `Bool` (`if-then-else`), so propagating it would break
        // `def f (s : Nat × Bool) : Bool := if s.2 then ..`. Note this
        // branch does NOT unify — it only disables further propagation.
        app.st.propagate_expected = false;
        return Ok(());
    }
    let Some(resulting) = get_resulting_type(app)? else {
        // Propagation postponed; `propagateExpected` stays true so a
        // later parameter can try again.
        return Ok(());
    };
    // oracle: `trySynthesizeAppInstMVars` (`App.lean:601`). `instMVars`
    // has no P1 producer — `main`'s `BinderInfo::InstImplicit` arm is
    // itself a named P2 seam, so nothing can push onto it — but guard
    // rather than silently skipping a synthesis pass the oracle runs.
    if !app.st.inst_mvars.is_empty() {
        return Err(ElabError::UnsupportedSyntax(
            "pending instance-implicit mvars require typeclass synthesis — M4b-3 P2".to_string(),
        ));
    }
    if app.elab.mctx.is_def_eq(expected, resulting)? {
        // oracle's own emphasised note (`App.lean:602-604`): "we only set
        // `propagateExpected := false` when propagation has SUCCEEDED".
        // On failure the flag stays true so the next explicit parameter
        // retries with more information.
        app.st.propagate_expected = false;
    }
    Ok(())
}

/// oracle: `Expr.isProp` (`Lean/Expr.lean:837-839`) — `| sort .zero =>
/// true | _ => false`.
///
/// DELIBERATELY the SYNTACTIC predicate, not `Lean.Meta.isProp`
/// (`Lean/Meta/InferType.lean:323`, "does `e` have type `Sort 0`").
/// `App.lean:594` writes `expectedType.isProp` with no `←`, so Lean's
/// generalized field notation resolves it to `Lean.Expr.isProp`; the
/// same file uses the monadic one at `App.lean:68` as `(← isProp eType)`,
/// which is how the two are told apart. The distinction is observable:
/// for an expected type like `Eq a b` the semantic predicate is TRUE
/// (it is a proposition) while the syntactic one is FALSE (it is an
/// application, not `Sort 0`), so using the semantic form would silently
/// disable propagation for every application elaborated against a
/// proposition. The oracle's own doc comment confirms the intent —
/// "we just don't propagate the expected type when it IS `Prop`".
fn is_prop(app: &AppElab, e: ExprId) -> bool {
    match app.node(e) {
        Node::Sort { level } => {
            let base = app.elab.view.store;
            matches!(
                *app.elab.mctx.store().level_row(Some(base), level),
                LevelRow::Zero
            )
        }
        _ => false,
    }
}

/// `Expr.hasLooseBVars` — read straight off the packed per-node metadata
/// (`ExprData::loose_bvar_range`, `leanr_kernel/src/expr.rs:246`), which
/// `Store::expr_data` already exposes publicly. The saturation sentinel
/// documented on `loose_bvar_range_exact` does not affect this test: a
/// packed range of `0` is `min(actual, SAT)`, so it is exact, and any
/// nonzero packed value (saturated or not) proves `actual > 0`.
fn has_loose_bvars(app: &AppElab, e: ExprId) -> bool {
    let base = app.elab.view.store;
    app.elab
        .mctx
        .store()
        .expr_data(Some(base), e)
        .loose_bvar_range()
        > 0
}

/// oracle: `BinderInfo.isExplicit`.
fn is_explicit_binder(bi: BinderInfo) -> bool {
    matches!(bi, BinderInfo::Default)
}

/// oracle: `getResultingType?` (`App.lean:509-514`) plus its worker
/// `getResultingTypeCore?` (`App.lean:445-509`) — the resulting type of
/// the application, if enough is known, obtained by SIMULATING `main`
/// without elaborating anything.
///
/// Returns `Ok(None)` for every postponement the oracle has. Each one
/// that were dropped would turn into an over-eager unification assigning
/// an mvar the oracle leaves open, so they are enumerated explicitly
/// below rather than folded together.
pub fn get_resulting_type(app: &mut AppElab) -> Result<Option<ExprId>, ElabError> {
    // oracle: `getFType'` (`App.lean:287-291`) — `getFType` then
    // `instantiateMVars`, CACHING the result back into `s.fType`.
    let f_type = app.get_f_type()?;
    let f_type = app.elab.mctx.instantiate_mvars(f_type)?;
    app.st.f_type = f_type;

    let explicit = app.ctx.explicit;
    let ellipsis = app.ctx.ellipsis;
    let num_implicit_params = app.ctx.num_implicit_params;

    // The simulation's own copies — `main'`'s arguments. Nothing below
    // writes back to `app.st`.
    let mut param_idx = app.param_idx();
    let mut num_args = app.st.args.len();
    let mut named: Vec<String> = app.st.named_args.iter().map(|n| n.name.clone()).collect();
    let mut ty = f_type;

    // oracle: `main'`, as a loop (every recursive call is in tail
    // position).
    loop {
        // oracle: "we want to return an `fType` that's *not* in WHNF, so
        // we keep the original `fType` and compute a separate `fType'`".
        // The `hasLooseBVars` disjunct is what keeps `whnfForall` off an
        // OPEN term: `main'` recurses into the binding BODY without
        // instantiating, so `ty` carries loose bvars from the second
        // iteration on whenever the telescope is dependent.
        let ty_prime = if matches!(app.node(ty), Node::Forall { .. }) || has_loose_bvars(app, ty) {
            ty
        } else {
            app.whnf_forall(ty)?
        };

        let Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = app.node(ty_prime)
        else {
            // oracle: the `else if numArgs > 0 || !namedArgs.isEmpty`
            // arm — POSTPONEMENT 4: currently more arguments than
            // parameters (the function type may still reduce to a
            // forall once more is known).
            if num_args > 0 || !named.is_empty() {
                return Ok(None);
            }
            return Ok(finalize_resulting(app, ty));
        };

        // oracle: `Term.findNamedArg? namedArgs binderName` — rendering
        // the binder name costs an allocation, so only do it when there
        // is a named argument that could match at all (an anonymous
        // binder never matches: a `NamedArg`'s name is source text and
        // is never empty).
        if !named.is_empty() {
            if let Some(n) = binder_name {
                let rendered = render_name(app, n);
                if named.contains(&rendered) {
                    // oracle: `main' (paramIdx+1) numArgs (eraseNamedArg
                    // ..) fTypeBody` — the named argument fills this
                    // parameter, so no positional one is consumed.
                    named.retain(|na| *na != rendered);
                    param_idx += 1;
                    ty = body;
                    continue;
                }
            }
        }

        // oracle: `processImplicit' () := main' (paramIdx+1) numArgs
        // namedArgs fTypeBody`, spelled out at each use below.
        if !explicit
            && matches!(binder_info, BinderInfo::StrictImplicit)
            && num_args == 0
            && named.is_empty()
        {
            // A strict implicit with nothing left to process ends the
            // application (`processStrictImplicitArg`).
            return Ok(finalize_resulting(app, ty));
        } else if !explicit && !is_explicit_binder(binder_info) {
            param_idx += 1;
            ty = body;
            continue;
        } else if param_idx < num_implicit_params {
            // Simulates `processExplicitArg`'s `numImplicitParams`
            // override from this point onward (structure projections,
            // M4b-4 — no P1 producer, kept for fidelity).
            param_idx += 1;
            ty = body;
            continue;
        } else if num_args > 0 {
            param_idx += 1;
            num_args -= 1;
            ty = body;
            continue;
        } else if ellipsis || (!explicit && is_opt_or_auto_param(app, binder_type)?) {
            param_idx += 1;
            ty = body;
            continue;
        } else if has_loose_bvars(app, ty_prime) {
            // POSTPONEMENT 1: the resulting type still depends on
            // arguments that have not been elaborated yet.
            return Ok(None);
        } else if !named.is_empty() {
            // oracle: `if (← findNamedArgDependsOn? fType' namedArgs)
            // .isSome then processImplicit' () else` POSTPONEMENT 2 —
            // named arguments remain and eta arguments would be needed.
            //
            // The `isSome` half needs `forallTelescopeReducing` +
            // `exprDependsOn` over real fvars, which arrives with Task
            // 7's eta/named-argument machinery. Collapsing both halves
            // onto the POSTPONEMENT is the conservative direction (it can
            // only propagate LESS, never more) and is unobservable in P1:
            // `main` has no named-argument path at all yet, so any
            // application whose `named_args` are non-empty necessarily
            // ends in `process_explicit_arg`'s "named arguments with
            // missing positional arguments (eta expansion) — M4b-3 P1
            // task 7" seam or `main`'s "too many arguments" seam. Task 7
            // restores the `isSome` half together with the eta arm it
            // belongs to.
            return Ok(None);
        } else if !explicit {
            if crate::app::args::has_opt_or_auto_param(app, ty_prime)? {
                // POSTPONEMENT 3: the resulting type still has
                // optParams or autoParams to fill.
                return Ok(None);
            }
            return Ok(finalize_resulting(app, ty));
        } else {
            return Ok(finalize_resulting(app, ty));
        }
    }
}

/// oracle: `getResultingTypeCore?.finalize'` (`App.lean:503-509`). Note
/// it takes `fType`, NOT `fType'`: the caller deliberately returns the
/// type that was never WHNF-ed.
fn finalize_resulting(app: &AppElab, f_type: ExprId) -> Option<ExprId> {
    if has_loose_bvars(app, f_type) {
        // POSTPONEMENT 1 again, at the end of the telescope.
        None
    } else {
        Some(f_type)
    }
}

/// oracle: `Expr.isOptParam || Expr.isAutoParam` for ONE parameter type.
/// `consume_type_annotations` strips exactly those two wrappers, so
/// "stripping changed the term" is the same predicate — the equivalence
/// `app::args::has_opt_or_auto_param` already relies on.
fn is_opt_or_auto_param(app: &mut AppElab, param_type: ExprId) -> Result<bool, ElabError> {
    Ok(app.consume_type_annotations(param_type)? != param_type)
}

/// `NameId` -> the rendered dotted name a `NamedArg` carries as a
/// `String` (`expand::NamedArg`'s own doc explains why named-argument
/// names stay source text rather than becoming `NameId`s).
fn render_name(app: &AppElab, n: leanr_kernel::bank::NameId) -> String {
    let base = app.elab.view.store;
    app.elab
        .mctx
        .store()
        .to_name(Some(base), Some(n))
        .to_string()
}
