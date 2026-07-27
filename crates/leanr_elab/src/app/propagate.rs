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

use crate::app::args::find_named_arg_depends_on;
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
///
/// `pub` only so `tests/app_smoke.rs` can pin the syntactic-vs-semantic
/// distinction directly; it has no caller outside this module.
pub fn is_prop(app: &AppElab, e: ExprId) -> bool {
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
        let ty_prime = if matches!(app.node(ty), Node::Forall { .. }) || app.has_loose_bvars(ty) {
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
                let rendered = app.render_name(n);
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
        } else if app.has_loose_bvars(ty_prime) {
            // POSTPONEMENT 1: the resulting type still depends on
            // arguments that have not been elaborated yet.
            return Ok(None);
        } else if !named.is_empty() {
            // oracle: `if (← findNamedArgDependsOn? fType' namedArgs)
            // .isSome then processImplicit' () else` POSTPONEMENT 2 —
            // named arguments remain and eta arguments would be needed.
            //
            // Task 6 collapsed both halves onto the POSTPONEMENT because
            // the `isSome` half needs `forallTelescopeReducing` +
            // `exprDependsOn` over real fvars, which did not exist yet;
            // that was sound only because every P1 path with non-empty
            // `named_args` terminated in `process_explicit_arg`'s
            // eta-expansion seam. Task 7 removes that seam, so the escape
            // is restored here — the SAME `find_named_arg_depends_on`
            // `main`'s own eta-vs-implicit fork calls, on `fType'`
            // exactly as `App.lean:478` passes it. Without it, an
            // application whose named argument determines a missing
            // parameter would postpone propagation the oracle performs.
            //
            // DISCRIMINATED, not merely reasoned about — collapsing this
            // back onto the postponement fails both of:
            //   * `app/namedDepPropagate2` in the oracle corpus
            //     (`(dpick PUnit.unit (z := Nat.zero) : Unit)`; the
            //     escape emits `dpick Unit ..`, the postponement
            //     `dpick PUnit.{1} ..`), and
            //   * `app_smoke.rs`'s
            //     `get_resulting_type_escapes_past_a_parameter_a_named_arg_determines`,
            //     which asserts this function's own return value rather
            //     than a downstream term.
            // Both were measured against a collapsed build; see the
            // task-7 fix report. Do not re-collapse.
            if find_named_arg_depends_on(app, ty_prime, &named)?.is_some() {
                param_idx += 1;
                ty = body;
                continue;
            }
            return Ok(None);
        } else if !explicit {
            if crate::app::args::has_opt_auto_params(app, ty_prime)? {
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
    if app.has_loose_bvars(f_type) {
        // POSTPONEMENT 1 again, at the end of the telescope.
        None
    } else {
        Some(f_type)
    }
}

/// oracle: `Expr.isOptParam || Expr.isAutoParam` for ONE parameter type
/// (`App.lean:472`). `consume_opt_auto_param` strips exactly those two
/// wrappers — and, deliberately, NOT the `outParam`/`semiOutParam` that
/// the full `consume_type_annotations` also strips — so "stripping
/// changed the term" is the same predicate. This is the equivalence
/// `app::args::has_opt_auto_params` relies on too.
fn is_opt_or_auto_param(app: &mut AppElab, param_type: ExprId) -> Result<bool, ElabError> {
    Ok(app.consume_opt_auto_param(param_type)? != param_type)
}
