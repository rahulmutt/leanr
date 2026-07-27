//! `ElabAppArgs.main` and the parameter-kind arms. Oracle:
//! `App.lean:730-951`.
//!
//! `kinds` is threaded as an explicit parameter down `main` ->
//! `process_explicit_arg` -> `elab_and_add_new_arg` rather than stored on
//! `AppElab`: the `KindInterner` is passed per call everywhere in this
//! crate (`elab.rs`'s own module doc — one `TermElabM` can elaborate
//! nodes drawn from different snapshots), and holding a `&KindInterner`
//! inside `AppElab` alongside the `&mut TermElabM` would add a lifetime
//! parameter that buys nothing.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;
use leanr_meta::MVarId;
use leanr_syntax::kind::KindInterner;

use crate::app::expand::Arg;
use crate::app::state::AppElab;
use crate::error::ElabError;

/// oracle: `main` (`App.lean:926-951`).
pub fn main(app: &mut AppElab, kinds: &KindInterner) -> Result<ExprId, ElabError> {
    loop {
        if app.f_type_is_forall()? {
            let binder_name = app.get_param_name();
            // Task 7 inserts the named-argument lookup here, BEFORE the
            // binder-info dispatch (the oracle checks `findNamedArg?`
            // first, `App.lean:930-938`).
            match app.get_param_info()? {
                BinderInfo::Default => {
                    if !process_explicit_arg(app, kinds, binder_name)? {
                        return crate::app::finalize::finalize(app);
                    }
                }
                BinderInfo::Implicit => {
                    if !process_implicit_arg(app, kinds, binder_name)? {
                        return crate::app::finalize::finalize(app);
                    }
                }
                BinderInfo::StrictImplicit => {
                    if !process_strict_implicit_arg(app, kinds, binder_name)? {
                        return crate::app::finalize::finalize(app);
                    }
                }
                BinderInfo::InstImplicit => {
                    // oracle: `processInstImplicitArg` (`App.lean:900+`)
                    // creates an instance mvar and pushes it onto
                    // `instMVars` for `synthesizeAppInstMVars`. Both need
                    // the synthesis client and the fixpoint.
                    return Err(ElabError::UnsupportedSyntax(
                        "instance-implicit arguments require typeclass synthesis \
                         and the synthetic-mvar fixpoint — M4b-3 P2"
                            .to_string(),
                    ));
                }
            }
        } else if app.has_args_to_process() {
            // oracle: `synthesizePendingAndNormalizeFunType`
            // (`App.lean:372-404`) — synthesize pending instance mvars,
            // then re-WHNF; if `fType` is STILL not a forall it tries
            // `coerceToFunction?` and otherwise reports "function
            // expected". Both halves are later plans.
            return Err(ElabError::UnsupportedSyntax(
                "too many arguments: normalizing the function type needs pending-instance \
                 synthesis (M4b-3 P2) and CoeFun (M4b-3 P4)"
                    .to_string(),
            ));
        } else {
            return crate::app::finalize::finalize(app);
        }
    }
}

/// oracle: `processExplicitArg` (`App.lean:765-877`). Returns `false`
/// when the oracle's own control flow reaches `finalize` (no argument
/// left to consume and no eta/optParam path applies), so `main` can
/// finalize rather than looping.
fn process_explicit_arg(
    app: &mut AppElab,
    kinds: &KindInterner,
    binder_name: Option<NameId>,
) -> Result<bool, ElabError> {
    if app.param_idx() < app.ctx.num_implicit_params {
        // Only reachable via structure-projection expansion (M4b-4),
        // which is the sole producer of `num_implicit_params > 0`.
        return Err(ElabError::UnsupportedSyntax(
            "numImplicitParams override (structure projection) — M4b-4".to_string(),
        ));
    }
    if let Some(arg) = app.st.args.first().cloned() {
        // oracle: `App.lean:803-806` — `propagateExpectedType arg` runs
        // BEFORE `modify fun s => { s with args }`, i.e. while the
        // argument about to be elaborated is still counted in
        // `s.args.length`. `get_resulting_type` walks that count, so
        // popping first would simulate one parameter too few. Hence the
        // clone-then-remove rather than `remove(0)` up front.
        crate::app::propagate::propagate_expected_type(app, kinds, &arg)?;
        app.st.args.remove(0);
        elab_and_add_new_arg(app, kinds, binder_name, arg)?;
        return Ok(true);
    }
    // No positional argument left. The oracle now branches on ellipsis,
    // optParam, autoParam, named args, and eta — Tasks 7-8 and P5. With
    // none of those in P1, this is `finalize`.
    if app.ctx.ellipsis {
        return Err(ElabError::UnsupportedSyntax(
            "`..` ellipsis argument filling — M4b-3 P5".to_string(),
        ));
    }
    if !app.st.named_args.is_empty() {
        return Err(ElabError::UnsupportedSyntax(
            "named arguments with missing positional arguments (eta expansion) — \
             M4b-3 P1 task 7"
                .to_string(),
        ));
    }
    // oracle: the `optParam`/`autoParam` default-filling arms
    // (`App.lean:827-855`) live here. `get_arg_expected_type` already
    // STRIPS the wrapper (task 3), so an explicitly-supplied argument to
    // a wrapped parameter is handled above; only the DEFAULT path is
    // deferred. Detect it rather than finalizing a shorter application
    // than the oracle would build.
    let f_type = app.get_f_type()?;
    if has_opt_or_auto_param(app, f_type)? {
        return Err(ElabError::UnsupportedSyntax(
            "optParam default / autoParam tactic argument — M4b-3 P5".to_string(),
        ));
    }
    Ok(false)
}

/// oracle: `hasOptAutoParams` (`App.lean:121-127`) over the WHOLE
/// remaining telescope, as `App.lean:873`'s `hasOptAutoParams
/// (← getFType)` demands — `getFType` is the entire remaining function
/// type, not the current parameter's.
///
/// The narrower current-parameter-only test the plan originally
/// specified here is a named-seam hole, not just an imprecision: for
/// `f : (a : Nat) → (b : Nat := 0) → Nat` applied with no positional
/// arguments, the oracle takes `addEtaArg` and builds `fun a => f a 0`,
/// while a test that finds no wrapper on `a` would return `false` and
/// let `main` finalize the bare partial application `f` — a DIFFERENT
/// term, silently, with no error and no seam. Over-detection is the
/// safe direction: it can only turn a would-be-wrong term into a named
/// `UnsupportedSyntax`.
///
/// Task 7 replaces this with the oracle's full
/// `forallTelescopeReducing` form (which WHNFs each body as it goes,
/// and which the eta decision needs anyway); this walks the already-
/// instantiated spine without reducing, which is strictly more
/// conservative — a telescope that only reveals a wrapper after
/// reduction is missed here, and Task 7 closes that.
///
/// Takes the type to walk as a parameter (Task 6): `App.lean:873`'s call
/// site passes `(← getFType)`, but `getResultingTypeCore?`'s own call
/// (`App.lean:484`) passes the SIMULATED remaining type `fType'`, which
/// is not `s.fType`. One function, two call sites, exactly as the oracle
/// has it.
pub(crate) fn has_opt_or_auto_param(app: &mut AppElab, mut cur: ExprId) -> Result<bool, ElabError> {
    // Walking into `body` carries LOOSE BVARS (a deeper binder's domain
    // may reference an earlier binder of this same telescope). That is
    // fine: `consume_type_annotations` only walks the application spine
    // and reads the head's `Const` name — it never instantiates, infers,
    // or reduces — so a loose bvar is just a non-`Const` head it falls
    // through on. See that method's own doc comment.
    while let Node::Forall {
        binder_type, body, ..
    } = app.node(cur)
    {
        if app.consume_type_annotations(binder_type)? != binder_type {
            return Ok(true);
        }
        cur = body;
    }
    Ok(false)
}

/// oracle: `addImplicitArg` (`App.lean:747-760`). Creates a fresh mvar
/// for the parameter, records it in `toSetErrorCtx` for error
/// attribution, and continues the loop.
///
/// No `kinds` parameter: unlike `process_explicit_arg`'s eventual
/// `elab_and_add_new_arg` call, nothing here parses or elaborates
/// surface syntax — the argument is a freshly minted mvar, not a
/// `Arg::Stx` — so there is no `KindInterner` use to thread. The
/// brief's own signature carried it only for symmetry with the other
/// two arms and ended in `let _ = kinds;`; dropping the unused
/// parameter here rather than shipping a discard.
fn add_implicit_arg(app: &mut AppElab) -> Result<(), ElabError> {
    let arg_type = app.get_arg_expected_type()?;
    // oracle: the `isNextOutParamOfLocalInstanceAndResult` branch
    // (`App.lean:749-757`) sets `resultTypeOutParam?` and disables
    // propagation. It needs class outParam positions from the
    // `classExtension`, which leanr does not decode until P2; the
    // guarding flag (`result_is_out_param_support`) is false in the
    // fixture env, so the branch is inert here rather than skipped
    // silently. `finalize` re-checks `result_type_out_param` (task 4).
    if app.ctx.result_is_out_param_support {
        return Err(ElabError::UnsupportedSyntax(
            "local-instance outParam result type requires classExtension decode — M4b-3 P2"
                .to_string(),
        ));
    }
    let arg = app.elab.mk_fresh_expr_mvar(arg_type)?;
    if let Node::MVar { id: Some(n) } = app.node(arg) {
        app.st.to_set_error_ctx.push(MVarId(n));
    }
    add_new_arg(app, arg)
}

/// oracle: `processImplicitArg` (`App.lean:879-885`) — under `@`, an
/// implicit parameter is filled from the positional arguments exactly
/// like an explicit one.
fn process_implicit_arg(
    app: &mut AppElab,
    kinds: &KindInterner,
    binder_name: Option<NameId>,
) -> Result<bool, ElabError> {
    if app.ctx.explicit {
        process_explicit_arg(app, kinds, binder_name)
    } else {
        add_implicit_arg(app)?;
        Ok(true)
    }
}

/// oracle: `processStrictImplicitArg` (`App.lean:887-895`) — a strict
/// implicit is inserted ONLY when there is still an argument to
/// process; otherwise the application finalizes here. This is the one
/// arm whose difference from `processImplicitArg` is invisible on
/// single-argument corpus terms, so `app_smoke.rs` gets a direct test.
fn process_strict_implicit_arg(
    app: &mut AppElab,
    kinds: &KindInterner,
    binder_name: Option<NameId>,
) -> Result<bool, ElabError> {
    if app.ctx.explicit {
        process_explicit_arg(app, kinds, binder_name)
    } else if app.has_args_to_process() {
        add_implicit_arg(app)?;
        Ok(true)
    } else {
        Ok(false)
    }
}

/// oracle: `addNewArg` (`App.lean:418-429`) — `f := f arg`, push onto
/// `fArgs`, and advance `fType` to its BINDING BODY (not a
/// re-instantiated type: the loose bvars are instantiated lazily by
/// `get_f_type`, which is what makes `paramIdx`/`fArgs` the single
/// source of truth).
pub fn add_new_arg(app: &mut AppElab, arg: ExprId) -> Result<(), ElabError> {
    let body = match app.node(app.st.f_type) {
        Node::Forall { body, .. } => body,
        _ => {
            return Err(ElabError::IllFormedSyntax(
                "add_new_arg on a non-forall fType".to_string(),
            ))
        }
    };
    // `base = Some(view.store)`, never `None`: both `app.st.f` (the head
    // constant, built by `head.rs` against the persistent store) and
    // `arg` can be PERSISTENT-region `ExprId`s, and `store_mut()` is the
    // SCRATCH store — routing a persistent id through it without a base
    // is `Store::store_for`'s own documented "silent wrong-row read"
    // (a `debug_assert!` in debug builds, nothing at all in release).
    let base = app.elab.view.store;
    let f = app
        .elab
        .mctx
        .store_mut()
        .expr_app(Some(base), app.st.f, arg)
        .map_err(leanr_meta::MetaError::from)?;
    app.st.f = f;
    app.st.f_args.push(arg);
    app.st.f_type = body;
    Ok(())
}

/// oracle: `elabAndAddNewArg` (`App.lean:431-441`) — elaborate the
/// argument against the parameter's expected type, `ensureArgType` it,
/// then `addNewArg`.
fn elab_and_add_new_arg(
    app: &mut AppElab,
    kinds: &KindInterner,
    _binder_name: Option<NameId>,
    arg: Arg,
) -> Result<(), ElabError> {
    let expected = app.get_arg_expected_type()?;
    let val = match arg {
        Arg::Expr(e) => e,
        Arg::Stx(elem) => app.elab.elab_term(&elem, kinds, Some(expected))?,
    };
    // oracle: `ensureArgType` = `ensureHasType expected val`
    // (coercion-inserting from P4 onward; here the M4b-1 behavior, which
    // ERRORS on a defeq mismatch).
    let inferred = app.elab.mctx.infer_type(val)?;
    if !app.elab.mctx.is_def_eq(inferred, expected)? {
        return Err(ElabError::TypeMismatch {
            expected,
            got: inferred,
        });
    }
    add_new_arg(app, val)
}
