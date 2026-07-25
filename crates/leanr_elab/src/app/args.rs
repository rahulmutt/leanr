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

use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;
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
                bi @ (BinderInfo::Implicit | BinderInfo::StrictImplicit) => {
                    // Task 5.
                    return Err(ElabError::UnsupportedSyntax(format!(
                        "implicit argument insertion ({bi:?}) — M4b-3 P1 task 5"
                    )));
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
    if !app.st.args.is_empty() {
        let arg = app.st.args.remove(0);
        // Task 6 inserts `propagate_expected_type(app, &arg)?` HERE —
        // the oracle propagates BEFORE elaborating the argument
        // (`App.lean:803-806`).
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
    if has_opt_or_auto_param(app)? {
        return Err(ElabError::UnsupportedSyntax(
            "optParam default / autoParam tactic argument — M4b-3 P5".to_string(),
        ));
    }
    Ok(false)
}

/// oracle: `hasOptAutoParams` (`App.lean:121-127`) restricted to the
/// CURRENT parameter — enough to detect the deferred default-filling
/// path without walking the whole remaining telescope (Task 7 widens
/// this to the oracle's full `forallTelescopeReducing` form, which the
/// eta decision needs).
fn has_opt_or_auto_param(app: &mut AppElab) -> Result<bool, ElabError> {
    let raw = app.get_param_type()?;
    let stripped = app.get_arg_expected_type()?;
    Ok(raw != stripped)
}

/// oracle: `addNewArg` (`App.lean:418-429`) — `f := f arg`, push onto
/// `fArgs`, and advance `fType` to its BINDING BODY (not a
/// re-instantiated type: the loose bvars are instantiated lazily by
/// `get_f_type`, which is what makes `paramIdx`/`fArgs` the single
/// source of truth).
pub fn add_new_arg(app: &mut AppElab, arg: ExprId) -> Result<(), ElabError> {
    let body = match app.node(app.st.f_type) {
        leanr_kernel::bank::terms::Node::Forall { body, .. } => body,
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
