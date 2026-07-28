//! oracle: `finalize` (`App.lean:610-660`).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};

use crate::app::state::AppElab;
use crate::error::ElabError;

pub fn finalize(app: &mut AppElab) -> Result<ExprId, ElabError> {
    // oracle: `let ref ← getRef; for mvarId in s.toSetErrorCtx do
    // registerMVarErrorImplicitArgInfo mvarId ref e` (`App.lean:616-620`)
    // — error CONTEXT only, never part of the emitted `Expr`. `e` here is
    // still `s.f` UNMODIFIED, since this runs before the eta-lambda
    // wrapping below — same ordering as the oracle's own `let mut e :=
    // s.f` immediately above its loop. `ref` is the oracle's ambient
    // `getRef`; `Context::stx` is its stand-in (this module's own doc).
    // P2a implemented this: `register_mvar_error_implicit_arg_info`
    // (`synthetic.rs`) is the ladder field this loop writes into, and
    // `AppElab::synthesize_app_inst_mvars` below already calls it for a
    // different producer (unsolved instance mvars) — this is the OTHER
    // caller, transliterated straight from the oracle rather than left
    // as a comment claiming its target does not exist yet.
    for mvar_id in std::mem::take(&mut app.st.to_set_error_ctx) {
        app.elab
            .register_mvar_error_implicit_arg_info(mvar_id, app.ctx.stx.clone(), app.st.f);
    }
    let mut e = app.st.f;

    // oracle: `unless s.etaArgs.isEmpty do
    //   e ← mkLambdaFVars (s.etaArgs.map (·.2)) e
    //   e := e.updateBinderNames (s.etaArgs.map (some <| ·.1)).toList`
    // (`App.lean:621-624`). The eta fvars are still live in the ambient
    // `lctx` here — `app::elab_app_aux` brackets the whole `main` call
    // and only restores AFTER `finalize` has abstracted them away.
    if !app.st.eta_args.is_empty() {
        let fvars: Vec<ExprId> = app.st.eta_args.iter().map(|(_, fvar)| *fvar).collect();
        e = app
            .elab
            .mctx
            .mk_lambda(&fvars, e)
            .map_err(ElabError::from)?;
        // `mk_lambda` takes each binder's name off its `lctx` decl, and
        // `add_eta_arg` declared those with FRESH names (so remaining
        // arguments could not capture the parameter's name). This step
        // puts the user-facing parameter names back, exactly as the
        // oracle's own `updateBinderNames` call does for exactly the same
        // reason.
        let names: Vec<Option<NameId>> = app.st.eta_args.iter().map(|(n, _)| *n).collect();
        e = update_binder_names(app, e, &names)?;
    }

    // oracle: `let eType ← inferType e` (`App.lean:629`), computed here
    // — BEFORE the `resultTypeOutParam?` branch — and guarded by the
    // oracle's own Remark (`App.lean:625-628`): do NOT reuse `s.fType`
    // as `eType` even when `etaArgs` is empty, because it may have been
    // unfolded (`get_f_type`/`whnf_forall` both rewrite it in place).
    let e_type = app.elab.mctx.infer_type(e)?;

    // oracle: the `resultTypeOutParam?` branch (`App.lean:637-648`).
    // `result_is_out_param_support` is false in the fixture env (no
    // `Lean.Internal.coeM`), so there is no P1 producer; guard anyway.
    if app.st.result_type_out_param.is_some() {
        return Err(ElabError::UnsupportedSyntax(
            "result-type outParam support requires default instances — M4b-3 P2b".to_string(),
        ));
    }

    // oracle: `if let some expectedType := s.expectedType? then
    // trySynthesizeAppInstMVars; discard <| isDefEq expectedType eType`
    // (`App.lean:647-655`).
    if let Some(expected) = app.st.expected_type {
        // oracle: `trySynthesizeAppInstMVars` (`App.lean:648`) runs
        // BEFORE the unification, so instance arguments are solved with
        // the information available at this point and `isDefEq` sees the
        // resulting assignments — it sits where the oracle's call sits,
        // matching `propagate::propagate_expected_type`'s own
        // transcription of the same line (`App.lean:601`).
        app.try_synthesize_app_inst_mvars()?;
        // `discard <|`: a FAILED unification is DELIBERATELY ignored
        // here — "caller must handle it" (`App.lean:649`). `ensureHasType`
        // reports the mismatch with the full application in hand, which
        // is a strictly better message than anything this site could
        // produce. A genuine `MetaError` (not a `false` verdict) still
        // propagates.
        let _ = app.elab.mctx.is_def_eq(expected, e_type)?;
    }

    // oracle: the trailing `synthesizeAppInstMVars` (`App.lean:656`,
    // defined at `App.lean:349-370`) — the COMMITTING pass that runs on
    // EVERY exit path, expected type or not. `Context::stx`'s own doc
    // explains why this needs a clone rather than a borrow of
    // `app.ctx.stx` directly: the method takes `&mut self`.
    let stx = app.ctx.stx.clone();
    app.synthesize_app_inst_mvars(&stx)?;
    Ok(e)
}

/// oracle: `Expr.updateBinderNames` (`Lean/Expr.lean:1394-1402`) — walk
/// `e`'s OUTERMOST binders in order, replacing each one's binder name
/// with the corresponding entry of `names`, and stop as soon as either
/// list runs out or `e` stops being a binder.
///
/// The oracle's parameter is `List (Option Name)`, where `none` means
/// "keep the existing name". This one is `&[Option<NameId>]` where the
/// `Option` is the NAME ITSELF (`None` = anonymous), because the sole
/// call site passes `s.etaArgs.map (some <| ·.1)` — every entry is
/// `some`, so the oracle's keep-existing case is unreachable and
/// modelling it would mean nesting `Option` twice for no caller.
fn update_binder_names(
    app: &mut AppElab,
    e: ExprId,
    names: &[Option<NameId>],
) -> Result<ExprId, ElabError> {
    let Some((name, rest)) = names.split_first() else {
        return Ok(e);
    };
    // `base = Some(view.store)`, never `None`: `binder_type` and `body`
    // are children of a term whose leaves can be PERSISTENT-region
    // `ExprId`s (the head constant, the fixture's own parameter types),
    // and `store_mut()` is the SCRATCH store — routing a persistent id
    // through it with no base is `Store::store_for`'s documented "silent
    // wrong-row read". Same convention as `args::add_new_arg` and
    // `state::f_type_is_forall`.
    let base = app.elab.view.store;
    match app.node(e) {
        Node::Lam {
            binder_type,
            body,
            binder_info,
            ..
        } => {
            let body = update_binder_names(app, body, rest)?;
            Ok(app
                .elab
                .mctx
                .store_mut()
                .expr_lam(Some(base), *name, binder_type, body, binder_info)
                .map_err(leanr_meta::MetaError::from)?)
        }
        Node::Forall {
            binder_type,
            body,
            binder_info,
            ..
        } => {
            let body = update_binder_names(app, body, rest)?;
            Ok(app
                .elab
                .mctx
                .store_mut()
                .expr_forall(Some(base), *name, binder_type, body, binder_info)
                .map_err(leanr_meta::MetaError::from)?)
        }
        _ => Ok(e),
    }
}
