//! oracle: `finalize` (`App.lean:610-660`).

use leanr_kernel::bank::ExprId;

use crate::app::state::AppElab;
use crate::error::ElabError;

pub fn finalize(app: &mut AppElab) -> Result<ExprId, ElabError> {
    // oracle: `for mvarId in s.toSetErrorCtx do
    // registerMVarErrorImplicitArgInfo ..` — error CONTEXT only, never
    // part of the emitted `Expr`. The ladder field it writes into
    // arrives in P2; until then the collected ids are simply unused.
    let e = app.st.f;

    // oracle: `unless s.etaArgs.isEmpty do e ← mkLambdaFVars ..`
    // (Task 7 populates `eta_args`).
    if !app.st.eta_args.is_empty() {
        return Err(ElabError::UnsupportedSyntax(
            "eta-expanded application (mkLambdaFVars over etaArgs) — M4b-3 P1 task 7".to_string(),
        ));
    }

    // oracle: `let eType ← inferType e` (`App.lean:633`), computed here
    // — BEFORE the `resultTypeOutParam?` branch — and guarded by the
    // oracle's own Remark (`App.lean:629-632`): do NOT reuse `s.fType`
    // as `eType` even when `etaArgs` is empty, because it may have been
    // unfolded (`get_f_type`/`whnf_forall` both rewrite it in place).
    let e_type = app.elab.mctx.infer_type(e)?;

    // oracle: the `resultTypeOutParam?` branch (`App.lean:637-648`).
    // `result_is_out_param_support` is false in the fixture env (no
    // `Lean.Internal.coeM`), so there is no P1 producer; guard anyway.
    if app.st.result_type_out_param.is_some() {
        return Err(ElabError::UnsupportedSyntax(
            "result-type outParam support requires default instances — M4b-3 P2".to_string(),
        ));
    }

    // oracle: `if let some expectedType := s.expectedType? then
    // trySynthesizeAppInstMVars; discard <| isDefEq expectedType eType`
    // (`App.lean:650-655`).
    if let Some(expected) = app.st.expected_type {
        // `trySynthesizeAppInstMVars` runs first in the oracle; the
        // `inst_mvars` guard below is P1's stand-in for it and rejects
        // the only state in which it would do anything.
        //
        // `discard <|`: a FAILED unification is DELIBERATELY ignored
        // here — "caller must handle it" (`App.lean:652`). `ensureHasType`
        // reports the mismatch with the full application in hand, which
        // is a strictly better message than anything this site could
        // produce. A genuine `MetaError` (not a `false` verdict) still
        // propagates.
        let _ = app.elab.mctx.is_def_eq(expected, e_type)?;
    }

    // oracle: `synthesizeAppInstMVars` (`App.lean:349-370`).
    if !app.st.inst_mvars.is_empty() {
        return Err(ElabError::UnsupportedSyntax(
            "pending instance-implicit mvars require typeclass synthesis — M4b-3 P2".to_string(),
        ));
    }
    Ok(e)
}
