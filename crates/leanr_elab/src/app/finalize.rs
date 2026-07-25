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
    // — a FAILED unification here is deliberately ignored: the caller
    // (`ensureHasType`) handles the mismatch. Task 6 adds this.

    // oracle: `synthesizeAppInstMVars` (`App.lean:349-370`).
    if !app.st.inst_mvars.is_empty() {
        return Err(ElabError::UnsupportedSyntax(
            "pending instance-implicit mvars require typeclass synthesis — M4b-3 P2".to_string(),
        ));
    }
    Ok(e)
}
