//! The overload shape guard. Oracle: `elabAppAux` (`App.lean:2202-2217`)
//! takes `candidates`, and with more than one runs `getSuccesses` /
//! ambiguity reporting / `mergeFailures`. That machinery is overloaded
//! elaboration, M4c-2b-ii: until it lands, an identifier with several
//! candidates is seamed by `resolve::expect_one` before it gets here, and
//! this guard asserts the shape instead.

use leanr_kernel::bank::ExprId;

use crate::error::ElabError;

pub fn expect_single(candidates: Vec<ExprId>) -> Result<ExprId, ElabError> {
    match candidates.len() {
        1 => Ok(candidates.into_iter().next().expect("len == 1")),
        0 => Err(ElabError::IllFormedSyntax(
            "elab_app_fn returned no candidates".to_string(),
        )),
        n => Err(ElabError::UnsupportedSyntax(format!(
            "overloaded application ({n} candidates) — M4c-2b-ii"
        ))),
    }
}
