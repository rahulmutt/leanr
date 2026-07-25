//! The overload shape guard. Oracle: `elabAppAux` (`App.lean:2202-2217`)
//! takes `candidates`, and with more than one runs `getSuccesses` /
//! ambiguity reporting / `mergeFailures`. That machinery is unreachable
//! while `resolve_global` resolves only exact names (no `open`, no
//! aliases, no `_root_`, no `choice` nodes), so it is NOT built
//! speculatively — the shape is asserted instead.

use leanr_kernel::bank::ExprId;

use crate::error::ElabError;

pub fn expect_single(candidates: Vec<ExprId>) -> Result<ExprId, ElabError> {
    match candidates.len() {
        1 => Ok(candidates.into_iter().next().expect("len == 1")),
        0 => Err(ElabError::IllFormedSyntax(
            "elab_app_fn returned no candidates".to_string(),
        )),
        n => Err(ElabError::UnsupportedSyntax(format!(
            "overloaded application ({n} candidates) requires namespace/alias \
             resolution — the slice that grows resolve_global owns this"
        ))),
    }
}
