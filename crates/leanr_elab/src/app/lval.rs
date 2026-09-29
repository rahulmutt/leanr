//! M4b-4a: the LVal machinery — dot notation's field and index
//! projections. Oracle: `Lean/Elab/App.lean:1435-1897` (pinned
//! v4.33.0-rc1). Design: docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md.

use leanr_kernel::bank::{ExprId, LevelId};
use leanr_syntax::kind::KindInterner;

use crate::app::AppCall;
use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `inductive LVal` (`TermElabM.lean:662-672`). The
/// `suffix?`/`fullRef` fields of `fieldName` only feed the
/// unknown-name error of an identifier-embedded field, which is P4's
/// (`resolveName`'s field split); they are added there.
#[derive(Debug, Clone)]
pub enum LVal {
    FieldName {
        r#ref: SynElem,
        name: String,
        levels: Vec<LevelId>,
    },
    FieldIdx {
        r#ref: SynElem,
        idx: usize,
        levels: Vec<LevelId>,
    },
}

/// oracle: `elabAppLVals` / `elabAppLValsAux` (`App.lean:1843-1897`).
pub fn elab_app_lvals(
    elab: &mut TermElabM,
    f: ExprId,
    lvals: Vec<LVal>,
    call: AppCall,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    if lvals.is_empty() {
        return crate::app::elab_app_args(elab, f, call, kinds);
    }
    Err(ElabError::UnsupportedSyntax(
        "field projection — M4b-4a P1 (lval.rs)".to_string(),
    ))
}
