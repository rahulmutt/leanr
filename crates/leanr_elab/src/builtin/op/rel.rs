//! oracle: `elabBinRelCore` (`Extra.lean:497-562`). macro/binop% P3 Task 4
//! fills this in; until then `binrel%`/`binrel_no_prop%` stop at a seam
//! named by the literal kind.

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;

use super::OpView;
use crate::elab::TermElabM;
use crate::error::ElabError;

pub(crate) fn elab_bin_rel_core(
    _elab: &mut TermElabM,
    view: &OpView,
    _no_prop: bool,
    _kinds: &KindInterner,
    _expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    Err(ElabError::UnsupportedSyntax(
        view.kind.syntax_kind().to_string(),
    ))
}
