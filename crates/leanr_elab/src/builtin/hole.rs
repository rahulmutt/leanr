//! `_` — oracle: `elabHole` (`Lean/Elab/BuiltinTerm.lean:64-67`):
//!
//! ```text
//! elabHole stx expectedType? := do
//!   let kind := if (← read).inPattern || !(← read).holesAsSyntheticOpaque
//!     then MetavarKind.natural else MetavarKind.syntheticOpaque
//!   let mvar ← mkFreshExprMVar expectedType? kind
//!   registerMVarErrorHoleInfo mvar.mvarId! stx
//!   pure mvar
//! ```
//!
//! `kind` (`Natural` vs. `SyntheticOpaque`) never shows up in this
//! crate's canonical output — the differential harness's encoding
//! scheme numbers an `mvar` node purely by first-occurrence INDEX
//! (`EncSt`'s own scheme, `leanr_meta/tests/support/mod.rs`), never by
//! kind — and `SyntheticOpaque`'s whole POINT (never resolved by
//! ordinary unification, only by the elaborator that created it) has no
//! observer anywhere in this slice: no pattern-elaboration context
//! exists yet to make `inPattern` meaningful, and nothing here ever
//! runs `is_def_eq` against an unassigned hole expecting a kind-
//! dependent answer. So `mk_fresh_expr_mvar` mints every hole
//! `MVarKind::Natural` uniformly (this task's own stated interface) —
//! not an approximation with an observable difference, just an unmade
//! distinction. `registerMVarErrorHoleInfo` (diagnostic bookkeeping
//! only, no `Expr` effect) has no analog in this crate.
//!
//! `expectedType?` reaching `none` (this crate's `expected: None`)
//! routes through `mkFreshExprMVarImpl`'s own `none` arm
//! (`Lean/Meta/Basic.lean:867-871`, read directly from the pinned
//! toolchain source before transcribing): first mint a fresh level mvar
//! `?u`, then a fresh expr mvar of type `Sort ?u` (this IS
//! `mkFreshTypeMVar`, inlined rather than given its own helper — one
//! call site, and inlining keeps `mk_fresh_expr_mvar`'s own signature
//! (`ty: ExprId`, no `Option`) exactly as this task specifies), then
//! mint the actual hole AT that type mvar.

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

use crate::elab::TermElabM;
use crate::error::ElabError;

pub fn elab_hole(
    elab: &mut TermElabM,
    _node: &SyntaxNode,
    _kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let ty = match expected {
        Some(t) => t,
        None => {
            // `mkFreshTypeMVar`: a fresh level mvar, then a fresh expr
            // mvar of type `Sort` that level.
            let u = elab.mk_fresh_level_mvar()?;
            let sort = elab
                .mctx
                .store_mut()
                .expr_sort(None, u)
                .map_err(leanr_meta::MetaError::from)?;
            elab.mk_fresh_expr_mvar(sort)?
        }
    };
    elab.mk_fresh_expr_mvar(ty)
}
