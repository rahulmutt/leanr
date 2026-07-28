//! `synthesizeSyntheticMVars` — the elaborator's scheduler. Oracle:
//! `Lean/Elab/SyntheticMVars.lean`, plus the state and registration
//! helpers from `Lean/Elab/Term/TermElabM.lean`.
//!
//! M4b-2 deliberately shipped no scheduler because no closed term in its
//! grammar created a synthetic mvar. M4b-3 P1 created the first ones
//! (implicit-argument mvars) but drained none. This module is where
//! every synthetic mvar leanr creates is finally either solved, resumed,
//! or reported stuck.
//!
//! The state lives on `TermElabM` (see `elab.rs`), mirroring the
//! oracle's `Term.State`/`Term.Context` one-to-one; only the `impl`
//! block is here. A nested sub-struct was rejected: every step touching
//! both the table and `&mut self` would need a `mem::take`/restore dance
//! for no structural gain (design spec § P2a).
//!
//! **Layout (M4b-3 P3 task 1).** P2a shipped this as one 804-line file.
//! It splits here, BEFORE P3's `synthesizeUsingDefault*` family adds
//! ~250 more lines to it (design spec § Amendment 2, item 3), along the
//! oracle's own seams:
//!
//! ```text
//!   state.rs ......... the decl/error tables and their registration
//!                      (`TermElabM.lean`'s half)
//!   ladder.rs ........ the step, the five rungs, `withSynthesize`,
//!                      `resumePostponed` (`SyntheticMVars.lean`'s
//!                      scheduler half)
//!   report.rs ........ stuck reporting and its priority sort
//!   default_inst.rs .. rung 3's real body (P3 task 5)
//! ```
//!
//! Every `impl<'e> TermElabM<'e>` block below is a continuation of the
//! same inherent impl; Rust allows one type's inherent methods to be
//! split across sibling modules of the defining crate, so the split
//! changes no call site and no visibility.

mod ladder;
mod report;
pub mod state;

pub use ladder::PostponeBehavior;
pub use state::{MVarErrorInfo, MVarErrorKind, SavedContext, SyntheticMVarDecl, SyntheticMVarKind};
