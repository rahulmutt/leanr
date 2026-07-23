//! M4b-1: the leaf term elaborator. `TermElabM` over `leanr_meta`'s
//! MetaM core; elaborates string literals, sorts, global-constant
//! identifiers, ascription, and holes. See
//! docs/superpowers/specs/2026-07-23-m4b1-leaf-term-elaborator-design.md.
pub mod builtin; // Tasks 4-6
pub mod dispatch;
pub mod elab;
pub mod error;
pub mod resolve; // Task 5

pub use elab::TermElabM;
pub use error::ElabError;
