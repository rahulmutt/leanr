//! The bridge between decoded `.olean` parser-extension entries and the
//! parser's grammar snapshot: interprets `ParserDescr` constant values
//! from the term bank into `Prim` productions and assembles the
//! per-import-set base snapshot. Sits between `leanr_olean` (which
//! decodes entries but never interprets) and `leanr_syntax` (which has
//! zero workspace deps) — see the M3b2a design spec.

mod alias;
mod assemble;
mod descr;

pub use assemble::{assemble, AssembledGrammar, SkipReason, SkippedEntry};
