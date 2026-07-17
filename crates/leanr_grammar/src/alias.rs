//! Moved to `leanr_syntax::grammar::alias` (M3b2b Task 5) so the
//! source-level `syntax`-command derivation shares the same pinned
//! table. This shim keeps `descr.rs`'s import path stable.

pub(crate) use leanr_syntax::grammar::alias::{lookup, AliasPrim};
