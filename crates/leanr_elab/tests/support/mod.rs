//! Cross-crate include of `leanr_meta`'s canonical decode/encode scheme
//! (`decode_expr`/`encode_expr`/`EncSt`/`fixture_in`/`replay_fixture_in`)
//! — ONE source of truth (`crates/leanr_meta/tests/support/mod.rs`),
//! extended by `leanr_meta`'s own tasks, never copied here. See that
//! file's own module doc for the scheme itself; this file contributes
//! nothing but the `#[path]` include.
#[path = "../../../leanr_meta/tests/support/mod.rs"]
mod meta_support;
pub use meta_support::*;
