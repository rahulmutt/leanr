//! The elaborator-level `MetaM` core: reduction, definitional equality,
//! and typeclass synthesis over terms containing metavariables.
//!
//! This is NOT `leanr_kernel`'s `whnf`/`is_def_eq`. The kernel's is a
//! total question about closed, mvar-free terms and is an INDEPENDENT
//! check on what this crate produces; no reduction logic is shared in
//! either direction, even where the rules coincide. See the spec's
//! § Scope decisions for why the kernel is not generalized over a
//! trait.
//!
//! spec: docs/superpowers/specs/2026-07-20-m4a-meta-core-design.md

mod config;
mod error;
mod mvar_ctx;
mod transparency;

pub use config::{Config, ProjReduction};
pub use error::MetaError;
pub use mvar_ctx::{MVarDecl, MVarId, MVarKind, MetavarContext};
pub use transparency::{can_unfold, TransparencyMode};
