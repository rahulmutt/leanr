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

mod assign;
mod cache;
mod config;
mod defeq;
mod discr_path;
pub mod discr_tree;
mod error;
mod infer;
mod lazy_delta;
mod level;
mod metactx;
mod mvar_ctx;
#[cfg(test)]
mod test_support;
mod transparency;
mod whnf;

pub use config::{Config, ProjReduction};
pub use discr_tree::DiscrTree;
pub use error::MetaError;
pub use metactx::{MetaCtx, DEFAULT_STEP_BUDGET};
pub use mvar_ctx::{LMVarId, MVarDecl, MVarId, MVarKind, MetavarContext};
pub use transparency::{can_unfold, TransparencyMode};
