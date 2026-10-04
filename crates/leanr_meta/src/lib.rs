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

mod abstract_proofs;
mod assign;
#[cfg(test)]
mod aux_recursor;
mod cache;
mod check;
mod check_assignment;
mod closure;
mod coe;
mod config;
mod defeq;
mod discr_path;
pub mod discr_tree;
mod error;
mod head_index;
mod infer;
mod instances;
mod kabstract;
mod lazy_delta;
mod level;
mod level_params;
mod local_decl_kind;
mod local_entry;
mod local_instance;
mod local_snapshot;
mod loose_bvar;
mod max_height;
mod metactx;
mod mk_binding;
mod mvar_ctx;
mod structure;
mod synth;
#[cfg(test)]
mod test_support;
mod transform;
mod transparency;
mod whnf;

pub use abstract_proofs::{aux_lemma_key, AuxLemmaCache, AuxLemmas};
pub use closure::ClosureResult;
pub use config::{Config, ProjReduction};
pub use discr_tree::DiscrTree;
pub use error::MetaError;
pub use level_params::{
    name_cmp, sort_decl_level_params, CollectLevelParams, LevelMVarToParamResult,
};
pub use local_decl_kind::LocalDeclKind;
pub use local_snapshot::LocalCtxSnapshot;
pub use metactx::{EnvExtensions, MetaCtx, MetaSnapshot, DEFAULT_STEP_BUDGET};
pub use mvar_ctx::{DelayedMVarAssignment, LMVarId, MVarDecl, MVarId, MVarKind, MetavarContext};
pub use synth::LOption;
pub use transform::TransformStep;
pub use transparency::{can_unfold, TransparencyMode};
