//! Kernel data model. This crate is the trusted computing base (see
//! AGENTS.md): it must depend on no other workspace crate, and it holds
//! only the data types in M1a — the checker arrives in M1b.
//!
//! Values of these types are built from UNTRUSTED `.olean` bytes by
//! `leanr_olean`, so they can be adversarially shaped (e.g. 100k-deep
//! `Name` parent chains). Nothing here may recurse proportionally to
//! value depth EXCEPT through `RecGuard::enter` (guard.rs), which
//! bounds depth (error at the cap, never a panic) and grows the stack
//! via `stacker` beneath it. Everything else stays loops or explicit
//! stacks, and the `Arc` tree types implement iterative `Drop`.

pub mod bank;
pub mod checked;
mod decl;
mod env;
mod error;
mod expr;
mod guard;
mod inductive;
mod level;
mod local_ctx;
mod name;
mod num;
mod quot;
mod quot_red;
mod replay;
mod subst;
mod syntax;
mod tc;
#[cfg(test)]
mod testenv;
mod used_consts;

pub use checked::{CheckedConstants, ConstSource};
pub use decl::{
    constant_info_eq, AxiomVal, ConstantInfo, ConstantVal, ConstructorVal, Declaration,
    DefinitionSafety, DefinitionVal, InductiveType, InductiveVal, OpaqueVal, QuotKind, QuotVal,
    RecursorRule, RecursorVal, ReducibilityHints, TheoremVal,
};
// Pre-flip decoder-boundary `Arc*` twins + their bridges: demoted to
// kernel test support (term-bank phase 3's direct-to-id decode flip —
// see `decl.rs`'s module doc). `#[cfg(test)] pub use` only takes effect
// when THIS crate is compiled under test (`cargo test -p leanr_kernel`,
// or any of its own `#[cfg(test)] mod`s); an external crate — including
// every `leanr_olean`/`leanr_cli` build, test or not — never sees these
// names, matching the fact that nothing outside this crate's own suites
// names them (verified via `grep -rn` for every Arc-decl symbol across
// `crates/*/src`, non-test call sites only).
#[cfg(test)]
pub use decl::{
    arc_constant_info_eq, to_constant_info, ArcAxiomVal, ArcConstantInfo, ArcConstantVal,
    ArcConstructorVal, ArcDeclaration, ArcDefinitionVal, ArcInductiveType, ArcInductiveVal,
    ArcOpaqueVal, ArcQuotVal, ArcRecursorRule, ArcRecursorVal, ArcTheoremVal,
};
pub use env::{Environment, EnvironmentError};
pub use error::KernelError;
pub use expr::{BinderInfo, DataValue, Expr, ExprData, ExprNode, KVMap, Literal};
pub use guard::{RecGuard, MAX_REC_DEPTH};
pub use level::Level;
pub use local_ctx::{FVarIdGen, LocalContext, LocalDecl};
pub use name::Name;
pub use num::{Int, Nat};
pub use replay::{replay, ReplayError, ReplayStats};
pub use subst::{
    abstract_fvars, instantiate, instantiate_core, instantiate_level_params, instantiate_rev,
    lift_loose_bvars,
};
pub use syntax::{Preresolved, SourceInfo, Substring, Syntax};
pub use tc::{Lbool, TypeChecker};
pub use used_consts::used_constants;
