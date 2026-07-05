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

mod decl;
mod env;
mod error;
mod expr;
mod guard;
mod level;
mod name;
mod num;
mod syntax;

pub use decl::{
    AxiomVal, ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety, DefinitionVal,
    InductiveVal, OpaqueVal, QuotKind, QuotVal, RecursorRule, RecursorVal, ReducibilityHints,
    TheoremVal,
};
pub use env::{Environment, EnvironmentError};
pub use error::KernelError;
pub use expr::{BinderInfo, DataValue, Expr, ExprData, ExprNode, KVMap, Literal};
pub use guard::{RecGuard, MAX_REC_DEPTH};
pub use level::Level;
pub use name::Name;
pub use num::{Int, Nat};
pub use syntax::{Preresolved, SourceInfo, Substring, Syntax};
