//! Kernel data model. This crate is the trusted computing base (see
//! AGENTS.md): it must depend on no other workspace crate, and it holds
//! only the data types in M1a — the checker arrives in M1b.
//!
//! Values of these types are built from UNTRUSTED `.olean` bytes by
//! `leanr_olean`, so they can be adversarially shaped (e.g. 100k-deep
//! `Name` parent chains). Nothing here may recurse proportionally to
//! value depth: traversals are loops or explicit stacks, and the `Arc`
//! tree types implement iterative `Drop`.

mod expr;
mod level;
mod name;
mod num;

pub use expr::{BinderInfo, DataValue, Expr, KVMap, Literal};
pub use level::Level;
pub use name::Name;
pub use num::{Int, Nat};
