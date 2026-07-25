//! Leaf elaborators, one module per family (design spec § Crate and
//! module layout). `lit` (M4b-1 Task 4) came first;
//! `sort`/`ascription`/`hole` (M4b-1 Task 6) complete M4b-1 slice 1.
//! `binder` (M4b-2) begins the binder-family elaborators.
//!
//! `ident` used to live here too. It is gone (M4b-3 P1 task 4): a bare
//! identifier is a ZERO-ARGUMENT APPLICATION in the oracle
//! (`elabIdent := elabAtom`, `App.lean:2246`), so its constant
//! resolution belongs to `crate::app::head`, not to a leaf module.
pub mod ascription;
pub mod binder;
pub mod hole;
pub mod lit;
pub mod sort;
