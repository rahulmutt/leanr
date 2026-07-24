//! Leaf elaborators, one module per family (design spec § Crate and
//! module layout). `lit` (Task 4) and `ident` (Task 5) came first;
//! `sort`/`ascription`/`hole` (Task 6) complete M4b-1 slice 1.
pub mod ascription;
pub mod hole;
pub mod ident;
pub mod lit;
pub mod sort;
