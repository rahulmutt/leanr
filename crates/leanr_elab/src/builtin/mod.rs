//! Leaf elaborators, one module per family (design spec § Crate and
//! module layout). `sort`/`ascription`/`hole` land in Task 6; `lit`
//! (Task 4) and `ident` (this task) are the first two.
pub mod ident;
pub mod lit;
