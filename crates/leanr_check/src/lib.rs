//! Parallel kernel-check driver over a frozen `CheckedConstants`.
//! Spec: docs/superpowers/specs/2026-07-10-m1-final-parallel-mathlib-design.md
pub mod graph;
pub mod schedule;

pub use schedule::{check_parallel, CheckFailure, CheckStats};
