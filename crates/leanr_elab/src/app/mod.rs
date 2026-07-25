//! M4b-3 P1: the application elaborator. Oracle: `Lean/Elab/App.lean`'s
//! `ElabAppArgs` namespace. See
//! docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md
//! § P1 — the application machinery.
//!
//! NOT in this plan, each a named seam (never a silent fall-through):
//!   instance-implicit arguments + the synthetic-mvar fixpoint . P2
//!   num/char/scientific literals ......................... P3
//!   coercions (CoeT/CoeFun/CoeSort, mkCoe) ............... P4
//!   optParam defaults / autoParam / `..` ellipsis ........ P5
//!   implicit-lambda insertion ............................ P5
//!   overload resolution (candidates > 1) ................. resolve_global slice
//!   elabAsElim, dot notation, LVal machinery ............. M4b-4

pub mod expand;
pub mod state;
