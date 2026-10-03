//! Command elaboration (M4c). M4c-1: a single non-recursive
//! `def`/`theorem`/`abbrev`/`opaque`/`axiom`/`example` becomes kernel
//! declarations (spec `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md`,
//! plan `docs/superpowers/plans/2026-10-03-m4c1-p2-command-elab.md`).

// Consumed from Task 6 on; remove this allow there.
#[allow(dead_code)]
pub(crate) mod view;
