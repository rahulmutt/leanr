//! M4b-1: the leaf term elaborator. `TermElabM` over `leanr_meta`'s
//! MetaM core; elaborates string literals, sorts, global-constant
//! identifiers, ascription, and holes. See
//! docs/superpowers/specs/2026-07-23-m4b1-leaf-term-elaborator-design.md.
//!
//! ## What this slice does NOT build
//!
//! Per the design spec's own *Scope* / *Out of scope* sections: this is
//! **leaf forms only** — a term whose elaboration emits an `Expr` with
//! no binder, no application, and no instance search. Everything else a
//! real term elaborator eventually handles is a *named* deferral —
//! `dispatch::dispatch` routes every unregistered syntax kind to
//! `ElabError::UnsupportedSyntax(kind)`, never a silent no-op or a
//! panic — not a gap discovered later:
//!
//! - **binders** (`fun`/`forall`/`let`/`have`/`show`) and the
//!   postponement / synthetic-mvar scheduling ladder they need — M4b-2.
//! - **application**, `@`, named/optional arguments (`elabApp`'s
//!   implicit/instance-implicit insertion) — M4b-3.
//! - **`num`/`char` literals** — deliberately *not* leaves (spec
//!   correction): both elaborate through an application
//!   (`OfNat.ofNat`/`Char.ofNat`) requiring instance synthesis and
//!   default instances, so they land in M4b-3 alongside application,
//!   not here. Only the string literal is a direct `Expr.lit` and stays
//!   a leaf.
//! - **coercions** (`mkCoe`) — `ensure_has_type`/`elab_term_ensuring_type`
//!   ERROR on a defeq mismatch in this slice rather than inserting a
//!   coercion; coercion insertion is M4b-3.
//! - **`elabAsElim`, dot notation, `binop%`, anonymous constructor
//!   `⟨⟩`** — M4b-4.
//! - **macro expansion** — `dispatch` never expands a macro form; the
//!   dispatch table only ever matches a syntax kind directly against a
//!   registered leaf elaborator. Deferred to the slice that first needs
//!   a macro form.
//! - **`open`/alias/`export`/`_root_` resolution** — `resolve.rs`'s
//!   `resolve_global` only resolves a global constant declared under
//!   the name exactly as written; namespace-prefix search, exported
//!   aliases, and root-qualification are a later slice (M4b-3/M4b-4
//!   own the pieces that first need them).
//!
//! See `dispatch.rs`'s own doc comment for the exact deferral list and
//! the named-seam audit (Task 7) confirming nothing above is silently
//! skipped.
pub mod builtin; // Tasks 4-6
pub mod dispatch;
pub mod elab;
pub mod error;
pub mod resolve; // Task 5

pub use elab::TermElabM;
pub use error::ElabError;
