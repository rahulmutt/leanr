//! The term elaborator. `TermElabM` over `leanr_meta`'s MetaM core.
//! Built in slices, each with its own design spec:
//!
//! - **M4b-1** — leaf forms: string literals, sorts, ascription, holes
//!   (docs/superpowers/specs/2026-07-23-m4b1-leaf-term-elaborator-design.md).
//! - **M4b-2** — binders and the let/have family: `fun`, `forall`,
//!   `arrow`, `depArrow`, `let`, `have`
//!   (docs/superpowers/specs/2026-07-24-m4b2-binders-postponement-design.md).
//! - **M4b-3 P1** — the application machinery, in `app/`: `elabApp` /
//!   `elabAtom` / `elabAppFn`'s ident case / `ElabAppArgs.main`,
//!   including implicit and strict-implicit insertion,
//!   `propagateExpectedType`, named arguments, eta-expansion, the `..`
//!   ellipsis, `@` explicit mode, and `.{u}` explicit universes
//!   (docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md).
//!   Identifiers moved here too: `elabIdent := elabAtom`
//!   (`App.lean:2246`), so a bare identifier is a zero-argument
//!   application, and M4b-1's leaf `builtin/ident.rs` is gone.
//!
//! ## What is NOT built yet
//!
//! Every remaining construct is a *named* deferral, never a gap
//! discovered later: `dispatch::dispatch` routes every unregistered
//! syntax kind to `ElabError::UnsupportedSyntax(kind)`, and every seam
//! inside `app/` carries its owning slice in the message. Never a
//! silent no-op, never a panic, never a wrong `ExprId`.
//!
//! - **instance-implicit arguments and the synthetic-mvar fixpoint**
//!   (`processInstImplicitArg`, `synthesizeAppInstMVars`) — M4b-3 P2,
//!   which also brings the `classExtension` decode the outParam guards
//!   need.
//! - **`num`/`char` literals** — deliberately *not* leaves (an M4b-1
//!   spec correction): both elaborate through an application
//!   (`OfNat.ofNat`/`Char.ofNat`) requiring instance synthesis and
//!   default instances — M4b-3 P3.
//! - **coercions** (`mkCoe`, `CoeT`/`CoeFun`/`CoeSort`) —
//!   `ensure_has_type`/`elab_term_ensuring_type` and `app`'s own
//!   `ensureArgType` ERROR on a defeq mismatch rather than inserting a
//!   coercion — M4b-3 P4.
//! - **optParam/autoParam default filling and implicit-lambda
//!   insertion** — M4b-3 P5. (The implicit-lambda *guard* is P1's, in
//!   `elab.rs`; only the insertion is deferred.)
//! - **overload resolution** (more than one candidate from
//!   `elabAppFn`) — the slice that grows `resolve_global`, since it is
//!   unreachable while only exact names resolve.
//! - **`elabAsElim`, dot notation / LVal machinery (`Term.proj`,
//!   `pipeProj`, `dotIdent`, `namedPattern`, `choice`), `binop%`,
//!   anonymous constructor `⟨⟩`** — M4b-4.
//! - **macro expansion** — `dispatch` never expands a macro form; the
//!   dispatch table only ever matches a syntax kind directly against a
//!   registered elaborator. Deferred to the slice that first needs a
//!   macro form.
//! - **`open`/alias/`export`/`_root_` resolution** — `resolve.rs`'s
//!   `resolve_global` only resolves a global constant declared under
//!   the name exactly as written; namespace-prefix search, exported
//!   aliases, and root-qualification are a later slice.
//!
//! See `dispatch.rs`'s doc comment for the kind-by-kind deferral table,
//! `app/mod.rs`'s for the site-by-site seam index inside the
//! application elaborator, and `tests/seam_audit.rs` for the gate that
//! holds all three lists to the code.
pub mod app; // M4b-3 P1
pub mod builtin; // Tasks 4-6
pub mod dispatch;
pub mod elab;
pub mod error;
pub mod resolve; // Task 5

pub use elab::TermElabM;
pub use error::ElabError;
