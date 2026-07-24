//! `(e)` / `(e : T)` — oracle: `expandParen`/`elabTypeAscription`
//! (`Lean/Elab/BuiltinNotation.lean:410-434`), read directly from the
//! pinned toolchain source before transcribing (never guessed).
//!
//! **`paren` never reaches a term elaborator in real Lean.**
//! `expandParen` is a MACRO (`@[builtin_macro Lean.Parser.Term.paren]`)
//! that rewrites `(e)` to `e` (or, if `e` contains a `·`, to a cdot
//! lambda) BEFORE elaboration ever sees a `paren` node — but this
//! crate's own design spec pins "no macro expansion in slice 1"
//! (`dispatch.rs`'s own module doc), and `Lean.Parser.Term.cdot` is
//! never registered in this crate's dispatch table at all (out of
//! scope entirely — no fixture row, no arm). So the ONLY branch
//! `expandParen` could ever take on input this crate can even parse is
//! its `hasCDot = false` one, `(← expandCDot? e h..).getD e = e` — "the
//! macro expansion is always a no-op here". `elab_paren` below runs
//! that no-op directly at the elaborator level (forward to the inner
//! term) rather than modeling macro expansion as a separate dispatch
//! phase — behaviorally identical for every input reachable through
//! this crate's own grammar, not an approximation of it.
//!
//! **`typeAscription` genuinely IS its own term elaborator**
//! (`@[builtin_term_elab typeAscription] elabTypeAscription`) — its
//! sibling macro (`expandTypeAscription`) only fires when the body
//! contains a `·` (`Macro.throwUnsupported` otherwise, falling through
//! to the real elaborator), so for every non-cdot input — this crate's
//! entire scope — `elabTypeAscription` runs unconditionally:
//!
//! ```text
//! elabTypeAscription
//!   | `(($e : $type)), _ := do
//!       let type ← withSynthesize (postpone := .yes) <| elabType type
//!       let e ← elabTerm e type
//!       ensureHasType type e
//!   | `(($e :)), expectedType? := do
//!       let e ← withSynthesize (postpone := .no) <| elabTerm e none
//!       ensureHasType expectedType? e
//! ```
//!
//! `withSynthesize`'s postponement scaffolding does not exist in this
//! slice (no scheduling ladder — `elab.rs`'s own doc, design spec's
//! "Fields the slice-2 scheduling ladder will need... deliberately not
//! added yet"), so both arms degenerate to their direct, unpostponed
//! shape: `elab_term(type, None)` then `elab_term_ensuring_type(e,
//! Some(type'))` for the first; `elab_term_ensuring_type(e, expected)`
//! for the second (no fixture row exercises the second arm — the
//! `opt(term)` type slot is genuinely optional grammar, transcribed
//! anyway as the direct, unambiguous port). `ensureHasType`'s coercion-
//! insertion path (`mkCoe`) is out of scope (M4b-3); a defeq mismatch
//! ERRORS here instead, matching `elab_term_ensuring_type`'s own
//! documented behavior.
//!
//! **Tree shape is NOT what the M4b-1 plan guessed.** A real parse dump
//! (this task's own throwaway probe, never committed — see the task
//! report) shows `typeAscription` is a SEPARATE top-level node kind,
//! never nested inside `paren`: `term.rs::register_paren_family`
//! registers `paren` and `typeAscription` as two DIFFERENT `leading2`
//! entries sharing only their `hygienicLParen` prefix, resolved against
//! each other by ordinary longest-match on the `:` token — `(Nat :
//! Type)` parses straight to a `typeAscription` node, `(Nat)` to a
//! `paren` node; dispatch (`dispatch.rs`) routes each kind name
//! directly to its own elaborator below, neither ever delegating
//! through the other. Both share the same non-trivia child layout up
//! to that point: `paren` = `[hygienicLParen, e, ")"]`;
//! `typeAscription` = `[hygienicLParen, e, ":", optType, ")"]`.

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `expandParen`'s no-cdot branch — `(e)` elaborates exactly
/// like `e`. Real non-trivia children: `[hygienicLParen, e, ")"]`.
pub fn elab_paren(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let children = non_trivia_children(node);
    let e: &SynElem = children
        .get(1)
        .expect("paren node always has an inner term child (grammar-guaranteed)");
    elab.elab_term(e, kinds, expected)
}

/// oracle: `elabTypeAscription`. Real non-trivia children:
/// `[hygienicLParen, e, ":", optType, ")"]` — `optType` is a
/// null-wrapped `optional(termParser)`, empty when the source wrote
/// `(e :)`.
pub fn elab_ascription(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let children = non_trivia_children(node);
    let e: &SynElem = children
        .get(1)
        .expect("typeAscription node always has an inner term child (grammar-guaranteed)");
    let opt_type = children
        .get(3)
        .expect("typeAscription node always has an opt-type child (grammar-guaranteed)");
    let opt_node = opt_type
        .as_node()
        .expect("the opt-type slot is always null-node-wrapped (grammar-guaranteed)");

    match non_trivia_children(opt_node).first() {
        // `($e :)` — no type constraint written; `ensureHasType
        // expectedType? e`.
        None => elab.elab_term_ensuring_type(e, kinds, expected),
        // `($e : $type)` — elaborate the type child as a term (no
        // expected type of its own), then check `e` against it.
        Some(ty_elem) => {
            let ty = elab.elab_term(ty_elem, kinds, None)?;
            elab.elab_term_ensuring_type(e, kinds, Some(ty))
        }
    }
}
