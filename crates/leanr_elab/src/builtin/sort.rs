//! `Prop` / `Type` / `Sort e` — oracle: `elabProp`/`elabSort`/
//! `elabTypeStx` (`Lean/Elab/BuiltinTerm.lean:21-34`) and the level
//! child's own elaborator, `Lean.Elab.Level.elabLevel`
//! (`Lean/Elab/Level.lean:61-90`), both read directly from the pinned
//! toolchain source before transcribing (never guessed):
//!
//! ```text
//! elabProp    _   _ := return mkSort Level.zero
//! elabSort    stx _ := return mkSort (← elabOptLevel stx[1])
//! elabTypeStx stx _ := return mkSort (mkLevelSucc (← elabOptLevel stx[1]))
//! elabOptLevel stx   := if stx.isNone then pure Level.zero else elabLevel stx[0]
//! ```
//!
//! So bare `Type` (no level argument) elaborates to `Sort (succ zero)`
//! — `Level.zero`, NOT a fresh level metavariable, despite this
//! crate's own design spec prose saying otherwise in one place ("`Type`
//! = `Sort (u+1)` with a fresh level metavariable"); that prose is
//! superseded here by the pinned oracle source itself (Global
//! Constraint: the fixture — and, upstream of it, the real toolchain
//! source it was regenerated from — is authoritative over any
//! prose/plan guess).
//!
//! **Real tree shape** (confirmed by a throwaway parse-dump probe,
//! never committed — see the task report): `Lean.Parser.Term.prop` /
//! `.sort` / `.type` are `leading2`-registered NODEs. `prop` has one
//! child (the `"Prop"` atom, never read). `sort`/`type` share the same
//! shape: `[<"Sort"|"Type" atom>, <null-wrapped optional level>]` —
//! `non_trivia_children(node)[1]` is always that null node; EMPTY
//! (zero non-trivia children of its own) when no level argument was
//! written, or wraps exactly one child (the level term) otherwise.
//!
//! **Level scope, Task 6**: `Lean.Parser.Level.hole` (`_`, a fresh
//! level mvar), a bare `num` node (`Level.ofNat`, decimal digits ->
//! that many `succ`s of `zero`), and a bare `<ident>` token (a level
//! PARAMETER lookup against `elab.level_names`) are fully transcribed.
//! `Lean.Parser.Level.max`/`.imax`/`.paren`/`.addLit` are named seams
//! (`UnsupportedSyntax`, exactly this crate's num/char-for-terms
//! precedent): no fixture row needs them, and each needs machinery
//! (recursive max/imax interning, or `checkUniverseOffset`'s Options
//! lookup) this task doesn't otherwise touch.
//! `checkUniverseOffset`'s 32-offset cap (`Level.lean:52-56`) is
//! likewise elided from the `num` branch — no fixture numeral exceeds
//! it, and reporting the cap would need a new `ElabError` variant,
//! outside this task's `error.rs`-excluded file scope.
//!
//! **`Sort u`/`Type u` are unreachable via this crate's own harness,
//! confirmed empirically against the real oracle**: a throwaway probe
//! (`Lean.Elab.Term.elabTerm` on bare source `"Sort u"`/`"Type u"` with
//! no enclosing declaration, the same entry point `dump_elab.lean`
//! itself pins) hits an uncaught internal auto-bound-implicit signal
//! even in the REAL Lean elaborator — `level_names` is populated by an
//! enclosing declaration's binder-collection pass, which does not exist
//! for a bare standalone term. The ident branch below is still fully
//! implemented (a direct, correct transcription, argued sound in its
//! own right) even though nothing in the committed corpus can reach it
//! today.

use leanr_kernel::bank::{ExprId, LevelId};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::{NodeOrToken, SyntaxNode};

use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `elabProp` — `mkSort Level.zero`, unconditionally; the node
/// carries no level argument to read.
pub fn elab_prop(
    elab: &mut TermElabM,
    _node: &SyntaxNode,
    _kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let store = elab.mctx.store_mut();
    let zero = store
        .level_zero(None)
        .map_err(leanr_meta::MetaError::from)?;
    let id = store
        .expr_sort(None, zero)
        .map_err(leanr_meta::MetaError::from)?;
    Ok(id)
}

/// oracle: `elabTypeStx` — `mkSort (mkLevelSucc (elabOptLevel stx[1]))`.
pub fn elab_type(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let level = elab_opt_level(elab, node, kinds)?;
    let store = elab.mctx.store_mut();
    let succ = store
        .level_succ(None, level)
        .map_err(leanr_meta::MetaError::from)?;
    let id = store
        .expr_sort(None, succ)
        .map_err(leanr_meta::MetaError::from)?;
    Ok(id)
}

/// oracle: `elabSort` — `mkSort (elabOptLevel stx[1])`.
pub fn elab_sort(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let level = elab_opt_level(elab, node, kinds)?;
    let store = elab.mctx.store_mut();
    let id = store
        .expr_sort(None, level)
        .map_err(leanr_meta::MetaError::from)?;
    Ok(id)
}

/// oracle: `elabOptLevel` — `pure Level.zero` when `stx[1]` (the
/// null-wrapped `optional(..)` slot) `isNone`; otherwise `elabLevel
/// stx[0]` on its one real child. See this module's own doc for the
/// exact non-trivia child layout `sort`/`type` share.
fn elab_opt_level(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<LevelId, ElabError> {
    let children = non_trivia_children(node);
    let opt = children
        .get(1)
        .expect("sort/type node always has an opt-level child (grammar-guaranteed)");
    let opt_node = opt
        .as_node()
        .expect("the opt-level slot is always null-node-wrapped (grammar-guaranteed)");
    match non_trivia_children(opt_node).first() {
        None => Ok(elab
            .mctx
            .store_mut()
            .level_zero(None)
            .map_err(leanr_meta::MetaError::from)?),
        Some(lvl_elem) => elab_level(elab, lvl_elem, kinds),
    }
}

/// oracle: `Lean.Elab.Level.elabLevel`. See this module's own doc for
/// the exact scope cut (`num`/`<ident>`/`Level.hole` implemented;
/// `max`/`imax`/`paren`/`addLit` named seams).
fn elab_level(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
) -> Result<LevelId, ElabError> {
    let name = kinds.name(elem.kind());
    match (name, elem) {
        // oracle: `stx.isNatLit?` -> `Level.ofNat val`, i.e. `val`
        // nested `succ`s of `zero`. `num`'s own text is the decimal
        // digits directly (`NumLit`'s self-wrap, `level.rs`'s own doc
        // comment) — a parser-validated token, always well-formed.
        ("num", NodeOrToken::Node(n)) => {
            let text = n.text().to_string();
            let val: u64 = text
                .trim()
                .parse()
                .expect("numeral token is well-formed (parser-validated)");
            let mut level = elab
                .mctx
                .store_mut()
                .level_zero(None)
                .map_err(leanr_meta::MetaError::from)?;
            for _ in 0..val {
                level = elab
                    .mctx
                    .store_mut()
                    .level_succ(None, level)
                    .map_err(leanr_meta::MetaError::from)?;
            }
            Ok(level)
        }
        // oracle: the `identKind` arm — a level PARAMETER reference,
        // valid only if already in `levelNames` (`elab.level_names`;
        // `autoBoundImplicit`'s auto-binding path is out of scope, see
        // this module's own doc — confirmed unreachable via this
        // crate's own standalone-term harness anyway).
        ("<ident>", NodeOrToken::Token(tok)) => {
            let raw = tok.text();
            let base = elab.view.store;
            let s = elab
                .mctx
                .store_mut()
                .intern_str(Some(base), raw)
                .map_err(leanr_meta::MetaError::from)?;
            let name_id = elab
                .mctx
                .store_mut()
                .name_str(Some(base), None, s)
                .map_err(leanr_meta::MetaError::from)?;
            if elab.level_names.contains(&name_id) {
                Ok(elab
                    .mctx
                    .store_mut()
                    .level_param(None, Some(name_id))
                    .map_err(leanr_meta::MetaError::from)?)
            } else {
                Err(ElabError::UnknownIdent(raw.to_string()))
            }
        }
        // oracle: `Lean.Parser.Level.hole` -> `mkFreshLevelMVar`.
        ("Lean.Parser.Level.hole", NodeOrToken::Node(_)) => elab.mk_fresh_level_mvar(),
        (other, _) => Err(ElabError::UnsupportedSyntax(other.to_string())),
    }
}
