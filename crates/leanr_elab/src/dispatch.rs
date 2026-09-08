//! The dispatch table: syntax-kind name -> leaf elaborator.
//!
//! `elaborator_name_for` is the single source of truth for "is this a
//! term-syntax kind we elaborate". M4b-1's tasks 4-6 grew it one arm per
//! LEAF kind, which is the framing the rest of this doc still uses;
//! every slice since has added non-leaf kinds to the same table
//! (M4b-2's binders and `let`/`have`, M4b-3 P1's `app`/`explicit`/
//! `explicitUniv`, M4b-3 P3's `num`/`char`/`scientific`), so "registered"
//! and "leaf" have not been synonyms since M4b-2 — `str` is the one
//! literal that really is a leaf, and `builtin::lit`'s own module doc
//! says so.
//! `dispatch` is the actual entry point `TermElabM::elab_term` calls;
//! an unregistered kind is `ElabError::UnsupportedSyntax`, never a
//! panic and never a wrong `ExprId` (named-seam discipline).
//!
//! **`SynElem`, not `SyntaxNode`** (Task 5 reconciliation): a leaf term
//! is not always a rowan NODE. `leanr_syntax`'s own grammar
//! (`builtin/term.rs`) registers a bare identifier as
//! `b.leading_raw("term", Prim::Ident)` — `Prim::Ident`'s own run arm
//! (`parse.rs`) is a plain `self.bump(t, KIND_IDENT)`, an unwrapped
//! leaf token with NO enclosing `start`/`finish` node pair (unlike
//! `str`/`num`/`char`, whose `Prim::StrLit`/etc go through `self.lit`,
//! which DOES wrap). Empirically confirmed (a throwaway probe test,
//! `cargo test -p leanr_elab --test zzscratch_probe -- --nocapture`,
//! never landed): parsing the term `"Nat"` produces a `KIND_NULL` root
//! whose ONLY child is a rowan TOKEN of kind `KIND_IDENT` (interned
//! name `"<ident>"`, not `"ident"` — `KindInterner::new`'s fixed-slot
//! list) — `root.first_child()` (node-only) finds nothing, so a term
//! position genuinely needs `SyntaxNode` OR `SyntaxToken` depending on
//! which leaf kind landed there. `SynElem` (`rowan::NodeOrToken`,
//! `leanr_syntax::tree`'s own re-export) is the minimal type that
//! covers both without forcing every existing Node-shaped leaf (`str`,
//! and Task 6's `sort`/hole) through a token-shaped API.

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::{is_trivia, KindInterner};
use leanr_syntax::tree::{NodeOrToken, SyntaxNode, SyntaxToken};

use crate::elab::TermElabM;
use crate::error::ElabError;

/// A term-syntax leaf position: a rowan NODE (`str`, and Task 6's
/// `sort`/`hole`/ascription — every kind that goes through `self.lit`
/// or a `leading2`/`nd`-style node wrap) or a rowan TOKEN (`ident` —
/// the one bare-leaf-token kind so far; see this module's doc comment).
pub type SynElem = NodeOrToken<SyntaxNode, SyntaxToken>;

/// Every syntactically-meaningful (non-trivia) child of `node`, in
/// source order. Task 6's multi-child leaves (`sort`/`type`'s optional
/// level argument, `paren`/`typeAscription`'s inner term(s)) all need
/// to navigate by POSITION, which the raw `children_with_tokens()`
/// stream doesn't support directly — it interleaves real syntax with
/// whitespace/comment trivia tokens (`is_trivia`, `leanr_syntax::kind`).
/// This is the leanr-tree equivalent of Lean's own `Syntax.getArg`/
/// `stx[i]`, which indexes into an ALREADY-trivia-stripped `Array
/// Syntax` (a `Syntax.node`'s `args` field never carries whitespace —
/// that lives only in each leaf's own `SourceInfo`), not a new
/// convention invented here.
pub(crate) fn non_trivia_children(node: &SyntaxNode) -> Vec<SynElem> {
    node.children_with_tokens()
        .filter(|el| !is_trivia(el.kind()))
        .collect()
}

/// The registered term-syntax kinds. Returns a stable label for a
/// registered kind, `None` otherwise. Grown by M4b-1's tasks 4-6 (which
/// completed M4b-1 slice 1) and by every slice since; see this module's
/// doc for why "registered" stopped meaning "leaf" at M4b-2, and
/// `tests/seam_audit.rs`'s `literal_kinds_are_registered_not_deferred`
/// for the gate on the four literal kinds.
/// Keyed on the kind's INTERNED name — `"<ident>"` for a bare
/// identifier (`KindInterner`'s fixed-slot name, not the string
/// `"ident"` a dynamically-interned node kind would have; see this
/// module's doc comment), `"str"` for a string literal (a real
/// `leading2`/`self.lit`-wrapped node kind), and Task 6's five
/// `Lean.Parser.Term.*` kinds (all real `leading2`-wrapped nodes,
/// confirmed against a fresh parse dump — see `builtin::ascription`'s
/// module doc for the `paren`/`typeAscription` shape correction).
pub fn elaborator_name_for(kind: &str) -> Option<&'static str> {
    match kind {
        "str" => Some("str"),
        "num" => Some("num"),
        "char" => Some("char"),
        "scientific" => Some("scientific"),
        "<ident>" => Some("ident"),
        "Lean.Parser.Term.prop" => Some("prop"),
        "Lean.Parser.Term.type" => Some("type"),
        "Lean.Parser.Term.sort" => Some("sort"),
        "Lean.Parser.Term.paren" => Some("paren"),
        "Lean.Parser.Term.typeAscription" => Some("typeAscription"),
        "Lean.Parser.Term.hole" => Some("hole"),
        "Lean.Parser.Term.arrow" => Some("arrow"),
        "Lean.Parser.Term.forall" => Some("forall"),
        "Lean.Parser.Term.depArrow" => Some("depArrow"),
        "Lean.Parser.Term.fun" => Some("fun"),
        "Lean.Parser.Term.let" => Some("let"),
        "Lean.Parser.Term.have" => Some("have"),
        "Lean.Parser.Term.app" => Some("app"),
        "Lean.Parser.Term.explicit" => Some("explicit"),
        "Lean.Parser.Term.explicitUniv" => Some("explicitUniv"),
        _ => None,
    }
}

/// Dispatch a term position to its leaf elaborator. Unregistered kind ->
/// UnsupportedSyntax (never a panic, never a wrong ExprId). A kind
/// registered above but arriving as the "wrong" `SynElem` variant (e.g.
/// `"str"`'s name matching on a bare TOKEN) is unreachable in practice —
/// `leanr_syntax`'s own grammar wraps `str/num/char` as nodes and
/// `ident` as a token, always the same way — but is still routed to
/// `UnsupportedSyntax` rather than panicking, per this crate's
/// never-panic-on-a-named-seam discipline.
///
/// Named-seam audit (M4b-1 Task 7, re-run and widened by M4b-3 P1
/// task 9). Every `match` block in this crate that reads a kind name
/// ends in a catch-all that NAMES what it saw — never a silent skip,
/// never a default. There are five, not the two the M4b-1 audit found,
/// because M4b-3 P1 added three kind-matching sites inside `app/`:
/// ```text
///   dispatch (here) ................ Err(UnsupportedSyntax(kind))
///   builtin::sort::elab_level ...... Err(UnsupportedSyntax(kind))    Lean.Parser.Level.*
///   app::elab_explicit ............. Err(UnsupportedSyntax(..))      `@`-in-term shape dispatch
///   app::peel_head ................. Err(UnsupportedSyntax(..))      `@`-in-head shape dispatch
///   app::head::elab_app_fn ......... Err(UnsupportedSyntax(..))      application-head kinds
/// ```
/// The three in `app/` carry a slice owner in the message rather than
/// the bare kind, since each corresponds to a specific oracle arm; see
/// `app/mod.rs`'s module doc for the index and `tests/seam_audit.rs`
/// for the gate. `resolve.rs`'s `resolve_global` still inspects no
/// syntax at all.
///
/// Deferred (each hits `UnsupportedSyntax` until its slice lands).
/// Reconciled by Task 9 against what M4b-3 P1 actually shipped —
/// implicit/strict-implicit insertion (task 5), named arguments and eta
/// expansion (task 7), the `..` ellipsis (task 7), `@` and `.{u}`
/// (task 8) all landed and are no longer deferred. Reconciled AGAIN by
/// M4b-3 P2a task 10 against what P2a shipped: instance-implicit
/// arguments and the synthetic-mvar fixpoint landed (tasks 2-9) and are
/// no longer deferred either. Reconciled a THIRD time by M4b-3
/// P2b-ii: the local-instance outParam feature landed (`app/args.rs`,
/// `app/finalize.rs`) and is no longer deferred either. Reconciled a
/// FOURTH time by M4b-3 P4 task 7: `mkCoe`/`ensureHasType` and the
/// `CoeT` half of coercion landed (`coe.rs`), leaving only `CoeFun`
/// (task 8) and `CoeSort` (task 9) deferred:
/// ```text
///   letI / haveI / let_fun / let_delayed / let_tmp / letrec  later slice (own oracle tier each)
///   coercions: CoeFun / CoeSort (mkCoe landed) . M4b-3 P4
///   optParam defaults / autoParam .............. M4b-3 P5
///   implicit-lambda insertion .................. M4b-3 P5
///   Term.proj / pipeProj / dotIdent ............ M4b-4 (LVal machinery)
///   Term.namedPattern / choice ................. M4b-4 (same elabAppFn arms)
///   elabAsElim (recursor heads seamed; aux
///     recursors + @[elab_as_elim] still open) .. M4b-4
///   binop%, anonymous constructor ⟨⟩ ........... M4b-4
///   macro expansion in dispatch ................ first macro-form slice
///   open / alias / export / _root_ resolution .. later slice
/// ```
/// The application arms above are registered, so the `M4b-3` seams in
/// that list are raised from INSIDE `app::args`/`app::finalize`/
/// `app::head`/`app::propagate`/`app::overload` (each naming its owning
/// slice) rather than from this table's catch-all; `app/mod.rs`'s own
/// module doc is the site-by-site index.
///
/// `Term.proj`, `Term.pipeProj`, `Term.dotIdent`, `Term.namedPattern`
/// and `choice` are deliberately NOT routed, even though the oracle
/// aliases four of them straight to `elabAtom`
/// (`App.lean:2247-2248`, `:2273-2274`; `elabPipeProj` at `:2250-2258`
/// desugars to `elabAppAux`) — which `app::elab_atom` already
/// implements. Routing them would be wrong, not merely early:
/// `elabAtom`'s work for these kinds happens inside `elabAppFn`, whose
/// field/fieldIdx/dotIdent arms (`App.lean:2084-2109`) build an `LVal`
/// list that `elabAppLVals`/`resolveLValAux` then resolves — the
/// dot-notation subsystem M4b-4 owns. Sending them to `elab_atom`
/// today would reach `app::head::elab_app_fn` with a non-ident head
/// and produce that module's M4b-4 seam anyway, one indirection later.
/// As whole terms they land on this table's catch-all instead, named by
/// their kind.
///
/// `num`/`char`/`scientific` are all registered above as of tasks 6-7,
/// and none of them is a LEAF: each elaborates through an application
/// (`@OfNat.ofNat.{u}` plus the default-instance rung,
/// `Char.ofNat`, `@OfScientific.ofScientific.{u}`) rather than straight
/// to an `Expr` node — `str` is the one literal that does.
/// See `builtin::lit`'s own module doc for the three shapes.
/// (`Lean.Parser.Level.max`/`.imax`/`.paren`/`.addLit`, the level-scope
/// analogue of the above, are named seams inside `elab_level` itself —
/// see `builtin::sort`'s own module doc — rather than this table, since
/// they are not term-position kinds `dispatch` ever sees directly.)
pub fn dispatch(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let name = kinds.name(elem.kind());
    match (name, elem) {
        ("str", NodeOrToken::Node(node)) => crate::builtin::lit::elab_str(elab, node, kinds),
        // oracle: `@[builtin_term_elab num] elabNumLit`
        // (`BuiltinTerm.lean:210-229`) — NOT a leaf: it emits
        // `@OfNat.ofNat.{u} ?α (rawNatLit v) ?inst` and leaves the
        // instance goal to the synthetic-mvar ladder.
        ("num", NodeOrToken::Node(node)) => {
            crate::builtin::lit::elab_num(elab, node, kinds, expected)
        }
        // oracle: `@[builtin_term_elab char] elabCharLit`
        // (`BuiltinTerm.lean:248-251`) — an application, not a leaf, but
        // a monomorphic one: `Char.ofNat (rawNatLit c)`, no instance and
        // no universe level.
        ("char", NodeOrToken::Node(node)) => {
            crate::builtin::lit::elab_char(elab, node, kinds, expected)
        }
        // oracle: `@[builtin_term_elab scientific] elabScientificLit`
        // (`BuiltinTerm.lean:236-246`) — `num`'s shape through
        // `OfScientific`, with the instance argument SECOND.
        ("scientific", NodeOrToken::Node(node)) => {
            crate::builtin::lit::elab_scientific(elab, node, kinds, expected)
        }
        // A bare identifier is a ZERO-ARGUMENT APPLICATION, not a leaf:
        // `elabIdent := elabAtom` (`App.lean:2246`). M4b-1's
        // `builtin/ident.rs` was a simplification of exactly this path
        // and is gone; its constant resolution now lives in
        // `app::head::elab_app_fn` (M4b-3 P1 task 4).
        ("<ident>", NodeOrToken::Token(_)) => crate::app::elab_atom(elab, elem, kinds, expected),
        ("Lean.Parser.Term.app", NodeOrToken::Node(node)) => {
            crate::app::elab_app(elab, node, kinds, expected)
        }
        // oracle: `elabExplicit` (`App.lean:2260-2271`) — a SHAPE
        // dispatch, not a plain `elabAtom` alias; see `app::elab_explicit`.
        ("Lean.Parser.Term.explicit", NodeOrToken::Node(_)) => {
            crate::app::elab_explicit(elab, elem, kinds, expected)
        }
        // oracle: `@[builtin_term_elab explicitUniv] elabExplicitUniv :=
        // elabAtom` (`App.lean:2249`) — a zero-argument application whose
        // head carries an explicit universe list; `app::peel_head` strips
        // the `.{us}` suffix exactly as `elabAppFn` does (`App.lean:2103`).
        ("Lean.Parser.Term.explicitUniv", NodeOrToken::Node(_)) => {
            crate::app::elab_atom(elab, elem, kinds, expected)
        }
        ("Lean.Parser.Term.prop", NodeOrToken::Node(node)) => {
            crate::builtin::sort::elab_prop(elab, node, kinds)
        }
        ("Lean.Parser.Term.type", NodeOrToken::Node(node)) => {
            crate::builtin::sort::elab_type(elab, node, kinds)
        }
        ("Lean.Parser.Term.sort", NodeOrToken::Node(node)) => {
            crate::builtin::sort::elab_sort(elab, node, kinds)
        }
        ("Lean.Parser.Term.paren", NodeOrToken::Node(node)) => {
            crate::builtin::ascription::elab_paren(elab, node, kinds, expected)
        }
        ("Lean.Parser.Term.typeAscription", NodeOrToken::Node(node)) => {
            crate::builtin::ascription::elab_ascription(elab, node, kinds, expected)
        }
        ("Lean.Parser.Term.hole", NodeOrToken::Node(node)) => {
            crate::builtin::hole::elab_hole(elab, node, kinds, expected)
        }
        ("Lean.Parser.Term.arrow", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_arrow(elab, node, kinds)
        }
        ("Lean.Parser.Term.forall", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_forall(elab, node, kinds)
        }
        ("Lean.Parser.Term.depArrow", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_dep_arrow(elab, node, kinds)
        }
        ("Lean.Parser.Term.fun", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_fun(elab, node, kinds)
        }
        ("Lean.Parser.Term.let", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_let_like(elab, node, kinds, expected, false)
        }
        ("Lean.Parser.Term.have", NodeOrToken::Node(node)) => {
            crate::builtin::binder::elab_let_like(elab, node, kinds, expected, true)
        }
        (other, _) => Err(ElabError::UnsupportedSyntax(other.to_string())),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn unregistered_kind_is_unsupported() {
        // A synthetic node of an unknown kind must dispatch to
        // UnsupportedSyntax carrying the kind name — never a panic,
        // never a wrong ExprId.
        let name = crate::dispatch::elaborator_name_for("Lean.Parser.Term.match");
        assert!(
            name.is_none(),
            "match is not a leaf and must not be registered"
        );
    }
}
