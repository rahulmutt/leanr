//! Syntax → argument lists. Oracle: `expandApp`/`expandArgs`
//! (`Lean/Elab/Arg.lean:62-84`). Pure syntax navigation — no `Expr` is
//! built here, and nothing in this file touches `MetaCtx`.
//!
//! Confirmed `Term.app` child layout (probe, Task 2 step 2: `cargo test
//! -p leanr_elab --test app_smoke probe_app_tree_shape -- --nocapture`,
//! and the follow-up `probe_app_args_and_named_arg_shape`, both run
//! before being deleted per Step 7):
//!
//! ```text
//! Nat.succ Nat.zero:
//!   [0] kind=<ident> text="Nat.succ"
//!   [1] kind=null    text=" Nat.zero"
//! ```
//!
//! `non_trivia_children(app_node)` is exactly `[head, args_null]` — index
//! 0 is the function head (a bare `<ident>` token for a dotted
//! identifier like `Nat.succ`; other head shapes are untested here),
//! index 1 is a single wrapping `null` node. `Lean.Parser.Term.app`'s
//! `many1(argument)` body opens that `null` node itself (`Ps::many_impl`
//! in `leanr_syntax::parse` calls `self.start(KIND_NULL)`); the
//! argument items are ITS children, reached by a second
//! `non_trivia_children` call. No trivia appears between `head` and the
//! `null` wrapper — the leading space before `Nat.zero` lives inside the
//! `null` node's own child stream (stripped by that second call).
//!
//! Confirmed argument-item shape:
//!
//! ```text
//! Nat.succ (n := Nat.zero):
//!   args-null non-trivia children:
//!     [0] kind=<atom>  text="("
//!     [1] kind=<ident> text="n"
//!     [2] kind=<atom>  text=":="
//!     [3] kind=<ident> text="Nat.zero"
//!     [4] kind=<atom>  text=")"
//!
//! Nat.succ ..:
//!   args-null non-trivia children:
//!     [0] kind=<atom>  text=".."
//! ```
//!
//! A PLAIN positional argument is one item (a `Node`, e.g.
//! `Lean.Parser.Term.paren`, or a bare `<ident>` token) as expected. A
//! NAMED argument and a trailing `..`, however, are **not** wrapped in
//! their own node at all: `leanr_syntax`'s `named_argument()` and
//! `ellipsis_arg()` (`crates/leanr_syntax/src/builtin/term.rs`) are
//! built from a bare `seq(...)`/`Prim::Symbol`, never a `Prim::Node`-
//! opening `b.leading`/`b.leading2` call the way every OTHER
//! term-category parser (including `paren`/`tuple`, which also start
//! with `(`) is registered — so their tokens flatten directly into the
//! enclosing `null` node instead of collecting under a
//! `Lean.Parser.Term.namedArgument` / `Lean.Parser.Term.ellipsis` kind
//! the way the oracle's `leading_parser`-based grammar does. This is a
//! genuine `leanr_syntax` grammar gap relative to the oracle — out of
//! scope for this task to fix (Global Constraints / ambiguity
//! resolution #3: a missing/malformed surface belongs to `leanr_syntax`'s
//! slice, not this one) — so `expand_args` below matches on ATOM TEXT
//! (`"("`, `":="`, `")"`, `".."`) and reassembles the flat run into a
//! `NamedArg`, rather than on a `"Lean.Parser.Term.namedArgument"` kind
//! name the current tree never produces. A raw `"("` atom sibling can
//! only originate from an unwrapped `named_argument()` run: every other
//! term-category parser capable of starting with `(` opens its own node
//! (`b.leading`/`b.leading2`), so a genuine positional parenthesized
//! argument always arrives as a single `Node` item, never a bare `(`
//! atom.

use crate::dispatch::{non_trivia_children, SynElem};
use crate::error::ElabError;
use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::{NodeOrToken, SyntaxNode};

/// oracle: `inductive Arg` (`Arg.lean:19-21`) — an argument is either
/// unelaborated syntax or an already-elaborated `Expr`. The `Expr` arm
/// has no P1 producer (it exists for dot-notation/`pipeProj` in M4b-4
/// and for `binop%`), but the type carries it so later slices need not
/// reshape the state machine.
#[derive(Debug, Clone)]
pub enum Arg {
    Stx(SynElem),
    Expr(ExprId),
}

/// oracle: `structure NamedArg` (`Arg.lean:34-45`).
#[derive(Debug, Clone)]
pub struct NamedArg {
    /// The identifier's raw source text (see the module doc on why this
    /// is not a `NameId`).
    pub name: String,
    pub val: Arg,
    /// oracle: `NamedArg.numImplicitParams` — overrides the binder info
    /// of the first N parameters to implicit. Only ever nonzero for
    /// structure-projection expansion (`f.val`), which is M4b-4, so
    /// every P1 producer sets 0. The field exists because
    /// `process_explicit_arg` branches on it.
    pub num_implicit_params: usize,
}

/// `item` is a bare atom token (`KIND_ATOM`) whose text is exactly
/// `text`. See the module doc: the only way to recognize the unwrapped
/// `(`/`:=`/`)`/`..` pieces `leanr_syntax` emits for named arguments and
/// the ellipsis, since none of them carry a distinguishing node kind.
fn is_atom(item: &SynElem, kinds: &KindInterner, text: &str) -> bool {
    match item {
        NodeOrToken::Token(tok) => kinds.name(tok.kind()) == "<atom>" && tok.text() == text,
        NodeOrToken::Node(_) => false,
    }
}

/// oracle: `expandApp` (`Arg.lean:82-84`).
pub fn expand_app(
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<(SynElem, Vec<NamedArg>, Vec<Arg>, bool), ElabError> {
    let ch = non_trivia_children(node);
    let head = ch
        .first()
        .cloned()
        .ok_or_else(|| ElabError::IllFormedSyntax("app: no function child".to_string()))?;
    let args_node = ch
        .get(1)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::IllFormedSyntax("app: no argument-list node".to_string()))?;
    let items = non_trivia_children(args_node);
    let (named, args, ellipsis) = expand_args(&items, kinds)?;
    Ok((head, named, args, ellipsis))
}

/// oracle: `expandArgs` (`Arg.lean:62-80`). Note the exact order: the
/// trailing `..` is popped FIRST (so a `..` anywhere else is the error
/// case), then each remaining item is classified.
///
/// As the module doc explains, `items` here is a FLAT list — a named
/// argument is not one item but a five-item run (`(`, name, `:=`,
/// value, `)`) and the ellipsis is a single bare `..` atom, not a node
/// of a distinguishing kind. This loop reassembles both from that flat
/// shape rather than matching a wrapping node's kind name.
pub fn expand_args(
    items: &[SynElem],
    kinds: &KindInterner,
) -> Result<(Vec<NamedArg>, Vec<Arg>, bool), ElabError> {
    let mut ellipsis = false;
    let mut end = items.len();
    if end > 0 && is_atom(&items[end - 1], kinds, "..") {
        end -= 1;
        ellipsis = true;
    }

    let mut named: Vec<NamedArg> = Vec::new();
    let mut args: Vec<Arg> = Vec::new();
    let mut idx = 0;
    while idx < end {
        let item = &items[idx];
        if is_atom(item, kinds, "..") {
            // oracle: `throwErrorAt stx "unexpected '..'"` — only a
            // TRAILING `..` is legal, and that one was popped above.
            return Err(ElabError::IllFormedSyntax("unexpected '..'".to_string()));
        }
        if is_atom(item, kinds, "(") {
            // Unwrapped named-argument run (module doc): `(` name `:=`
            // value `)`, five flat siblings.
            let name_item = items
                .get(idx + 1)
                .ok_or_else(|| ElabError::IllFormedSyntax("namedArgument: no name".to_string()))?;
            let name = match name_item {
                NodeOrToken::Token(t) => t.text().to_string(),
                NodeOrToken::Node(n) => n.text().to_string(),
            };
            let has_assign = items
                .get(idx + 2)
                .is_some_and(|el| is_atom(el, kinds, ":="));
            if !has_assign {
                return Err(ElabError::IllFormedSyntax(
                    "namedArgument: missing ':='".to_string(),
                ));
            }
            let val = items
                .get(idx + 3)
                .cloned()
                .ok_or_else(|| ElabError::IllFormedSyntax("namedArgument: no value".to_string()))?;
            let has_close = items.get(idx + 4).is_some_and(|el| is_atom(el, kinds, ")"));
            if !has_close {
                return Err(ElabError::IllFormedSyntax(
                    "namedArgument: missing ')'".to_string(),
                ));
            }
            // oracle: `addNamedArg` (`Arg.lean:55-59`) errors on a
            // repeated name rather than silently keeping one.
            if named.iter().any(|na| na.name == name) {
                return Err(ElabError::DuplicateNamedArg(name));
            }
            named.push(NamedArg {
                name,
                val: Arg::Stx(val),
                num_implicit_params: 0,
            });
            idx += 5;
            continue;
        }
        args.push(Arg::Stx(item.clone()));
        idx += 1;
    }
    Ok((named, args, ellipsis))
}
