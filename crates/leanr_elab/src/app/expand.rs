//! Syntax → argument lists. Oracle: `expandApp`/`expandArgs`
//! (`Lean/Elab/Arg.lean:62-84`). Pure syntax navigation — no `Expr` is
//! built here, and nothing in this file touches `MetaCtx`.
//!
//! Confirmed `Term.app` child layout (probe, Task 2 step 2: `cargo test
//! -p leanr_elab --test app_smoke probe_app_tree_shape -- --nocapture`):
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
//! Confirmed argument-item shape (fix round 1: `leanr_syntax`'s
//! `named_argument`/`ellipsis_arg` (`crates/leanr_syntax/src/builtin/
//! term.rs`) originally left named arguments and the ellipsis as bare
//! `seq(...)`s whose tokens flattened into this `null` node with no
//! kind of their own — a real gap against the oracle, whose
//! `namedArgument`/`ellipsis` are genuine `leading_parser`s. Fixed at
//! the grammar level (see that file's doc comments on those two
//! functions), then re-probed here — `cargo test -p leanr_elab --test
//! app_smoke -- --nocapture` with a throwaway probe, since deleted per
//! the same M4b-1 "never landed" precedent as Step 2's probe — against
//! a fresh oracle dump (`lean --run dump_syntax.lean`, pinned
//! v4.33.0-rc1) of the same two sources, confirmed byte-for-byte
//! identical):
//!
//! ```text
//! Nat.succ (n := Nat.zero):
//!   args-null non-trivia children:
//!     [0] kind=Lean.Parser.Term.namedArgument text="(n := Nat.zero)"
//!       [0] kind=<atom>  text="("
//!       [1] kind=<ident> text="n"
//!       [2] kind=<atom>  text=":="
//!       [3] kind=<ident> text="Nat.zero"
//!       [4] kind=<atom>  text=")"
//!
//! Nat.succ ..:
//!   args-null non-trivia children:
//!     [0] kind=Lean.Parser.Term.ellipsis text=".."
//!       [0] kind=<atom>  text=".."
//! ```
//!
//! A PLAIN positional argument, a NAMED argument, and the ellipsis are
//! ALL a single item in the args-null's own child list, distinguished
//! by kind name — exactly how `Lean/Elab/Arg.lean`'s own `expandArgs`
//! dispatches on `stx.getKind`, and exactly how `expand_args` below
//! matches. Inside a `Lean.Parser.Term.namedArgument` node, `stx[1]`
//! (this file's index 1, via `non_trivia_children`) is the name and
//! `stx[3]` (index 3) is the value, matching the oracle's own
//! `stx[1]`/`stx[3]` indexing exactly (no trivia sits between these
//! children, so the trivia-stripped and raw positions coincide here).

use crate::dispatch::{non_trivia_children, SynElem};
use crate::error::ElabError;
use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

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
pub fn expand_args(
    items: &[SynElem],
    kinds: &KindInterner,
) -> Result<(Vec<NamedArg>, Vec<Arg>, bool), ElabError> {
    let mut items = items.to_vec();
    let mut ellipsis = false;
    if let Some(last) = items.last() {
        if kinds.name(last.kind()) == "Lean.Parser.Term.ellipsis" {
            items.pop();
            ellipsis = true;
        }
    }
    let mut named: Vec<NamedArg> = Vec::new();
    let mut args: Vec<Arg> = Vec::new();
    for item in items {
        match kinds.name(item.kind()) {
            "Lean.Parser.Term.namedArgument" => {
                let node = item.as_node().ok_or_else(|| {
                    ElabError::IllFormedSyntax("namedArgument is not a node".to_string())
                })?;
                let nch = non_trivia_children(node);
                // oracle: `stx[1].getId` is the name, `stx[3]` the
                // value — confirmed against both a fresh oracle dump and
                // leanr's own (now node-wrapped) tree, module doc above.
                let name_tok = nch.get(1).ok_or_else(|| {
                    ElabError::IllFormedSyntax("namedArgument: no name".to_string())
                })?;
                let name = match name_tok {
                    leanr_syntax::tree::NodeOrToken::Token(t) => t.text().to_string(),
                    leanr_syntax::tree::NodeOrToken::Node(n) => n.text().to_string(),
                };
                let val = nch.get(3).cloned().ok_or_else(|| {
                    ElabError::IllFormedSyntax("namedArgument: no value".to_string())
                })?;
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
            }
            "Lean.Parser.Term.ellipsis" => {
                // oracle: `throwErrorAt stx "unexpected '..'"` — only a
                // TRAILING `..` is legal, and that one was popped above.
                return Err(ElabError::IllFormedSyntax("unexpected '..'".to_string()));
            }
            _ => args.push(Arg::Stx(item)),
        }
    }
    Ok((named, args, ellipsis))
}
