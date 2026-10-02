//! Macro expansion in dispatch (macro/binop% P2; design spec § P2).
//!
//! oracle: `elabTermAux` (`Lean/Elab/Term/TermElabM.lean:1823-1856`) runs
//! `expandMacroImpl?` (`:1831`) before the implicit-lambda check and
//! before any elaborator, and recurses on the result (`:1837`). leanr
//! has no VM to run Init's compiled `macro_rules`, so [`expand`] reads
//! the hand-ported [`init::INIT_MACROS`] instead. A VM later replaces
//! the table behind the same call. Mathlib's own notations stay
//! unsupported until then (`UnsupportedSyntax`, named by their kind).
//!
//! Expansion is pure: no `Expr`, no `MetaCtx`, and the same answer for
//! the same node every time. That is what lets a postponed notation
//! store its ORIGINAL node and re-expand on resume
//! (`elab.rs`'s `TermTarget::Expanded`).

pub mod init;

use leanr_syntax::kind::KindInterner;

use crate::dispatch::{non_trivia_children, SynElem};
use crate::error::ElabError;
use init::{Head, Shape};

/// The `binop%` family (`Lean/Elab/Extra.lean:478-482`, `:564-566`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpKind {
    BinOp,
    BinOpLazy,
    BinRel,
    BinRelNoProp,
    UnOp,
    LeftAct,
    RightAct,
}

impl OpKind {
    /// The kind of the literal form (`binop% f a b`, …), as `leanr_syntax`
    /// registers it (`builtin/term/term_app.rs`'s `register_binop_family`).
    pub fn syntax_kind(self) -> &'static str {
        match self {
            OpKind::BinOp => "Lean.Parser.Term.binop",
            OpKind::BinOpLazy => "Lean.Parser.Term.binop_lazy",
            OpKind::BinRel => "Lean.Parser.Term.binrel",
            OpKind::BinRelNoProp => "Lean.Parser.Term.binrel_no_prop",
            OpKind::UnOp => "Lean.Parser.Term.unop",
            OpKind::LeftAct => "Lean.Parser.Term.leftact",
            OpKind::RightAct => "Lean.Parser.Term.rightact",
        }
    }
}

/// A notation's expansion. leanr cannot build nodes inside an existing
/// rowan tree, so this stands for the synthesized syntax.
///
/// `f` models the quotation's hygienic identifier: a global the
/// quotation pre-resolved, never looked up in the local context, so
/// `fun (And : Nat) => True ∧ False` still means the global `And`.
/// `args` are the notation's own operand subtrees, so error positions
/// land on real source.
#[derive(Debug, Clone)]
pub enum Expansion {
    /// `binop% f a b` and the rest of the family. Elaborated by P3; until
    /// then a named `UnsupportedSyntax` seam.
    Op {
        kind: OpKind,
        f: &'static str,
        args: Vec<SynElem>,
    },
    /// `f a b`, a plain application.
    App { f: &'static str, args: Vec<SynElem> },
}

impl Expansion {
    /// The kind the expanded syntax would carry in the oracle.
    pub fn kind_name(&self) -> &'static str {
        match self {
            Expansion::Op { kind, .. } => kind.syntax_kind(),
            Expansion::App { .. } => "Lean.Parser.Term.app",
        }
    }

    pub fn f(&self) -> &'static str {
        match self {
            Expansion::Op { f, .. } | Expansion::App { f, .. } => f,
        }
    }

    pub fn args(&self) -> &[SynElem] {
        match self {
            Expansion::Op { args, .. } | Expansion::App { args, .. } => args,
        }
    }
}

/// Env-agnostic by design: the table fires on the kind name alone and
/// ignores the environment's macro attribute, so an environment that
/// redeclares e.g. `«term_∧_»` with a different macro would still expand
/// to `And`. Today unreachable (no same-file notation pipeline; core
/// Init/Lean/Std do not override these kinds); the VM slice replaces the
/// table.
///
/// oracle: `expandMacroImpl?` (`Lean/Elab/Util.lean:157-167`) over the
/// table. `Ok(None)`: no row for this kind, so elaborate `elem` as is.
pub fn expand(elem: &SynElem, kinds: &KindInterner) -> Result<Option<Expansion>, ElabError> {
    let Some(row) = init::lookup(kinds.name(elem.kind())) else {
        return Ok(None);
    };
    let node = elem.as_node().ok_or_else(|| {
        ElabError::IllFormedSyntax(format!(
            "{}: a notation that is a token, not a node",
            row.kind
        ))
    })?;
    let ch = non_trivia_children(node);
    let args = match (row.shape, ch.as_slice()) {
        (Shape::Infix, [lhs, _, rhs]) => vec![lhs.clone(), rhs.clone()],
        (Shape::Prefix, [_, operand]) => vec![operand.clone()],
        _ => {
            return Err(ElabError::IllFormedSyntax(format!(
                "{}: {} children, expected {}",
                row.kind,
                ch.len(),
                row.arity() + 1
            )))
        }
    };
    Ok(Some(match row.head {
        Head::Op(kind) => Expansion::Op {
            kind,
            f: row.f,
            args,
        },
        Head::App => Expansion::App { f: row.f, args },
    }))
}
