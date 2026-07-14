//! The parser as data (spec §Architecture / grammar): `Prim` is a
//! combinator tree the interpreter in `parse.rs` walks. Deliberately
//! ParserDescr-shaped: M3b maps `.olean`-decoded ParserDescr values
//! into this same enum, so builtin and user grammar run identically.
//! Builtin productions (builtin/*.rs) are Rust fns returning `Prim`.
//!
//! Categories/`GrammarSnapshot` arrive in Task 6 — this module is
//! deliberately just the combinator data structure for now.

use std::sync::Arc;

use crate::kind::SyntaxKind;

#[derive(Clone, Debug)]
pub enum Prim {
    /// Sequence; children parse in order into the current node.
    Seq(Vec<Prim>),
    /// `leading_parser`: open node `kind`; `prec` gates against the
    /// category's right-binding power (None = always).
    Node {
        kind: SyntaxKind,
        prec: Option<u32>,
        body: Arc<Prim>,
    },
    /// `trailing_parser`: only legal as a category trailing entry.
    /// The already-parsed lhs becomes the node's first child (Pratt
    /// wrap); `lhs_prec` is the minimum lhs precedence.
    TrailingNode {
        kind: SyntaxKind,
        prec: u32,
        lhs_prec: u32,
        body: Arc<Prim>,
    },
    /// Expect this exact atom token (must be in the snapshot's table).
    Symbol(String),
    /// Ident that is RESERVED in the table but allowed here (Lean
    /// `nonReservedSymbol`, e.g. contextual keywords).
    NonReservedSymbol(String),
    Ident,
    /// Literal leaves — each wraps its token in the Lean node kind:
    /// "num", "scientific", "str", "char", "name".
    NumLit,
    ScientificLit,
    StrLit,
    CharLit,
    NameLit,
    /// Raw digit run after `.` (projections `x.1`) — Lean `fieldIdx`.
    FieldIdx,
    /// Recurse into a category at the given right-binding power.
    Category {
        name: String,
        rbp: u32,
    },
    Optional(Arc<Prim>),
    Many(Arc<Prim>),
    Many1(Arc<Prim>),
    /// Items + separator atoms interleaved flat in one `null` node.
    SepBy {
        item: Arc<Prim>,
        sep: String,
        allow_trailing: bool,
    },
    SepBy1 {
        item: Arc<Prim>,
        sep: String,
        allow_trailing: bool,
    },
    OrElse(Vec<Prim>),
    Atomic(Arc<Prim>),
    Lookahead(Arc<Prim>),
    NotFollowedBy(Arc<Prim>),
    /// Group results into a "group" node (Lean `group`).
    Group(Arc<Prim>),
    // --- position/precedence checks (Task 6 implements semantics) ---
    WithPosition(Arc<Prim>),
    CheckColGt,
    CheckColGe,
    CheckColEq,
    CheckLineEq,
    CheckPrec(u32),
    CheckLhsPrec(u32),
    CheckWsBefore,
    CheckNoWsBefore,
    /// `many1Indent` / `sepByIndent` (do-blocks, tactic seqs) —
    /// Task 6 gives these their withPosition+colGe expansion.
    Many1Indent(Arc<Prim>),
    SepByIndentSemicolon(Arc<Prim>),
    /// Zero-width success producing a `Syntax.missing` leaf (used by
    /// error recovery and a few builtin productions).
    EmitMissing,
}

// Terse constructors — builtin/*.rs is written in these.
pub fn seq(ps: impl IntoIterator<Item = Prim>) -> Prim {
    Prim::Seq(ps.into_iter().collect())
}
/// An always-fires `Node` (`prec: None`) — the common case;
/// precedence-gated nodes are built with the `Prim::Node` literal
/// directly (see `builtin`'s `leading_parser` definitions).
pub fn node(kind: SyntaxKind, body: Prim) -> Prim {
    Prim::Node {
        kind,
        prec: None,
        body: Arc::new(body),
    }
}
pub fn sym(s: &str) -> Prim {
    Prim::Symbol(s.to_string())
}
pub fn opt(p: Prim) -> Prim {
    Prim::Optional(Arc::new(p))
}
pub fn many(p: Prim) -> Prim {
    Prim::Many(Arc::new(p))
}
pub fn many1(p: Prim) -> Prim {
    Prim::Many1(Arc::new(p))
}
pub fn sep_by1(item: Prim, sep: &str) -> Prim {
    Prim::SepBy1 {
        item: Arc::new(item),
        sep: sep.to_string(),
        allow_trailing: false,
    }
}
pub fn or_else(ps: impl IntoIterator<Item = Prim>) -> Prim {
    Prim::OrElse(ps.into_iter().collect())
}
pub fn atomic(p: Prim) -> Prim {
    Prim::Atomic(Arc::new(p))
}
pub fn cat(name: &str, rbp: u32) -> Prim {
    Prim::Category {
        name: name.to_string(),
        rbp,
    }
}
