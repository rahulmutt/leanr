//! The hand-ported Init macro table (macro/binop% design spec § The
//! table). leanr has no VM, so Init's compiled `macro_rules` cannot run;
//! each row reproduces one. Where a kind has two macros (the
//! `infixl`-generated `f a b` and a later `macro_rules`), the row is the
//! one `expandMacroImpl?` (`Lean/Elab/Util.lean:157-167`) picks: the most
//! recently declared, which is the first entry `getEntries` returns.
//!
//! `tests/oracle_op.rs`'s `table_matches_oracle_expansions` holds this
//! table to the oracle's `op-expansions.jsonl` in both directions, and the
//! regen task diffs that file against the real Init. Kind names are the
//! oracle's `Name.toString` spelling, which is also `KindInterner`'s.

use super::OpKind;

/// Where the operands sit among the notation node's non-trivia children.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shape {
    /// `lhs op rhs`: children `[lhs, atom, rhs]`.
    Infix,
    /// `op x`: children `[atom, x]`.
    Prefix,
}

/// What the expansion's head is applied through.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Head {
    /// `binop% f a b` and the rest of the family.
    Op(OpKind),
    /// A plain application `f a b`.
    App,
}

#[derive(Debug)]
pub struct MacroRow {
    pub kind: &'static str,
    pub shape: Shape,
    pub head: Head,
    /// The global the quotation's hygienic identifier pre-resolves to.
    pub f: &'static str,
}

impl MacroRow {
    pub fn expansion_kind(&self) -> &'static str {
        match self.head {
            Head::Op(k) => k.syntax_kind(),
            Head::App => "Lean.Parser.Term.app",
        }
    }

    pub fn arity(&self) -> usize {
        match self.shape {
            Shape::Infix => 2,
            Shape::Prefix => 1,
        }
    }
}

const fn op(kind: &'static str, k: OpKind, f: &'static str) -> MacroRow {
    MacroRow {
        kind,
        shape: Shape::Infix,
        head: Head::Op(k),
        f,
    }
}

const fn app(kind: &'static str, shape: Shape, f: &'static str) -> MacroRow {
    MacroRow {
        kind,
        shape,
        head: Head::App,
        f,
    }
}

/// One row per kind. Citations are `Init/Notation.lean` unless noted.
pub static INIT_MACROS: &[MacroRow] = &[
    op("«term_|||_»", OpKind::BinOp, "HOr.hOr"),    // :302
    op("«term_^^^_»", OpKind::BinOp, "HXor.hXor"),  // :303
    op("«term_&&&_»", OpKind::BinOp, "HAnd.hAnd"),  // :304
    op("«term_+_»", OpKind::BinOp, "HAdd.hAdd"),    // :305
    op("«term_-_»", OpKind::BinOp, "HSub.hSub"),    // :306
    op("«term_*_»", OpKind::BinOp, "HMul.hMul"),    // :307
    op("«term_/_»", OpKind::BinOp, "HDiv.hDiv"),    // :308
    op("«term_%_»", OpKind::BinOp, "HMod.hMod"),    // :309
    op("«term_^_»", OpKind::RightAct, "HPow.hPow"), // :311
    op("«term_++_»", OpKind::BinOp, "HAppend.hAppend"), // :312
    MacroRow {
        kind: "«term-_»",
        shape: Shape::Prefix,
        head: Head::Op(OpKind::UnOp),
        f: "Neg.neg",
    }, // :313
    op("«term_•_»", OpKind::LeftAct, "HSMul.hSMul"), // :347
    op("«term_>=_»", OpKind::BinRel, "GE.ge"),      // :372
    op("«term_<=_»", OpKind::BinRel, "LE.le"),      // :373
    op("«term_≤_»", OpKind::BinRel, "LE.le"),       // :389
    op("«term_<_»", OpKind::BinRel, "LT.lt"),       // :390
    op("«term_>_»", OpKind::BinRel, "GT.gt"),       // :391
    op("«term_≥_»", OpKind::BinRel, "GE.ge"),       // :392
    op("«term_=_»", OpKind::BinRel, "Eq"),          // :393
    op("«term_==_»", OpKind::BinRelNoProp, "BEq.beq"), // :394
    op("«term_<|>_»", OpKind::BinOpLazy, "HOrElse.hOrElse"), // :436
    op("«term_>>_»", OpKind::BinOpLazy, "HAndThen.hAndThen"), // :437
    op("«term_!=_»", OpKind::BinRelNoProp, "bne"),  // Init/Core.lean:777
    op("«term_≠_»", OpKind::BinRel, "Ne"),          // Init/Core.lean:880
    app("«term_∧_»", Shape::Infix, "And"),          // :404 (infixr, unicode `/\`)
    app("«term_∨_»", Shape::Infix, "Or"),           // :405 (infixr, unicode `\/`)
    app("«term¬_»", Shape::Prefix, "Not"),          // :406 (notation)
    app("«term_<->_»", Shape::Infix, "Iff"),        // Init/Core.lean:196
    app("«term_↔_»", Shape::Infix, "Iff"),          // Init/Core.lean:197
];

/// The row for a syntax kind, if Init declares a macro for it.
pub fn lookup(kind: &str) -> Option<&'static MacroRow> {
    INIT_MACROS.iter().find(|r| r.kind == kind)
}

#[cfg(test)]
mod tests {
    #[test]
    fn kinds_are_unique() {
        let mut kinds: Vec<&str> = super::INIT_MACROS.iter().map(|r| r.kind).collect();
        kinds.sort_unstable();
        kinds.dedup();
        assert_eq!(kinds.len(), super::INIT_MACROS.len());
    }
}
