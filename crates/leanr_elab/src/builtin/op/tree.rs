//! oracle: `BinOpKind`, `Tree` and `toTree` (`Extra.lean:154-229`).

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;

use super::{grow, resolve_head, OpView};
use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::{TermElabM, TermTarget};
use crate::error::ElabError;
use crate::macros::OpKind;
use crate::synthetic::PostponeBehavior;

/// oracle: `BinOpKind` (`:154-159`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BinOpKind {
    Regular,
    Lazy,
    LeftAct,
    RightAct,
}

/// oracle: `Tree` (`:161-180`). The `infoTrees` payload and the macro name
/// are dropped (no info trees in leanr), and so is `macroExpansion`'s
/// expanded syntax `stx'`: an `Expansion` is not a `SynElem`, and nothing
/// reads it without info trees or `withMacroExpansion`'s error context.
#[derive(Debug, Clone)]
pub(crate) enum Tree {
    Term {
        r#ref: SynElem,
        val: ExprId,
    },
    BinOp {
        r#ref: SynElem,
        kind: BinOpKind,
        f: ExprId,
        lhs: Box<Tree>,
        rhs: Box<Tree>,
    },
    UnOp {
        r#ref: SynElem,
        f: ExprId,
        arg: Box<Tree>,
    },
    MacroExpansion {
        stx: SynElem,
        nested: Box<Tree>,
    },
}

impl Tree {
    pub(crate) fn ref_elem(&self) -> &SynElem {
        match self {
            Tree::Term { r#ref, .. } | Tree::BinOp { r#ref, .. } | Tree::UnOp { r#ref, .. } => {
                r#ref
            }
            Tree::MacroExpansion { stx, .. } => stx,
        }
    }
}

/// oracle: `toTree` (`:183-192`) on syntax already known to be an op node:
/// `go`, then `synthesizeSyntheticMVars (postpone := .yes)`.
pub(crate) fn to_tree_view(
    elab: &mut TermElabM,
    view: &OpView,
    kinds: &KindInterner,
) -> Result<Tree, ElabError> {
    let t = process_view(elab, view, kinds)?;
    elab.synthesize_synthetic_mvars(PostponeBehavior::Yes, kinds)?;
    Ok(t)
}

/// oracle: `toTree` on an arbitrary operand (`binrel%`'s two sides,
/// `:531-532`).
pub(crate) fn to_tree(
    elab: &mut TermElabM,
    s: &SynElem,
    kinds: &KindInterner,
) -> Result<Tree, ElabError> {
    let t = go(elab, s, kinds)?;
    elab.synthesize_synthetic_mvars(PostponeBehavior::Yes, kinds)?;
    Ok(t)
}

/// oracle: `toTree.go` (`:194-213`).
fn go(elab: &mut TermElabM, s: &SynElem, kinds: &KindInterner) -> Result<Tree, ElabError> {
    grow(|| {
        // The five literal kinds `go` matches (`:196-200`); `binrel%` falls
        // through to the `_` arm, which makes it a leaf.
        if let Some(view) = OpView::from_literal(s, kinds)? {
            if !view.kind.is_rel() {
                return process_view(elab, &view, kinds);
            }
        }
        // `(($h:hygieneInfo $e))`: recurse unless `e` has a `·` (`:201-205`).
        if kinds.name(s.kind()) == "Lean.Parser.Term.paren" {
            let inner = paren_inner(s)?;
            return if has_cdot(&inner, kinds) {
                process_leaf(elab, TermTarget::Stx(s.clone()), s, kinds)
            } else {
                go(elab, &inner, kinds)
            };
        }
        // `expandMacroImpl?` (`:206-213`): an op expansion continues the
        // tree; anything else it expands to (an `App`, or `binrel%`) is a
        // LEAF of the expanded syntax, which is what `go s'` on it does in
        // the oracle (its `_` arm finds no further macro).
        match crate::macros::expand(s, kinds)? {
            Some(exp) => {
                let nested = match OpView::from_expansion(s, &exp) {
                    Some(view) if !view.kind.is_rel() => process_view(elab, &view, kinds)?,
                    _ => process_leaf(
                        elab,
                        TermTarget::Expanded {
                            r#ref: s.clone(),
                            exp,
                        },
                        s,
                        kinds,
                    )?,
                };
                Ok(Tree::MacroExpansion {
                    stx: s.clone(),
                    nested: Box::new(nested),
                })
            }
            None => process_leaf(elab, TermTarget::Stx(s.clone()), s, kinds),
        }
    })
}

/// oracle: `processBinOp` / `processUnOp` (`:215-224`).
fn process_view(
    elab: &mut TermElabM,
    view: &OpView,
    kinds: &KindInterner,
) -> Result<Tree, ElabError> {
    let f = resolve_head(elab, &view.head)?;
    let r#ref = view.r#ref.clone();
    let kind = match view.kind {
        OpKind::UnOp => {
            let arg = go(elab, &view.args[0], kinds)?;
            return Ok(Tree::UnOp {
                r#ref,
                f,
                arg: Box::new(arg),
            });
        }
        OpKind::BinOp => BinOpKind::Regular,
        OpKind::BinOpLazy => BinOpKind::Lazy,
        OpKind::LeftAct => BinOpKind::LeftAct,
        OpKind::RightAct => BinOpKind::RightAct,
        OpKind::BinRel | OpKind::BinRelNoProp => {
            return Err(ElabError::Internal(
                "op tree: process_view on a binrel".into(),
            ))
        }
    };
    // `leftact`/`rightact`: that side is a leaf (`:217-219`).
    let lhs = if kind == BinOpKind::LeftAct {
        process_leaf(
            elab,
            TermTarget::Stx(view.args[0].clone()),
            &view.args[0],
            kinds,
        )?
    } else {
        go(elab, &view.args[0], kinds)?
    };
    let rhs = if kind == BinOpKind::RightAct {
        process_leaf(
            elab,
            TermTarget::Stx(view.args[1].clone()),
            &view.args[1],
            kinds,
        )?
    } else {
        go(elab, &view.args[1], kinds)?
    };
    Ok(Tree::BinOp {
        r#ref,
        kind,
        f,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    })
}

/// oracle: `processLeaf` (`:226-229`): `elabTerm s none`.
fn process_leaf(
    elab: &mut TermElabM,
    target: TermTarget,
    r#ref: &SynElem,
    kinds: &KindInterner,
) -> Result<Tree, ElabError> {
    let val = elab.elab_target(&target, kinds, None)?;
    Ok(Tree::Term {
        r#ref: r#ref.clone(),
        val,
    })
}

fn paren_inner(s: &SynElem) -> Result<SynElem, ElabError> {
    s.as_node()
        .and_then(|n| non_trivia_children(n).into_iter().nth(1))
        .ok_or_else(|| ElabError::IllFormedSyntax("paren: no inner term".into()))
}

/// oracle: `hasCDot` (`Lean/Elab/BuiltinNotation.lean:306-311`) with
/// `isCDotBinderKind` (`:285-286`) and `isCDotForInfo` (`:292-299`). The
/// search stops at a cdot binder (`paren`, `typeAscription`, `tuple`): that
/// node owns its own `·`. `isCDotForInfo` compares the cdot's hygiene info
/// with the paren's. Every `·` that leanr parses from source carries the
/// same (empty) macro scopes as its enclosing paren, so any `cdot` node
/// matches.
fn has_cdot(e: &SynElem, kinds: &KindInterner) -> bool {
    match kinds.name(e.kind()) {
        "Lean.Parser.Term.paren" | "Lean.Parser.Term.typeAscription" | "Lean.Parser.Term.tuple" => {
            false
        }
        "Lean.Parser.Term.cdot" => true,
        _ => e
            .as_node()
            .is_some_and(|n| non_trivia_children(n).iter().any(|c| has_cdot(c, kinds))),
    }
}
