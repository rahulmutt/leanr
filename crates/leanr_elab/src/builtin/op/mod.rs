//! The `binop%` family elaborator (macro/binop% P3; design spec § P3).
//! oracle: `Lean/Elab/Extra.lean:154-566`.
//!
//! The oracle's doc (`Extra.lean:80-152`) explains the protocol: a whole
//! tree of nested `binop%`/`unop%`/`leftact%`/`rightact%` notation is
//! elaborated at once. Its leaves are elaborated WITHOUT an expected type.
//! Their types are joined to a "maximal" type along coercions (`analyze`).
//! The leaves are then coerced up to it (`apply_coe`). Only then are the
//! operators applied (`to_expr_core`).
//!
//! Two entry points share [`OpView`]: P2's table expansions (`elab.rs`'s
//! `TermTarget::Expanded`, with a pre-resolved global head: hygiene) and
//! the literal syntax `binop% f a b` (`dispatch`, head resolved by
//! `resolveId?`).
//!
//! Every recursion here (`tree::go`, `analyze`'s walk, `apply_coe`,
//! `to_expr_core`) is one frame per operator of a user-written chain, so
//! each grows the stack on demand ([`grow`]), as `elab.rs`'s anonymous
//! constructor tail does.
//!
//! Not modelled: info trees (the oracle's `Tree.term` payload and
//! `withTermInfoContext'`), and the trace classes. `withRef` is not
//! modelled either: leanr's errors carry no positions yet. Also not
//! modelled: `resolveId?`'s `checkDeprecated` (`TermElabM.lean:2221`);
//! it only logs a warning.

pub mod analyze;
mod rel;
pub mod to_expr;
mod tree;

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::NodeOrToken;

use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::macros::{Expansion, OpKind};

/// Run `f` with at least `elab.rs`'s red zone of stack left, growing it
/// otherwise (`stacker`, the idiom of `leanr_meta`'s `MetaCtx::guarded`).
/// A 300-operand chain is 300 nested frames of each walk.
pub(crate) fn grow<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(crate::elab::RED_ZONE, crate::elab::STACK_CHUNK, f)
}

/// Where an op node's head comes from.
#[derive(Debug, Clone)]
pub(crate) enum OpHead {
    /// A table expansion: the quotation's pre-resolved global.
    Global(&'static str),
    /// Literal syntax: the identifier as written, for `resolveId?`.
    Ident(SynElem),
}

/// One `binop%`-family node, from either entry point.
#[derive(Debug, Clone)]
pub(crate) struct OpView {
    pub kind: OpKind,
    pub head: OpHead,
    /// Operand subtrees: two, or one for `unop%`.
    pub args: Vec<SynElem>,
    /// The original syntax: the notation node, or the literal node.
    pub r#ref: SynElem,
}

impl OpView {
    pub(crate) fn from_expansion(r#ref: &SynElem, exp: &Expansion) -> Option<OpView> {
        match exp {
            Expansion::Op { kind, f, args } => Some(OpView {
                kind: *kind,
                head: OpHead::Global(f),
                args: args.clone(),
                r#ref: r#ref.clone(),
            }),
            Expansion::App { .. } => None,
        }
    }

    /// A literal node: non-trivia children `[atom, f, a, b]`, or
    /// `[atom, f, a]` for `unop%` (`leanr_syntax`'s `term_app.rs`,
    /// `register_binop_family`). `Ok(None)`: not one of the seven kinds.
    pub(crate) fn from_literal(
        elem: &SynElem,
        kinds: &KindInterner,
    ) -> Result<Option<OpView>, ElabError> {
        let name = kinds.name(elem.kind());
        let Some(kind) = OpKind::ALL.into_iter().find(|k| k.syntax_kind() == name) else {
            return Ok(None);
        };
        let node = elem
            .as_node()
            .ok_or_else(|| ElabError::IllFormedSyntax(format!("{name}: a token")))?;
        let ch = non_trivia_children(node);
        let arity = if kind == OpKind::UnOp { 1 } else { 2 };
        if ch.len() != arity + 2 {
            return Err(ElabError::IllFormedSyntax(format!(
                "{name}: {} children, expected {}",
                ch.len(),
                arity + 2
            )));
        }
        Ok(Some(OpView {
            kind,
            head: OpHead::Ident(ch[1].clone()),
            args: ch[2..].to_vec(),
            r#ref: elem.clone(),
        }))
    }
}

/// oracle: `elabOp` (`Extra.lean:475-476`, registered at `:478-482`) and
/// `elabBinRel{,NoProp}` (`:564-566`).
pub(crate) fn elab_op_view(
    elab: &mut TermElabM,
    view: &OpView,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    match view.kind {
        OpKind::BinRel => rel::elab_bin_rel_core(elab, view, false, kinds, expected),
        OpKind::BinRelNoProp => rel::elab_bin_rel_core(elab, view, true, kinds, expected),
        _ => {
            let tree = tree::to_tree_view(elab, view, kinds)?;
            to_expr::to_expr(elab, &tree, expected, kinds)
        }
    }
}

/// `processBinOp`/`processUnOp`'s
/// `let some f ← resolveId? f | throwUnknownConstantAt f f.getId`
/// (`Extra.lean:216`, `:223`; `elabBinRelCore`'s `:498`/`:554`). A table
/// head is the quotation's pre-resolved global: `mkConst` with fresh
/// levels, never a local.
pub(crate) fn resolve_head(elab: &mut TermElabM, head: &OpHead) -> Result<ExprId, ElabError> {
    match head {
        OpHead::Global(f) => {
            let name = crate::app::head::intern_dotted(elab, f)?;
            if elab.view.get(name).is_none() {
                return Err(ElabError::UnknownConstant(f.to_string()));
            }
            crate::app::head::mk_const(elab, name, &[], f)
        }
        OpHead::Ident(elem) => {
            let raw = match elem {
                NodeOrToken::Token(t) => t.text().to_string(),
                NodeOrToken::Node(_) => {
                    return Err(ElabError::IllFormedSyntax("identifier expected".into()))
                }
            };
            resolve_id(elab, &raw)?.ok_or(ElabError::UnknownConstant(raw))
        }
    }
}

/// oracle: `resolveId?` (`TermElabM.lean:2211-2224`): `resolveName`, keep
/// the candidates with NO leftover field projections, `none` if there is
/// none. `resolveName` tries locals first (`:2180-2181`; a local hit hides
/// the globals even when its projections are then filtered away). `catch
/// _ => []` keeps only the not-found case: leanr's resolver reports a miss
/// as `UnknownIdent`. Every other error propagates (`AmbiguousIdent` is
/// the oracle's "ambiguous term" throw at `:2223`).
///
/// The identifier is decoded (`app::head::ident_prefixes`), as in
/// `app::head::elab_app_fn_id`, so a local binder's name matches the same way.
fn resolve_id(elab: &mut TermElabM, raw: &str) -> Result<Option<ExprId>, ElabError> {
    let (_, prefixes) = crate::app::head::ident_prefixes(elab, raw)?;
    if let Some((fvar, n_fields)) = crate::resolve::resolve_local_name(&elab.mctx, &prefixes) {
        return Ok((n_fields == 0).then_some(fvar));
    }
    match crate::resolve::resolve_global_name(&elab.view, &prefixes, raw) {
        Ok((cname, 0)) => Ok(Some(crate::app::head::mk_const(elab, cname, &[], raw)?)),
        Ok(_) | Err(ElabError::UnknownIdent(_)) => Ok(None),
        Err(e) => Err(e),
    }
}

/// The declared constant `name` at fresh level mvars (`rel.rs`'s `Bool`;
/// also the white-box tests' hook).
#[doc(hidden)]
pub fn mk_const_named(elab: &mut TermElabM, name: &str) -> Result<ExprId, ElabError> {
    let n = crate::app::head::intern_dotted(elab, name)?;
    if elab.view.get(n).is_none() {
        return Err(ElabError::UnknownConstant(name.to_string()));
    }
    crate::app::head::mk_const(elab, n, &[], name)
}
