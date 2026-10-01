//! oracle: `Lean/HeadIndex.lean` (v4.33.0-rc1) — `HeadIndex`,
//! `Expr.headNumArgs`, `Expr.toHeadIndex`. Consumed by `kabstract.rs`.
//! leanr's existing discrimination-tree keys (`discr_path.rs`) are a
//! different oracle structure (`DiscrTree.Key`) and are not reused.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId, NatId, StrId};

use crate::{MetaCtx, MetaError};

/// oracle: `inductive HeadIndex`. `fvar`/`mvar`/`const` carry the id the
/// node does; hash-consing makes `NameId`/`NatId`/`StrId` equality
/// structural. `Proj` carries the index as `u64` so `Proj`/`ProjBig`
/// compare equal for equal indices.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HeadIndex {
    FVar(Option<NameId>),
    MVar(Option<NameId>),
    Const(Option<NameId>),
    Proj(Option<NameId>, u64),
    LitNat(NatId),
    LitStr(StrId),
    Sort,
    Lam,
    Forall,
}

impl<'e> MetaCtx<'e> {
    /// oracle: `Expr.headNumArgs` — count `app` spines, looking through
    /// `letE` bodies and `mdata`.
    pub(crate) fn head_num_args(&self, mut e: ExprId) -> usize {
        let mut n = 0;
        loop {
            match self.node(e) {
                Node::App { f, .. } => {
                    n += 1;
                    e = f;
                }
                Node::LetE { body, .. } => e = body,
                Node::MData { expr, .. } => e = expr,
                _ => return n,
            }
        }
    }

    /// oracle: `Expr.toHeadIndex` = `toHeadIndexQuick?` falling back to
    /// `toHeadIndexSlow`. The slow path differs only at `letE`, where it
    /// instantiates the body with the value before continuing — so a
    /// single loop that does that at `letE` IS the oracle's result: the
    /// quick path returns `none` (falls back) exactly when it would reach
    /// a loose `bvar`, i.e. when a let body's head is the let-bound
    /// variable, and instantiating first is what the slow path does.
    /// A loose `bvar` reached without a binding `letE` is the oracle's
    /// `panic!` (unreachable from `kabstract`, which never asks about a
    /// term with loose bvars); here it is an error, never a panic.
    #[allow(clippy::wrong_self_convention)] // oracle name `toHeadIndex`; needs &mut for `instantiate1`
    pub(crate) fn to_head_index(&mut self, mut e: ExprId) -> Result<HeadIndex, MetaError> {
        loop {
            return Ok(match self.node(e) {
                Node::MVar { id } => HeadIndex::MVar(id),
                Node::FVar { id } => HeadIndex::FVar(id),
                Node::Const { name, .. } => HeadIndex::Const(name),
                Node::Proj { type_name, idx, .. } => HeadIndex::Proj(type_name, idx as u64),
                Node::ProjBig { type_name, idx, .. } => {
                    let base = Some(self.view.store);
                    let n = self.scratch.nat_at(base, idx);
                    // Indices beyond u64 cannot occur in a well-formed
                    // proj; saturate rather than panic (the key is only
                    // a filter — `isDefEq` still decides).
                    HeadIndex::Proj(type_name, n.to_usize().map_or(u64::MAX, |v| v as u64))
                }
                Node::Sort { .. } => HeadIndex::Sort,
                Node::Lam { .. } => HeadIndex::Lam,
                Node::Forall { .. } => HeadIndex::Forall,
                Node::LitNat { v } => HeadIndex::LitNat(v),
                Node::LitStr { v } => HeadIndex::LitStr(v),
                Node::App { f, .. } => {
                    e = f;
                    continue;
                }
                Node::MData { expr, .. } => {
                    e = expr;
                    continue;
                }
                Node::LetE { value, body, .. } => {
                    e = self.instantiate1(body, value)?;
                    continue;
                }
                Node::BVar { .. } | Node::BVarBig { .. } => {
                    return Err(MetaError::Infer(
                        "toHeadIndex: loose bound variable (oracle: panic)".into(),
                    ))
                }
            });
        }
    }
}
