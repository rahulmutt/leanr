//! Id-twin substitution walkers (the bank-native counterpart of
//! `crate::subst`; oracle: src/kernel/instantiate.cpp,
//! src/kernel/expr.cpp:448-466, src/kernel/abstract.cpp, at the pinned
//! githash — see `crate::subst`'s module doc / ARCHITECTURE.md for the
//! pin). `Arc<Expr>` -> `ExprId` via the phase-1 bank (spec:
//! docs/superpowers/specs/2026-07-06-compact-expr-term-bank-design.md).
//! Porting is representation-only: no algorithmic change from
//! `subst.rs`. Every oracle citation below is copied verbatim from the
//! Arc source.
//!
//! `instantiate_level_params`'s public signature takes `params: &[NameId]`/
//! `args: &[LevelId]` (ids throughout, matching every other bank-native
//! entry point — Task 4's TypeChecker call sites hold `Vec<NameId>` /
//! `LevelId` lists straight off `ConstantVal`/`Const` nodes). The ids are
//! loop-invariant across the traversal, so the entry point bridges each
//! one to `Arc<Name>`/`Arc<Level>` exactly once, up front, via
//! `to_name`/`to_level`; the traversal itself (`lparams_go`) still passes
//! those `Arc` slices down unchanged, because the substitution is
//! delegated to `Level::instantiate_params` (`crate::level`), which also
//! renormalizes (`mk_succ`/`mk_max_pair`/`mk_imax_pair`) — logic this
//! task's scope (one new file, the six `Expr`-tree walkers) does not
//! re-host in id space. Sort/Const level children bridge out via
//! `to_level`, get substituted through the already-proven Arc walker,
//! and bridge back in via `intern_level`.
//!
//! Recursion discipline (crate-wide invariant, see lib.rs/guard.rs): the
//! only sanctioned recursive descent is through `RecGuard::enter`.
//!
//! The oracle's `replace_fn.cpp` (its generic tree-rewrite helper that
//! every function below specializes) passes an `offset` counter to its
//! callback that starts at 0 and increments by exactly one crossing into
//! a `Lam`/`Forall`/`LetE` *body* (never for the binder's own type, nor
//! `LetE`'s value — both live in the outer scope, matching `combine_binder`/
//! `combine_let`'s own asymmetry, `crate::expr`). Every function below
//! threads that same `offset` explicitly.

use std::collections::HashMap;

use num_bigint::BigUint;

use super::local_ctx::LocalContext;
use super::terms::Node;
use super::{ExprId, LevelId, NameId, Store};
use crate::{KernelError, Level, Name, Nat, RecGuard};
use std::sync::Arc;

/// Per-top-level-call visit cache, the id-twin of `crate::subst`'s
/// `VisitCache`: `replace_rec_fn` memoizes every visited node keyed by
/// (pointer, offset) there (replace_fn.cpp:27-30); here the key is
/// `(ExprId, offset)` since ids ARE the node identity (the interning
/// invariant: equal ids <=> structurally equal terms, `bank/mod.rs`
/// module doc / `bank/tests.rs`). Without this memo, traversal work
/// (not output size, which the interner already dedups) is proportional
/// to the term's *tree* expansion rather than its DAG size — exponential
/// on maximally-shared terms (see `instantiate_deep_dag_is_linear_not_exponential`
/// below).
type VisitCache = HashMap<(ExprId, u32), ExprId>;

/// Exact `usize` extraction for a `BigUint` proven small elsewhere by
/// the caller (bounded by a real slice length) — never truncates via an
/// `as` cast; reports `KernelError::LooseBVar` on the should-be-
/// impossible case where that bound didn't hold, rather than panicking.
/// Verbatim port of `crate::subst::biguint_to_usize`.
fn biguint_to_usize(v: &BigUint) -> Result<usize, KernelError> {
    let digits = v.to_u64_digits();
    if digits.len() > 1 {
        return Err(KernelError::LooseBVar);
    }
    let d = digits.first().copied().unwrap_or(0);
    usize::try_from(d).map_err(|_| KernelError::LooseBVar)
}

/// Read a `BVar`/`BVarBig` row's raw index as a `Nat` (the `Node` split
/// between an inline `u32` and a pooled `NatId` is a storage-only detail
/// — every caller in this file just needs "the index as a `Nat`", same
/// as the Arc side's `idx: &Nat` field).
fn bvar_index_nat(st: &Store, base: Option<&Store>, node: Node) -> Nat {
    match node {
        Node::BVar { idx } => Nat::from(idx as u64),
        Node::BVarBig { idx } => st.nat_at(base, idx).clone(),
        _ => unreachable!("bvar_index_nat: caller already matched on BVar/BVarBig"),
    }
}

// ---------------------------------------------------------------------
// instantiate / instantiate_rev — oracle: instantiate.cpp:15-38 (forward)
// and :99-118 (reverse).
// ---------------------------------------------------------------------

/// oracle: instantiate.cpp:15-38 (`instantiate(expr const&, unsigned s,
/// unsigned n, expr const*)`). Replaces loose bvars `#s..#(s+subst.len())`
/// with `subst` (`subst[0]` replaces the OUTERMOST substituted slot,
/// i.e. `#(s+n-1)`; `subst[n-1]` replaces `#s`) — the oracle's own
/// indexing, `subst[vidx - s1]` (instantiate.cpp:29), pins this
/// convention exactly.
pub fn instantiate_core(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    s: u32,
    subst: &[ExprId],
    g: &mut RecGuard,
) -> Result<ExprId, KernelError> {
    // instantiate.cpp:16 (`n == 0` guard): an empty substitution list can
    // never change anything — short-circuit before touching the tree so
    // the caller gets the identical id back (sharing discipline).
    if subst.is_empty() {
        return Ok(e);
    }
    instantiate_go(st, base, e, s, 0, subst, false, g, &mut VisitCache::new())
}

/// oracle: instantiate.cpp:42 (`expr instantiate(expr const & e, expr
/// const & s) { return instantiate(e, 0, s); }`) — the common
/// single-substitution form.
pub fn instantiate(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    sub: ExprId,
    g: &mut RecGuard,
) -> Result<ExprId, KernelError> {
    instantiate_core(st, base, e, 0, std::slice::from_ref(&sub), g)
}

/// oracle: instantiate.cpp:99-118 (`instantiate_rev`) — `subst` given
/// innermost-first: `subst[subst.len()-1]` replaces `#0`, matching the
/// oracle's own index, `subst[n - (vidx - offset) - 1]`
/// (instantiate.cpp:110).
pub fn instantiate_rev(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    subst: &[ExprId],
    g: &mut RecGuard,
) -> Result<ExprId, KernelError> {
    // Same empty-list fast path as `instantiate_core`; see
    // `crate::subst::instantiate_rev`'s doc comment for why this is safe
    // (identical reasoning, `Arc`->id sharing swapped in).
    if subst.is_empty() {
        return Ok(e);
    }
    instantiate_go(st, base, e, 0, 0, subst, true, g, &mut VisitCache::new())
}

/// Shared walker for `instantiate_core`/`instantiate_rev` (oracle:
/// instantiate.cpp:15-38 and :99-118 are the same shape, differing only
/// in which end of `subst` index `n-1` maps to, selected by `rev`).
///
/// `s` is the caller's original threshold; `offset` is how many binders
/// *this call* has descended through so far (starts at 0, `+1` per
/// `Lam`/`ForallE`/`LetE` body — never for a type or `LetE`'s value).
/// Kept apart from `s` because a chosen substitution's own loose bvars
/// are lifted by `offset` ALONE (instantiate.cpp:29's
/// `lift_loose_bvars(subst[...], offset)`), never by the combined
/// `s + offset` — `s` only shifts which slice of bvar indices this call
/// targets, it is not extra binder depth to correct for.
#[allow(clippy::too_many_arguments)]
fn instantiate_go(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    s: u32,
    offset: u32,
    subst: &[ExprId],
    rev: bool,
    g: &mut RecGuard,
    cache: &mut VisitCache,
) -> Result<ExprId, KernelError> {
    // instantiate.cpp:19-21 (`s1 = s + offset; if (s1 < s) ...`): an
    // overflow past `u32::MAX` means no real vidx can be `>= s1`, so
    // there is nothing this call could do here — same as the oracle.
    let s1 = match s.checked_add(offset) {
        Some(v) => v,
        None => return Ok(e),
    };
    // instantiate.cpp:22-23 (and :62-63 for the `instantiate_rev`/core
    // variant): skip the whole subtree once its packed range proves no
    // loose bvar `>= s1` survives in it. Only trusted when the packed
    // word is *exact* (see `loose_bvar_range_exact`'s doc in expr.rs) —
    // a saturated word must never justify a skip.
    if let Some(range) = st.expr_data(base, e).loose_bvar_range_exact() {
        if (range as u64) <= (s1 as u64) {
            return Ok(e);
        }
    }
    // replace_fn.cpp:27-28 — visit-cache lookup (after the cheap skips,
    // which allocate nothing and would only bloat the cache).
    let key = (e, offset);
    if let Some(&r) = cache.get(&key) {
        return Ok(r);
    }
    let r = match st.expr_node(base, e) {
        node @ (Node::BVar { .. } | Node::BVarBig { .. }) => {
            let idx = bvar_index_nat(st, base, node);
            instantiate_bvar(st, base, e, &idx, s1, offset, subst, rev, g)?
        }
        // Atoms with no children and (per the intern-constructors in
        // terms.rs) an always-exact range of 0: the skip check above
        // already handles them whenever it applies. Kept as a
        // non-panicking fallback rather than `unreachable!()`, same
        // posture as the Arc side.
        Node::FVar { .. }
        | Node::MVar { .. }
        | Node::Sort { .. }
        | Node::Const { .. }
        | Node::LitNat { .. }
        | Node::LitStr { .. } => e,
        Node::App { f, arg } => {
            let (f2, arg2) = g.enter(|g| {
                Ok((
                    instantiate_go(st, base, f, s, offset, subst, rev, g, cache)?,
                    instantiate_go(st, base, arg, s, offset, subst, rev, g, cache)?,
                ))
            })?;
            if f2 == f && arg2 == arg {
                e
            } else {
                st.expr_app(base, f2, arg2)?
            }
        }
        Node::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    instantiate_go(st, base, binder_type, s, offset, subst, rev, g, cache)?,
                    instantiate_go(st, base, body, s, offset + 1, subst, rev, g, cache)?,
                ))
            })?;
            if bt2 == binder_type && bd2 == body {
                e
            } else {
                st.expr_lam(base, binder_name, bt2, bd2, binder_info)?
            }
        }
        Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    instantiate_go(st, base, binder_type, s, offset, subst, rev, g, cache)?,
                    instantiate_go(st, base, body, s, offset + 1, subst, rev, g, cache)?,
                ))
            })?;
            if bt2 == binder_type && bd2 == body {
                e
            } else {
                st.expr_forall(base, binder_name, bt2, bd2, binder_info)?
            }
        }
        Node::LetE {
            decl_name,
            ty,
            value,
            body,
            non_dep,
        } => {
            let (t2, v2, b2) = g.enter(|g| {
                Ok((
                    instantiate_go(st, base, ty, s, offset, subst, rev, g, cache)?,
                    instantiate_go(st, base, value, s, offset, subst, rev, g, cache)?,
                    instantiate_go(st, base, body, s, offset + 1, subst, rev, g, cache)?,
                ))
            })?;
            if t2 == ty && v2 == value && b2 == body {
                e
            } else {
                st.expr_let(base, decl_name, t2, v2, b2, non_dep)?
            }
        }
        Node::MData { data, expr } => {
            let expr2 =
                g.enter(|g| instantiate_go(st, base, expr, s, offset, subst, rev, g, cache))?;
            if expr2 == expr {
                e
            } else {
                st.expr_mdata(base, data, expr2)?
            }
        }
        node @ (Node::Proj { .. } | Node::ProjBig { .. }) => {
            let (type_name, structure) = match node {
                Node::Proj {
                    type_name,
                    structure,
                    ..
                }
                | Node::ProjBig {
                    type_name,
                    structure,
                    ..
                } => (type_name, structure),
                _ => unreachable!(),
            };
            let structure2 =
                g.enter(|g| instantiate_go(st, base, structure, s, offset, subst, rev, g, cache))?;
            if structure2 == structure {
                e
            } else {
                let idx_nat = match node {
                    Node::Proj { idx, .. } => Nat::from(idx as u64),
                    Node::ProjBig { idx, .. } => st.nat_at(base, idx).clone(),
                    _ => unreachable!(),
                };
                st.expr_proj(base, type_name, &idx_nat, structure2)?
            }
        }
    };
    // replace_fn.cpp:30 (`save_result`) — memoize this node's rewrite.
    cache.insert(key, r);
    Ok(r)
}

/// The `is_bvar(m)` branch shared by `instantiate_go`'s two callers
/// (instantiate.cpp:24-33 forward, :105-114 reverse). `idx` is the raw
/// (bignum) `Nat` index — compared exactly against `s1`/`h` via
/// `BigUint` arithmetic, never truncated through a packed `u32`, since a
/// term can carry an attacker-supplied loose bvar far beyond `u32`
/// range (only reachable when the packed range is saturated — see
/// `instantiate_go`'s skip check above, which never fires in that case,
/// so control can reach here with an arbitrarily large `idx`).
#[allow(clippy::too_many_arguments)]
fn instantiate_bvar(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    idx: &Nat,
    s1: u32,
    offset: u32,
    subst: &[ExprId],
    rev: bool,
    g: &mut RecGuard,
) -> Result<ExprId, KernelError> {
    let s1_big = BigUint::from(s1);
    if idx.0 < s1_big {
        // instantiate.cpp:26 (`vidx >= s1` guard failing): below the
        // substitution window — refers to an outer binder, untouched.
        return Ok(e);
    }
    let n = subst.len();
    let n_big = BigUint::from(n as u64);
    let h_big = &s1_big + &n_big;
    if idx.0 < h_big {
        // instantiate.cpp:28-29: within the window — pick the matching
        // substitution and lift ITS OWN loose bvars by `offset` (see
        // `instantiate_go`'s doc comment for why not `s1`).
        let rel_big = &idx.0 - &s1_big;
        let rel = biguint_to_usize(&rel_big)?;
        let sub_idx = if rev { n - 1 - rel } else { rel };
        let chosen = *subst.get(sub_idx).ok_or(KernelError::LooseBVar)?;
        lift_loose_bvars(st, base, chosen, 0, offset, g)
    } else {
        // instantiate.cpp:31: at/above the window — shift down by `n`
        // (exact bignum subtraction; `idx >= h = s1 + n >= n` so this
        // never underflows).
        let new_idx = &idx.0 - &n_big;
        st.expr_bvar(base, &Nat(new_idx))
    }
}

// ---------------------------------------------------------------------
// lift_loose_bvars — oracle: expr.cpp:448-460.
// ---------------------------------------------------------------------

/// oracle: expr.cpp:448-460 (`lift_loose_bvars(expr const&, unsigned s,
/// unsigned d)`). Lifts every loose bvar `>= s` by `d`.
pub fn lift_loose_bvars(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    s: u32,
    d: u32,
    g: &mut RecGuard,
) -> Result<ExprId, KernelError> {
    // expr.cpp:449 (`d == 0` guard): lifting by nothing is the identity;
    // preserves the id exactly like the oracle's early return.
    if d == 0 {
        return Ok(e);
    }
    lift_go(st, base, e, s, 0, d, g, &mut VisitCache::new())
}

/// `offset` tracks binder depth crossed by this call, same convention as
/// `instantiate_go` (oracle's `replace` callback argument); `s1 = s +
/// offset` is compared against the packed range exactly as
/// `instantiate_go` does (expr.cpp:452-455).
#[allow(clippy::too_many_arguments)]
fn lift_go(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    s: u32,
    offset: u32,
    d: u32,
    g: &mut RecGuard,
    cache: &mut VisitCache,
) -> Result<ExprId, KernelError> {
    let s1 = match s.checked_add(offset) {
        Some(v) => v,
        None => return Ok(e),
    };
    if let Some(range) = st.expr_data(base, e).loose_bvar_range_exact() {
        if (range as u64) <= (s1 as u64) {
            return Ok(e);
        }
    }
    // replace_fn.cpp:27-30 — visit cache (see `VisitCache`).
    let key = (e, offset);
    if let Some(&r) = cache.get(&key) {
        return Ok(r);
    }
    let r = match st.expr_node(base, e) {
        node @ (Node::BVar { .. } | Node::BVarBig { .. }) => {
            let idx = bvar_index_nat(st, base, node);
            let s1_big = BigUint::from(s1);
            if idx.0 >= s1_big {
                // expr.cpp:457-458: exact bignum add, never an `as` cast.
                let d_big = BigUint::from(d);
                st.expr_bvar(base, &Nat(&idx.0 + &d_big))?
            } else {
                e
            }
        }
        Node::FVar { .. }
        | Node::MVar { .. }
        | Node::Sort { .. }
        | Node::Const { .. }
        | Node::LitNat { .. }
        | Node::LitStr { .. } => e,
        Node::App { f, arg } => {
            let (f2, arg2) = g.enter(|g| {
                Ok((
                    lift_go(st, base, f, s, offset, d, g, cache)?,
                    lift_go(st, base, arg, s, offset, d, g, cache)?,
                ))
            })?;
            if f2 == f && arg2 == arg {
                e
            } else {
                st.expr_app(base, f2, arg2)?
            }
        }
        Node::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    lift_go(st, base, binder_type, s, offset, d, g, cache)?,
                    lift_go(st, base, body, s, offset + 1, d, g, cache)?,
                ))
            })?;
            if bt2 == binder_type && bd2 == body {
                e
            } else {
                st.expr_lam(base, binder_name, bt2, bd2, binder_info)?
            }
        }
        Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    lift_go(st, base, binder_type, s, offset, d, g, cache)?,
                    lift_go(st, base, body, s, offset + 1, d, g, cache)?,
                ))
            })?;
            if bt2 == binder_type && bd2 == body {
                e
            } else {
                st.expr_forall(base, binder_name, bt2, bd2, binder_info)?
            }
        }
        Node::LetE {
            decl_name,
            ty,
            value,
            body,
            non_dep,
        } => {
            let (t2, v2, b2) = g.enter(|g| {
                Ok((
                    lift_go(st, base, ty, s, offset, d, g, cache)?,
                    lift_go(st, base, value, s, offset, d, g, cache)?,
                    lift_go(st, base, body, s, offset + 1, d, g, cache)?,
                ))
            })?;
            if t2 == ty && v2 == value && b2 == body {
                e
            } else {
                st.expr_let(base, decl_name, t2, v2, b2, non_dep)?
            }
        }
        Node::MData { data, expr } => {
            let expr2 = g.enter(|g| lift_go(st, base, expr, s, offset, d, g, cache))?;
            if expr2 == expr {
                e
            } else {
                st.expr_mdata(base, data, expr2)?
            }
        }
        node @ (Node::Proj { .. } | Node::ProjBig { .. }) => {
            let (type_name, structure) = match node {
                Node::Proj {
                    type_name,
                    structure,
                    ..
                }
                | Node::ProjBig {
                    type_name,
                    structure,
                    ..
                } => (type_name, structure),
                _ => unreachable!(),
            };
            let structure2 = g.enter(|g| lift_go(st, base, structure, s, offset, d, g, cache))?;
            if structure2 == structure {
                e
            } else {
                let idx_nat = match node {
                    Node::Proj { idx, .. } => Nat::from(idx as u64),
                    Node::ProjBig { idx, .. } => st.nat_at(base, idx).clone(),
                    _ => unreachable!(),
                };
                st.expr_proj(base, type_name, &idx_nat, structure2)?
            }
        }
    };
    // replace_fn.cpp:30 (`save_result`) — memoize this node's rewrite.
    cache.insert(key, r);
    Ok(r)
}

// ---------------------------------------------------------------------
// abstract_fvars — oracle: abstract.cpp:12-27 (`abstract`).
// ---------------------------------------------------------------------

/// oracle: abstract.cpp:12-27 (`abstract(expr const&, unsigned n, expr
/// const* subst)`) — fvars (by id) become loose bvars. Innermost is the
/// LAST fvar in `fvars`: an id matching `fvars[i]` becomes
/// `bvar(offset + fvars.len() - i - 1)` (abstract.cpp:22,
/// `offset + n - i - 1`), and the scan below walks `fvars` from the end
/// backward exactly like the oracle's `while (i > 0) { --i; ... }` so a
/// duplicate id (if ever present) resolves to the same (last) entry.
pub fn abstract_fvars(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    fvars: &[ExprId],
    g: &mut RecGuard,
) -> Result<ExprId, KernelError> {
    if fvars.is_empty() || !st.expr_data(base, e).has_fvar() {
        return Ok(e);
    }
    abstract_go(st, base, e, 0, fvars, g, &mut VisitCache::new())
}

fn abstract_go(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    offset: u32,
    fvars: &[ExprId],
    g: &mut RecGuard,
    cache: &mut VisitCache,
) -> Result<ExprId, KernelError> {
    // abstract.cpp:18-19: per-node skip — `has_fvar` is an exact boolean
    // flag (no saturation concern, unlike `loose_bvar_range`), so this
    // check is always safe to trust.
    if !st.expr_data(base, e).has_fvar() {
        return Ok(e);
    }
    // replace_fn.cpp:27-30 — visit cache (see `VisitCache`).
    let key = (e, offset);
    if let Some(&r) = cache.get(&key) {
        return Ok(r);
    }
    let r = match st.expr_node(base, e) {
        Node::FVar { id } => {
            let n = fvars.len();
            let mut hit = None;
            for i in (0..n).rev() {
                if let Node::FVar { id: fid } = st.expr_node(base, fvars[i]) {
                    if fid == id {
                        let rel = (n as u64) - (i as u64) - 1;
                        let new_idx = (offset as u64)
                            .checked_add(rel)
                            .ok_or(KernelError::LooseBVar)?;
                        hit = Some(new_idx);
                        break;
                    }
                }
            }
            match hit {
                // abstract.cpp's FVar-hit case returns straight from the
                // rewrite (crate::subst's Arc `abstract_go`, subst.rs:546)
                // without going through `save_result` — match that
                // control flow exactly (verbatim-port constraint) rather
                // than falling through to this function's cache insert.
                Some(new_idx) => return st.expr_bvar(base, &Nat::from(new_idx)),
                None => e,
            }
        }
        // `has_fvar` is false for these atoms by construction (see
        // terms.rs's intern-constructors), so the skip check above
        // already covers them; kept as a non-panicking fallback.
        Node::BVar { .. }
        | Node::BVarBig { .. }
        | Node::MVar { .. }
        | Node::Sort { .. }
        | Node::Const { .. }
        | Node::LitNat { .. }
        | Node::LitStr { .. } => e,
        Node::App { f, arg } => {
            let (f2, arg2) = g.enter(|g| {
                Ok((
                    abstract_go(st, base, f, offset, fvars, g, cache)?,
                    abstract_go(st, base, arg, offset, fvars, g, cache)?,
                ))
            })?;
            if f2 == f && arg2 == arg {
                e
            } else {
                st.expr_app(base, f2, arg2)?
            }
        }
        Node::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    abstract_go(st, base, binder_type, offset, fvars, g, cache)?,
                    abstract_go(st, base, body, offset + 1, fvars, g, cache)?,
                ))
            })?;
            if bt2 == binder_type && bd2 == body {
                e
            } else {
                st.expr_lam(base, binder_name, bt2, bd2, binder_info)?
            }
        }
        Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    abstract_go(st, base, binder_type, offset, fvars, g, cache)?,
                    abstract_go(st, base, body, offset + 1, fvars, g, cache)?,
                ))
            })?;
            if bt2 == binder_type && bd2 == body {
                e
            } else {
                st.expr_forall(base, binder_name, bt2, bd2, binder_info)?
            }
        }
        Node::LetE {
            decl_name,
            ty,
            value,
            body,
            non_dep,
        } => {
            let (t2, v2, b2) = g.enter(|g| {
                Ok((
                    abstract_go(st, base, ty, offset, fvars, g, cache)?,
                    abstract_go(st, base, value, offset, fvars, g, cache)?,
                    abstract_go(st, base, body, offset + 1, fvars, g, cache)?,
                ))
            })?;
            if t2 == ty && v2 == value && b2 == body {
                e
            } else {
                st.expr_let(base, decl_name, t2, v2, b2, non_dep)?
            }
        }
        Node::MData { data, expr } => {
            let expr2 = g.enter(|g| abstract_go(st, base, expr, offset, fvars, g, cache))?;
            if expr2 == expr {
                e
            } else {
                st.expr_mdata(base, data, expr2)?
            }
        }
        node @ (Node::Proj { .. } | Node::ProjBig { .. }) => {
            let (type_name, structure) = match node {
                Node::Proj {
                    type_name,
                    structure,
                    ..
                }
                | Node::ProjBig {
                    type_name,
                    structure,
                    ..
                } => (type_name, structure),
                _ => unreachable!(),
            };
            let structure2 =
                g.enter(|g| abstract_go(st, base, structure, offset, fvars, g, cache))?;
            if structure2 == structure {
                e
            } else {
                let idx_nat = match node {
                    Node::Proj { idx, .. } => Nat::from(idx as u64),
                    Node::ProjBig { idx, .. } => st.nat_at(base, idx).clone(),
                    _ => unreachable!(),
                };
                st.expr_proj(base, type_name, &idx_nat, structure2)?
            }
        }
    };
    // replace_fn.cpp:30 (`save_result`) — memoize this node's rewrite.
    cache.insert(key, r);
    Ok(r)
}

// ---------------------------------------------------------------------
// instantiate_level_params — oracle: instantiate.cpp:232-246.
// ---------------------------------------------------------------------

/// oracle: instantiate.cpp:232-246 (`instantiate_lparams`). Rebuilds
/// `Sort`/`Const` levels via `Level::instantiate_params` (see this
/// module's doc comment for why the level substitution itself stays on
/// the Arc side), skipping subtrees with `!has_level_param()`. No
/// binder-depth bookkeeping is needed (level params are orthogonal to
/// bvar scope).
pub fn instantiate_level_params(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    params: &[NameId],
    args: &[LevelId],
    g: &mut RecGuard,
) -> Result<ExprId, KernelError> {
    // instantiate.cpp:233-234 (`!has_param_univ(e)` guard).
    if !st.expr_data(base, e).has_level_param() {
        return Ok(e);
    }
    // `params`/`args` are loop-invariant across the traversal below, so
    // bridge each id to its `Arc` form exactly once here rather than per
    // visited node (see this module's doc comment).
    let params: Vec<Arc<Name>> = params
        .iter()
        .map(|&id| st.to_name(base, Some(id)))
        .collect();
    let args: Vec<Arc<Level>> = args.iter().map(|&id| st.to_level(base, id)).collect();
    lparams_go(st, base, e, &params, &args, g, &mut VisitCache::new())
}

fn lparams_go(
    st: &mut Store,
    base: Option<&Store>,
    e: ExprId,
    params: &[Arc<Name>],
    args: &[Arc<Level>],
    g: &mut RecGuard,
    cache: &mut VisitCache,
) -> Result<ExprId, KernelError> {
    // instantiate.cpp:236-237: per-node skip, exact boolean flag.
    if !st.expr_data(base, e).has_level_param() {
        return Ok(e);
    }
    // replace_fn.cpp:27-30 — visit cache (see `VisitCache`). Level-param
    // substitution is offset-independent (no bvar bookkeeping), so the
    // key's offset component is fixed at 0 (mirroring the oracle's
    // pointer-only `replace_fn` cache, replace_fn.cpp:79-84).
    let key = (e, 0u32);
    if let Some(&r) = cache.get(&key) {
        return Ok(r);
    }
    let r = match st.expr_node(base, e) {
        // instantiate.cpp:240-241 (`is_sort(e)` branch).
        Node::Sort { level } => {
            let al = st.to_level(base, level);
            let al2 = Level::instantiate_params(&al, params, args, g)?;
            if Arc::ptr_eq(&al2, &al) {
                e
            } else {
                let level2 = st.intern_level(base, &al2)?;
                st.expr_sort(base, level2)?
            }
        }
        // instantiate.cpp:238-239 (`is_constant(e)` branch, `map_reuse`
        // over `const_levels`).
        Node::Const { name, levels } => {
            let level_ids: Vec<LevelId> = st.level_list_at(base, levels).to_vec();
            let mut changed = false;
            let mut out = Vec::with_capacity(level_ids.len());
            for lid in level_ids {
                let al = st.to_level(base, lid);
                let al2 = Level::instantiate_params(&al, params, args, g)?;
                let lid2 = if Arc::ptr_eq(&al2, &al) {
                    lid
                } else {
                    changed = true;
                    st.intern_level(base, &al2)?
                };
                out.push(lid2);
            }
            if changed {
                let ls = st.intern_level_list(base, &out)?;
                st.expr_const(base, name, ls)?
            } else {
                e
            }
        }
        // `has_level_param` is false for these atoms by construction;
        // the skip check above already covers them (non-panicking
        // fallback, same rationale as elsewhere in this file).
        Node::BVar { .. }
        | Node::BVarBig { .. }
        | Node::FVar { .. }
        | Node::MVar { .. }
        | Node::LitNat { .. }
        | Node::LitStr { .. } => e,
        Node::App { f, arg } => {
            let (f2, arg2) = g.enter(|g| {
                Ok((
                    lparams_go(st, base, f, params, args, g, cache)?,
                    lparams_go(st, base, arg, params, args, g, cache)?,
                ))
            })?;
            if f2 == f && arg2 == arg {
                e
            } else {
                st.expr_app(base, f2, arg2)?
            }
        }
        Node::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    lparams_go(st, base, binder_type, params, args, g, cache)?,
                    lparams_go(st, base, body, params, args, g, cache)?,
                ))
            })?;
            if bt2 == binder_type && bd2 == body {
                e
            } else {
                st.expr_lam(base, binder_name, bt2, bd2, binder_info)?
            }
        }
        Node::Forall {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    lparams_go(st, base, binder_type, params, args, g, cache)?,
                    lparams_go(st, base, body, params, args, g, cache)?,
                ))
            })?;
            if bt2 == binder_type && bd2 == body {
                e
            } else {
                st.expr_forall(base, binder_name, bt2, bd2, binder_info)?
            }
        }
        Node::LetE {
            decl_name,
            ty,
            value,
            body,
            non_dep,
        } => {
            let (t2, v2, b2) = g.enter(|g| {
                Ok((
                    lparams_go(st, base, ty, params, args, g, cache)?,
                    lparams_go(st, base, value, params, args, g, cache)?,
                    lparams_go(st, base, body, params, args, g, cache)?,
                ))
            })?;
            if t2 == ty && v2 == value && b2 == body {
                e
            } else {
                st.expr_let(base, decl_name, t2, v2, b2, non_dep)?
            }
        }
        Node::MData { data, expr } => {
            let expr2 = g.enter(|g| lparams_go(st, base, expr, params, args, g, cache))?;
            if expr2 == expr {
                e
            } else {
                st.expr_mdata(base, data, expr2)?
            }
        }
        node @ (Node::Proj { .. } | Node::ProjBig { .. }) => {
            let (type_name, structure) = match node {
                Node::Proj {
                    type_name,
                    structure,
                    ..
                }
                | Node::ProjBig {
                    type_name,
                    structure,
                    ..
                } => (type_name, structure),
                _ => unreachable!(),
            };
            let structure2 =
                g.enter(|g| lparams_go(st, base, structure, params, args, g, cache))?;
            if structure2 == structure {
                e
            } else {
                let idx_nat = match node {
                    Node::Proj { idx, .. } => Nat::from(idx as u64),
                    Node::ProjBig { idx, .. } => st.nat_at(base, idx).clone(),
                    _ => unreachable!(),
                };
                st.expr_proj(base, type_name, &idx_nat, structure2)?
            }
        }
    };
    // replace_fn.cpp:30 (`save_result`) — memoize this node's rewrite.
    cache.insert(key, r);
    Ok(r)
}

// ---------------------------------------------------------------------
// mk_pi / mk_lambda — oracle: local_ctx.h:94-99 / local_ctx.cpp:93-121
// (`local_ctx::mk_binding`). These land HERE rather than in
// `bank/local_ctx.rs` because they call `abstract_fvars` above (Task 2's
// Consumes note; confirmed against the Arc side, `crate::local_ctx.rs:
// 181-249`). Free functions taking `&LocalContext` (not methods), per
// the brief: `bank/local_ctx.rs`'s `LocalContext` was already closed out
// in Task 2 without them. A `g: &mut RecGuard` parameter is added beyond
// the brief's illustrative signature (which omitted it) because
// `abstract_fvars` needs one — the brief explicitly sanctions this kind
// of correction for `instantiate_core`'s own signature ("if it takes an
// offset or RecGuard, keep it"), and the Arc `mk_pi`/`mk_lambda`
// (`local_ctx.rs:181-199`) both take one too.
// ---------------------------------------------------------------------

/// Id-twin of the Arc port's own `LocalContext::decl_for` helper
/// (`crate::local_ctx.rs:169-176` — not an oracle citation; the oracle
/// has no equivalent named helper, it's inlined into `mk_binding`,
/// local_ctx.cpp:93-115) — look up the declaration for a telescope
/// entry, or panic. Not an untrusted-input path: see the Arc module's
/// doc comment (`crate::local_ctx` module docs) for the two-layer
/// invariant (kernel-internal `fvars` provenance +
/// `check_no_metavar_no_fvar` admission gate) that makes a mismatched
/// entry a kernel-internal contract violation, not attacker input.
fn decl_for<'a>(
    st: &Store,
    base: Option<&Store>,
    lctx: &'a LocalContext,
    fvar: ExprId,
) -> &'a super::local_ctx::LocalDecl {
    match st.expr_node(base, fvar) {
        Node::FVar { id: Some(id) } => lctx
            .get(id)
            .unwrap_or_else(|| panic!("mk_pi/mk_lambda: fvar not declared in this context")),
        _ => panic!("mk_pi/mk_lambda: fvars entry is not an Expr::fvar"),
    }
}

/// oracle: local_ctx.h:94-99 / local_ctx.cpp:93-121
/// (`mk_binding<is_lambda=false>` via the `mk_pi` wrapper) — rebuild a
/// Π-telescope over `fvars` around `e`.
pub fn mk_pi(
    st: &mut Store,
    base: Option<&Store>,
    lctx: &LocalContext,
    fvars: &[ExprId],
    e: ExprId,
    g: &mut RecGuard,
) -> Result<ExprId, KernelError> {
    mk_binding(st, base, lctx, fvars, e, false, g)
}

/// oracle: local_ctx.h:94-99 / local_ctx.cpp:93-121
/// (`mk_binding<is_lambda=true>` via the `mk_lambda` wrapper).
pub fn mk_lambda(
    st: &mut Store,
    base: Option<&Store>,
    lctx: &LocalContext,
    fvars: &[ExprId],
    e: ExprId,
    g: &mut RecGuard,
) -> Result<ExprId, KernelError> {
    mk_binding(st, base, lctx, fvars, e, true, g)
}

/// oracle: local_ctx.cpp:93-115 (`local_ctx::mk_binding`). Same
/// fold-right-to-left shape as the Arc port
/// (`crate::local_ctx::LocalContext::mk_binding`'s doc comment explains
/// why abstracting the body one fvar at a time, as the fold reaches it,
/// is equivalent to the oracle's single upfront `abstract(b, num,
/// fvars)` — that argument carries over unchanged here since
/// `abstract_fvars`'s offset bookkeeping is identical).
///
/// `non_dep` is always `false` for the rebuilt `LetE`, matching the
/// oracle (local_ctx.cpp:107's 4-arg `mk_let` defaults `nondep = false`
/// — `mk_binding` never computes a real `non_dep` bit).
fn mk_binding(
    st: &mut Store,
    base: Option<&Store>,
    lctx: &LocalContext,
    fvars: &[ExprId],
    e: ExprId,
    is_lambda: bool,
    g: &mut RecGuard,
) -> Result<ExprId, KernelError> {
    let mut r = e;
    let mut i = fvars.len();
    while i > 0 {
        i -= 1;
        r = abstract_fvars(st, base, r, std::slice::from_ref(&fvars[i]), g)?;
        let decl = decl_for(st, base, lctx, fvars[i]);
        let (ty, binder_name, binder_info, value) =
            (decl.ty, decl.binder_name, decl.binder_info, decl.value);
        let ty2 = abstract_fvars(st, base, ty, &fvars[..i], g)?;
        r = if let Some(value) = value {
            let value2 = abstract_fvars(st, base, value, &fvars[..i], g)?;
            st.expr_let(base, binder_name, ty2, value2, r, false)?
        } else if is_lambda {
            st.expr_lam(base, binder_name, ty2, r, binder_info)?
        } else {
            st.expr_forall(base, binder_name, ty2, r, binder_info)?
        };
    }
    Ok(r)
}

#[cfg(test)]
mod tests {
    use super::super::local_ctx::{FVarIdGen, LocalContext};
    use super::super::terms::Node;
    use super::super::testgen;
    use super::*;
    use crate::bank::Store;
    use crate::testenv::g;
    use crate::{BinderInfo, Level, Name, Nat, RecGuard};
    use std::sync::Arc;

    fn nm(s: &str) -> Arc<Name> {
        Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: s.to_string(),
        })
    }

    // ------------------------------------------------------------------
    // Ported Arc `subst.rs` inline unit tests (same mapping as Task 2:
    // `Arc<Expr>` constructors -> `st.expr_*` intern-constructors,
    // `Arc::ptr_eq`/`ExprNode` matches -> `ExprId` equality/`Node`
    // matches — the interning invariant makes id equality the exact
    // id-space analog of Arc pointer equality for "was this rewritten").
    // ------------------------------------------------------------------

    #[test]
    fn instantiate_hits_only_index_zero_at_top() {
        let mut g = RecGuard::new();
        let mut st = Store::persistent();
        // (#0 #1)[x] = (x #0) — #1 shifts down to #0
        let b0 = st.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let b1 = st.expr_bvar(None, &Nat::from(1u64)).unwrap();
        let e = st.expr_app(None, b0, b1).unwrap();
        let x = st.expr_lit_nat(None, &Nat::from(7u64)).unwrap();
        let r = instantiate(&mut st, None, e, x, &mut g).unwrap();
        let Node::App { f, arg } = st.expr_node(None, r) else {
            panic!()
        };
        assert_eq!(f, x);
        assert_eq!(arg, b0);
    }

    #[test]
    fn instantiate_shifts_under_binders() {
        let mut g = RecGuard::new();
        let mut st = Store::persistent();
        // (λ x, #1)[y] = λ x, y — the #1 refers past the λ to the substituted slot
        let lit0 = st.expr_lit_nat(None, &Nat::from(0u64)).unwrap();
        let b1 = st.expr_bvar(None, &Nat::from(1u64)).unwrap();
        let e = st
            .expr_lam(None, None, lit0, b1, BinderInfo::Default)
            .unwrap();
        let lit7 = st.expr_lit_nat(None, &Nat::from(7u64)).unwrap();
        let r = instantiate(&mut st, None, e, lit7, &mut g).unwrap();
        let Node::Lam { body, .. } = st.expr_node(None, r) else {
            panic!()
        };
        assert_eq!(body, lit7);
        // and the substituted term's own loose bvars are lifted:
        // (λ x, #1)[#0] = λ x, #1
        let b0 = st.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let r2 = instantiate(&mut st, None, e, b0, &mut g).unwrap();
        let Node::Lam { body: body2, .. } = st.expr_node(None, r2) else {
            panic!()
        };
        assert_eq!(body2, b1);
    }

    #[test]
    fn closed_subtrees_are_shared_not_copied() {
        let mut g = RecGuard::new();
        let mut st = Store::persistent();
        let l1 = st.expr_lit_nat(None, &Nat::from(1u64)).unwrap();
        let l2 = st.expr_lit_nat(None, &Nat::from(2u64)).unwrap();
        let closed = st.expr_app(None, l1, l2).unwrap();
        let b0 = st.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let e = st.expr_app(None, closed, b0).unwrap();
        let l9 = st.expr_lit_nat(None, &Nat::from(9u64)).unwrap();
        let r = instantiate(&mut st, None, e, l9, &mut g).unwrap();
        let Node::App { f, .. } = st.expr_node(None, r) else {
            panic!()
        };
        assert_eq!(f, closed); // the whole point of looseBVarRange
    }

    #[test]
    fn abstract_then_instantiate_roundtrips() {
        let mut g = RecGuard::new();
        let mut st = Store::persistent();
        let h = st.intern_name(None, &nm("h")).unwrap();
        let fv = st.expr_fvar(None, h).unwrap();
        let l3 = st.expr_lit_nat(None, &Nat::from(3u64)).unwrap();
        let e = st.expr_app(None, fv, l3).unwrap();
        let abs = abstract_fvars(&mut st, None, e, &[fv], &mut g).unwrap();
        assert_eq!(st.expr_data(None, abs).loose_bvar_range(), 1);
        assert!(!st.expr_data(None, abs).has_fvar());
        let back = instantiate(&mut st, None, abs, fv, &mut g).unwrap();
        assert_eq!(back, e);
    }

    #[test]
    fn instantiate_rev_order_matches_oracle() {
        let mut g = RecGuard::new();
        let mut st = Store::persistent();
        // instantiate_rev: subst[len-1] replaces #0 (innermost-last).
        let b0 = st.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let b1 = st.expr_bvar(None, &Nat::from(1u64)).unwrap();
        let e = st.expr_app(None, b0, b1).unwrap();
        let l10 = st.expr_lit_nat(None, &Nat::from(10u64)).unwrap();
        let l20 = st.expr_lit_nat(None, &Nat::from(20u64)).unwrap();
        let r = instantiate_rev(&mut st, None, e, &[l10, l20], &mut g).unwrap();
        let Node::App { f, arg } = st.expr_node(None, r) else {
            panic!()
        };
        assert_eq!(f, l20);
        assert_eq!(arg, l10);
    }

    // ------------------------------------------------------------------
    // Sharing preservation (oracle: kernel/replace_fn.cpp:27-30 — the
    // (pointer, offset)-keyed visit cache in `replace_rec_fn`, here
    // `(ExprId, offset)`). NOTE: unlike the Arc side (where a distinct
    // `Arc` allocation is the observable failure mode), the interning
    // invariant means a *correct* rewrite of a shared subterm always
    // lands on the same id whether or not the memo fires — these single-
    // level tests below assert that invariant, not memo use per se.
    // `instantiate_deep_dag_is_linear_not_exponential` (further down) is
    // the test that actually exercises the memo: without it, the walk
    // itself (not the output) tree-expands, and the test times out.
    // ------------------------------------------------------------------

    #[test]
    fn instantiate_preserves_dag_sharing() {
        let mut g = RecGuard::new();
        let mut st = Store::persistent();
        let b0 = st.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let l1 = st.expr_lit_nat(None, &Nat::from(1u64)).unwrap();
        let x = st.expr_app(None, b0, l1).unwrap();
        let e = st.expr_app(None, x, x).unwrap();
        let l7 = st.expr_lit_nat(None, &Nat::from(7u64)).unwrap();
        let r = instantiate(&mut st, None, e, l7, &mut g).unwrap();
        let Node::App { f, arg } = st.expr_node(None, r) else {
            panic!()
        };
        assert_eq!(
            f, arg,
            "instantiate must rewrite a shared subterm to a single id, not two"
        );
    }

    #[test]
    fn abstract_preserves_dag_sharing() {
        let mut g = RecGuard::new();
        let mut st = Store::persistent();
        let h = st.intern_name(None, &nm("h")).unwrap();
        let fv = st.expr_fvar(None, h).unwrap();
        let l1 = st.expr_lit_nat(None, &Nat::from(1u64)).unwrap();
        let x = st.expr_app(None, fv, l1).unwrap();
        let e = st.expr_app(None, x, x).unwrap();
        let r = abstract_fvars(&mut st, None, e, &[fv], &mut g).unwrap();
        let Node::App { f, arg } = st.expr_node(None, r) else {
            panic!()
        };
        assert_eq!(
            f, arg,
            "abstract_fvars must rewrite a shared subterm to a single id, not two"
        );
    }

    #[test]
    fn instantiate_deep_dag_is_linear_not_exponential() {
        let mut g = RecGuard::new();
        let mut st = Store::persistent();
        // 64 levels of App(x, x) doubling over a loose bvar: a 64-node
        // DAG whose tree expansion is ~2^64 (id, offset) visits without
        // the memo. Only a memoized traversal can finish this promptly.
        let mut x = st.expr_bvar(None, &Nat::from(0u64)).unwrap();
        for _ in 0..64 {
            x = st.expr_app(None, x, x).unwrap();
        }
        let l7 = st.expr_lit_nat(None, &Nat::from(7u64)).unwrap();
        let r = instantiate(&mut st, None, x, l7, &mut g).unwrap();
        assert_eq!(st.expr_data(None, r).loose_bvar_range(), 0);
    }

    #[test]
    fn lift_preserves_dag_sharing() {
        let mut g = RecGuard::new();
        let mut st = Store::persistent();
        let b0 = st.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let l1 = st.expr_lit_nat(None, &Nat::from(1u64)).unwrap();
        let x = st.expr_app(None, b0, l1).unwrap();
        let e = st.expr_app(None, x, x).unwrap();
        let r = lift_loose_bvars(&mut st, None, e, 0, 1, &mut g).unwrap();
        let Node::App { f, arg } = st.expr_node(None, r) else {
            panic!()
        };
        assert_eq!(
            f, arg,
            "lift_loose_bvars must rewrite a shared subterm to a single id, not two"
        );
    }

    #[test]
    fn level_params_preserve_dag_sharing() {
        let mut g = RecGuard::new();
        let mut st = Store::persistent();
        let u = nm("u");
        let lu = st
            .intern_level(None, &Arc::new(Level::Param(Arc::clone(&u))))
            .unwrap();
        let f_name = st.intern_name(None, &nm("f")).unwrap();
        let levels = st.intern_level_list(None, &[lu]).unwrap();
        let c = st.expr_const(None, f_name, levels).unwrap();
        let l1 = st.expr_lit_nat(None, &Nat::from(1u64)).unwrap();
        let x = st.expr_app(None, c, l1).unwrap();
        let e = st.expr_app(None, x, x).unwrap();
        let u_id = st.intern_name(None, &u).unwrap().unwrap();
        let zero_id = st.intern_level(None, &Arc::new(Level::Zero)).unwrap();
        let r = instantiate_level_params(&mut st, None, e, &[u_id], &[zero_id], &mut g).unwrap();
        let Node::App { f, arg } = st.expr_node(None, r) else {
            panic!()
        };
        assert_eq!(
            f, arg,
            "instantiate_level_params must rewrite a shared subterm to a single id, not two"
        );
    }

    #[test]
    fn level_params_substitute_in_const_and_sort() {
        let mut g = RecGuard::new();
        let mut st = Store::persistent();
        let u = nm("u");
        let lu = st
            .intern_level(None, &Arc::new(Level::Param(Arc::clone(&u))))
            .unwrap();
        let f_name = st.intern_name(None, &nm("f")).unwrap();
        let levels = st.intern_level_list(None, &[lu]).unwrap();
        let c = st.expr_const(None, f_name, levels).unwrap();
        let u_id = st.intern_name(None, &u).unwrap().unwrap();
        let zero_id = st.intern_level(None, &Arc::new(Level::Zero)).unwrap();
        let r = instantiate_level_params(&mut st, None, c, &[u_id], &[zero_id], &mut g).unwrap();
        let Node::Const {
            levels: levels2, ..
        } = st.expr_node(None, r)
        else {
            panic!()
        };
        let level_ids = st.level_list_at(None, levels2);
        assert_eq!(level_ids.len(), 1);
        match st.level_row(None, level_ids[0]) {
            super::super::levels::LevelRow::Zero => {}
            other => panic!("expected Zero, got {other:?}"),
        }
        assert!(!st.expr_data(None, r).has_level_param());
    }

    // ------------------------------------------------------------------
    // `mk_pi`/`mk_lambda` — port of the Arc `local_ctx.rs` telescope
    // test, since these two functions land in THIS file (module doc
    // above).
    // ------------------------------------------------------------------

    #[test]
    fn mk_pi_roundtrips_a_telescope() {
        let mut g = RecGuard::new();
        let mut st = Store::persistent();
        let mut lctx = LocalContext::default();
        let mut fgen = FVarIdGen::default();
        let no_levels = st.intern_level_list(None, &[]).unwrap();
        let nat_name = st.intern_name(None, &nm("Nat")).unwrap();
        let nat = st.expr_const(None, nat_name, no_levels).unwrap();
        // x : Nat, y : Vec x (dependent-type stand-in)
        let x = lctx
            .mk_local_decl(&mut st, None, &mut fgen, None, nat, BinderInfo::Default)
            .unwrap();
        let vec_name = st.intern_name(None, &nm("Vec")).unwrap();
        let vec_ctor = st.expr_const(None, vec_name, no_levels).unwrap();
        let vec_x = st.expr_app(None, vec_ctor, x).unwrap();
        let y = lctx
            .mk_local_decl(&mut st, None, &mut fgen, None, vec_x, BinderInfo::Implicit)
            .unwrap();
        let body = st.expr_app(None, y, x).unwrap();
        let pi = mk_pi(&mut st, None, &lctx, &[x, y], body, &mut g).unwrap();
        // Result must be closed and shaped Π (x : Nat), Π {y : Vec #0}, #0 #1
        assert_eq!(st.expr_data(None, pi).loose_bvar_range(), 0);
        assert!(!st.expr_data(None, pi).has_fvar());
        let Node::Forall {
            binder_type,
            body: inner,
            ..
        } = st.expr_node(None, pi)
        else {
            panic!()
        };
        assert_eq!(binder_type, nat);
        let Node::Forall {
            binder_info,
            binder_type: bt2,
            body: b2,
            ..
        } = st.expr_node(None, inner)
        else {
            panic!()
        };
        assert_eq!(binder_info, BinderInfo::Implicit);
        assert_eq!(st.expr_data(None, bt2).loose_bvar_range(), 1); // Vec #0
        assert_eq!(st.expr_data(None, b2).loose_bvar_range(), 2); // #0 #1
    }

    // ------------------------------------------------------------------
    // Differential property suite (the task's real gate): drive the
    // SAME operation through both representations and bridge-compare,
    // 500 seeds per op, via `bank::testgen`.
    // ------------------------------------------------------------------

    #[test]
    fn instantiate_matches_arc_kernel() {
        for seed in 0u64..500 {
            let (arc_e, arc_subst) = testgen::expr_and_closed_subst(seed);
            let mut st = Store::scratch();
            let base = Store::persistent();
            let e = st.intern_expr(Some(&base), &arc_e).unwrap();
            let sub_id = st.intern_expr(Some(&base), &arc_subst[0]).unwrap();
            let got = super::instantiate(&mut st, Some(&base), e, sub_id, &mut g()).unwrap();
            let want = crate::instantiate(&arc_e, &arc_subst[0], &mut g()).unwrap();
            let got_arc = st.to_expr(Some(&base), got, &mut g()).unwrap();
            assert!(
                crate::Expr::structural_eq(&got_arc, &want, &mut g()).unwrap(),
                "seed {seed}"
            );
        }
    }

    #[test]
    fn instantiate_rev_matches_arc_kernel() {
        for seed in 0u64..500 {
            let (arc_e, arc_subst) = testgen::expr_and_closed_subst(seed);
            let mut st = Store::scratch();
            let base = Store::persistent();
            let e = st.intern_expr(Some(&base), &arc_e).unwrap();
            let subst: Vec<_> = arc_subst
                .iter()
                .map(|t| st.intern_expr(Some(&base), t).unwrap())
                .collect();
            let got = super::instantiate_rev(&mut st, Some(&base), e, &subst, &mut g()).unwrap();
            let want = crate::instantiate_rev(&arc_e, &arc_subst, &mut g()).unwrap();
            let got_arc = st.to_expr(Some(&base), got, &mut g()).unwrap();
            assert!(
                crate::Expr::structural_eq(&got_arc, &want, &mut g()).unwrap(),
                "seed {seed}"
            );
        }
    }

    #[test]
    fn instantiate_core_matches_arc_kernel() {
        for seed in 0u64..500 {
            let (arc_e, s, arc_subst) = testgen::expr_and_offset_subst(seed);
            let mut st = Store::scratch();
            let base = Store::persistent();
            let e = st.intern_expr(Some(&base), &arc_e).unwrap();
            let subst: Vec<_> = arc_subst
                .iter()
                .map(|t| st.intern_expr(Some(&base), t).unwrap())
                .collect();
            let got =
                super::instantiate_core(&mut st, Some(&base), e, s, &subst, &mut g()).unwrap();
            let want = crate::instantiate_core(&arc_e, s, &arc_subst, &mut g()).unwrap();
            let got_arc = st.to_expr(Some(&base), got, &mut g()).unwrap();
            assert!(
                crate::Expr::structural_eq(&got_arc, &want, &mut g()).unwrap(),
                "seed {seed}"
            );
        }
    }

    #[test]
    fn lift_loose_bvars_matches_arc_kernel() {
        for seed in 0u64..500 {
            let (arc_e, s, d) = testgen::expr_and_lift_args(seed);
            let mut st = Store::scratch();
            let base = Store::persistent();
            let e = st.intern_expr(Some(&base), &arc_e).unwrap();
            let got = super::lift_loose_bvars(&mut st, Some(&base), e, s, d, &mut g()).unwrap();
            let want = crate::lift_loose_bvars(&arc_e, s, d, &mut g()).unwrap();
            let got_arc = st.to_expr(Some(&base), got, &mut g()).unwrap();
            assert!(
                crate::Expr::structural_eq(&got_arc, &want, &mut g()).unwrap(),
                "seed {seed}"
            );
        }
    }

    #[test]
    fn abstract_fvars_matches_arc_kernel() {
        for seed in 0u64..500 {
            let (arc_e, arc_fvars) = testgen::expr_and_fvars(seed);
            let mut st = Store::scratch();
            let base = Store::persistent();
            let e = st.intern_expr(Some(&base), &arc_e).unwrap();
            let fvars: Vec<_> = arc_fvars
                .iter()
                .map(|f| st.intern_expr(Some(&base), f).unwrap())
                .collect();
            let got = super::abstract_fvars(&mut st, Some(&base), e, &fvars, &mut g()).unwrap();
            let want = crate::abstract_fvars(&arc_e, &arc_fvars, &mut g()).unwrap();
            let got_arc = st.to_expr(Some(&base), got, &mut g()).unwrap();
            assert!(
                crate::Expr::structural_eq(&got_arc, &want, &mut g()).unwrap(),
                "seed {seed}"
            );
        }
    }

    #[test]
    fn instantiate_level_params_matches_arc_kernel() {
        for seed in 0u64..500 {
            let (arc_e, params, args) = testgen::expr_with_level_params(seed);
            let mut st = Store::scratch();
            let base = Store::persistent();
            let e = st.intern_expr(Some(&base), &arc_e).unwrap();
            let param_ids: Vec<_> = params
                .iter()
                .map(|p| st.intern_name(Some(&base), p).unwrap().unwrap())
                .collect();
            let arg_ids: Vec<_> = args
                .iter()
                .map(|a| st.intern_level(Some(&base), a).unwrap())
                .collect();
            let got = super::instantiate_level_params(
                &mut st,
                Some(&base),
                e,
                &param_ids,
                &arg_ids,
                &mut g(),
            )
            .unwrap();
            let want = crate::instantiate_level_params(&arc_e, &params, &args, &mut g()).unwrap();
            let got_arc = st.to_expr(Some(&base), got, &mut g()).unwrap();
            assert!(
                crate::Expr::structural_eq(&got_arc, &want, &mut g()).unwrap(),
                "seed {seed}"
            );
        }
    }
}
