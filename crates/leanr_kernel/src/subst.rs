//! Substitution: `instantiate`/`instantiate_rev` (replace loose bvars
//! with terms), `lift_loose_bvars` (shift loose bvars up), `abstract_fvars`
//! (turn fvars into loose bvars), and `instantiate_level_params` (level
//! param substitution walking `Sort`/`Const`).
//!
//! Oracle: src/kernel/instantiate.cpp, src/kernel/expr.cpp:448-466,
//! src/kernel/abstract.cpp, at the pinned githash (see expr.rs/level.rs
//! module docs). Every port below cites its oracle line range.
//!
//! Recursion discipline (crate-wide invariant, see lib.rs/guard.rs): the
//! only sanctioned recursive descent is through `RecGuard::enter`.
//!
//! The oracle's `replace_fn.cpp` (its generic tree-rewrite helper that
//! every function below specializes) passes a `offset` counter to its
//! callback that starts at 0 and increments by exactly one crossing into
//! a `Lam`/`ForallE`/`LetE` *body* (never for the binder's own type, nor
//! `LetE`'s value — both live in the outer scope, matching `ExprData`'s
//! own `combine_binder`/`combine_let` asymmetry in expr.rs). Every
//! function below threads that same `offset` explicitly since Rust has
//! no closure-capturing tree-rewrite helper to hide it behind.
use std::sync::Arc;

use num_bigint::BigUint;

use crate::{Expr, ExprNode, KernelError, Level, Name, Nat, RecGuard};

/// Exact `usize` extraction for a `BigUint` proven small elsewhere by
/// the caller (bounded by a real slice length) — never truncates via an
/// `as` cast; reports `KernelError::LooseBVar` on the should-be-
/// impossible case where that bound didn't hold, rather than panicking
/// (the task brief's "checked/exact bignum arithmetic ... no panic on
/// untrusted input" discipline). Mirrors `nat_lossy_u64` in expr.rs but
/// is exact (not lossy) since every call site here has already checked
/// the value fits.
fn biguint_to_usize(v: &BigUint) -> Result<usize, KernelError> {
    let digits = v.to_u64_digits();
    if digits.len() > 1 {
        return Err(KernelError::LooseBVar);
    }
    let d = digits.first().copied().unwrap_or(0);
    usize::try_from(d).map_err(|_| KernelError::LooseBVar)
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
    e: &Arc<Expr>,
    s: u32,
    subst: &[Arc<Expr>],
    g: &mut RecGuard,
) -> Result<Arc<Expr>, KernelError> {
    // instantiate.cpp:16 (`n == 0` guard): an empty substitution list can
    // never change anything — short-circuit before touching the tree so
    // the caller gets the identical `Arc` back (sharing discipline).
    if subst.is_empty() {
        return Ok(Arc::clone(e));
    }
    instantiate_go(e, s, 0, subst, false, g)
}

/// oracle: instantiate.cpp:42 (`expr instantiate(expr const & e, expr
/// const & s) { return instantiate(e, 0, s); }`) — the common
/// single-substitution form.
pub fn instantiate(
    e: &Arc<Expr>,
    sub: &Arc<Expr>,
    g: &mut RecGuard,
) -> Result<Arc<Expr>, KernelError> {
    instantiate_core(e, 0, std::slice::from_ref(sub), g)
}

/// oracle: instantiate.cpp:99-118 (`instantiate_rev`) — `subst` given
/// innermost-first: `subst[subst.len()-1]` replaces `#0`, matching the
/// oracle's own index, `subst[n - (vidx - offset) - 1]`
/// (instantiate.cpp:110).
pub fn instantiate_rev(
    e: &Arc<Expr>,
    subst: &[Arc<Expr>],
    g: &mut RecGuard,
) -> Result<Arc<Expr>, KernelError> {
    // Same empty-list fast path as `instantiate_core`; the oracle's own
    // `instantiate_rev` has no explicit `n == 0` guard (only
    // `has_loose_bvars`), but with `n == 0` its per-node closure would
    // rebuild every bvar it touches via `mk_bvar(vidx - nat(0))` — same
    // value, fresh allocation. Skipping up front instead preserves
    // sharing without changing the result.
    if subst.is_empty() {
        return Ok(Arc::clone(e));
    }
    instantiate_go(e, 0, 0, subst, true, g)
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
fn instantiate_go(
    e: &Arc<Expr>,
    s: u32,
    offset: u32,
    subst: &[Arc<Expr>],
    rev: bool,
    g: &mut RecGuard,
) -> Result<Arc<Expr>, KernelError> {
    // instantiate.cpp:19-21 (`s1 = s + offset; if (s1 < s) ...`): an
    // overflow past `u32::MAX` means no real vidx can be `>= s1`, so
    // there is nothing this call could do here — same as the oracle.
    let s1 = match s.checked_add(offset) {
        Some(v) => v,
        None => return Ok(Arc::clone(e)),
    };
    // instantiate.cpp:22-23 (and :62-63 for the `instantiate_rev`/core
    // variant): skip the whole subtree once its packed range proves no
    // loose bvar `>= s1` survives in it. Only trusted when the packed
    // word is *exact* (see `ExprData::loose_bvar_range_exact`'s doc in
    // expr.rs) — a saturated word must never justify a skip.
    if let Some(range) = e.data().loose_bvar_range_exact() {
        if (range as u64) <= (s1 as u64) {
            return Ok(Arc::clone(e));
        }
    }
    match e.node() {
        ExprNode::BVar { idx } => instantiate_bvar(e, idx, s1, offset, subst, rev, g),
        // Atoms with no children and (per the smart constructors in
        // expr.rs) an always-exact range of 0: the skip check above
        // already handles them whenever it applies. Kept as a
        // non-panicking fallback rather than `unreachable!()` since the
        // match is keyed off already-decoded (if internally-produced)
        // data, per the crate's discipline (see e.g.
        // `Level::instantiate_params`'s Zero/MVar arm).
        ExprNode::FVar { .. }
        | ExprNode::MVar { .. }
        | ExprNode::Sort { .. }
        | ExprNode::Const { .. }
        | ExprNode::Lit(_) => Ok(Arc::clone(e)),
        ExprNode::App { f, arg } => {
            let (f, arg) = (Arc::clone(f), Arc::clone(arg));
            let (f2, arg2) = g.enter(|g| {
                Ok((
                    instantiate_go(&f, s, offset, subst, rev, g)?,
                    instantiate_go(&arg, s, offset, subst, rev, g)?,
                ))
            })?;
            if Arc::ptr_eq(&f2, &f) && Arc::ptr_eq(&arg2, &arg) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::app(f2, arg2))
            }
        }
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bn, bi) = (Arc::clone(binder_name), *binder_info);
            let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    instantiate_go(&bt, s, offset, subst, rev, g)?,
                    instantiate_go(&bd, s, offset + 1, subst, rev, g)?,
                ))
            })?;
            if Arc::ptr_eq(&bt2, &bt) && Arc::ptr_eq(&bd2, &bd) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::lam(bn, bt2, bd2, bi))
            }
        }
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bn, bi) = (Arc::clone(binder_name), *binder_info);
            let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    instantiate_go(&bt, s, offset, subst, rev, g)?,
                    instantiate_go(&bd, s, offset + 1, subst, rev, g)?,
                ))
            })?;
            if Arc::ptr_eq(&bt2, &bt) && Arc::ptr_eq(&bd2, &bd) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::forall_e(bn, bt2, bd2, bi))
            }
        }
        ExprNode::LetE {
            decl_name,
            ty,
            value,
            body,
            non_dep,
        } => {
            let dn = Arc::clone(decl_name);
            let nd = *non_dep;
            let (t, v, b) = (Arc::clone(ty), Arc::clone(value), Arc::clone(body));
            let (t2, v2, b2) = g.enter(|g| {
                Ok((
                    instantiate_go(&t, s, offset, subst, rev, g)?,
                    instantiate_go(&v, s, offset, subst, rev, g)?,
                    instantiate_go(&b, s, offset + 1, subst, rev, g)?,
                ))
            })?;
            if Arc::ptr_eq(&t2, &t) && Arc::ptr_eq(&v2, &v) && Arc::ptr_eq(&b2, &b) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::let_e(dn, t2, v2, b2, nd))
            }
        }
        ExprNode::MData { data, expr } => {
            let inner = Arc::clone(expr);
            let inner2 = g.enter(|g| instantiate_go(&inner, s, offset, subst, rev, g))?;
            if Arc::ptr_eq(&inner2, &inner) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::mdata(data.clone(), inner2))
            }
        }
        ExprNode::Proj {
            type_name,
            idx,
            structure,
        } => {
            let (tn, ix) = (Arc::clone(type_name), idx.clone());
            let st = Arc::clone(structure);
            let st2 = g.enter(|g| instantiate_go(&st, s, offset, subst, rev, g))?;
            if Arc::ptr_eq(&st2, &st) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::proj(tn, ix, st2))
            }
        }
    }
}

/// The `is_bvar(m)` branch shared by `instantiate_go`'s two callers
/// (instantiate.cpp:24-33 forward, :105-114 reverse). `idx` is the raw
/// (bignum) `Nat` index — compared exactly against `s1`/`h` via
/// `BigUint` arithmetic, never truncated through a packed `u32`, since a
/// term can carry an attacker-supplied loose bvar far beyond `u32`
/// range (only reachable when the packed range is saturated — see
/// `instantiate_go`'s skip check above, which never fires in that case,
/// so control can reach here with an arbitrarily large `idx`).
fn instantiate_bvar(
    e: &Arc<Expr>,
    idx: &Nat,
    s1: u32,
    offset: u32,
    subst: &[Arc<Expr>],
    rev: bool,
    g: &mut RecGuard,
) -> Result<Arc<Expr>, KernelError> {
    let s1_big = BigUint::from(s1);
    if idx.0 < s1_big {
        // instantiate.cpp:26 (`vidx >= s1` guard failing): below the
        // substitution window — refers to an outer binder, untouched.
        return Ok(Arc::clone(e));
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
        let chosen = subst.get(sub_idx).ok_or(KernelError::LooseBVar)?;
        lift_loose_bvars(chosen, 0, offset, g)
    } else {
        // instantiate.cpp:31: at/above the window — shift down by `n`
        // (exact bignum subtraction; `idx >= h = s1 + n >= n` so this
        // never underflows).
        let new_idx = &idx.0 - &n_big;
        Ok(Expr::bvar(Nat(new_idx)))
    }
}

// ---------------------------------------------------------------------
// lift_loose_bvars — oracle: expr.cpp:448-460.
// ---------------------------------------------------------------------

/// oracle: expr.cpp:448-460 (`lift_loose_bvars(expr const&, unsigned s,
/// unsigned d)`). Lifts every loose bvar `>= s` by `d`.
pub fn lift_loose_bvars(
    e: &Arc<Expr>,
    s: u32,
    d: u32,
    g: &mut RecGuard,
) -> Result<Arc<Expr>, KernelError> {
    // expr.cpp:449 (`d == 0` guard): lifting by nothing is the identity;
    // preserves the `Arc` exactly like the oracle's early return.
    if d == 0 {
        return Ok(Arc::clone(e));
    }
    lift_go(e, s, 0, d, g)
}

/// `offset` tracks binder depth crossed by this call, same convention as
/// `instantiate_go` (oracle's `replace` callback argument); `s1 = s +
/// offset` is compared against the packed range exactly as
/// `instantiate_go` does (expr.cpp:452-455).
fn lift_go(
    e: &Arc<Expr>,
    s: u32,
    offset: u32,
    d: u32,
    g: &mut RecGuard,
) -> Result<Arc<Expr>, KernelError> {
    let s1 = match s.checked_add(offset) {
        Some(v) => v,
        None => return Ok(Arc::clone(e)),
    };
    if let Some(range) = e.data().loose_bvar_range_exact() {
        if (range as u64) <= (s1 as u64) {
            return Ok(Arc::clone(e));
        }
    }
    match e.node() {
        ExprNode::BVar { idx } => {
            let s1_big = BigUint::from(s1);
            if idx.0 >= s1_big {
                // expr.cpp:457-458: exact bignum add, never an `as` cast.
                let d_big = BigUint::from(d);
                Ok(Expr::bvar(Nat(&idx.0 + &d_big)))
            } else {
                Ok(Arc::clone(e))
            }
        }
        ExprNode::FVar { .. }
        | ExprNode::MVar { .. }
        | ExprNode::Sort { .. }
        | ExprNode::Const { .. }
        | ExprNode::Lit(_) => Ok(Arc::clone(e)),
        ExprNode::App { f, arg } => {
            let (f, arg) = (Arc::clone(f), Arc::clone(arg));
            let (f2, arg2) = g.enter(|g| {
                Ok((
                    lift_go(&f, s, offset, d, g)?,
                    lift_go(&arg, s, offset, d, g)?,
                ))
            })?;
            if Arc::ptr_eq(&f2, &f) && Arc::ptr_eq(&arg2, &arg) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::app(f2, arg2))
            }
        }
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bn, bi) = (Arc::clone(binder_name), *binder_info);
            let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    lift_go(&bt, s, offset, d, g)?,
                    lift_go(&bd, s, offset + 1, d, g)?,
                ))
            })?;
            if Arc::ptr_eq(&bt2, &bt) && Arc::ptr_eq(&bd2, &bd) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::lam(bn, bt2, bd2, bi))
            }
        }
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bn, bi) = (Arc::clone(binder_name), *binder_info);
            let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    lift_go(&bt, s, offset, d, g)?,
                    lift_go(&bd, s, offset + 1, d, g)?,
                ))
            })?;
            if Arc::ptr_eq(&bt2, &bt) && Arc::ptr_eq(&bd2, &bd) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::forall_e(bn, bt2, bd2, bi))
            }
        }
        ExprNode::LetE {
            decl_name,
            ty,
            value,
            body,
            non_dep,
        } => {
            let dn = Arc::clone(decl_name);
            let nd = *non_dep;
            let (t, v, b) = (Arc::clone(ty), Arc::clone(value), Arc::clone(body));
            let (t2, v2, b2) = g.enter(|g| {
                Ok((
                    lift_go(&t, s, offset, d, g)?,
                    lift_go(&v, s, offset, d, g)?,
                    lift_go(&b, s, offset + 1, d, g)?,
                ))
            })?;
            if Arc::ptr_eq(&t2, &t) && Arc::ptr_eq(&v2, &v) && Arc::ptr_eq(&b2, &b) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::let_e(dn, t2, v2, b2, nd))
            }
        }
        ExprNode::MData { data, expr } => {
            let inner = Arc::clone(expr);
            let inner2 = g.enter(|g| lift_go(&inner, s, offset, d, g))?;
            if Arc::ptr_eq(&inner2, &inner) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::mdata(data.clone(), inner2))
            }
        }
        ExprNode::Proj {
            type_name,
            idx,
            structure,
        } => {
            let (tn, ix) = (Arc::clone(type_name), idx.clone());
            let st = Arc::clone(structure);
            let st2 = g.enter(|g| lift_go(&st, s, offset, d, g))?;
            if Arc::ptr_eq(&st2, &st) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::proj(tn, ix, st2))
            }
        }
    }
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
    e: &Arc<Expr>,
    fvars: &[Arc<Expr>],
    g: &mut RecGuard,
) -> Result<Arc<Expr>, KernelError> {
    if fvars.is_empty() || !e.data().has_fvar() {
        return Ok(Arc::clone(e));
    }
    abstract_go(e, 0, fvars, g)
}

fn abstract_go(
    e: &Arc<Expr>,
    offset: u32,
    fvars: &[Arc<Expr>],
    g: &mut RecGuard,
) -> Result<Arc<Expr>, KernelError> {
    // abstract.cpp:18-19: per-node skip — `has_fvar` is an exact boolean
    // flag (no saturation concern, unlike `loose_bvar_range`), so this
    // check is always safe to trust.
    if !e.data().has_fvar() {
        return Ok(Arc::clone(e));
    }
    match e.node() {
        ExprNode::FVar { id } => {
            let n = fvars.len();
            for i in (0..n).rev() {
                if let ExprNode::FVar { id: fid } = fvars[i].node() {
                    if fid == id {
                        let rel = (n as u64) - (i as u64) - 1;
                        let new_idx = (offset as u64)
                            .checked_add(rel)
                            .ok_or(KernelError::LooseBVar)?;
                        return Ok(Expr::bvar(Nat::from(new_idx)));
                    }
                }
            }
            Ok(Arc::clone(e))
        }
        // `has_fvar` is false for these atoms by construction (see
        // expr.rs smart constructors), so the skip check above already
        // covers them; kept as a non-panicking fallback.
        ExprNode::BVar { .. }
        | ExprNode::MVar { .. }
        | ExprNode::Sort { .. }
        | ExprNode::Const { .. }
        | ExprNode::Lit(_) => Ok(Arc::clone(e)),
        ExprNode::App { f, arg } => {
            let (f, arg) = (Arc::clone(f), Arc::clone(arg));
            let (f2, arg2) = g.enter(|g| {
                Ok((
                    abstract_go(&f, offset, fvars, g)?,
                    abstract_go(&arg, offset, fvars, g)?,
                ))
            })?;
            if Arc::ptr_eq(&f2, &f) && Arc::ptr_eq(&arg2, &arg) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::app(f2, arg2))
            }
        }
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bn, bi) = (Arc::clone(binder_name), *binder_info);
            let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    abstract_go(&bt, offset, fvars, g)?,
                    abstract_go(&bd, offset + 1, fvars, g)?,
                ))
            })?;
            if Arc::ptr_eq(&bt2, &bt) && Arc::ptr_eq(&bd2, &bd) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::lam(bn, bt2, bd2, bi))
            }
        }
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bn, bi) = (Arc::clone(binder_name), *binder_info);
            let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    abstract_go(&bt, offset, fvars, g)?,
                    abstract_go(&bd, offset + 1, fvars, g)?,
                ))
            })?;
            if Arc::ptr_eq(&bt2, &bt) && Arc::ptr_eq(&bd2, &bd) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::forall_e(bn, bt2, bd2, bi))
            }
        }
        ExprNode::LetE {
            decl_name,
            ty,
            value,
            body,
            non_dep,
        } => {
            let dn = Arc::clone(decl_name);
            let nd = *non_dep;
            let (t, v, b) = (Arc::clone(ty), Arc::clone(value), Arc::clone(body));
            let (t2, v2, b2) = g.enter(|g| {
                Ok((
                    abstract_go(&t, offset, fvars, g)?,
                    abstract_go(&v, offset, fvars, g)?,
                    abstract_go(&b, offset + 1, fvars, g)?,
                ))
            })?;
            if Arc::ptr_eq(&t2, &t) && Arc::ptr_eq(&v2, &v) && Arc::ptr_eq(&b2, &b) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::let_e(dn, t2, v2, b2, nd))
            }
        }
        ExprNode::MData { data, expr } => {
            let inner = Arc::clone(expr);
            let inner2 = g.enter(|g| abstract_go(&inner, offset, fvars, g))?;
            if Arc::ptr_eq(&inner2, &inner) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::mdata(data.clone(), inner2))
            }
        }
        ExprNode::Proj {
            type_name,
            idx,
            structure,
        } => {
            let (tn, ix) = (Arc::clone(type_name), idx.clone());
            let st = Arc::clone(structure);
            let st2 = g.enter(|g| abstract_go(&st, offset, fvars, g))?;
            if Arc::ptr_eq(&st2, &st) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::proj(tn, ix, st2))
            }
        }
    }
}

// ---------------------------------------------------------------------
// instantiate_level_params — oracle: instantiate.cpp:232-246.
// ---------------------------------------------------------------------

/// oracle: instantiate.cpp:232-246 (`instantiate_lparams`). Rebuilds
/// `Sort`/`Const` levels via `Level::instantiate_params`, skipping
/// subtrees with `!has_level_param()`. No binder-depth bookkeeping is
/// needed (level params are orthogonal to bvar scope).
pub fn instantiate_level_params(
    e: &Arc<Expr>,
    params: &[Arc<Name>],
    args: &[Arc<Level>],
    g: &mut RecGuard,
) -> Result<Arc<Expr>, KernelError> {
    // instantiate.cpp:233-234 (`!has_param_univ(e)` guard).
    if !e.data().has_level_param() {
        return Ok(Arc::clone(e));
    }
    lparams_go(e, params, args, g)
}

fn lparams_go(
    e: &Arc<Expr>,
    params: &[Arc<Name>],
    args: &[Arc<Level>],
    g: &mut RecGuard,
) -> Result<Arc<Expr>, KernelError> {
    // instantiate.cpp:236-237: per-node skip, exact boolean flag.
    if !e.data().has_level_param() {
        return Ok(Arc::clone(e));
    }
    match e.node() {
        // instantiate.cpp:240-241 (`is_sort(e)` branch).
        ExprNode::Sort { level } => {
            let l = Arc::clone(level);
            let l2 = Level::instantiate_params(&l, params, args, g)?;
            if Arc::ptr_eq(&l2, &l) {
                Ok(Arc::clone(e))
            } else {
                Expr::sort(l2, g)
            }
        }
        // instantiate.cpp:238-239 (`is_constant(e)` branch, `map_reuse`
        // over `const_levels`).
        ExprNode::Const { name, levels } => {
            let nm = Arc::clone(name);
            let mut changed = false;
            let mut out = Vec::with_capacity(levels.len());
            for l in levels {
                let l2 = Level::instantiate_params(l, params, args, g)?;
                if !Arc::ptr_eq(&l2, l) {
                    changed = true;
                }
                out.push(l2);
            }
            if changed {
                Expr::const_(nm, out, g)
            } else {
                Ok(Arc::clone(e))
            }
        }
        // `has_level_param` is false for these atoms by construction;
        // the skip check above already covers them (non-panicking
        // fallback, same rationale as elsewhere in this file).
        ExprNode::BVar { .. }
        | ExprNode::FVar { .. }
        | ExprNode::MVar { .. }
        | ExprNode::Lit(_) => Ok(Arc::clone(e)),
        ExprNode::App { f, arg } => {
            let (f, arg) = (Arc::clone(f), Arc::clone(arg));
            let (f2, arg2) = g.enter(|g| {
                Ok((
                    lparams_go(&f, params, args, g)?,
                    lparams_go(&arg, params, args, g)?,
                ))
            })?;
            if Arc::ptr_eq(&f2, &f) && Arc::ptr_eq(&arg2, &arg) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::app(f2, arg2))
            }
        }
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bn, bi) = (Arc::clone(binder_name), *binder_info);
            let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    lparams_go(&bt, params, args, g)?,
                    lparams_go(&bd, params, args, g)?,
                ))
            })?;
            if Arc::ptr_eq(&bt2, &bt) && Arc::ptr_eq(&bd2, &bd) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::lam(bn, bt2, bd2, bi))
            }
        }
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => {
            let (bn, bi) = (Arc::clone(binder_name), *binder_info);
            let (bt, bd) = (Arc::clone(binder_type), Arc::clone(body));
            let (bt2, bd2) = g.enter(|g| {
                Ok((
                    lparams_go(&bt, params, args, g)?,
                    lparams_go(&bd, params, args, g)?,
                ))
            })?;
            if Arc::ptr_eq(&bt2, &bt) && Arc::ptr_eq(&bd2, &bd) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::forall_e(bn, bt2, bd2, bi))
            }
        }
        ExprNode::LetE {
            decl_name,
            ty,
            value,
            body,
            non_dep,
        } => {
            let dn = Arc::clone(decl_name);
            let nd = *non_dep;
            let (t, v, b) = (Arc::clone(ty), Arc::clone(value), Arc::clone(body));
            let (t2, v2, b2) = g.enter(|g| {
                Ok((
                    lparams_go(&t, params, args, g)?,
                    lparams_go(&v, params, args, g)?,
                    lparams_go(&b, params, args, g)?,
                ))
            })?;
            if Arc::ptr_eq(&t2, &t) && Arc::ptr_eq(&v2, &v) && Arc::ptr_eq(&b2, &b) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::let_e(dn, t2, v2, b2, nd))
            }
        }
        ExprNode::MData { data, expr } => {
            let inner = Arc::clone(expr);
            let inner2 = g.enter(|g| lparams_go(&inner, params, args, g))?;
            if Arc::ptr_eq(&inner2, &inner) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::mdata(data.clone(), inner2))
            }
        }
        ExprNode::Proj {
            type_name,
            idx,
            structure,
        } => {
            let (tn, ix) = (Arc::clone(type_name), idx.clone());
            let st = Arc::clone(structure);
            let st2 = g.enter(|g| lparams_go(&st, params, args, g))?;
            if Arc::ptr_eq(&st2, &st) {
                Ok(Arc::clone(e))
            } else {
                Ok(Expr::proj(tn, ix, st2))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BinderInfo, Expr, ExprNode, Literal, Name, Nat, RecGuard};
    use std::sync::Arc;

    // `Name::from_str` doesn't exist (see name.rs / Tasks 2 & 3's own
    // test helpers): build a single-component name with an `Anonymous`
    // parent by hand instead.
    fn nm(s: &str) -> Arc<Name> {
        Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: s.to_string(),
        })
    }
    fn bv(i: u64) -> Arc<Expr> {
        Expr::bvar(Nat::from(i))
    }
    fn lit(i: u64) -> Arc<Expr> {
        Expr::lit(Literal::NatVal(Nat::from(i)))
    }

    #[test]
    fn instantiate_hits_only_index_zero_at_top() {
        let mut g = RecGuard::new();
        // (#0 #1)[x] = (x #0)  — #1 shifts down to #0
        let e = Expr::app(bv(0), bv(1));
        let r = instantiate(&e, &lit(7), &mut g).unwrap();
        let ExprNode::App { f, arg } = r.node() else {
            panic!()
        };
        assert!(Expr::structural_eq(f, &lit(7), &mut g).unwrap());
        assert!(Expr::structural_eq(arg, &bv(0), &mut g).unwrap());
    }

    #[test]
    fn instantiate_shifts_under_binders() {
        let mut g = RecGuard::new();
        // (λ x, #1)[y] = λ x, y   (the #1 refers past the λ to the substituted slot)
        let e = Expr::lam(nm("x"), lit(0), bv(1), BinderInfo::Default);
        let r = instantiate(&e, &lit(7), &mut g).unwrap();
        let ExprNode::Lam { body, .. } = r.node() else {
            panic!()
        };
        assert!(Expr::structural_eq(body, &lit(7), &mut g).unwrap());
        // and the substituted term's own loose bvars are lifted:
        // (λ x, #1)[#0] = λ x, #1
        let r2 = instantiate(&e, &bv(0), &mut g).unwrap();
        let ExprNode::Lam { body, .. } = r2.node() else {
            panic!()
        };
        assert!(Expr::structural_eq(body, &bv(1), &mut g).unwrap());
    }

    #[test]
    fn closed_subtrees_are_shared_not_copied() {
        let mut g = RecGuard::new();
        let closed = Expr::app(lit(1), lit(2));
        let e = Expr::app(Arc::clone(&closed), bv(0));
        let r = instantiate(&e, &lit(9), &mut g).unwrap();
        let ExprNode::App { f, .. } = r.node() else {
            panic!()
        };
        assert!(Arc::ptr_eq(f, &closed)); // the whole point of looseBVarRange
    }

    #[test]
    fn abstract_then_instantiate_roundtrips() {
        let mut g = RecGuard::new();
        let fv = Expr::fvar(nm("h"));
        let e = Expr::app(Arc::clone(&fv), lit(3));
        let abs = abstract_fvars(&e, &[Arc::clone(&fv)], &mut g).unwrap();
        assert_eq!(abs.data().loose_bvar_range(), 1);
        assert!(!abs.data().has_fvar());
        let back = instantiate(&abs, &fv, &mut g).unwrap();
        assert!(Expr::structural_eq(&back, &e, &mut g).unwrap());
    }

    #[test]
    fn instantiate_rev_order_matches_oracle() {
        let mut g = RecGuard::new();
        // instantiate_rev: subst[len-1] replaces #0 (innermost-last).
        let e = Expr::app(bv(0), bv(1));
        let r = instantiate_rev(&e, &[lit(10), lit(20)], &mut g).unwrap();
        let ExprNode::App { f, arg } = r.node() else {
            panic!()
        };
        assert!(Expr::structural_eq(f, &lit(20), &mut g).unwrap());
        assert!(Expr::structural_eq(arg, &lit(10), &mut g).unwrap());
    }

    #[test]
    fn level_params_substitute_in_const_and_sort() {
        let mut g = RecGuard::new();
        let u = nm("u");
        let c = Expr::const_(
            nm("f"),
            vec![Arc::new(crate::Level::Param(Arc::clone(&u)))],
            &mut g,
        )
        .unwrap();
        let r =
            instantiate_level_params(&c, &[u], &[Arc::new(crate::Level::Zero)], &mut g).unwrap();
        let ExprNode::Const { levels, .. } = r.node() else {
            panic!()
        };
        assert!(levels[0].is_zero());
        assert!(!r.data().has_level_param());
    }
}
