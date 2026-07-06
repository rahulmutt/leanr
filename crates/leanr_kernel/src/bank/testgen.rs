//! Deterministic seed-based term/level generator shared by `bank`'s
//! differential property tests. `Rng`/`nm`/`gen_expr` are a mechanical
//! move from `bank/tests.rs` (Task 3 migration step 1 — every existing
//! call site there keeps producing the exact same seed -> term mapping,
//! see `gen_expr`'s doc comment below); the rest is new, added for
//! `bank/subst.rs`'s differential suite.

use crate::{BinderInfo, DataValue, Expr, KVMap, Level, Literal, Name, Nat, RecGuard};
use std::sync::Arc;

/// SplitMix64 — deterministic, dependency-free.
pub(crate) struct Rng(pub(crate) u64);

impl Rng {
    pub(crate) fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    pub(crate) fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

pub(crate) fn nm(s: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: s.to_string(),
    })
}

/// Random term over a tiny vocabulary; `depth` bounds recursion.
/// `allow_bvar` selects the depth-0 atom set: `true` reproduces
/// `bank/tests.rs`'s original generator bit-for-bit (same `below(5)`
/// branch order); `false` (see `gen_closed_expr`) drops the `BVar` atom
/// entirely so no generated term below can ever contain one, making the
/// whole result closed (`loose_bvar_range() == 0`) — needed for
/// substitution arguments in `bank/subst.rs`'s differential suite.
fn gen_expr_impl(r: &mut Rng, depth: u32, allow_bvar: bool, g: &mut RecGuard) -> Arc<Expr> {
    if depth == 0 {
        if allow_bvar {
            return match r.below(5) {
                0 => Expr::bvar(Nat::from(r.below(3))),
                1 => Expr::lit(Literal::NatVal(Nat::from(r.below(5)))),
                2 => Expr::const_(nm(["A", "B"][r.below(2) as usize]), vec![], g).unwrap(),
                3 => Expr::sort(Arc::new(Level::Succ(Arc::new(Level::Zero))), g).unwrap(),
                _ => Expr::fvar(nm(["fv1", "fv2"][r.below(2) as usize])),
            };
        }
        return match r.below(4) {
            0 => Expr::lit(Literal::NatVal(Nat::from(r.below(5)))),
            1 => Expr::const_(nm(["A", "B"][r.below(2) as usize]), vec![], g).unwrap(),
            2 => Expr::sort(Arc::new(Level::Succ(Arc::new(Level::Zero))), g).unwrap(),
            _ => Expr::fvar(nm(["fv1", "fv2"][r.below(2) as usize])),
        };
    }
    match r.below(6) {
        0 => Expr::app(
            gen_expr_impl(r, depth - 1, allow_bvar, g),
            gen_expr_impl(r, depth - 1, allow_bvar, g),
        ),
        1 => Expr::lam(
            nm(["x", "y"][r.below(2) as usize]),
            gen_expr_impl(r, depth - 1, allow_bvar, g),
            gen_expr_impl(r, depth - 1, allow_bvar, g),
            [BinderInfo::Default, BinderInfo::Implicit][r.below(2) as usize],
        ),
        2 => Expr::forall_e(
            nm("x"),
            gen_expr_impl(r, depth - 1, allow_bvar, g),
            gen_expr_impl(r, depth - 1, allow_bvar, g),
            BinderInfo::Default,
        ),
        3 => Expr::let_e(
            nm("z"),
            gen_expr_impl(r, depth - 1, allow_bvar, g),
            gen_expr_impl(r, depth - 1, allow_bvar, g),
            gen_expr_impl(r, depth - 1, allow_bvar, g),
            r.below(2) == 0,
        ),
        4 => Expr::proj(
            nm("S"),
            Nat::from(r.below(3)),
            gen_expr_impl(r, depth - 1, allow_bvar, g),
        ),
        _ => Expr::mdata(
            KVMap(vec![(nm("k"), DataValue::OfBool(r.below(2) == 0))]),
            gen_expr_impl(r, depth - 1, allow_bvar, g),
        ),
    }
}

/// The original `bank/tests.rs` generator (moved verbatim — behavior
/// unchanged, see `gen_expr_impl`'s doc comment).
pub(crate) fn gen_expr(r: &mut Rng, depth: u32, g: &mut RecGuard) -> Arc<Expr> {
    gen_expr_impl(r, depth, true, g)
}

/// `gen_expr`, but never emits a `BVar` node anywhere in the tree, so
/// the result is always closed — suitable as a substitution argument in
/// `bank/subst.rs`'s differential suite (`instantiate`/`instantiate_rev`
/// substitute terms into another term's loose-bvar slots; those
/// substituted terms don't need loose bvars of their own to exercise
/// the walkers being tested).
pub(crate) fn gen_closed_expr(r: &mut Rng, depth: u32, g: &mut RecGuard) -> Arc<Expr> {
    gen_expr_impl(r, depth, false, g)
}

/// Random level tree that may reference `params` (`Level::Param`) —
/// vocabulary for `expr_with_level_params` below. `depth` bounds
/// `Succ`/`Max`/`IMax` nesting the same way `gen_expr`'s `depth` bounds
/// terms.
fn gen_level(r: &mut Rng, params: &[Arc<Name>], depth: u32) -> Arc<Level> {
    if depth == 0 || r.below(3) == 0 {
        if !params.is_empty() && r.below(2) == 0 {
            let i = r.below(params.len() as u64) as usize;
            return Arc::new(Level::Param(Arc::clone(&params[i])));
        }
        return Arc::new(Level::Zero);
    }
    match r.below(3) {
        0 => Arc::new(Level::Succ(gen_level(r, params, depth - 1))),
        1 => Arc::new(Level::Max(
            gen_level(r, params, depth - 1),
            gen_level(r, params, depth - 1),
        )),
        _ => Arc::new(Level::IMax(
            gen_level(r, params, depth - 1),
            gen_level(r, params, depth - 1),
        )),
    }
}

/// `gen_expr`, but `Sort`/`Const` nodes carry `gen_level`-built levels
/// that may reference `params` — the vocabulary
/// `instantiate_level_params`'s differential test needs to exercise
/// substitution at all.
fn gen_expr_with_params(
    r: &mut Rng,
    depth: u32,
    params: &[Arc<Name>],
    g: &mut RecGuard,
) -> Arc<Expr> {
    if depth == 0 {
        return match r.below(5) {
            0 => Expr::bvar(Nat::from(r.below(3))),
            1 => Expr::lit(Literal::NatVal(Nat::from(r.below(5)))),
            2 => Expr::const_(
                nm(["A", "B"][r.below(2) as usize]),
                vec![gen_level(r, params, 2)],
                g,
            )
            .unwrap(),
            3 => Expr::sort(gen_level(r, params, 2), g).unwrap(),
            _ => Expr::fvar(nm(["fv1", "fv2"][r.below(2) as usize])),
        };
    }
    match r.below(6) {
        0 => Expr::app(
            gen_expr_with_params(r, depth - 1, params, g),
            gen_expr_with_params(r, depth - 1, params, g),
        ),
        1 => Expr::lam(
            nm(["x", "y"][r.below(2) as usize]),
            gen_expr_with_params(r, depth - 1, params, g),
            gen_expr_with_params(r, depth - 1, params, g),
            [BinderInfo::Default, BinderInfo::Implicit][r.below(2) as usize],
        ),
        2 => Expr::forall_e(
            nm("x"),
            gen_expr_with_params(r, depth - 1, params, g),
            gen_expr_with_params(r, depth - 1, params, g),
            BinderInfo::Default,
        ),
        3 => Expr::let_e(
            nm("z"),
            gen_expr_with_params(r, depth - 1, params, g),
            gen_expr_with_params(r, depth - 1, params, g),
            gen_expr_with_params(r, depth - 1, params, g),
            r.below(2) == 0,
        ),
        4 => Expr::proj(
            nm("S"),
            Nat::from(r.below(3)),
            gen_expr_with_params(r, depth - 1, params, g),
        ),
        _ => Expr::mdata(
            KVMap(vec![(nm("k"), DataValue::OfBool(r.below(2) == 0))]),
            gen_expr_with_params(r, depth - 1, params, g),
        ),
    }
}

// ---------------------------------------------------------------------
// Seed-keyed entry points for `bank/subst.rs`'s differential suite.
// Each is deterministic in `seed` alone.
// ---------------------------------------------------------------------

/// `(e, subst)`: a random term plus 1-3 CLOSED substitution terms —
/// vocabulary for `instantiate`/`instantiate_rev`.
pub(crate) fn expr_and_closed_subst(seed: u64) -> (Arc<Expr>, Vec<Arc<Expr>>) {
    let mut r = Rng(seed);
    let mut g = RecGuard::new();
    let e = gen_expr(&mut r, 4, &mut g);
    let n = 1 + r.below(3) as usize;
    let subst = (0..n).map(|_| gen_closed_expr(&mut r, 2, &mut g)).collect();
    (e, subst)
}

/// `(e, s, subst)`: same shape plus a random starting offset `s` — for
/// `instantiate_core`.
pub(crate) fn expr_and_offset_subst(seed: u64) -> (Arc<Expr>, u32, Vec<Arc<Expr>>) {
    let mut r = Rng(seed);
    let mut g = RecGuard::new();
    let e = gen_expr(&mut r, 4, &mut g);
    let s = r.below(3) as u32;
    let n = 1 + r.below(3) as usize;
    let subst = (0..n).map(|_| gen_closed_expr(&mut r, 2, &mut g)).collect();
    (e, s, subst)
}

/// `(e, s, d)` — for `lift_loose_bvars`.
pub(crate) fn expr_and_lift_args(seed: u64) -> (Arc<Expr>, u32, u32) {
    let mut r = Rng(seed);
    let mut g = RecGuard::new();
    let e = gen_expr(&mut r, 4, &mut g);
    let s = r.below(3) as u32;
    let d = r.below(4) as u32;
    (e, s, d)
}

/// `(e, fvars)` — for `abstract_fvars`. `fvars` is drawn from the same
/// `fv1`/`fv2`/`fv3` vocabulary `gen_expr`'s `FVar` atoms use, so
/// abstracting a real occurrence (not just an always-empty match) is
/// common.
pub(crate) fn expr_and_fvars(seed: u64) -> (Arc<Expr>, Vec<Arc<Expr>>) {
    let mut r = Rng(seed);
    let mut g = RecGuard::new();
    let e = gen_expr(&mut r, 4, &mut g);
    let candidates = [
        Expr::fvar(nm("fv1")),
        Expr::fvar(nm("fv2")),
        Expr::fvar(nm("fv3")),
    ];
    let n = r.below(4) as usize;
    let fvars = (0..n)
        .map(|_| Arc::clone(&candidates[r.below(3) as usize]))
        .collect();
    (e, fvars)
}

/// `(e, params, args)` — for `instantiate_level_params`: `e` may
/// contain `Sort`/`Const` nodes whose levels reference `params`.
pub(crate) fn expr_with_level_params(seed: u64) -> (Arc<Expr>, Vec<Arc<Name>>, Vec<Arc<Level>>) {
    let mut r = Rng(seed);
    let mut g = RecGuard::new();
    let params = vec![nm("u"), nm("v")];
    let args = vec![
        Arc::new(Level::Zero),
        Arc::new(Level::Succ(Arc::new(Level::Param(nm("w"))))),
    ];
    let e = gen_expr_with_params(&mut r, 4, &params, &mut g);
    (e, params, args)
}
