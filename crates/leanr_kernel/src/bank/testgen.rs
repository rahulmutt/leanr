//! Deterministic seed-based term generator shared by `bank`'s property
//! tests. `Rng`/`nm`/`gen_expr` are a mechanical move from
//! `bank/tests.rs` (Task 3 migration step 1 — every existing call site
//! there keeps producing the exact same seed -> term mapping, see
//! `gen_expr`'s doc comment below).
//!
//! Migration Task 8 removed the level/offset/fvar/closed-subst
//! generators (`gen_closed_expr`, `gen_level`, `gen_expr_with_params`,
//! `expr_and_closed_subst`, `expr_and_offset_subst`,
//! `expr_and_lift_args`, `expr_and_fvars`, `expr_with_level_params`)
//! that fed `bank/subst.rs`'s Arc-vs-id differential suite: that suite
//! compared against the Arc `subst.rs` kernel, which the flip deletes,
//! so both the suite and its now-orphaned generators went with it.

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
