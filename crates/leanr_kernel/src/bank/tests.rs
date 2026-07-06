//! Bank-level unit tests plus differential property tests for the
//! interning invariant (spec §1): equal ids ⇔ `Expr::structural_eq`.
//! The existing `Arc<Expr>` representation is the oracle.

use super::*;
use crate::{BinderInfo, Expr, Level, Literal, Name, Nat, RecGuard};
use std::sync::Arc;

#[test]
fn id_roundtrips_index_and_region() {
    let p = ExprId::from_index(0, false).unwrap();
    assert_eq!(p.index(), 0);
    assert!(!p.is_scratch());
    let s = ExprId::from_index(12345, true).unwrap();
    assert_eq!(s.index(), 12345);
    assert!(s.is_scratch());
    assert_eq!(ExprId::from_bits(s.bits()), Some(s));
}

#[test]
fn id_max_index_is_bounded() {
    assert!(ExprId::from_index(MAX_INDEX, false).is_some());
    assert!(ExprId::from_index(MAX_INDEX + 1, false).is_none());
}

#[test]
fn zero_bits_is_no_id() {
    assert_eq!(ExprId::from_bits(0), None);
}

#[test]
fn region_bit_alone_is_no_id() {
    // REGION_BIT set but the low 31 bits are all zero: `index()` would
    // underflow on this value, so `from_bits` must reject it just like
    // it rejects 0.
    assert_eq!(ExprId::from_bits(REGION_BIT), None);
}

#[test]
fn from_bits_round_trips_valid_bits() {
    let p = ExprId::from_index(0, false).unwrap();
    let s = ExprId::from_index(12345, true).unwrap();
    assert_eq!(ExprId::from_bits(p.bits()).unwrap().index(), p.index());
    assert_eq!(ExprId::from_bits(s.bits()).unwrap().index(), s.index());
    assert!(ExprId::from_bits(s.bits()).unwrap().is_scratch());
}

/// SplitMix64 — deterministic, dependency-free.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn nm(s: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: s.to_string(),
    })
}

/// Random term over a tiny vocabulary; `depth` bounds recursion.
fn gen_expr(r: &mut Rng, depth: u32, g: &mut RecGuard) -> Arc<Expr> {
    if depth == 0 {
        return match r.below(4) {
            0 => Expr::bvar(Nat::from(r.below(3))),
            1 => Expr::lit(Literal::NatVal(Nat::from(r.below(5)))),
            2 => Expr::const_(nm(["A", "B"][r.below(2) as usize]), vec![], g).unwrap(),
            _ => Expr::sort(Arc::new(Level::Succ(Arc::new(Level::Zero))), g).unwrap(),
        };
    }
    match r.below(5) {
        0 => Expr::app(gen_expr(r, depth - 1, g), gen_expr(r, depth - 1, g)),
        1 => Expr::lam(
            nm(["x", "y"][r.below(2) as usize]),
            gen_expr(r, depth - 1, g),
            gen_expr(r, depth - 1, g),
            [BinderInfo::Default, BinderInfo::Implicit][r.below(2) as usize],
        ),
        2 => Expr::forall_e(
            nm("x"),
            gen_expr(r, depth - 1, g),
            gen_expr(r, depth - 1, g),
            BinderInfo::Default,
        ),
        3 => Expr::let_e(
            nm("z"),
            gen_expr(r, depth - 1, g),
            gen_expr(r, depth - 1, g),
            gen_expr(r, depth - 1, g),
            r.below(2) == 0,
        ),
        _ => Expr::proj(nm("S"), Nat::from(r.below(3)), gen_expr(r, depth - 1, g)),
    }
}

#[test]
fn interning_invariant_id_eq_iff_structural_eq() {
    let mut g = RecGuard::new();
    let mut s = Store::persistent();
    // Two independent streams with overlapping seeds ⇒ plenty of
    // structurally-equal-but-pointer-distinct pairs.
    let mut terms: Vec<Arc<Expr>> = Vec::new();
    for seed in 0..60u64 {
        let mut r = Rng(seed % 30); // seeds repeat: duplicates guaranteed
        terms.push(gen_expr(&mut r, 4, &mut g));
    }
    let ids: Vec<_> = terms
        .iter()
        .map(|e| s.intern_expr(None, e).unwrap())
        .collect();
    for i in 0..terms.len() {
        for j in i..terms.len() {
            let structural = Expr::structural_eq(&terms[i], &terms[j], &mut g).unwrap();
            assert_eq!(
                ids[i] == ids[j],
                structural,
                "invariant violated between term {i} and term {j}"
            );
        }
    }
}

#[test]
fn roundtrip_preserves_structure_and_data_word() {
    let mut g = RecGuard::new();
    let mut s = Store::persistent();
    for seed in 0..40u64 {
        let mut r = Rng(seed);
        let e = gen_expr(&mut r, 4, &mut g);
        let id = s.intern_expr(None, &e).unwrap();
        let back = s.to_expr(None, id, &mut g).unwrap();
        assert!(
            Expr::structural_eq(&e, &back, &mut g).unwrap(),
            "seed {seed}"
        );
        assert_eq!(back.data(), e.data(), "seed {seed}");
    }
}

#[test]
fn reinterning_a_roundtripped_term_is_id_stable() {
    let mut g = RecGuard::new();
    let mut s = Store::persistent();
    for seed in 0..20u64 {
        let mut r = Rng(seed);
        let e = gen_expr(&mut r, 3, &mut g);
        let id = s.intern_expr(None, &e).unwrap();
        let back = s.to_expr(None, id, &mut g).unwrap();
        let id2 = s.intern_expr(None, &back).unwrap();
        assert_eq!(id, id2, "seed {seed}");
    }
}
