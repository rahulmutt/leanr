//! Bank-level unit tests plus differential property tests for the
//! interning invariant (spec §1): equal ids ⇔ `Expr::structural_eq`.
//! The existing `Arc<Expr>` representation is the oracle.

use super::testgen::{gen_expr, nm, Rng};
use super::*;
use crate::{DataValue, Expr, KVMap, Nat, RecGuard};
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
fn scratch_and_promote_preserve_the_interning_invariant() {
    let mut g = RecGuard::new();

    // Seed a persistent store from seeds 0..30.
    let mut base = Store::persistent();
    let mut persistent_terms: Vec<Arc<Expr>> = Vec::new();
    let mut persistent_ids: Vec<ExprId> = Vec::new();
    for seed in 0..30u64 {
        let mut r = Rng(seed);
        let e = gen_expr(&mut r, 4, &mut g);
        let id = base.intern_expr(None, &e).unwrap();
        persistent_ids.push(id);
        persistent_terms.push(e);
    }

    // Intern terms from seeds 0..60 (repeats guarantee scratch/base and
    // scratch/scratch structural duplicates) through a scratch overlay.
    let mut scr = Store::scratch();
    let mut scratch_terms: Vec<Arc<Expr>> = Vec::new();
    let mut scratch_ids: Vec<ExprId> = Vec::new();
    for seed in 0..60u64 {
        let mut r = Rng(seed % 30);
        let e = gen_expr(&mut r, 4, &mut g);
        let id = scr.intern_expr(Some(&base), &e).unwrap();
        scratch_ids.push(id);
        scratch_terms.push(e);
    }

    // Ids are globally canonical across regions: pairwise id equality
    // (direct `==`, no region-aware translation) must agree with
    // `Expr::structural_eq` across BOTH id sets together.
    let all_terms: Vec<&Arc<Expr>> = persistent_terms
        .iter()
        .chain(scratch_terms.iter())
        .collect();
    let all_ids: Vec<ExprId> = persistent_ids
        .iter()
        .copied()
        .chain(scratch_ids.iter().copied())
        .collect();
    for i in 0..all_terms.len() {
        for j in i..all_terms.len() {
            let structural = Expr::structural_eq(all_terms[i], all_terms[j], &mut g).unwrap();
            assert_eq!(
                all_ids[i] == all_ids[j],
                structural,
                "invariant violated between term {i} and term {j}"
            );
        }
    }

    // Promote every scratch-region root id into base; the promoted
    // term must read back from base ALONE structurally equal to the
    // original, and promoting the same sid twice must be idempotent.
    for (i, &sid) in scratch_ids.iter().enumerate() {
        let pid1 = scratch::promote(&mut base, &scr, sid).unwrap();
        let back = base.to_expr(None, pid1, &mut g).unwrap();
        assert!(
            Expr::structural_eq(&back, &scratch_terms[i], &mut g).unwrap(),
            "promoted term {i} does not read back structurally equal from base alone"
        );
        let pid2 = scratch::promote(&mut base, &scr, sid).unwrap();
        assert_eq!(
            pid1, pid2,
            "promoting scratch id {i} twice must be idempotent"
        );
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

/// Interning a kvmap via pre-built rows must hit the same canonical
/// KVMapId as the Arc-bridge `intern_kvmap` on the same logical map —
/// this equivalence is what makes the phase-3 direct decoder's kvmaps
/// id-identical to the bridge's.
#[test]
fn kvmap_rows_and_arc_bridge_agree() {
    let mut st = Store::persistent();
    let name = st.intern_name(None, &nm("k")).unwrap();
    let map = KVMap(vec![(nm("k"), DataValue::OfNat(Nat::from(7u64)))]);
    let via_arc = st.intern_kvmap(None, &map).unwrap();
    let nat = st.intern_nat(None, &Nat::from(7u64)).unwrap();
    let via_rows = st
        .intern_kvmap_rows(None, vec![(name, pools::DataValueRow::Nat(nat))])
        .unwrap();
    assert_eq!(via_arc, via_rows);
}
