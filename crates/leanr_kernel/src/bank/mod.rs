//! Index-based term bank (spec:
//! docs/superpowers/specs/2026-07-06-compact-expr-term-bank-design.md).
//!
//! Phase 1: standalone next to the `Arc<Expr>` representation; nothing
//! in the production kernel path uses this module yet. Every id type
//! carries a region bit (persistent env bank vs per-declaration
//! scratch); the low 31 bits of the raw bits are never 0, so probe
//! tables can use 0 as the empty sentinel.

pub mod pools;
pub mod probe;

use std::num::NonZeroU32;

/// Top bit of every id: set ⇒ the row lives in the scratch region.
pub const REGION_BIT: u32 = 1 << 31;
/// Largest storable row index per region: bits = index + 1 must stay
/// below `REGION_BIT`.
pub const MAX_INDEX: u32 = REGION_BIT - 2;

macro_rules! id_type {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name(NonZeroU32);

        impl $name {
            pub fn from_index(index: u32, scratch: bool) -> Option<$name> {
                if index > MAX_INDEX {
                    return None;
                }
                let bits = (index + 1) | if scratch { REGION_BIT } else { 0 };
                NonZeroU32::new(bits).map($name)
            }
            pub fn from_bits(bits: u32) -> Option<$name> {
                // Reject bits whose low 31 bits are all zero: `index()`
                // subtracts 1 from them and would underflow (only the
                // region bit may be set, e.g. plain 0 or `REGION_BIT`).
                if bits & !REGION_BIT == 0 {
                    return None;
                }
                NonZeroU32::new(bits).map($name)
            }
            pub fn bits(self) -> u32 {
                self.0.get()
            }
            pub fn index(self) -> usize {
                ((self.0.get() & !REGION_BIT) - 1) as usize
            }
            pub fn is_scratch(self) -> bool {
                self.0.get() & REGION_BIT != 0
            }
        }
    };
}

id_type!(/** Expression row id. */ ExprId);
id_type!(/** Hierarchical name id (`None` = anonymous). */ NameId);
id_type!(/** Universe level id. */ LevelId);
id_type!(/** String-pool id. */ StrId);
id_type!(/** Nat (bignum) pool id. */ NatId);
id_type!(/** Int (bignum) pool id. */ IntId);
id_type!(/** Level-list pool id (Const's levels). */ LevelsId);
id_type!(/** KVMap pool id. */ KVMapId);
id_type!(/** LetE spill pool id. */ SpillId);

use crate::{Int, KernelError, Nat};
use pools::ValuePool;

/// Stable sip-style hash for pool values (DefaultHasher is fine: hashes
/// never persist and only feed in-process probe tables).
pub(crate) fn sip<T: std::hash::Hash + ?Sized>(x: &T) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::Hasher;
    let mut h = DefaultHasher::new();
    x.hash(&mut h);
    h.finish()
}

/// One region's complete storage (spec §2). The persistent `Store` is
/// phase 2's `Environment` bank; a scratch `Store` is a per-declaration
/// overlay whose intern methods consult `base` first.
pub struct Store {
    pub region: u32,
    pub strs: ValuePool<Box<str>>,
    pub nats: ValuePool<Nat>,
    pub ints: ValuePool<Int>,
    // Extended by Tasks 3-6: names, levels, level_lists, kvmaps,
    // spills, terms.
}

impl Store {
    pub fn persistent() -> Store {
        Store::new(0)
    }
    pub fn scratch() -> Store {
        Store::new(REGION_BIT)
    }
    fn new(region: u32) -> Store {
        Store {
            region,
            strs: ValuePool::new(region),
            nats: ValuePool::new(region),
            ints: ValuePool::new(region),
        }
    }

    /// Route an id to the store owning its region. `base` is `None`
    /// only when `self` IS the persistent store.
    fn store_for<'a>(&'a self, base: Option<&'a Store>, scratch_bit: bool) -> &'a Store {
        if scratch_bit {
            self
        } else {
            base.unwrap_or(self)
        }
    }

    pub fn intern_str(&mut self, base: Option<&Store>, s: &str) -> Result<StrId, KernelError> {
        let h = sip(s);
        if let Some(b) = base {
            if let Some(bits) = b.strs.lookup(h, |t| &**t == s) {
                return StrId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        let bits = self
            .strs
            .intern(h, |t| &**t == s, || s.into(), |t| sip(&**t))?;
        StrId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }

    pub fn str_at<'a>(&'a self, base: Option<&'a Store>, id: StrId) -> &'a str {
        self.store_for(base, id.is_scratch())
            .strs
            .get(id.index())
            .map(|b| &**b)
            .expect("StrId minted by intern ⇒ valid")
    }

    pub fn intern_nat(&mut self, base: Option<&Store>, n: &Nat) -> Result<NatId, KernelError> {
        let h = sip(n);
        if let Some(b) = base {
            if let Some(bits) = b.nats.lookup(h, |t| t == n) {
                return NatId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        let bits = self.nats.intern(h, |t| t == n, || n.clone(), sip)?;
        NatId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }

    pub fn nat_at<'a>(&'a self, base: Option<&'a Store>, id: NatId) -> &'a Nat {
        self.store_for(base, id.is_scratch())
            .nats
            .get(id.index())
            .expect("NatId minted by intern ⇒ valid")
    }

    pub fn intern_int(&mut self, base: Option<&Store>, i: &Int) -> Result<IntId, KernelError> {
        let h = sip(i);
        if let Some(b) = base {
            if let Some(bits) = b.ints.lookup(h, |t| t == i) {
                return IntId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        let bits = self.ints.intern(h, |t| t == i, || i.clone(), sip)?;
        IntId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }

    pub fn int_at<'a>(&'a self, base: Option<&'a Store>, id: IntId) -> &'a Int {
        self.store_for(base, id.is_scratch())
            .ints
            .get(id.index())
            .expect("IntId minted by intern ⇒ valid")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
