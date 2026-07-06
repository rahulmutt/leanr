//! Index-based term bank (spec:
//! docs/superpowers/specs/2026-07-06-compact-expr-term-bank-design.md).
//!
//! Phase 1: standalone next to the `Arc<Expr>` representation; nothing
//! in the production kernel path uses this module yet. Every id type
//! carries a region bit (persistent env bank vs per-declaration
//! scratch); the low 31 bits of the raw bits are never 0, so probe
//! tables can use 0 as the empty sentinel.

pub mod names;
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

use crate::{Int, KernelError, Name, Nat};
use pools::ValuePool;
use std::sync::Arc;

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
    pub names: names::NameBank,
    // Extended by Tasks 4-6: levels, level_lists, kvmaps, spills, terms.
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
            names: names::NameBank::new(region),
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

    fn name_hash_of(&self, base: Option<&Store>, id: Option<NameId>) -> u64 {
        match id {
            None => 0,
            Some(id) => self
                .store_for(base, id.is_scratch())
                .names
                .hash_of(id.index()),
        }
    }

    fn name_intern_row(
        &mut self,
        base: Option<&Store>,
        hash: u64,
        row: names::NameRow,
    ) -> Result<NameId, KernelError> {
        if let Some(b) = base {
            if let Some(bits) = b.names.lookup(hash, &row) {
                return NameId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        if let Some(bits) = self.names.lookup(hash, &row) {
            return NameId::from_bits(bits).ok_or(KernelError::BankExhausted);
        }
        let bits = self.names.insert(hash, row)?;
        NameId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }

    pub fn name_str(
        &mut self,
        base: Option<&Store>,
        parent: Option<NameId>,
        part: StrId,
    ) -> Result<NameId, KernelError> {
        let ph = self.name_hash_of(base, parent);
        let sh = sip(self.str_at(base, part));
        let h = crate::expr::mix(1, crate::expr::mix(ph, sh));
        self.name_intern_row(base, h, names::NameRow::Str { parent, part })
    }

    pub fn name_num(
        &mut self,
        base: Option<&Store>,
        parent: Option<NameId>,
        part: NatId,
    ) -> Result<NameId, KernelError> {
        let ph = self.name_hash_of(base, parent);
        let nh = sip(self.nat_at(base, part));
        let h = crate::expr::mix(2, crate::expr::mix(ph, nh));
        self.name_intern_row(base, h, names::NameRow::Num { parent, part })
    }

    pub fn name_row<'a>(&'a self, base: Option<&'a Store>, id: NameId) -> &'a names::NameRow {
        self.store_for(base, id.is_scratch())
            .names
            .row(id.index())
            .expect("NameId minted by intern ⇒ valid")
    }

    /// Bridge: intern an `Arc<Name>` chain (iterative — parent chains
    /// are attacker-depth).
    pub fn intern_name(
        &mut self,
        base: Option<&Store>,
        n: &Arc<Name>,
    ) -> Result<Option<NameId>, KernelError> {
        // Collect components root-last, then intern root-first.
        let mut chain: Vec<&Name> = Vec::new();
        let mut cur: &Name = n;
        loop {
            match cur {
                Name::Anonymous => break,
                Name::Str { parent, .. } | Name::Num { parent, .. } => {
                    chain.push(cur);
                    cur = parent;
                }
            }
        }
        let mut id: Option<NameId> = None;
        for comp in chain.into_iter().rev() {
            id = Some(match comp {
                Name::Str { part, .. } => {
                    let s = self.intern_str(base, part)?;
                    self.name_str(base, id, s)?
                }
                Name::Num { part, .. } => {
                    let p = self.intern_nat(base, part)?;
                    self.name_num(base, id, p)?
                }
                Name::Anonymous => unreachable!("filtered above"),
            });
        }
        Ok(id)
    }

    /// Bridge: rebuild an `Arc<Name>` (iterative).
    pub fn to_name(&self, base: Option<&Store>, id: Option<NameId>) -> Arc<Name> {
        let mut chain: Vec<NameId> = Vec::new();
        let mut cur = id;
        while let Some(c) = cur {
            chain.push(c);
            cur = match self.name_row(base, c) {
                names::NameRow::Str { parent, .. } | names::NameRow::Num { parent, .. } => *parent,
            };
        }
        let mut out = Arc::new(Name::Anonymous);
        for c in chain.into_iter().rev() {
            out = match *self.name_row(base, c) {
                names::NameRow::Str { part, .. } => Arc::new(Name::Str {
                    parent: out,
                    part: self.str_at(base, part).to_string(),
                }),
                names::NameRow::Num { part, .. } => Arc::new(Name::Num {
                    parent: out,
                    part: self.nat_at(base, part).clone(),
                }),
            };
        }
        out
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
