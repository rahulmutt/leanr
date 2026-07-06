//! Universe-level bank (spec: `LevelId`). Anonymous param/mvar names
//! are `Option<NameId>::None`, mirroring how `NameBank` represents the
//! anonymous name — decoded params/mvars carry real names when the
//! source `Level` does, but `Level` itself allows anonymous `Arc<Name>`
//! leaves, so the row keeps that optionality.

use super::probe::IdTable;
use super::{LevelId, NameId, MAX_INDEX};
use crate::KernelError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LevelRow {
    Zero,
    Succ(LevelId),
    Max(LevelId, LevelId),
    IMax(LevelId, LevelId),
    Param(Option<NameId>),
    MVar(Option<NameId>),
}

pub struct LevelBank {
    rows: Vec<LevelRow>,
    hashes: Vec<u64>,
    flags: Vec<u8>,
    table: IdTable,
    region: u32,
}

impl LevelBank {
    pub fn new(region: u32) -> LevelBank {
        LevelBank {
            rows: Vec::new(),
            hashes: Vec::new(),
            flags: Vec::new(),
            table: IdTable::new(),
            region,
        }
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn row(&self, index: usize) -> Option<&LevelRow> {
        self.rows.get(index)
    }

    pub fn hash_of(&self, index: usize) -> u64 {
        self.hashes[index]
    }

    pub fn flags_of(&self, index: usize) -> u8 {
        self.flags[index]
    }

    pub fn lookup(&self, hash: u64, row: &LevelRow) -> Option<u32> {
        self.table.lookup(hash, |bits| {
            self.rows[((bits & !super::REGION_BIT) - 1) as usize] == *row
        })
    }

    pub(crate) fn insert(
        &mut self,
        hash: u64,
        flags: u8,
        row: LevelRow,
    ) -> Result<u32, KernelError> {
        let index = u32::try_from(self.rows.len()).map_err(|_| KernelError::BankExhausted)?;
        if index > MAX_INDEX {
            return Err(KernelError::BankExhausted);
        }
        self.rows.push(row);
        self.hashes.push(hash);
        self.flags.push(flags);
        let bits = (index + 1) | self.region;
        let hashes = &self.hashes;
        self.table.insert(hash, bits, |b| {
            hashes[((b & !super::REGION_BIT) - 1) as usize]
        });
        Ok(bits)
    }
}

#[cfg(test)]
mod tests {
    use crate::bank::Store;
    use crate::{Level, Name, RecGuard};
    use std::sync::Arc;

    fn lp(s: &str) -> Arc<Level> {
        Arc::new(Level::Param(Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: s.to_string(),
        })))
    }

    #[test]
    fn level_interns_dedup() {
        let mut s = Store::persistent();
        let a = s
            .intern_level(None, &Arc::new(Level::Succ(Arc::new(Level::Zero))))
            .unwrap();
        let b = s
            .intern_level(None, &Arc::new(Level::Succ(Arc::new(Level::Zero))))
            .unwrap();
        assert_eq!(a, b);
        let c = s.intern_level(None, &Arc::new(Level::Zero)).unwrap();
        assert_ne!(a, c);
    }

    #[test]
    fn level_flags_track_param_and_mvar() {
        let mut s = Store::persistent();
        let p = s.intern_level(None, &lp("u")).unwrap();
        assert_eq!(s.level_flags(None, p), 0b01);
        let m = s
            .intern_level(None, &Arc::new(Level::MVar(Arc::new(Name::Anonymous))))
            .unwrap();
        assert_eq!(s.level_flags(None, m), 0b10);
        let mx = s
            .intern_level(None, &Arc::new(Level::Max(lp("u"), Arc::new(Level::Zero))))
            .unwrap();
        assert_eq!(s.level_flags(None, mx), 0b01);
    }

    #[test]
    fn level_roundtrips_structurally() {
        let mut s = Store::persistent();
        let mut g = RecGuard::new();
        let orig = Arc::new(Level::IMax(lp("u"), Arc::new(Level::Succ(lp("v")))));
        let id = s.intern_level(None, &orig).unwrap();
        let back = s.to_level(None, id);
        assert!(Level::structural_eq(&orig, &back, &mut g).unwrap());
    }

    #[test]
    fn deep_level_chain_is_iterative() {
        let mut s = Store::persistent();
        let mut l = Arc::new(Level::Zero);
        for _ in 0..100_000 {
            l = Arc::new(Level::Succ(l));
        }
        // Must not overflow the stack; dedup makes the second intern id-equal.
        let a = s.intern_level(None, &l).unwrap();
        let b = s.intern_level(None, &l).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn level_list_pool_dedups() {
        let mut s = Store::persistent();
        let u = s.intern_level(None, &lp("u")).unwrap();
        let z = s.intern_level(None, &Arc::new(Level::Zero)).unwrap();
        let a = s.intern_level_list(None, &[u, z]).unwrap();
        let b = s.intern_level_list(None, &[u, z]).unwrap();
        let c = s.intern_level_list(None, &[z, u]).unwrap();
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(s.level_list_at(None, a), &[u, z]);
    }
}
