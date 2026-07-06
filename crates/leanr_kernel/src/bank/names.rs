//! Hierarchical name bank (spec §1: `NameId`). The anonymous name is
//! `Option<NameId>::None` everywhere, so every stored row is a real
//! `Str`/`Num` component.

use super::probe::IdTable;
use super::{NameId, NatId, StrId, MAX_INDEX};
use crate::KernelError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NameRow {
    Str { parent: Option<NameId>, part: StrId },
    Num { parent: Option<NameId>, part: NatId },
}

pub struct NameBank {
    rows: Vec<NameRow>,
    hashes: Vec<u64>,
    table: IdTable,
    region: u32,
}

impl NameBank {
    pub fn new(region: u32) -> NameBank {
        NameBank {
            rows: Vec::new(),
            hashes: Vec::new(),
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

    pub fn row(&self, index: usize) -> Option<&NameRow> {
        self.rows.get(index)
    }

    pub fn hash_of(&self, index: usize) -> u64 {
        self.hashes[index]
    }

    pub fn lookup(&self, hash: u64, row: &NameRow) -> Option<u32> {
        self.table.lookup(hash, |bits| {
            self.rows[((bits & !super::REGION_BIT) - 1) as usize] == *row
        })
    }

    pub(crate) fn insert(&mut self, hash: u64, row: NameRow) -> Result<u32, KernelError> {
        let index = u32::try_from(self.rows.len()).map_err(|_| KernelError::BankExhausted)?;
        if index > MAX_INDEX {
            return Err(KernelError::BankExhausted);
        }
        self.rows.push(row);
        self.hashes.push(hash);
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
    use crate::Name;
    use std::sync::Arc;

    fn nm(parts: &[&str]) -> Arc<Name> {
        let mut n = Arc::new(Name::Anonymous);
        for p in parts {
            n = Arc::new(Name::Str {
                parent: n,
                part: p.to_string(),
            });
        }
        n
    }

    #[test]
    fn name_interns_dedup_across_trees() {
        let mut s = Store::persistent();
        let a = s.intern_name(None, &nm(&["Foo", "bar"])).unwrap();
        let b = s.intern_name(None, &nm(&["Foo", "bar"])).unwrap();
        let c = s.intern_name(None, &nm(&["Foo", "baz"])).unwrap();
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert!(a.is_some());
    }

    #[test]
    fn anonymous_is_none() {
        let mut s = Store::persistent();
        assert_eq!(
            s.intern_name(None, &Arc::new(Name::Anonymous)).unwrap(),
            None
        );
    }

    #[test]
    fn name_roundtrips() {
        let mut s = Store::persistent();
        let orig = nm(&["Init", "Data", "Char"]);
        let id = s.intern_name(None, &orig).unwrap();
        let back = s.to_name(None, id);
        assert_eq!(&back, &orig);
    }

    #[test]
    fn shared_prefix_shares_rows() {
        let mut s = Store::persistent();
        let a = s.intern_name(None, &nm(&["Foo", "bar"])).unwrap().unwrap();
        let b = s.intern_name(None, &nm(&["Foo", "baz"])).unwrap().unwrap();
        // Both rows' parents are the same "Foo" id.
        let pa = match s.name_row(None, a) {
            crate::bank::names::NameRow::Str { parent, .. } => *parent,
            _ => panic!(),
        };
        let pb = match s.name_row(None, b) {
            crate::bank::names::NameRow::Str { parent, .. } => *parent,
            _ => panic!(),
        };
        assert_eq!(pa, pb);
    }
}
