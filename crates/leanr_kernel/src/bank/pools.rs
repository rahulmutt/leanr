//! Deduplicated value pools (spec §1 "side pools"). One `ValuePool<T>`
//! = `Vec<T>` rows + an `IdTable` that rehashes rows from the vec, so
//! values are stored exactly once.

use super::probe::IdTable;
use super::MAX_INDEX;
use crate::KernelError;

pub struct ValuePool<T> {
    items: Vec<T>,
    table: IdTable,
    region: u32,
}

impl<T> ValuePool<T> {
    pub fn new(region: u32) -> ValuePool<T> {
        ValuePool {
            items: Vec::new(),
            table: IdTable::new(),
            region,
        }
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.items.get(index)
    }

    fn row_of_bits(&self, bits: u32) -> &T {
        // bits produced by this pool: strip region, -1.
        &self.items[((bits & !super::REGION_BIT) - 1) as usize]
    }

    /// Probe for an existing row (read-only; used cross-region).
    pub fn lookup(&self, hash: u64, mut eq: impl FnMut(&T) -> bool) -> Option<u32> {
        self.table.lookup(hash, |bits| eq(self.row_of_bits(bits)))
    }

    /// Intern: return existing bits or append a new row.
    pub fn intern(
        &mut self,
        hash: u64,
        eq: impl FnMut(&T) -> bool,
        make: impl FnOnce() -> T,
        mut rehash: impl FnMut(&T) -> u64,
    ) -> Result<u32, KernelError> {
        if let Some(bits) = self.lookup(hash, eq) {
            return Ok(bits);
        }
        let index = u32::try_from(self.items.len()).map_err(|_| KernelError::BankExhausted)?;
        if index > MAX_INDEX {
            return Err(KernelError::BankExhausted);
        }
        self.items.push(make());
        let bits = (index + 1) | self.region;
        // Rehash borrows rows immutably; split via a local closure over
        // the (already pushed) items.
        let items = &self.items;
        self.table.insert(hash, bits, |b| {
            rehash(&items[((b & !super::REGION_BIT) - 1) as usize])
        });
        Ok(bits)
    }
}

#[cfg(test)]
mod tests {
    use crate::bank::{Store, REGION_BIT};
    use crate::Nat;

    #[test]
    fn str_pool_dedups() {
        let mut s = Store::persistent();
        let a = s.intern_str(None, "hello").unwrap();
        let b = s.intern_str(None, "hello").unwrap();
        let c = s.intern_str(None, "world").unwrap();
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(s.str_at(None, a), "hello");
    }

    #[test]
    fn nat_pool_dedups_by_value() {
        let mut s = Store::persistent();
        let a = s.intern_nat(None, &Nat::from(7u64)).unwrap();
        let b = s.intern_nat(None, &Nat::from(7u64)).unwrap();
        assert_eq!(a, b);
        assert_eq!(s.nat_at(None, a), &Nat::from(7u64));
    }

    #[test]
    fn scratch_consults_base_first() {
        let mut base = Store::persistent();
        let pa = base.intern_str(None, "shared").unwrap();
        let mut scr = Store::scratch();
        let sa = scr.intern_str(Some(&base), "shared").unwrap();
        // Structurally equal ⇒ the persistent id, not a new scratch row.
        assert_eq!(sa, pa);
        assert!(!sa.is_scratch());
        // A genuinely new string goes to scratch with the region bit.
        let sb = scr.intern_str(Some(&base), "fresh").unwrap();
        assert!(sb.is_scratch());
        assert_eq!(sb.bits() & REGION_BIT, REGION_BIT);
        assert_eq!(scr.str_at(Some(&base), sb), "fresh");
        // Resolving a base id through the pair still works.
        assert_eq!(scr.str_at(Some(&base), pa), "shared");
    }
}
