//! Deduplicated value pools (spec §1 "side pools"). One `ValuePool<T>`
//! = `Vec<T>` rows + an `IdTable` that rehashes rows from the vec, so
//! values are stored exactly once.

use super::probe::IdTable;
use super::{IntId, NameId, NatId, StrId, MAX_INDEX};
use crate::expr::mix;
use crate::{KernelError, Syntax};
use std::sync::Arc;

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

/// A bridged `DataValue` (spec Task 5): names/nats/ints/strs go through
/// their leaf pools, but `Syntax` is kept as the exact `Arc` the caller
/// handed in (never re-interned into a pool of its own), so
/// `Arc::ptr_eq` — the ptr-eq rule `data_value_eq` documents in
/// expr.rs — stays exact after the bridge.
#[derive(Debug, Clone)]
pub enum DataValueRow {
    Str(StrId),
    Bool(bool),
    Name(Option<NameId>),
    Nat(NatId),
    Int(IntId),
    Syntax(Arc<Syntax>),
}

/// Manual, mirroring `data_value_eq`'s match exactly: every arm is
/// value/id equality except `Syntax`, which is `Arc::ptr_eq`.
impl PartialEq for DataValueRow {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (DataValueRow::Str(a), DataValueRow::Str(b)) => a == b,
            (DataValueRow::Bool(a), DataValueRow::Bool(b)) => a == b,
            (DataValueRow::Name(a), DataValueRow::Name(b)) => a == b,
            (DataValueRow::Nat(a), DataValueRow::Nat(b)) => a == b,
            (DataValueRow::Int(a), DataValueRow::Int(b)) => a == b,
            (DataValueRow::Syntax(a), DataValueRow::Syntax(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }
}

/// Content hash of a single bridged value, consistent with the
/// `PartialEq` above: `Syntax` hashes by `Arc::as_ptr` (the same
/// identity `Arc::ptr_eq` compares), everything else by id bits/value.
pub(crate) fn data_value_row_hash(v: &DataValueRow) -> u64 {
    match v {
        DataValueRow::Str(id) => mix(0, id.bits() as u64),
        DataValueRow::Bool(b) => mix(1, u64::from(*b)),
        DataValueRow::Name(id) => mix(2, id.map_or(0, |i| u64::from(i.bits()))),
        DataValueRow::Nat(id) => mix(3, u64::from(id.bits())),
        DataValueRow::Int(id) => mix(4, u64::from(id.bits())),
        DataValueRow::Syntax(a) => mix(5, Arc::as_ptr(a) as u64),
    }
}

/// A bridged `KVMap`: order-sensitive, like `kvmap_eq`. `Box<[T]>`'s
/// derived `PartialEq` already compares element-wise in order, so this
/// matches `kvmap_eq`'s semantics exactly once `DataValueRow`'s manual
/// `PartialEq` is in place.
#[derive(Debug, Clone, PartialEq)]
pub struct KVMapRow(pub Box<[(Option<NameId>, DataValueRow)]>);

/// Content hash of a `KVMapRow`, recomputable purely from the stored
/// row (no external state) — the `ValuePool::intern` rehash contract.
pub(crate) fn kvmap_row_hash(row: &KVMapRow) -> u64 {
    let mut h = 17u64;
    for (name, value) in row.0.iter() {
        let nh = name.map_or(0, |id| u64::from(id.bits()));
        h = mix(h, mix(nh, data_value_row_hash(value)));
    }
    h
}

/// Phase 1 `LetE` spill row: `(decl_name, body ExprId bits)`. `terms.rs`
/// (Task 6) is the only writer; all fields are plain id bits/values, so
/// derived equality/hashing already matches the interning invariant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SpillRow {
    pub name: Option<NameId>,
    pub body_or_aux: u32,
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

    #[test]
    fn kvmap_pool_dedups_and_roundtrips() {
        use crate::expr::{DataValue, KVMap};
        let mut s = Store::persistent();
        let nm = std::sync::Arc::new(crate::Name::Str {
            parent: std::sync::Arc::new(crate::Name::Anonymous),
            part: "k".to_string(),
        });
        let m = KVMap(vec![(nm.clone(), DataValue::OfBool(true))]);
        let a = s.intern_kvmap(None, &m).unwrap();
        let b = s
            .intern_kvmap(None, &KVMap(vec![(nm.clone(), DataValue::OfBool(true))]))
            .unwrap();
        assert_eq!(a, b);
        let back = s.to_kvmap(None, a);
        assert!(crate::expr::kvmap_eq(&back, &m));
    }

    #[test]
    fn spill_pool_dedups() {
        let mut s = Store::persistent();
        let a = s.intern_spill(None, None, 42).unwrap();
        let b = s.intern_spill(None, None, 42).unwrap();
        let c = s.intern_spill(None, None, 43).unwrap();
        assert_eq!(a, b);
        assert_ne!(a, c);
    }
}
