//! Open-addressing id table (spec §1 "dedup at construction").
//!
//! Stores raw id *bits* (`u32`, nonzero — id encodings guarantee this)
//! in power-of-two slot arrays; `0` is the empty-slot sentinel. Keys are
//! never stored: the caller rehashes/compares rows straight from its
//! bank arrays, so the table costs ~4-8 bytes per entry at 50% max load.
//! Safe code only.

pub struct IdTable {
    /// Power-of-two slot array; 0 = empty (id bits are never 0).
    slots: Vec<u32>,
    len: u32,
}

impl Default for IdTable {
    fn default() -> Self {
        Self::new()
    }
}

impl IdTable {
    pub fn new() -> IdTable {
        IdTable {
            slots: vec![0; 16],
            len: 0,
        }
    }

    pub fn len(&self) -> u32 {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Triangular probing over a power-of-two table visits every slot.
    fn probe_start(&self, hash: u64) -> usize {
        // Fold the high bits in so low-entropy hashes still spread.
        ((hash ^ (hash >> 32)) as usize) & (self.slots.len() - 1)
    }

    /// Find an entry whose stored bits satisfy `eq` under `hash`.
    /// `eq` receives candidate id bits and must compare the actual rows.
    pub fn lookup(&self, hash: u64, mut eq: impl FnMut(u32) -> bool) -> Option<u32> {
        let mask = self.slots.len() - 1;
        let mut i = self.probe_start(hash);
        let mut step = 0usize;
        loop {
            let bits = self.slots[i];
            if bits == 0 {
                return None;
            }
            if eq(bits) {
                return Some(bits);
            }
            step += 1;
            if step > self.slots.len() {
                return None; // table full of non-matches (cannot happen below max load)
            }
            i = (i + step) & mask;
        }
    }

    /// Insert `bits` under `hash`. The caller has already checked the
    /// entry is absent (`lookup` returned `None`). Grows at 50% load;
    /// `rehash` recomputes the hash of an existing entry from its bits.
    pub fn insert(&mut self, hash: u64, bits: u32, mut rehash: impl FnMut(u32) -> u64) {
        debug_assert_ne!(bits, 0);
        if (self.len as usize + 1) * 2 > self.slots.len() {
            let new_len = self.slots.len() * 2;
            let old = std::mem::replace(&mut self.slots, vec![0; new_len]);
            for b in old {
                if b != 0 {
                    let h = rehash(b);
                    self.place(h, b);
                }
            }
        }
        self.place(hash, bits);
        self.len += 1;
    }

    fn place(&mut self, hash: u64, bits: u32) {
        let mask = self.slots.len() - 1;
        let mut i = self.probe_start(hash);
        let mut step = 0usize;
        while self.slots[i] != 0 {
            step += 1;
            i = (i + step) & mask;
        }
        self.slots[i] = bits;
    }
}

#[cfg(test)]
mod tests {
    use super::IdTable;

    #[test]
    fn insert_then_lookup_finds_bits() {
        let mut t = IdTable::new();
        t.insert(42, 7, |_| unreachable!("no growth at one entry"));
        assert_eq!(t.lookup(42, |bits| bits == 7), Some(7));
        assert_eq!(t.len(), 1);
    }

    #[test]
    fn lookup_misses_on_eq_false() {
        let mut t = IdTable::new();
        t.insert(42, 7, |_| unreachable!());
        // Same hash, eq rejects: a collision that is not the same row.
        assert_eq!(t.lookup(42, |_| false), None);
    }

    #[test]
    fn colliding_hashes_coexist() {
        let mut t = IdTable::new();
        // All the same hash — forces probe chains.
        for id in 1..=100u32 {
            t.insert(5, id, |bits| if bits <= 100 { 5 } else { unreachable!() });
        }
        for id in 1..=100u32 {
            assert_eq!(t.lookup(5, |bits| bits == id), Some(id), "id {id}");
        }
        assert_eq!(t.len(), 100);
    }

    #[test]
    fn growth_preserves_entries() {
        let mut t = IdTable::new();
        // Distinct hashes, enough to force several doublings; rehash
        // callback recomputes each entry's hash (here: identity of bits).
        for id in 1..=10_000u32 {
            t.insert(id as u64, id, |bits| bits as u64);
        }
        for id in (1..=10_000u32).step_by(97) {
            assert_eq!(t.lookup(id as u64, |bits| bits == id), Some(id));
        }
        assert_eq!(t.len(), 10_000);
    }
}
