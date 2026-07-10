//! Index-based term bank (spec:
//! docs/superpowers/specs/2026-07-06-compact-expr-term-bank-design.md).
//!
//! Phase 2 (kernel-migration flip, `docs/superpowers/specs/
//! 2026-07-06-term-bank-kernel-migration-design.md`): this bank IS the
//! kernel's term representation. `decl.rs`, `local_ctx.rs`, `subst.rs`,
//! `tc.rs`, `quot.rs`/`quot_red.rs`, `inductive.rs`, `env.rs`, and
//! `replay.rs` (all one level up, at the crate root) run entirely on
//! `ExprId`/`NameId`/`LevelId`; only the phase-1 storage primitives
//! (`Store` and its side pools/probe table/scratch machinery) live in
//! this module. Every id type carries a region bit (persistent env bank
//! vs per-declaration scratch); the low 31 bits of the raw bits are
//! never 0, so probe tables can use 0 as the empty sentinel.

pub mod levels;
pub mod names;
pub mod pools;
pub mod probe;
pub mod scratch;
pub mod terms;

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

use crate::{DataValue, Int, KVMap, KernelError, Level, Name, Nat};
use pools::{kvmap_row_hash, DataValueRow, KVMapRow, SpillRow, ValuePool};
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
    pub levels: levels::LevelBank,
    pub level_lists: ValuePool<Box<[LevelId]>>,
    pub kvmaps: ValuePool<KVMapRow>,
    pub spills: ValuePool<SpillRow>,
    pub terms: terms::TermBank,
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
            levels: levels::LevelBank::new(region),
            level_lists: ValuePool::new(region),
            kvmaps: ValuePool::new(region),
            spills: ValuePool::new(region),
            terms: terms::TermBank::new(region),
        }
    }

    /// Number of expr rows this store holds (own region only — used by
    /// tests to check that scratch interning never mutates `base`).
    pub fn terms_len(&self) -> usize {
        self.terms.len()
    }

    /// Route an id to the store owning its region. `base` is `None`
    /// only when `self` IS the persistent store.
    fn store_for<'a>(&'a self, base: Option<&'a Store>, scratch_bit: bool) -> &'a Store {
        // Misroute guard: a persistent-region id (`!scratch_bit`) can
        // only be resolved against `self` directly when `self` IS the
        // persistent store. If `self` is a scratch store and no `base`
        // was supplied, falling through to `self` would silently read
        // the wrong row (scratch's own pool row at that index) instead
        // of erroring or routing to the real persistent store.
        debug_assert!(
            scratch_bit || base.is_some() || self.region == 0,
            "store_for: persistent-region id resolved on a scratch store with base = None (silent wrong-row read)"
        );
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

    fn level_hash(&self, base: Option<&Store>, id: LevelId) -> u64 {
        self.store_for(base, id.is_scratch())
            .levels
            .hash_of(id.index())
    }

    pub fn level_flags(&self, base: Option<&Store>, id: LevelId) -> u8 {
        self.store_for(base, id.is_scratch())
            .levels
            .flags_of(id.index())
    }

    pub fn level_row<'a>(&'a self, base: Option<&'a Store>, id: LevelId) -> &'a levels::LevelRow {
        self.store_for(base, id.is_scratch())
            .levels
            .row(id.index())
            .expect("LevelId minted by intern ⇒ valid")
    }

    fn level_intern_row(
        &mut self,
        base: Option<&Store>,
        hash: u64,
        flags: u8,
        row: levels::LevelRow,
    ) -> Result<LevelId, KernelError> {
        if let Some(b) = base {
            if let Some(bits) = b.levels.lookup(hash, &row) {
                return LevelId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        if let Some(bits) = self.levels.lookup(hash, &row) {
            return LevelId::from_bits(bits).ok_or(KernelError::BankExhausted);
        }
        let bits = self.levels.insert(hash, flags, row)?;
        LevelId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }

    pub fn level_zero(&mut self, base: Option<&Store>) -> Result<LevelId, KernelError> {
        self.level_intern_row(base, 11, 0, levels::LevelRow::Zero)
    }

    pub fn level_succ(&mut self, base: Option<&Store>, a: LevelId) -> Result<LevelId, KernelError> {
        let h = crate::expr::mix(12, self.level_hash(base, a));
        let f = self.level_flags(base, a);
        self.level_intern_row(base, h, f, levels::LevelRow::Succ(a))
    }

    pub fn level_max(
        &mut self,
        base: Option<&Store>,
        a: LevelId,
        b: LevelId,
    ) -> Result<LevelId, KernelError> {
        let h = crate::expr::mix(
            13,
            crate::expr::mix(self.level_hash(base, a), self.level_hash(base, b)),
        );
        let f = self.level_flags(base, a) | self.level_flags(base, b);
        self.level_intern_row(base, h, f, levels::LevelRow::Max(a, b))
    }

    pub fn level_imax(
        &mut self,
        base: Option<&Store>,
        a: LevelId,
        b: LevelId,
    ) -> Result<LevelId, KernelError> {
        let h = crate::expr::mix(
            14,
            crate::expr::mix(self.level_hash(base, a), self.level_hash(base, b)),
        );
        let f = self.level_flags(base, a) | self.level_flags(base, b);
        self.level_intern_row(base, h, f, levels::LevelRow::IMax(a, b))
    }

    pub fn level_param(
        &mut self,
        base: Option<&Store>,
        n: Option<NameId>,
    ) -> Result<LevelId, KernelError> {
        let h = crate::expr::mix(15, self.name_hash_of(base, n));
        self.level_intern_row(base, h, 0b01, levels::LevelRow::Param(n))
    }

    pub fn level_mvar(
        &mut self,
        base: Option<&Store>,
        n: Option<NameId>,
    ) -> Result<LevelId, KernelError> {
        let h = crate::expr::mix(16, self.name_hash_of(base, n));
        self.level_intern_row(base, h, 0b10, levels::LevelRow::MVar(n))
    }

    /// Bridge: intern an `Arc<Level>` tree (iterative post-order with an
    /// in-call memo keyed by `Arc::as_ptr` — sound for the call duration
    /// only, exactly as `intern_name`'s attacker-depth handling and
    /// `intern.rs`'s expr bridges document; adversarial `Succ` chains are
    /// attacker-depth).
    pub fn intern_level(
        &mut self,
        base: Option<&Store>,
        l: &Arc<Level>,
    ) -> Result<LevelId, KernelError> {
        use std::collections::HashMap;
        enum Frame<'a> {
            Enter(&'a Arc<Level>),
            Exit(&'a Arc<Level>),
        }
        let mut memo: HashMap<usize, LevelId> = HashMap::new();
        let mut out: Vec<LevelId> = Vec::new();
        let mut stack = vec![Frame::Enter(l)];
        while let Some(fr) = stack.pop() {
            match fr {
                Frame::Enter(l) => {
                    if let Some(&id) = memo.get(&(Arc::as_ptr(l) as usize)) {
                        out.push(id);
                        continue;
                    }
                    match l.as_ref() {
                        Level::Zero | Level::Param(_) | Level::MVar(_) => {
                            stack.push(Frame::Exit(l))
                        }
                        Level::Succ(a) => {
                            stack.push(Frame::Exit(l));
                            stack.push(Frame::Enter(a));
                        }
                        Level::Max(a, b) | Level::IMax(a, b) => {
                            stack.push(Frame::Exit(l));
                            stack.push(Frame::Enter(b));
                            stack.push(Frame::Enter(a));
                        }
                    }
                }
                Frame::Exit(l) => {
                    let id = match l.as_ref() {
                        Level::Zero => self.level_zero(base)?,
                        Level::Succ(_) => {
                            let a = out.pop().expect("child pushed by Enter");
                            self.level_succ(base, a)?
                        }
                        Level::Max(_, _) => {
                            let b = out.pop().expect("child");
                            let a = out.pop().expect("child");
                            self.level_max(base, a, b)?
                        }
                        Level::IMax(_, _) => {
                            let b = out.pop().expect("child");
                            let a = out.pop().expect("child");
                            self.level_imax(base, a, b)?
                        }
                        Level::Param(n) => {
                            let n = self.intern_name(base, n)?;
                            self.level_param(base, n)?
                        }
                        Level::MVar(n) => {
                            let n = self.intern_name(base, n)?;
                            self.level_mvar(base, n)?
                        }
                    };
                    memo.insert(Arc::as_ptr(l) as usize, id);
                    out.push(id);
                }
            }
        }
        Ok(out.pop().expect("root"))
    }

    /// Bridge: rebuild an `Arc<Level>` (iterative — same two-phase stack
    /// as `intern_level`, run in reverse, with an in-call memo keyed by
    /// `LevelId` since dedup means many parents can share one child row).
    pub fn to_level(&self, base: Option<&Store>, id: LevelId) -> Arc<Level> {
        use std::collections::HashMap;
        enum Frame {
            Enter(LevelId),
            Exit(LevelId),
        }
        let mut memo: HashMap<LevelId, Arc<Level>> = HashMap::new();
        let mut out: Vec<Arc<Level>> = Vec::new();
        let mut stack = vec![Frame::Enter(id)];
        while let Some(fr) = stack.pop() {
            match fr {
                Frame::Enter(id) => {
                    if let Some(l) = memo.get(&id) {
                        out.push(Arc::clone(l));
                        continue;
                    }
                    match *self.level_row(base, id) {
                        levels::LevelRow::Zero
                        | levels::LevelRow::Param(_)
                        | levels::LevelRow::MVar(_) => {
                            stack.push(Frame::Exit(id));
                        }
                        levels::LevelRow::Succ(a) => {
                            stack.push(Frame::Exit(id));
                            stack.push(Frame::Enter(a));
                        }
                        levels::LevelRow::Max(a, b) | levels::LevelRow::IMax(a, b) => {
                            stack.push(Frame::Exit(id));
                            stack.push(Frame::Enter(b));
                            stack.push(Frame::Enter(a));
                        }
                    }
                }
                Frame::Exit(id) => {
                    let l = match *self.level_row(base, id) {
                        levels::LevelRow::Zero => Arc::new(Level::Zero),
                        levels::LevelRow::Succ(_) => {
                            let a = out.pop().expect("child pushed by Enter");
                            Arc::new(Level::Succ(a))
                        }
                        levels::LevelRow::Max(_, _) => {
                            let b = out.pop().expect("child");
                            let a = out.pop().expect("child");
                            Arc::new(Level::Max(a, b))
                        }
                        levels::LevelRow::IMax(_, _) => {
                            let b = out.pop().expect("child");
                            let a = out.pop().expect("child");
                            Arc::new(Level::IMax(a, b))
                        }
                        levels::LevelRow::Param(n) => Arc::new(Level::Param(self.to_name(base, n))),
                        levels::LevelRow::MVar(n) => Arc::new(Level::MVar(self.to_name(base, n))),
                    };
                    memo.insert(id, Arc::clone(&l));
                    out.push(l);
                }
            }
        }
        out.pop().expect("root")
    }

    pub fn intern_level_list(
        &mut self,
        base: Option<&Store>,
        ids: &[LevelId],
    ) -> Result<LevelsId, KernelError> {
        let h = sip(&ids.iter().map(|i| i.bits()).collect::<Vec<u32>>());
        if let Some(b) = base {
            if let Some(bits) = b.level_lists.lookup(h, |t| {
                t.len() == ids.len() && t.iter().zip(ids).all(|(a, b)| a == b)
            }) {
                return LevelsId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        let bits = self.level_lists.intern(
            h,
            |t| t.len() == ids.len() && t.iter().zip(ids).all(|(a, b)| a == b),
            || ids.to_vec().into_boxed_slice(),
            |t| sip(&t.iter().map(|i| i.bits()).collect::<Vec<u32>>()),
        )?;
        LevelsId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }

    pub fn level_list_at<'a>(&'a self, base: Option<&'a Store>, id: LevelsId) -> &'a [LevelId] {
        self.store_for(base, id.is_scratch())
            .level_lists
            .get(id.index())
            .map(|b| &**b)
            .expect("LevelsId minted by intern ⇒ valid")
    }

    /// Bridge: intern a single `DataValue` (used by `intern_kvmap`).
    /// `OfSyntax` is kept as the caller's exact `Arc` — never re-interned
    /// into a pool of its own — so `Arc::ptr_eq` stays exact.
    fn intern_data_value(
        &mut self,
        base: Option<&Store>,
        v: &DataValue,
    ) -> Result<DataValueRow, KernelError> {
        Ok(match v {
            DataValue::OfString(s) => DataValueRow::Str(self.intern_str(base, s)?),
            DataValue::OfBool(b) => DataValueRow::Bool(*b),
            DataValue::OfName(n) => DataValueRow::Name(self.intern_name(base, n)?),
            DataValue::OfNat(n) => DataValueRow::Nat(self.intern_nat(base, n)?),
            DataValue::OfInt(i) => DataValueRow::Int(self.intern_int(base, i)?),
            DataValue::OfSyntax(s) => DataValueRow::Syntax(Arc::clone(s)),
        })
    }

    /// Bridge: rebuild a single `DataValue` from a stored `DataValueRow`
    /// (used by `to_kvmap`). The `Syntax` arm clones the stored `Arc`,
    /// preserving the exact ptr-eq semantics `data_value_eq` uses.
    fn data_value_of(&self, base: Option<&Store>, v: &DataValueRow) -> DataValue {
        match v {
            DataValueRow::Str(id) => DataValue::OfString(self.str_at(base, *id).to_string()),
            DataValueRow::Bool(b) => DataValue::OfBool(*b),
            DataValueRow::Name(id) => DataValue::OfName(self.to_name(base, *id)),
            DataValueRow::Nat(id) => DataValue::OfNat(self.nat_at(base, *id).clone()),
            DataValueRow::Int(id) => DataValue::OfInt(self.int_at(base, *id).clone()),
            DataValueRow::Syntax(s) => DataValue::OfSyntax(Arc::clone(s)),
        }
    }

    /// Id-native kvmap intern (phase 3, direct decode): the caller has
    /// already interned every entry's leaves and hands the finished
    /// rows. `intern_kvmap` (the Arc bridge) reduces to leaf-bridging
    /// plus this.
    pub fn intern_kvmap_rows(
        &mut self,
        base: Option<&Store>,
        entries: Vec<(Option<NameId>, DataValueRow)>,
    ) -> Result<KVMapId, KernelError> {
        let row = KVMapRow(entries.into_boxed_slice());
        let h = kvmap_row_hash(&row);
        if let Some(b) = base {
            if let Some(bits) = b.kvmaps.lookup(h, |t| *t == row) {
                return KVMapId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        let bits = self
            .kvmaps
            .intern(h, |t| *t == row, || row.clone(), kvmap_row_hash)?;
        KVMapId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }

    /// Bridge: intern a `KVMap` (base lookup → own intern, following
    /// `intern_str`/`intern_nat`'s pattern). Each entry is bridged
    /// through `intern_name` and the leaf pools first, then the
    /// resulting row is interned as a whole.
    pub fn intern_kvmap(
        &mut self,
        base: Option<&Store>,
        m: &KVMap,
    ) -> Result<KVMapId, KernelError> {
        let mut entries: Vec<(Option<NameId>, DataValueRow)> = Vec::with_capacity(m.0.len());
        for (name, value) in m.0.iter() {
            let n = self.intern_name(base, name)?;
            let v = self.intern_data_value(base, value)?;
            entries.push((n, v));
        }
        self.intern_kvmap_rows(base, entries)
    }

    pub fn kvmap_at<'a>(&'a self, base: Option<&'a Store>, id: KVMapId) -> &'a KVMapRow {
        self.store_for(base, id.is_scratch())
            .kvmaps
            .get(id.index())
            .expect("KVMapId minted by intern ⇒ valid")
    }

    /// Bridge: rebuild a `KVMap` from its stored row.
    pub fn to_kvmap(&self, base: Option<&Store>, id: KVMapId) -> KVMap {
        let row = self.kvmap_at(base, id);
        KVMap(
            row.0
                .iter()
                .map(|(n, v)| (self.to_name(base, *n), self.data_value_of(base, v)))
                .collect(),
        )
    }

    /// Bridge: intern a phase-1 `LetE` spill row (`terms.rs`/Task 6 is
    /// the only writer of real data here; `body_bits` is an `ExprId`'s
    /// raw bits, opaque at this layer).
    pub fn intern_spill(
        &mut self,
        base: Option<&Store>,
        name: Option<NameId>,
        body_bits: u32,
    ) -> Result<SpillId, KernelError> {
        let row = SpillRow {
            name,
            body_or_aux: body_bits,
        };
        let h = sip(&row);
        if let Some(b) = base {
            if let Some(bits) = b.spills.lookup(h, |t| *t == row) {
                return SpillId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        let bits = self.spills.intern(h, |t| *t == row, || row, sip)?;
        SpillId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }

    pub fn spill_at<'a>(&'a self, base: Option<&'a Store>, id: SpillId) -> &'a SpillRow {
        self.store_for(base, id.is_scratch())
            .spills
            .get(id.index())
            .expect("SpillId minted by intern ⇒ valid")
    }
}

#[cfg(test)]
pub(crate) mod testgen;
#[cfg(test)]
mod tests;
