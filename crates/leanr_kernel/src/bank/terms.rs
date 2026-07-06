//! Expression term bank (spec: `ExprId`, Task 6). Struct-of-arrays rows
//! (21 B/row) dedup every `Expr` shape into `TermBank`; `Node` is the
//! read-only decoded view and mirrors `ExprNode` one level down (ids
//! instead of `Arc` children).

use super::probe::IdTable;
use super::{ExprId, KVMapId, LevelId, LevelsId, NameId, NatId, SpillId, Store, StrId, MAX_INDEX};
use crate::expr::{
    bvar_loose_range, combine_app, combine_binder, combine_let, depth_of, literal_hash, mix,
    nat_lossy_u64, TAG_BVAR, TAG_CONST, TAG_FVAR, TAG_LIT, TAG_MVAR, TAG_SORT,
};
use crate::{BinderInfo, ExprData, KernelError, Literal, Nat};

/// Per-row shape discriminant (bits 0-3 of the packed tag byte).
/// `#[repr(u8)]`, 15 ≤ 16 so it fits alongside `BinderInfo` (bits 4-5)
/// and `non_dep` (bit 6) in one byte.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Tag {
    BVar = 0,
    BVarBig = 1,
    FVar = 2,
    MVar = 3,
    Sort = 4,
    Const = 5,
    App = 6,
    Lam = 7,
    Forall = 8,
    LetE = 9,
    LitNat = 10,
    LitStr = 11,
    MData = 12,
    Proj = 13,
    ProjBig = 14,
}

const BINDER_INFO_SHIFT: u32 = 4;
const NON_DEP_BIT: u32 = 6;

fn binder_info_bits(bi: BinderInfo) -> u8 {
    match bi {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

fn binder_info_of_bits(byte: u8) -> BinderInfo {
    match (byte >> BINDER_INFO_SHIFT) & 0b11 {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        _ => BinderInfo::InstImplicit,
    }
}

fn non_dep_of_bits(byte: u8) -> bool {
    (byte >> NON_DEP_BIT) & 1 == 1
}

/// Pack a row's `Tag` + `BinderInfo` + `non_dep` into one byte (spec
/// §1: bits 0-3 tag, bits 4-5 `BinderInfo`, bit 6 `non_dep`). Only
/// `Lam`/`Forall` rows carry a non-default `BinderInfo`; only `LetE`
/// rows carry `non_dep` — every other constructor passes the defaults,
/// so the unused bits are always zero and never collide with the tag.
fn pack_tag(tag: Tag, binder_info: BinderInfo, non_dep: bool) -> u8 {
    (tag as u8)
        | (binder_info_bits(binder_info) << BINDER_INFO_SHIFT)
        | ((non_dep as u8) << NON_DEP_BIT)
}

/// Decode the low 4 bits back into a `Tag`. Rows are only ever produced
/// by this module's own intern methods (never decoded straight from
/// untrusted bytes), so an out-of-range nibble is an internal-invariant
/// violation, not attacker-triggerable — a panic here is the sanctioned
/// `expect`-style posture the brief allows for "minted by us" data.
fn tag_of(byte: u8) -> Tag {
    match byte & 0x0F {
        0 => Tag::BVar,
        1 => Tag::BVarBig,
        2 => Tag::FVar,
        3 => Tag::MVar,
        4 => Tag::Sort,
        5 => Tag::Const,
        6 => Tag::App,
        7 => Tag::Lam,
        8 => Tag::Forall,
        9 => Tag::LetE,
        10 => Tag::LitNat,
        11 => Tag::LitStr,
        12 => Tag::MData,
        13 => Tag::Proj,
        14 => Tag::ProjBig,
        _ => unreachable!("tag bytes are only ever produced by this module's pack_tag"),
    }
}

/// `idx` as an inline `u32` when it fits (bvar/proj's inline fast path),
/// `None` when it needs a pooled `NatId` instead. Mirrors
/// `nat_lossy_u64`'s digit inspection but demands an *exact* fit.
fn nat_as_u32(n: &Nat) -> Option<u32> {
    let digits = n.0.to_u64_digits();
    match digits.len() {
        0 => Some(0),
        1 => u32::try_from(digits[0]).ok(),
        _ => None,
    }
}

/// Reassemble `ExprData`'s packed word from its public accessors, in
/// the exact bit layout `ExprData::pack` documents (hash: bits 0-31,
/// approxDepth: 32-39, hasFVar/hasExprMVar/hasLevelMVar/hasLevelParam:
/// bits 40-43, looseBVarRange: bits 44-63). `ExprData` itself never
/// exposes its raw `u64` (the brief's expr.rs edits are visibility-only,
/// no new accessor), so this reconstructs the same word purely from the
/// 7 already-public getters — round-tripping through `data_of_word`
/// below (via `ExprData::pack` again) reproduces a bit-identical
/// `ExprData`, since those 7 values are its entire content.
fn word_of(d: ExprData) -> u64 {
    let mut w = d.hash() as u64;
    w |= (d.approx_depth() as u64) << 32;
    if d.has_fvar() {
        w |= 1 << 40;
    }
    if d.has_expr_mvar() {
        w |= 1 << 41;
    }
    if d.has_level_mvar() {
        w |= 1 << 42;
    }
    if d.has_level_param() {
        w |= 1 << 43;
    }
    w |= (d.loose_bvar_range() as u64) << 44;
    w
}

/// Inverse of `word_of`: decode the 7 fields back out of the stored
/// word and hand them to `ExprData::pack`, which reproduces the
/// identical `ExprData` (pack is a pure function of exactly these 7
/// values).
fn data_of_word(w: u64) -> ExprData {
    let hash = w & 0xFFFF_FFFF;
    let depth = ((w >> 32) & 0xFF) as u8;
    let has_fvar = (w >> 40) & 1 == 1;
    let has_expr_mvar = (w >> 41) & 1 == 1;
    let has_level_mvar = (w >> 42) & 1 == 1;
    let has_level_param = (w >> 43) & 1 == 1;
    let range = (w >> 44) as u32;
    ExprData::pack(
        hash,
        range,
        depth,
        has_fvar,
        has_expr_mvar,
        has_level_mvar,
        has_level_param,
    )
}

/// Struct-of-arrays expression rows (spec §1): 21 B/row (1 tag byte + 3
/// `u32` + 1 `u64`) plus the probe table. Every row is either an inline
/// scalar or an id into a deduplicated pool, so `(tagbyte, a, b, c)`
/// alone is a complete identity — see `lookup` below.
pub struct TermBank {
    tags: Vec<u8>,
    a: Vec<u32>,
    b: Vec<u32>,
    c: Vec<u32>,
    data: Vec<u64>,
    table: IdTable,
    region: u32,
}

impl TermBank {
    pub fn new(region: u32) -> TermBank {
        TermBank {
            tags: Vec::new(),
            a: Vec::new(),
            b: Vec::new(),
            c: Vec::new(),
            data: Vec::new(),
            table: IdTable::new(),
            region,
        }
    }

    pub fn len(&self) -> usize {
        self.tags.len()
    }

    pub fn is_empty(&self) -> bool {
        self.tags.is_empty()
    }

    pub fn tag_byte(&self, index: usize) -> u8 {
        self.tags[index]
    }

    pub fn abc(&self, index: usize) -> (u32, u32, u32) {
        (self.a[index], self.b[index], self.c[index])
    }

    pub fn data_word(&self, index: usize) -> u64 {
        self.data[index]
    }

    /// Row equality for the probe: same packed tag byte AND same `a, b,
    /// c` (spec §1 invariant — complete because every field is an id
    /// into a deduplicated pool or an inline scalar).
    pub fn lookup(&self, hash: u64, tagbyte: u8, a: u32, b: u32, c: u32) -> Option<u32> {
        self.table.lookup(hash, |bits| {
            let i = ((bits & !super::REGION_BIT) - 1) as usize;
            self.tags[i] == tagbyte && self.a[i] == a && self.b[i] == b && self.c[i] == c
        })
    }

    pub(crate) fn insert(
        &mut self,
        hash: u64,
        tagbyte: u8,
        a: u32,
        b: u32,
        c: u32,
        data: u64,
    ) -> Result<u32, KernelError> {
        let index = u32::try_from(self.tags.len()).map_err(|_| KernelError::BankExhausted)?;
        if index > MAX_INDEX {
            return Err(KernelError::BankExhausted);
        }
        self.tags.push(tagbyte);
        self.a.push(a);
        self.b.push(b);
        self.c.push(c);
        self.data.push(data);
        let bits = (index + 1) | self.region;
        let (tags, aa, bb, cc, dd) = (&self.tags, &self.a, &self.b, &self.c, &self.data);
        self.table.insert(hash, bits, |bt| {
            let i = ((bt & !super::REGION_BIT) - 1) as usize;
            let row_hash = mix(
                tags[i] as u64,
                mix(aa[i] as u64, mix(bb[i] as u64, cc[i] as u64)),
            );
            mix(row_hash, dd[i])
        });
        Ok(bits)
    }
}

/// Decoded view of one `TermBank` row (mirrors `ExprNode` one level
/// down: every recursive child is an id, not an `Arc`). Fully `Copy` —
/// every field is either a plain scalar or an id newtype.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Node {
    BVar {
        idx: u32,
    },
    BVarBig {
        idx: NatId,
    },
    FVar {
        id: Option<NameId>,
    },
    MVar {
        id: Option<NameId>,
    },
    Sort {
        level: LevelId,
    },
    Const {
        name: Option<NameId>,
        levels: LevelsId,
    },
    App {
        f: ExprId,
        arg: ExprId,
    },
    Lam {
        binder_name: Option<NameId>,
        binder_type: ExprId,
        body: ExprId,
        binder_info: BinderInfo,
    },
    Forall {
        binder_name: Option<NameId>,
        binder_type: ExprId,
        body: ExprId,
        binder_info: BinderInfo,
    },
    LetE {
        decl_name: Option<NameId>,
        ty: ExprId,
        value: ExprId,
        body: ExprId,
        non_dep: bool,
    },
    LitNat {
        v: NatId,
    },
    LitStr {
        v: StrId,
    },
    MData {
        data: KVMapId,
        expr: ExprId,
    },
    Proj {
        type_name: Option<NameId>,
        idx: u32,
        structure: ExprId,
    },
    ProjBig {
        type_name: Option<NameId>,
        idx: NatId,
        structure: ExprId,
    },
}

impl Store {
    /// Base lookup → own lookup → append+insert, exactly like
    /// `NameBank`/`LevelBank`'s `*_intern_row` helpers. The table hash
    /// extends the row-content hash with the `data` word (Step 3
    /// formulation): `mix(tagbyte, mix(a, mix(b, c)))` then
    /// `mix(row_hash, word)` — never `data` alone, since `combine_binder`
    /// makes `Lam`/`Forall` share a data word (only the tag byte, folded
    /// into `row_hash`, disambiguates them).
    fn term_intern_row(
        &mut self,
        base: Option<&Store>,
        tagbyte: u8,
        a: u32,
        b: u32,
        c: u32,
        word: u64,
    ) -> Result<ExprId, KernelError> {
        let row_hash = mix(tagbyte as u64, mix(a as u64, mix(b as u64, c as u64)));
        let hash = mix(row_hash, word);
        if let Some(base_store) = base {
            if let Some(bits) = base_store.terms.lookup(hash, tagbyte, a, b, c) {
                return ExprId::from_bits(bits).ok_or(KernelError::BankExhausted);
            }
        }
        if let Some(bits) = self.terms.lookup(hash, tagbyte, a, b, c) {
            return ExprId::from_bits(bits).ok_or(KernelError::BankExhausted);
        }
        let bits = self.terms.insert(hash, tagbyte, a, b, c, word)?;
        ExprId::from_bits(bits).ok_or(KernelError::BankExhausted)
    }

    /// oracle: `Expr.bvar` (see `Expr::bvar`, expr.rs) — byte-identical
    /// `ExprData` for level-free terms. Inline `u32` index when it fits
    /// (tag `BVar`), else a pooled `NatId` (tag `BVarBig`).
    pub fn expr_bvar(&mut self, base: Option<&Store>, idx: &Nat) -> Result<ExprId, KernelError> {
        let range = bvar_loose_range(idx);
        let h = mix(TAG_BVAR, nat_lossy_u64(idx));
        let data = ExprData::pack(h, range, 1, false, false, false, false);
        let (tag, a) = match nat_as_u32(idx) {
            Some(v) => (Tag::BVar, v),
            None => {
                let id = self.intern_nat(base, idx)?;
                (Tag::BVarBig, id.bits())
            }
        };
        let tagbyte = pack_tag(tag, BinderInfo::Default, false);
        self.term_intern_row(base, tagbyte, a, 0, 0, word_of(data))
    }

    /// oracle: `Expr.fvar`.
    pub fn expr_fvar(
        &mut self,
        base: Option<&Store>,
        name: Option<NameId>,
    ) -> Result<ExprId, KernelError> {
        let nh = self.name_hash_of(base, name);
        let h = mix(TAG_FVAR, nh);
        let data = ExprData::pack(h, 0, 1, true, false, false, false);
        let a = name.map_or(0, |n| n.bits());
        let tagbyte = pack_tag(Tag::FVar, BinderInfo::Default, false);
        self.term_intern_row(base, tagbyte, a, 0, 0, word_of(data))
    }

    /// oracle: `Expr.mvar`.
    pub fn expr_mvar(
        &mut self,
        base: Option<&Store>,
        name: Option<NameId>,
    ) -> Result<ExprId, KernelError> {
        let nh = self.name_hash_of(base, name);
        let h = mix(TAG_MVAR, nh);
        let data = ExprData::pack(h, 0, 1, false, true, false, false);
        let a = name.map_or(0, |n| n.bits());
        let tagbyte = pack_tag(Tag::MVar, BinderInfo::Default, false);
        self.term_intern_row(base, tagbyte, a, 0, 0, word_of(data))
    }

    /// oracle: `Expr.sort`. O(1), no `RecGuard`: the level walk is
    /// already amortized into `LevelBank`'s cached hash/flags.
    pub fn expr_sort(
        &mut self,
        base: Option<&Store>,
        level: LevelId,
    ) -> Result<ExprId, KernelError> {
        let lh = self.level_hash(base, level);
        let flags = self.level_flags(base, level);
        let has_param = flags & 0b01 != 0;
        let has_mvar = flags & 0b10 != 0;
        let h = mix(TAG_SORT, lh);
        let data = ExprData::pack(h, 0, 1, false, false, has_mvar, has_param);
        let tagbyte = pack_tag(Tag::Sort, BinderInfo::Default, false);
        self.term_intern_row(base, tagbyte, level.bits(), 0, 0, word_of(data))
    }

    /// oracle: `Expr.const_`. Folds the pooled level list's hashes/flags
    /// (list already lives in `level_lists`; O(len), no `RecGuard`).
    pub fn expr_const(
        &mut self,
        base: Option<&Store>,
        name: Option<NameId>,
        levels: LevelsId,
    ) -> Result<ExprId, KernelError> {
        let mut has_mvar = false;
        let mut has_param = false;
        let mut levels_hash: u64 = 0;
        for &l in self.level_list_at(base, levels) {
            let flags = self.level_flags(base, l);
            has_param |= flags & 0b01 != 0;
            has_mvar |= flags & 0b10 != 0;
            levels_hash = mix(levels_hash, self.level_hash(base, l));
        }
        let nh = self.name_hash_of(base, name);
        let h = mix(TAG_CONST, mix(nh, levels_hash));
        let data = ExprData::pack(h, 0, 1, false, false, has_mvar, has_param);
        let a = name.map_or(0, |n| n.bits());
        let tagbyte = pack_tag(Tag::Const, BinderInfo::Default, false);
        self.term_intern_row(base, tagbyte, a, levels.bits(), 0, word_of(data))
    }

    /// oracle: `Expr.app` (`combine_app`).
    pub fn expr_app(
        &mut self,
        base: Option<&Store>,
        f: ExprId,
        arg: ExprId,
    ) -> Result<ExprId, KernelError> {
        let fd = self.expr_data(base, f);
        let ad = self.expr_data(base, arg);
        let data = combine_app(fd, ad);
        let tagbyte = pack_tag(Tag::App, BinderInfo::Default, false);
        self.term_intern_row(base, tagbyte, f.bits(), arg.bits(), 0, word_of(data))
    }

    /// oracle: `Expr.lam` (`combine_binder`).
    pub fn expr_lam(
        &mut self,
        base: Option<&Store>,
        binder_name: Option<NameId>,
        binder_type: ExprId,
        body: ExprId,
        binder_info: BinderInfo,
    ) -> Result<ExprId, KernelError> {
        let td = self.expr_data(base, binder_type);
        let bd = self.expr_data(base, body);
        let data = combine_binder(td, bd);
        let c = binder_name.map_or(0, |n| n.bits());
        let tagbyte = pack_tag(Tag::Lam, binder_info, false);
        self.term_intern_row(
            base,
            tagbyte,
            binder_type.bits(),
            body.bits(),
            c,
            word_of(data),
        )
    }

    /// oracle: `Expr.forall_e` (`combine_binder`). Same recurrence as
    /// `expr_lam`; only the tag byte differs, which is exactly what
    /// keeps the two from colliding in the probe.
    pub fn expr_forall(
        &mut self,
        base: Option<&Store>,
        binder_name: Option<NameId>,
        binder_type: ExprId,
        body: ExprId,
        binder_info: BinderInfo,
    ) -> Result<ExprId, KernelError> {
        let td = self.expr_data(base, binder_type);
        let bd = self.expr_data(base, body);
        let data = combine_binder(td, bd);
        let c = binder_name.map_or(0, |n| n.bits());
        let tagbyte = pack_tag(Tag::Forall, binder_info, false);
        self.term_intern_row(
            base,
            tagbyte,
            binder_type.bits(),
            body.bits(),
            c,
            word_of(data),
        )
    }

    /// oracle: `Expr.let_e` (`combine_let`). Row: `a = ty, b = value, c
    /// = spill(decl_name, body)` (Task 5's deduplicated spill pool) —
    /// `LetE` has one more child than the 3 row slots hold, so
    /// `decl_name`/`body` share a pooled spill row.
    pub fn expr_let(
        &mut self,
        base: Option<&Store>,
        decl_name: Option<NameId>,
        ty: ExprId,
        value: ExprId,
        body: ExprId,
        non_dep: bool,
    ) -> Result<ExprId, KernelError> {
        let td = self.expr_data(base, ty);
        let vd = self.expr_data(base, value);
        let bd = self.expr_data(base, body);
        let data = combine_let(td, vd, bd);
        let spill = self.intern_spill(base, decl_name, body.bits())?;
        let tagbyte = pack_tag(Tag::LetE, BinderInfo::Default, non_dep);
        self.term_intern_row(
            base,
            tagbyte,
            ty.bits(),
            value.bits(),
            spill.bits(),
            word_of(data),
        )
    }

    /// oracle: `Expr.lit(Literal::NatVal(_))`. Builds the `Literal`
    /// transiently so `literal_hash` matches expr.rs's convention.
    pub fn expr_lit_nat(&mut self, base: Option<&Store>, n: &Nat) -> Result<ExprId, KernelError> {
        let id = self.intern_nat(base, n)?;
        let lit = Literal::NatVal(n.clone());
        let h = mix(TAG_LIT, literal_hash(&lit));
        let data = ExprData::pack(h, 0, 1, false, false, false, false);
        let tagbyte = pack_tag(Tag::LitNat, BinderInfo::Default, false);
        self.term_intern_row(base, tagbyte, id.bits(), 0, 0, word_of(data))
    }

    /// oracle: `Expr.lit(Literal::StrVal(_))`.
    pub fn expr_lit_str(&mut self, base: Option<&Store>, s: &str) -> Result<ExprId, KernelError> {
        let id = self.intern_str(base, s)?;
        let lit = Literal::StrVal(s.to_string());
        let h = mix(TAG_LIT, literal_hash(&lit));
        let data = ExprData::pack(h, 0, 1, false, false, false, false);
        let tagbyte = pack_tag(Tag::LitStr, BinderInfo::Default, false);
        self.term_intern_row(base, tagbyte, id.bits(), 0, 0, word_of(data))
    }

    /// oracle: `Expr.mdata`.
    pub fn expr_mdata(
        &mut self,
        base: Option<&Store>,
        data_id: KVMapId,
        child: ExprId,
    ) -> Result<ExprId, KernelError> {
        let cd = self.expr_data(base, child);
        let depth = depth_of(cd.approx_depth());
        let h = mix(depth as u64, cd.hash() as u64);
        let out = ExprData::pack(
            h,
            cd.loose_bvar_range(),
            depth,
            cd.has_fvar(),
            cd.has_expr_mvar(),
            cd.has_level_mvar(),
            cd.has_level_param(),
        );
        let tagbyte = pack_tag(Tag::MData, BinderInfo::Default, false);
        self.term_intern_row(base, tagbyte, data_id.bits(), child.bits(), 0, word_of(out))
    }

    /// oracle: `Expr.proj`. Inline `u32` index when it fits (tag
    /// `Proj`), else a pooled `NatId` (tag `ProjBig`).
    pub fn expr_proj(
        &mut self,
        base: Option<&Store>,
        type_name: Option<NameId>,
        idx: &Nat,
        structure: ExprId,
    ) -> Result<ExprId, KernelError> {
        let cd = self.expr_data(base, structure);
        let depth = depth_of(cd.approx_depth());
        let nh = self.name_hash_of(base, type_name);
        let ih = nat_lossy_u64(idx);
        let h = mix(depth as u64, mix(nh, mix(ih, cd.hash() as u64)));
        let out = ExprData::pack(
            h,
            cd.loose_bvar_range(),
            depth,
            cd.has_fvar(),
            cd.has_expr_mvar(),
            cd.has_level_mvar(),
            cd.has_level_param(),
        );
        let a = type_name.map_or(0, |n| n.bits());
        match nat_as_u32(idx) {
            Some(v) => {
                let tagbyte = pack_tag(Tag::Proj, BinderInfo::Default, false);
                self.term_intern_row(base, tagbyte, a, v, structure.bits(), word_of(out))
            }
            None => {
                let id = self.intern_nat(base, idx)?;
                let tagbyte = pack_tag(Tag::ProjBig, BinderInfo::Default, false);
                self.term_intern_row(base, tagbyte, a, id.bits(), structure.bits(), word_of(out))
            }
        }
    }

    /// Decode a row into its `Node` view.
    pub fn expr_node(&self, base: Option<&Store>, id: ExprId) -> Node {
        let store = self.store_for(base, id.is_scratch());
        let i = id.index();
        let tagbyte = store.terms.tag_byte(i);
        let (a, b, c) = store.terms.abc(i);
        match tag_of(tagbyte) {
            Tag::BVar => Node::BVar { idx: a },
            Tag::BVarBig => Node::BVarBig {
                idx: NatId::from_bits(a).expect("NatId minted by intern ⇒ valid"),
            },
            Tag::FVar => Node::FVar {
                id: NameId::from_bits(a),
            },
            Tag::MVar => Node::MVar {
                id: NameId::from_bits(a),
            },
            Tag::Sort => Node::Sort {
                level: LevelId::from_bits(a).expect("LevelId minted by intern ⇒ valid"),
            },
            Tag::Const => Node::Const {
                name: NameId::from_bits(a),
                levels: LevelsId::from_bits(b).expect("LevelsId minted by intern ⇒ valid"),
            },
            Tag::App => Node::App {
                f: ExprId::from_bits(a).expect("ExprId minted by intern ⇒ valid"),
                arg: ExprId::from_bits(b).expect("ExprId minted by intern ⇒ valid"),
            },
            Tag::Lam => Node::Lam {
                binder_name: NameId::from_bits(c),
                binder_type: ExprId::from_bits(a).expect("ExprId minted by intern ⇒ valid"),
                body: ExprId::from_bits(b).expect("ExprId minted by intern ⇒ valid"),
                binder_info: binder_info_of_bits(tagbyte),
            },
            Tag::Forall => Node::Forall {
                binder_name: NameId::from_bits(c),
                binder_type: ExprId::from_bits(a).expect("ExprId minted by intern ⇒ valid"),
                body: ExprId::from_bits(b).expect("ExprId minted by intern ⇒ valid"),
                binder_info: binder_info_of_bits(tagbyte),
            },
            Tag::LetE => {
                let spill_id = SpillId::from_bits(c).expect("SpillId minted by intern ⇒ valid");
                let spill = self.spill_at(base, spill_id);
                Node::LetE {
                    decl_name: spill.name,
                    ty: ExprId::from_bits(a).expect("ExprId minted by intern ⇒ valid"),
                    value: ExprId::from_bits(b).expect("ExprId minted by intern ⇒ valid"),
                    body: ExprId::from_bits(spill.body_or_aux)
                        .expect("ExprId minted by intern ⇒ valid"),
                    non_dep: non_dep_of_bits(tagbyte),
                }
            }
            Tag::LitNat => Node::LitNat {
                v: NatId::from_bits(a).expect("NatId minted by intern ⇒ valid"),
            },
            Tag::LitStr => Node::LitStr {
                v: StrId::from_bits(a).expect("StrId minted by intern ⇒ valid"),
            },
            Tag::MData => Node::MData {
                data: KVMapId::from_bits(a).expect("KVMapId minted by intern ⇒ valid"),
                expr: ExprId::from_bits(b).expect("ExprId minted by intern ⇒ valid"),
            },
            Tag::Proj => Node::Proj {
                type_name: NameId::from_bits(a),
                idx: b,
                structure: ExprId::from_bits(c).expect("ExprId minted by intern ⇒ valid"),
            },
            Tag::ProjBig => Node::ProjBig {
                type_name: NameId::from_bits(a),
                idx: NatId::from_bits(b).expect("NatId minted by intern ⇒ valid"),
                structure: ExprId::from_bits(c).expect("ExprId minted by intern ⇒ valid"),
            },
        }
    }

    /// Decode a row's cached `ExprData` word.
    pub fn expr_data(&self, base: Option<&Store>, id: ExprId) -> ExprData {
        let store = self.store_for(base, id.is_scratch());
        data_of_word(store.terms.data_word(id.index()))
    }
}

#[cfg(test)]
mod tests {
    use crate::bank::Store;
    use crate::{BinderInfo, Expr, Nat};
    use std::sync::Arc;

    #[test]
    fn app_dedups_and_children_route() {
        let mut s = Store::persistent();
        let n = s.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let a1 = s.expr_app(None, n, n).unwrap();
        let a2 = s.expr_app(None, n, n).unwrap();
        assert_eq!(a1, a2);
        match s.expr_node(None, a1) {
            crate::bank::terms::Node::App { f, arg } => {
                assert_eq!(f, n);
                assert_eq!(arg, n);
            }
            other => panic!("expected App, got {other:?}"),
        }
    }

    #[test]
    fn lam_and_forall_do_not_collide() {
        let mut s = Store::persistent();
        let t = s.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let b = s.expr_bvar(None, &Nat::from(1u64)).unwrap();
        let lam = s.expr_lam(None, None, t, b, BinderInfo::Default).unwrap();
        let pi = s
            .expr_forall(None, None, t, b, BinderInfo::Default)
            .unwrap();
        assert_ne!(lam, pi);
    }

    #[test]
    fn binder_info_distinguishes_rows() {
        let mut s = Store::persistent();
        let t = s.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let b = s.expr_bvar(None, &Nat::from(1u64)).unwrap();
        let d = s.expr_lam(None, None, t, b, BinderInfo::Default).unwrap();
        let i = s.expr_lam(None, None, t, b, BinderInfo::Implicit).unwrap();
        assert_ne!(d, i);
    }

    #[test]
    fn data_word_matches_smart_constructor_for_level_free_terms() {
        // bvar/app/lam carry no levels, so even the hash halves must match
        // expr.rs exactly (same mix, same recurrences).
        let mut s = Store::persistent();
        let bank_bvar = s.expr_bvar(None, &Nat::from(3u64)).unwrap();
        let arc_bvar = Expr::bvar(Nat::from(3u64));
        assert_eq!(s.expr_data(None, bank_bvar), arc_bvar.data());
        let bank_app = s.expr_app(None, bank_bvar, bank_bvar).unwrap();
        let arc_app = Expr::app(Arc::clone(&arc_bvar), arc_bvar);
        assert_eq!(s.expr_data(None, bank_app), arc_app.data());
    }

    #[test]
    fn big_bvar_index_pools() {
        let mut s = Store::persistent();
        let big = Nat(num_bigint::BigUint::from(u64::MAX) * 4u32);
        let a = s.expr_bvar(None, &big).unwrap();
        let b = s.expr_bvar(None, &big).unwrap();
        assert_eq!(a, b);
        match s.expr_node(None, a) {
            crate::bank::terms::Node::BVarBig { idx } => {
                assert_eq!(s.nat_at(None, idx), &big);
            }
            other => panic!("expected BVarBig, got {other:?}"),
        }
    }

    #[test]
    fn lete_spill_roundtrips() {
        let mut s = Store::persistent();
        let t = s.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let l1 = s.expr_let(None, None, t, t, t, false).unwrap();
        let l2 = s.expr_let(None, None, t, t, t, false).unwrap();
        let l3 = s.expr_let(None, None, t, t, t, true).unwrap();
        assert_eq!(l1, l2);
        assert_ne!(l1, l3); // non_dep is part of identity
        match s.expr_node(None, l1) {
            crate::bank::terms::Node::LetE {
                ty,
                value,
                body,
                non_dep,
                ..
            } => {
                assert_eq!((ty, value, body, non_dep), (t, t, t, false));
            }
            other => panic!("expected LetE, got {other:?}"),
        }
    }

    #[test]
    fn sort_flags_come_from_level_bank() {
        let mut s = Store::persistent();
        let u = {
            let n = s.intern_str(None, "u").unwrap();
            let n = s.name_str(None, None, n).unwrap();
            s.level_param(None, Some(n)).unwrap()
        };
        let srt = s.expr_sort(None, u).unwrap();
        let d = s.expr_data(None, srt);
        assert!(d.has_level_param());
        assert!(!d.has_level_mvar());
        assert_eq!(d.loose_bvar_range(), 0);
    }
}
