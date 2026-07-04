//! Phase A of `.olean` decoding: walk the compacted object region into
//! a validated, offset-memoized [`RawValue`] DAG.
//!
//! This module is the ENTIRE untrusted-bytes surface of leanr_olean
//! (docs/THREAT_MODEL.md): every pointer is bounds- and
//! alignment-checked, every tag matched against what the oracle's
//! compactor can emit, cycles are detected, and both the walk and
//! `RawValue`'s `Drop` are iterative so adversarial nesting cannot
//! overflow the stack. Phase B (`interp`) consumes the DAG and never
//! touches raw bytes.
//!
//! Region model (oracle at v4.32.0-rc1 — src/library/module.cpp:107-144
//! v2 write path :317-343; src/runtime/compact.cpp:479-517 root slot,
//! :163-166 8-byte alignment, :183-198 max-sharing):
//! file = [88-byte header][8-byte root pointer word][objects...].
//! Pointer words are `base_addr`-relative addresses of the file start;
//! odd words are boxed scalars (lean.h:324-326).

use std::collections::HashMap;
use std::mem;
use std::sync::Arc;

use num_bigint::{BigInt, BigUint, Sign};

use crate::{OleanError, OleanHeader, HEADER_LEN};

/// File offset of the root pointer word (compact.cpp:483-489: the
/// compactor allocates the root slot before any object).
const ROOT_PTR_OFFSET: u64 = HEADER_LEN as u64;
/// First possible object offset: right after the root slot.
const FIRST_OBJECT_OFFSET: u64 = ROOT_PTR_OFFSET + 8;
/// The compactor's internal null sentinel (compact.cpp:156-161);
/// never valid in a written file.
const NULL_SENTINEL: u64 = u64::MAX - 1;

// Non-constructor tags, lean.h:92-104.
const TAG_PROMISE: u8 = 244;
const TAG_CLOSURE: u8 = 245;
const TAG_ARRAY: u8 = 246;
const TAG_STRUCT_ARRAY: u8 = 247;
const TAG_SCALAR_ARRAY: u8 = 248;
const TAG_STRING: u8 = 249;
const TAG_MPZ: u8 = 250;
const TAG_THUNK: u8 = 251;
const TAG_TASK: u8 = 252;
const TAG_REF: u8 = 253;

/// A decoded object graph node. Owned, `Arc`-shared exactly where the
/// file shared offsets. `Indirect` wraps thunk/task/ref/promise value
/// cells (compact.cpp insert_thunk/insert_task/insert_promise/
/// insert_ref: single compacted value at byte offset 8).
///
/// Deviation from the plan's verbatim code (Tasks 1-2 review): `Debug`
/// is NOT derived. A derived impl would recurse into `Arc<RawValue>`
/// children with the graph's depth, and `deep_graphs_decode_and_drop_iteratively`
/// below builds 200k-deep graphs — a derived Debug would stack-overflow
/// on exactly the adversarial input this decoder exists to survive. The
/// manual impl below prints the variant name and flat fields only,
/// rendering child `Arc<RawValue>`s as `..` placeholders; it never
/// recurses into them (same pattern as `leanr_kernel::expr::Expr`).
pub(crate) enum RawValue {
    Scalar(u64),
    Ctor {
        tag: u8,
        fields: Vec<Arc<RawValue>>,
        scalars: Vec<u8>,
    },
    Array(Vec<Arc<RawValue>>),
    ScalarArray {
        elem_size: u8,
        data: Vec<u8>,
    },
    Str(String),
    BigInt(BigInt),
    Indirect(Arc<RawValue>),
}

/// Manual (non-derived) impl: flat, non-recursive formatting so it stays
/// safe on adversarially deep chains (see the invariant note on `RawValue`).
impl std::fmt::Debug for RawValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RawValue::Scalar(v) => write!(f, "RawValue::Scalar({v})"),
            RawValue::Ctor {
                tag,
                fields,
                scalars,
            } => write!(
                f,
                "RawValue::Ctor {{ tag: {tag}, fields: [{} ..], scalars: {scalars:?} }}",
                fields.len()
            ),
            RawValue::Array(elems) => write!(f, "RawValue::Array([{} ..])", elems.len()),
            RawValue::ScalarArray { elem_size, data } => write!(
                f,
                "RawValue::ScalarArray {{ elem_size: {elem_size}, data: [{} bytes] }}",
                data.len()
            ),
            RawValue::Str(s) => write!(f, "RawValue::Str({s:?})"),
            RawValue::BigInt(i) => write!(f, "RawValue::BigInt({i})"),
            RawValue::Indirect(_) => f.write_str("RawValue::Indirect(..)"),
        }
    }
}

impl Drop for RawValue {
    fn drop(&mut self) {
        // Adversarial nesting depth: unwind with an explicit stack.
        let mut stack: Vec<Arc<RawValue>> = Vec::new();
        take_raw_children(self, &mut stack);
        while let Some(node) = stack.pop() {
            if let Ok(mut owned) = Arc::try_unwrap(node) {
                take_raw_children(&mut owned, &mut stack);
            }
        }
    }
}

fn take_raw_children(v: &mut RawValue, stack: &mut Vec<Arc<RawValue>>) {
    match v {
        RawValue::Scalar(_)
        | RawValue::ScalarArray { .. }
        | RawValue::Str(_)
        | RawValue::BigInt(_) => {}
        RawValue::Ctor { fields, .. } => stack.append(fields),
        RawValue::Array(elems) => stack.append(elems),
        RawValue::Indirect(inner) => {
            stack.push(mem::replace(inner, Arc::new(RawValue::Scalar(0))));
        }
    }
}

/// Parse a whole `.olean` file into its root value (phase A entry;
/// Task 6's `ModuleData::parse` is the public wrapper).
pub(crate) fn parse_bytes(bytes: &[u8]) -> Result<Arc<RawValue>, OleanError> {
    let header = OleanHeader::parse(bytes)?;
    // v3 moves the object data (module.cpp:133-140); everything this
    // decoder assumes below is the v2 layout.
    if header.version != 2 {
        return Err(OleanError::UnsupportedVersion(header.version));
    }
    let region = Region {
        bytes,
        base_addr: header.base_addr,
        // flags bit 0: GMP vs Lean-native bignum encoding (module.cpp:114-122).
        gmp: header.flags & 1 == 1,
    };
    match region.resolve(region.word(ROOT_PTR_OFFSET)?)? {
        Word::Scalar(v) => Ok(Arc::new(RawValue::Scalar(v))),
        Word::ObjectAt(off) => decode_graph(&region, off),
    }
}

struct Region<'a> {
    bytes: &'a [u8],
    base_addr: u64,
    gmp: bool,
}

enum Word {
    Scalar(u64),
    ObjectAt(u64),
}

impl Region<'_> {
    fn len(&self) -> u64 {
        self.bytes.len() as u64
    }

    fn slice(&self, off: u64, len: u64) -> Result<&[u8], OleanError> {
        let end = off
            .checked_add(len)
            .ok_or(OleanError::OutOfBounds { offset: off })?;
        if end > self.len() {
            return Err(OleanError::OutOfBounds { offset: off });
        }
        Ok(&self.bytes[off as usize..end as usize])
    }

    fn word(&self, off: u64) -> Result<u64, OleanError> {
        Ok(u64::from_le_bytes(
            self.slice(off, 8)?.try_into().expect("8 bytes"),
        ))
    }

    fn u32(&self, off: u64) -> Result<u32, OleanError> {
        Ok(u32::from_le_bytes(
            self.slice(off, 4)?.try_into().expect("4 bytes"),
        ))
    }

    /// Classify a pointer word (lean.h:324-326; layout reference).
    fn resolve(&self, word: u64) -> Result<Word, OleanError> {
        if word & 1 == 1 {
            return Ok(Word::Scalar(word >> 1));
        }
        if word == NULL_SENTINEL {
            return Err(OleanError::BadPointer { word });
        }
        let off = word
            .checked_sub(self.base_addr)
            .ok_or(OleanError::BadPointer { word })?;
        if off < FIRST_OBJECT_OFFSET
            || off % 8 != 0
            || off.checked_add(8).is_none_or(|end| end > self.len())
        {
            return Err(OleanError::BadPointer { word });
        }
        Ok(Word::ObjectAt(off))
    }
}

/// One object's parsed shape: everything needed to (a) enumerate its
/// children and (b) build its `RawValue` once the children exist.
enum Shape {
    Ctor {
        tag: u8,
        field_words: Vec<u64>,
        scalars: Vec<u8>,
    },
    Array {
        elem_words: Vec<u64>,
    },
    ScalarArray {
        elem_size: u8,
        data: Vec<u8>,
    },
    Str(String),
    BigInt(BigInt),
    Indirect {
        value_word: u64,
    },
}

impl Shape {
    fn child_words(&self) -> &[u64] {
        match self {
            Shape::Ctor { field_words, .. } => field_words,
            Shape::Array { elem_words } => elem_words,
            Shape::Indirect { value_word } => std::slice::from_ref(value_word),
            _ => &[],
        }
    }
}

/// Read and validate the object at `off` (layout reference in the M1a
/// plan; object header lean.h:143-148, payloads lean.h:182-209).
///
/// Header word decode: `m_rc` is bytes 0-3, `m_cs_sz` bytes 4-5,
/// `m_other` byte 6, `m_tag` byte 7 (lean.h:143-148, little-endian) —
/// the shifts below implement exactly that.
fn read_object(region: &Region, off: u64) -> Result<Shape, OleanError> {
    let header = region.word(off)?;
    let rc = header as u32;
    let cs_sz = (header >> 32) as u16;
    let other = (header >> 48) as u8;
    let tag = (header >> 56) as u8;
    if rc != 0 {
        // lean_set_non_heap_header zeroes m_rc for every region object.
        return Err(OleanError::Malformed {
            offset: off,
            what: "nonzero refcount",
        });
    }
    match tag {
        TAG_ARRAY => {
            let size = region.word(off + 8)?;
            // Guard allocation: an honest size fits in the file.
            if size > (region.len() - off) / 8 {
                return Err(OleanError::Malformed {
                    offset: off,
                    what: "array size",
                });
            }
            let mut elem_words = Vec::with_capacity(size as usize);
            for i in 0..size {
                elem_words.push(region.word(off + 24 + 8 * i)?);
            }
            Ok(Shape::Array { elem_words })
        }
        TAG_SCALAR_ARRAY => {
            if !(1..=8).contains(&other) {
                return Err(OleanError::Malformed {
                    offset: off,
                    what: "sarray elem size",
                });
            }
            let size = region.word(off + 8)?;
            let byte_len = size
                .checked_mul(other as u64)
                .ok_or(OleanError::Malformed {
                    offset: off,
                    what: "sarray size",
                })?;
            Ok(Shape::ScalarArray {
                elem_size: other,
                data: region.slice(off + 24, byte_len)?.to_vec(),
            })
        }
        TAG_STRING => {
            let size = region.word(off + 8)?;
            if size == 0 {
                return Err(OleanError::Malformed {
                    offset: off,
                    what: "empty string object",
                });
            }
            let data = region.slice(off + 32, size)?;
            if data[data.len() - 1] != 0 {
                return Err(OleanError::Malformed {
                    offset: off,
                    what: "string missing NUL",
                });
            }
            let s = std::str::from_utf8(&data[..data.len() - 1]).map_err(|_| {
                OleanError::Malformed {
                    offset: off,
                    what: "string not UTF-8",
                }
            })?;
            Ok(Shape::Str(s.to_string()))
        }
        TAG_MPZ => {
            if !region.gmp {
                // module.cpp:114-122: flag bit 0 = 0 means Lean-native
                // limb encoding; every official build uses GMP. Revisit
                // only if the stdlib sweep ever hits this.
                return Err(OleanError::Unsupported {
                    what: "non-GMP bignum encoding",
                });
            }
            let alloc = region.u32(off + 8)? as i32;
            let mp_size = region.u32(off + 12)? as i32;
            let data_ptr = region.word(off + 16)?;
            let nlimbs = mp_size.unsigned_abs() as u64;
            // Avoid `mp_size.abs()`, which panics on `i32::MIN` for this
            // attacker-controlled value; compare magnitudes as `u64` instead
            // (alloc must equal |mp_size| and be non-negative).
            if nlimbs == 0 || alloc < 0 || alloc as u64 != nlimbs {
                return Err(OleanError::Malformed {
                    offset: off,
                    what: "mpz limb count",
                });
            }
            // insert_mpz (compact.cpp:407-421) always points _mp_d at
            // the limbs directly following the 24-byte mpz_object.
            // `off + 24` cannot overflow (off + 8 <= file len, a usize,
            // already checked by `resolve`/`region.word`), but
            // `base_addr` is attacker-controlled and may be near
            // `u64::MAX`, so the addition must be checked.
            if region.base_addr.checked_add(off + 24) != Some(data_ptr) {
                return Err(OleanError::Malformed {
                    offset: off,
                    what: "mpz data pointer",
                });
            }
            let limb_bytes = region.slice(off + 24, 8 * nlimbs)?;
            let magnitude = BigUint::from_bytes_le(limb_bytes);
            let sign = if mp_size < 0 { Sign::Minus } else { Sign::Plus };
            Ok(Shape::BigInt(BigInt::from_biguint(sign, magnitude)))
        }
        TAG_PROMISE | TAG_THUNK | TAG_TASK | TAG_REF => {
            // Value cell at byte offset 8 (compact.cpp fix_thunk et al.).
            Ok(Shape::Indirect {
                value_word: region.word(off + 8)?,
            })
        }
        TAG_CLOSURE => Err(OleanError::Unsupported {
            what: "closure (v3-only content)",
        }),
        TAG_STRUCT_ARRAY | 254 | 255 => Err(OleanError::BadTag { offset: off, tag }),
        _ => {
            // Constructor object: `other` = #pointer fields; cs_sz =
            // heap byte size (>= logical size; see layout reference —
            // minimum-length checks only).
            let num_fields = other as u64;
            let min_sz = 8 + 8 * num_fields;
            if (cs_sz as u64) < min_sz {
                return Err(OleanError::Malformed {
                    offset: off,
                    what: "ctor size",
                });
            }
            let mut field_words = Vec::with_capacity(num_fields as usize);
            for i in 0..num_fields {
                field_words.push(region.word(off + 8 + 8 * i)?);
            }
            let scalars = region.slice(off + min_sz, cs_sz as u64 - min_sz)?.to_vec();
            Ok(Shape::Ctor {
                tag,
                field_words,
                scalars,
            })
        }
    }
}

enum Slot {
    InProgress,
    Done(Arc<RawValue>),
}

/// Iterative post-order DFS with offset memoization. `InProgress` on
/// re-visit means the offset is on the current DFS path → cycle.
fn decode_graph(region: &Region, root_off: u64) -> Result<Arc<RawValue>, OleanError> {
    enum Step {
        Visit(u64),
        Build(u64, Shape),
    }
    let mut memo: HashMap<u64, Slot> = HashMap::new();
    let mut stack = vec![Step::Visit(root_off)];
    while let Some(step) = stack.pop() {
        match step {
            Step::Visit(off) => match memo.get(&off) {
                Some(Slot::Done(_)) => {}
                Some(Slot::InProgress) => return Err(OleanError::Cycle { offset: off }),
                None => {
                    memo.insert(off, Slot::InProgress);
                    let shape = read_object(region, off)?;
                    let children: Vec<u64> = shape.child_words().to_vec();
                    stack.push(Step::Build(off, shape));
                    for word in children {
                        if let Word::ObjectAt(child) = region.resolve(word)? {
                            stack.push(Step::Visit(child));
                        }
                    }
                }
            },
            Step::Build(off, shape) => {
                let resolve_child = |word: u64| -> Result<Arc<RawValue>, OleanError> {
                    match region.resolve(word)? {
                        Word::Scalar(v) => Ok(Arc::new(RawValue::Scalar(v))),
                        Word::ObjectAt(o) => match memo.get(&o) {
                            Some(Slot::Done(v)) => Ok(Arc::clone(v)),
                            // Post-order guarantees children are built;
                            // reaching this is a decoder bug, and the
                            // spec says internal errors panic loudly.
                            _ => unreachable!("child at {o:#x} not built before parent"),
                        },
                    }
                };
                let value = match shape {
                    Shape::Ctor {
                        tag,
                        field_words,
                        scalars,
                    } => RawValue::Ctor {
                        tag,
                        fields: field_words
                            .iter()
                            .map(|w| resolve_child(*w))
                            .collect::<Result<_, _>>()?,
                        scalars,
                    },
                    Shape::Array { elem_words } => RawValue::Array(
                        elem_words
                            .iter()
                            .map(|w| resolve_child(*w))
                            .collect::<Result<_, _>>()?,
                    ),
                    Shape::ScalarArray { elem_size, data } => {
                        RawValue::ScalarArray { elem_size, data }
                    }
                    Shape::Str(s) => RawValue::Str(s),
                    Shape::BigInt(i) => RawValue::BigInt(i),
                    Shape::Indirect { value_word } => {
                        RawValue::Indirect(resolve_child(value_word)?)
                    }
                };
                memo.insert(off, Slot::Done(Arc::new(value)));
            }
        }
    }
    match memo.remove(&root_off) {
        Some(Slot::Done(v)) => Ok(v),
        _ => unreachable!("root not built by the DFS"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::OleanError;
    use proptest::prelude::*;

    /// Builds a syntactically valid v2 olean byte buffer around
    /// hand-placed objects (layout reference in the M1a plan).
    struct Builder {
        bytes: Vec<u8>,
    }

    const BASE: u64 = 0x7a0f_0000_0000;

    fn boxed(v: u64) -> u64 {
        (v << 1) | 1
    }

    impl Builder {
        fn new() -> Builder {
            let mut bytes = Vec::new();
            bytes.extend_from_slice(b"olean"); // marker
            bytes.push(2); // version
            bytes.push(1); // flags: GMP bignums
            bytes.extend_from_slice(&[0u8; 33]); // lean_version
            bytes.extend_from_slice(&[b'a'; 40]); // githash (hex)
            bytes.extend_from_slice(&BASE.to_le_bytes()); // base_addr
            bytes.extend_from_slice(&[0u8; 8]); // root slot (patched later)
            Builder { bytes }
        }

        fn set_root(&mut self, word: u64) {
            self.bytes[88..96].copy_from_slice(&word.to_le_bytes());
        }

        /// Hand-patch the header's `base_addr` field (offset 80..88), for
        /// tests that need a `base_addr` other than the fixed [`BASE`]
        /// (e.g. one near `u64::MAX` to probe overflow windows).
        fn set_base_addr(&mut self, addr: u64) {
            self.bytes[80..88].copy_from_slice(&addr.to_le_bytes());
        }

        fn align(&mut self) {
            while !self.bytes.len().is_multiple_of(8) {
                self.bytes.push(0);
            }
        }

        /// Emit an object header + body; returns the pointer word.
        fn object(&mut self, tag: u8, other: u8, cs_sz: u16, body: &[u8]) -> u64 {
            self.align();
            let off = self.bytes.len() as u64;
            self.bytes.extend_from_slice(&0u32.to_le_bytes()); // m_rc
            self.bytes.extend_from_slice(&cs_sz.to_le_bytes());
            self.bytes.push(other);
            self.bytes.push(tag);
            self.bytes.extend_from_slice(body);
            BASE + off
        }

        fn ctor(&mut self, tag: u8, fields: &[u64], scalars: &[u8]) -> u64 {
            let mut body = Vec::new();
            for f in fields {
                body.extend_from_slice(&f.to_le_bytes());
            }
            body.extend_from_slice(scalars);
            let cs_sz = (8 + body.len()) as u16;
            self.object(tag, fields.len() as u8, cs_sz, &body)
        }

        fn array(&mut self, elems: &[u64]) -> u64 {
            let mut body = Vec::new();
            body.extend_from_slice(&(elems.len() as u64).to_le_bytes()); // size
            body.extend_from_slice(&(elems.len() as u64).to_le_bytes()); // capacity
            for e in elems {
                body.extend_from_slice(&e.to_le_bytes());
            }
            self.object(246, 0, 1, &body)
        }

        fn string(&mut self, s: &str) -> u64 {
            let size = (s.len() + 1) as u64;
            let mut body = Vec::new();
            body.extend_from_slice(&size.to_le_bytes());
            body.extend_from_slice(&size.to_le_bytes()); // capacity
            body.extend_from_slice(&(s.chars().count() as u64).to_le_bytes());
            body.extend_from_slice(s.as_bytes());
            body.push(0);
            self.object(249, 0, 1, &body)
        }

        fn mpz(&mut self, limbs: &[u64], negative: bool) -> u64 {
            self.align();
            let off = self.bytes.len() as u64;
            let n = limbs.len() as i32;
            let mut body = Vec::new();
            body.extend_from_slice(&n.to_le_bytes()); // _mp_alloc
            body.extend_from_slice(&(if negative { -n } else { n }).to_le_bytes()); // _mp_size
            body.extend_from_slice(&(BASE + off + 24).to_le_bytes()); // _mp_d
            for l in limbs {
                body.extend_from_slice(&l.to_le_bytes());
            }
            self.object(250, 0, 24, &body)
        }

        /// Reserve a ctor whose field words get patched later (cycles).
        fn patch_field(&mut self, obj_word: u64, field_idx: usize, new_word: u64) {
            let off = (obj_word - BASE) as usize + 8 + field_idx * 8;
            self.bytes[off..off + 8].copy_from_slice(&new_word.to_le_bytes());
        }

        fn finish(self) -> Vec<u8> {
            self.bytes
        }
    }

    fn parse(b: Builder) -> Result<Arc<RawValue>, OleanError> {
        parse_bytes(&b.finish())
    }

    #[test]
    fn scalar_root() {
        let mut b = Builder::new();
        b.set_root(boxed(21));
        assert!(matches!(*parse(b).unwrap(), RawValue::Scalar(21)));
    }

    #[test]
    fn ctor_graph_preserves_sharing() {
        let mut b = Builder::new();
        let s = b.string("hi");
        let root = b.ctor(0, &[s, s], &[7]);
        b.set_root(root);
        let v = parse(b).unwrap();
        let RawValue::Ctor {
            tag: 0,
            fields,
            scalars,
        } = &*v
        else {
            panic!("expected ctor, got {v:?}")
        };
        assert_eq!(scalars, &[7]);
        assert!(
            Arc::ptr_eq(&fields[0], &fields[1]),
            "memo must dedupe shared offsets"
        );
        assert!(matches!(&*fields[0], RawValue::Str(s) if s == "hi"));
    }

    #[test]
    fn arrays_and_bignums_decode() {
        let mut b = Builder::new();
        let big = b.mpz(&[0, 1], false); // 2^64
        let arr = b.array(&[boxed(1), big]);
        b.set_root(arr);
        let v = parse(b).unwrap();
        let RawValue::Array(elems) = &*v else {
            panic!()
        };
        assert!(matches!(&*elems[0], RawValue::Scalar(1)));
        let RawValue::BigInt(i) = &*elems[1] else {
            panic!()
        };
        assert_eq!(*i, num_bigint::BigInt::from(2u128.pow(64)));
    }

    #[test]
    fn negative_mpz_keeps_its_sign() {
        let mut b = Builder::new();
        let big = b.mpz(&[0, 1], true);
        b.set_root(big);
        let RawValue::BigInt(i) = &*parse(b).unwrap() else {
            panic!()
        };
        assert_eq!(*i, -num_bigint::BigInt::from(2u128.pow(64)));
    }

    #[test]
    fn cycles_error_instead_of_hanging() {
        let mut b = Builder::new();
        let c = b.ctor(0, &[boxed(0)], &[]);
        b.patch_field(c, 0, c); // now points at itself
        b.set_root(c);
        assert!(matches!(parse(b), Err(OleanError::Cycle { .. })));
    }

    #[test]
    fn bad_pointers_and_tags_error() {
        let mut b = Builder::new();
        let unaligned = b.ctor(0, &[BASE + 100], &[]); // even but 100 % 8 != 0
        b.set_root(unaligned);
        assert!(matches!(parse(b), Err(OleanError::BadPointer { .. })));

        let mut b = Builder::new();
        let oob = b.ctor(0, &[BASE + (1 << 20)], &[]); // aligned but past EOF
        b.set_root(oob);
        assert!(matches!(parse(b), Err(OleanError::BadPointer { .. })));

        let mut b = Builder::new();
        let bad = b.object(247, 0, 1, &[0; 16]); // StructArray: never valid
        b.set_root(bad);
        assert!(matches!(parse(b), Err(OleanError::BadTag { tag: 247, .. })));

        let mut b = Builder::new();
        let closure = b.object(245, 0, 24, &[0; 24]);
        b.set_root(closure);
        assert!(matches!(parse(b), Err(OleanError::Unsupported { .. })));
    }

    #[test]
    fn resolve_offset_near_u64_max_does_not_panic() {
        // Regression for a `checked_sub`-then-raw-`+` overflow: with
        // base_addr = 0, off = word - base_addr = word directly, so
        // word = u64::MAX - 7 gives off = u64::MAX - 7 (aligned, well
        // past FIRST_OBJECT_OFFSET). The old `off + 8 > self.len()`
        // check overflowed `off + 8` in debug builds instead of
        // rejecting the pointer.
        let mut b = Builder::new();
        b.set_base_addr(0);
        b.set_root(u64::MAX - 7);
        assert!(matches!(parse(b), Err(OleanError::BadPointer { .. })));
    }

    #[test]
    fn mpz_size_i32_min_does_not_panic() {
        // Regression: `_mp_size` is an attacker-controlled i32 read
        // straight from the file; the old `mp_size.abs()` panicked for
        // `i32::MIN` (which has no positive `i32` representation).
        let mut b = Builder::new();
        let mut body = Vec::new();
        body.extend_from_slice(&0i32.to_le_bytes()); // _mp_alloc
        body.extend_from_slice(&i32::MIN.to_le_bytes()); // _mp_size
        body.extend_from_slice(&0u64.to_le_bytes()); // _mp_d (unreached: fails before use)
        let obj = b.object(TAG_MPZ, 0, 24, &body);
        b.set_root(obj);
        assert!(matches!(
            parse(b),
            Err(OleanError::Malformed {
                what: "mpz limb count",
                ..
            })
        ));
    }

    #[test]
    fn mpz_data_pointer_check_near_u64_max_does_not_panic() {
        // Regression: `region.base_addr + off + 24` overflowed in debug
        // builds when `base_addr` (attacker-controlled, from the header)
        // sits close to `u64::MAX`. Pick base_addr so the first object's
        // pointer word (off = 96, the first `FIRST_OBJECT_OFFSET`) both
        // resolves cleanly *and* pushes `base_addr + off + 24` past
        // `u64::MAX`.
        let mut b = Builder::new();
        let big = b.mpz(&[1], false); // gets past the limb-count check
        assert_eq!(big - BASE, 96, "test assumes the mpz is the first object");
        b.set_root(big); // patched below to the real base_addr-relative word
        let base_addr = u64::MAX - 99;
        b.set_base_addr(base_addr);
        // off = 96 relative to base_addr; word = base_addr + 96, chosen
        // even (not a boxed scalar) and distinct from NULL_SENTINEL.
        let word = base_addr + 96;
        assert_eq!(word, u64::MAX - 3);
        assert_eq!(word % 2, 0);
        b.set_root(word);
        assert!(matches!(
            parse(b),
            Err(OleanError::Malformed {
                what: "mpz data pointer",
                ..
            })
        ));
    }

    #[test]
    fn version_3_is_rejected() {
        let mut b = Builder::new();
        b.bytes[5] = 3;
        b.set_root(boxed(0));
        assert!(matches!(parse(b), Err(OleanError::UnsupportedVersion(3))));
    }

    #[test]
    fn deep_graphs_decode_and_drop_iteratively() {
        let mut b = Builder::new();
        let mut prev = boxed(0);
        for _ in 0..200_000 {
            prev = b.ctor(1, &[prev], &[]);
        }
        b.set_root(prev);
        let v = parse(b).unwrap();
        drop(v); // must not overflow the stack
    }

    #[test]
    fn the_real_oracle_fixture_decodes() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/fixtures/Sample.olean"
        );
        let bytes = std::fs::read(path).unwrap();
        let v = parse_bytes(&bytes).unwrap();
        assert!(
            matches!(&*v, RawValue::Ctor { tag: 0, .. }),
            "root must be ModuleData"
        );
    }

    proptest! {
        /// Untrusted input: never panic, never hang, whatever the bytes.
        #[test]
        fn arbitrary_bytes_never_panic(bytes in proptest::collection::vec(any::<u8>(), 0..512)) {
            let _ = parse_bytes(&bytes);
        }

        /// Mutations of a real file exercise deep decoder paths.
        #[test]
        fn mutated_fixture_never_panics(idx in 0usize..100_000, byte in any::<u8>()) {
            let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/fixtures/Sample.olean");
            let mut bytes = std::fs::read(path).unwrap();
            let i = idx % bytes.len();
            bytes[i] = byte;
            let _ = parse_bytes(&bytes);
        }
    }
}
