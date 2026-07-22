//! Reader for official Lean `.olean` artifacts.
//!
//! Trust boundary: input bytes are UNTRUSTED (see docs/THREAT_MODEL.md).
//! No code path may panic on arbitrary input.
//!
//! # Header layout
//!
//! The brief's hypothesized layout (16-byte `oleanfile!!!!!!!` magic followed
//! by a 40-byte githash and a `u64` base address at offset 56, 64 bytes
//! total) does NOT match the oracle toolchain pinned in `lean-toolchain`
//! (`leanprover/lean4:v4.32.0-rc1`, commit `b4812ae5...`). That hypothesis
//! predates a header format change in later Lean versions (a version/flags
//! byte pair plus an embedded Lean version string were inserted between the
//! magic and the githash).
//!
//! The actual on-disk layout was read directly from the oracle's C++ writer,
//! `struct olean_header` in `src/library/module.cpp` at the pinned tag
//! (lines 106-144 define the struct; lines 327-331 and 353-357 are the two
//! write sites for the v2/v3 formats, which share this fixed header prefix;
//! lines 482-499 are the read/validation side):
//!
//! ```text
//! offset  0..5   marker:       5 bytes,  ASCII b"olean"
//! offset  5      version:     1 byte,   2 = v2 (plain) olean, 3 = v3 (allows closures)
//! offset  6      flags:       1 byte,   bit 0 = bignums use GMP encoding, bits 1-7 reserved
//! offset  7..40  lean_version: 33 bytes, e.g. "4.32.0-rc1", NUL-padded, not
//!                              necessarily NUL-terminated (unused by this parser)
//! offset 40..80  githash:     40 bytes, build githash, NUL-padded, not
//!                              necessarily NUL-terminated
//! offset 80..88  base_addr:   8 bytes,  little-endian u64; the mmap address the
//!                              file's compacted-object region was written to be
//!                              loaded at
//! offset 88..    start of the version-dependent body (v2: compacted data
//!                              immediately; v3: a `size_t` data_size followed by
//!                              compacted data and trailer sections) -- M1 territory.
//! ```
//!
//! `static_assert(sizeof(olean_header) == 5 + 1 + 1 + 33 + 40 + sizeof(size_t), ...)`
//! (module.cpp:144) confirms the 88-byte total (`size_t` is 8 bytes on every
//! platform Lean ships for). This was cross-checked byte-for-byte against
//! `tests/fixtures/Sample.olean`: bytes 0..5 are `olean`, byte 5 is `\x02`
//! (v2), byte 6 is `\x01` (GMP), bytes 7.. spell `4.32.0-rc1` followed by
//! zero padding to offset 40, and bytes 40..80 are exactly the 40 ASCII-hex
//! githash bytes recorded in `tests/fixtures/oracle-githash.txt` with no
//! padding (the hash happens to fill the field exactly).
//!
//! This parser deliberately does not gate on the `version` byte: the fields
//! it reads (`marker`, `githash`, `base_addr`) live at the same fixed offsets
//! in both the v2 and v3 formats (module.cpp:328/354), and full parsing of
//! the version-dependent body beyond the header is out of scope for M0
//! (tracked for M1's object-graph parsing).

use thiserror::Error;

/// Byte offset and length of the `marker` field (module.cpp:109).
const MAGIC: &[u8; 5] = b"olean";
/// Byte offset of the `githash` field (module.cpp:130): starts right after
/// the 5-byte marker, 1-byte version, 1-byte flags, and 33-byte lean_version.
const GITHASH_OFFSET: usize = 40;
/// Length in bytes of the `githash` field (module.cpp:130).
const GITHASH_LEN: usize = 40;
/// Byte offset of the `base_addr` field (module.cpp:132): right after the
/// githash field.
const BASE_ADDR_OFFSET: usize = GITHASH_OFFSET + GITHASH_LEN;
/// Total fixed-header length (module.cpp:144): `5 + 1 + 1 + 33 + 40 + 8`.
pub(crate) const HEADER_LEN: usize = BASE_ADDR_OFFSET + 8;

/// Parsed prefix of an `.olean` file's fixed header.
///
/// The full `olean_header` (embedded Lean version string) minus the parts
/// this crate has no use for; the object graph that follows the header is
/// decoded by the `raw` module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OleanHeader {
    /// Format version (module.cpp:110-122, byte 5): 2 = v2 (plain) olean,
    /// 3 = v3 (allows closures). The `raw` decoder only reads v2.
    pub version: u8,
    /// Format flags (module.cpp:110-122, byte 6): bit 0 = bignums use GMP
    /// encoding, bits 1-7 reserved.
    pub flags: u8,
    /// The build githash the file was produced by, as ASCII hex.
    pub githash: String,
    /// The mmap base address the compacted object region was written for.
    ///
    /// This is a real 64-bit pointer value chosen by the writer (derived
    /// from hashing the module name; see `CompactedRegion.save`'s `key`
    /// parameter), not a small integer -- it is expected to be nonzero for
    /// every file the oracle produces.
    pub base_addr: u64,
}

/// Failure parsing an `.olean` header from untrusted bytes.
///
/// `.olean` files are UNTRUSTED input at the trust boundary (see
/// docs/THREAT_MODEL.md); every variant here corresponds to a defensive
/// check on attacker-controlled bytes, and no combination of input bytes
/// may cause a panic instead of one of these errors.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum OleanError {
    /// Fewer than `HEADER_LEN` bytes were supplied; carries the actual length.
    #[error("not an olean file: {0} bytes is smaller than the {HEADER_LEN}-byte header")]
    Truncated(usize),
    /// The first 5 bytes are not the `b"olean"` marker.
    #[error("not an olean file: bad magic bytes")]
    BadMagic,
    /// The githash field is not (NUL-padded) ASCII hex.
    #[error("olean header corrupt: githash is not ASCII hex")]
    BadGithash,
    /// The version byte is not 2 (the plain module format). v3 regions
    /// (allowClosures) and unknown future versions are out of scope.
    #[error("unsupported olean format version {0} (leanr reads v2 module files)")]
    UnsupportedVersion(u8),
    /// A read past the end of the file (offset is the file offset).
    #[error("olean corrupt: read past end of file at offset {offset:#x}")]
    OutOfBounds { offset: u64 },
    /// A pointer word that is not a boxed scalar and does not resolve
    /// to an aligned in-bounds object (word is the raw pointer value).
    #[error("olean corrupt: bad object pointer {word:#x}")]
    BadPointer { word: u64 },
    /// Two companion parts declare overlapping logical address ranges, so a
    /// cross-part pointer could resolve into the wrong region. Rejected up
    /// front, mirroring the oracle (`region_reader::sort_and_validate_dep_regions`,
    /// src/runtime/compact.cpp:538-562). Carries the two colliding base
    /// addresses.
    #[error("olean corrupt: companion parts overlap (base {base_a:#x} vs {base_b:#x})")]
    RegionOverlap { base_a: u64, base_b: u64 },
    /// An object tag that cannot appear in a module's object graph.
    #[error("olean corrupt: unexpected object tag {tag} at offset {offset:#x}")]
    BadTag { offset: u64, tag: u8 },
    /// The object graph contains a reference cycle (legitimate files
    /// are acyclic; a crafted cycle must error, not hang).
    #[error("olean corrupt: object cycle at offset {offset:#x}")]
    Cycle { offset: u64 },
    /// A structurally invalid object (bad sizes, bad UTF-8, bad enum
    /// byte, ...). `what` names the check that failed.
    #[error("olean corrupt: {what} at offset {offset:#x}")]
    Malformed { offset: u64, what: &'static str },
    /// A well-formed construct leanr does not read yet.
    #[error("unsupported olean content: {what}")]
    Unsupported { what: &'static str },
    /// The same constant name appears in more than one companion part with
    /// structurally different `ConstantInfo`s. Legitimate parts only ever
    /// re-list a shared constant identically (the `.private` part is a
    /// superset of the base part); a genuine disagreement is corruption.
    #[error("olean module data malformed: constant '{name}' differs across parts")]
    DuplicateConstant { name: String },
    /// Phase B found a raw value whose shape does not match the kernel
    /// type expected at that position (bad ctor tag, wrong field
    /// count, scalar where an object belongs, ...).
    #[error("olean module data malformed: expected {expected}")]
    BadShape { expected: &'static str },
    /// Interning into the term bank failed while decoding directly to
    /// ids (phase 3) — e.g. a bank's u32 id space exhausted
    /// (`KernelError::BankExhausted`). Not reachable from legitimate
    /// files; incompleteness, never unsoundness.
    #[error("olean decode: kernel interning failed: {0}")]
    Kernel(#[from] leanr_kernel::KernelError),
}

impl OleanHeader {
    /// Parse the fixed header prefix of an `.olean` file.
    ///
    /// `bytes` is untrusted input: every access is bounds-checked and no
    /// path panics, whatever bytes are supplied (see the
    /// `arbitrary_bytes_never_panic` proptest).
    pub fn parse(bytes: &[u8]) -> Result<OleanHeader, OleanError> {
        if bytes.len() < HEADER_LEN {
            return Err(OleanError::Truncated(bytes.len()));
        }
        if &bytes[..MAGIC.len()] != MAGIC {
            return Err(OleanError::BadMagic);
        }

        let version = bytes[5];
        let flags = bytes[6];

        let githash_field = &bytes[GITHASH_OFFSET..GITHASH_OFFSET + GITHASH_LEN];
        // `strncpy` (module.cpp:331/357) NUL-pads on the right; a hash that
        // exactly fills the field (as in our fixture) has no NUL at all.
        let hash_end = githash_field
            .iter()
            .position(|&b| b == 0)
            .unwrap_or(githash_field.len());
        let (hash_bytes, padding) = githash_field.split_at(hash_end);
        if hash_bytes.is_empty()
            || !hash_bytes.iter().all(u8::is_ascii_hexdigit)
            || !padding.iter().all(|&b| b == 0)
        {
            return Err(OleanError::BadGithash);
        }
        // Every byte in `hash_bytes` was checked to be an ASCII hex digit above.
        let githash = String::from_utf8(hash_bytes.to_vec()).expect("checked ASCII hex above");

        let base_addr_bytes: [u8; 8] = bytes[BASE_ADDR_OFFSET..BASE_ADDR_OFFSET + 8]
            .try_into()
            .expect("slice is exactly 8 bytes by construction");
        let base_addr = u64::from_le_bytes(base_addr_bytes);

        Ok(OleanHeader {
            version,
            flags,
            githash,
            base_addr,
        })
    }
}

mod interp;
mod interp_id;
mod loader;
mod module_data;
mod raw;

pub use loader::{load_closure, LoadError, SearchPath};
pub use module_data::{
    CatBehavior, DefaultInstanceEntry, DiscrKey, EntryScope, Import, InstanceEntry, MatcherAltInfo,
    MatcherEntry, ModuleData, ParserEntry, PartKind, ReducibilityEntry, ReducibilityStatus,
    ScopedParserEntry,
};
