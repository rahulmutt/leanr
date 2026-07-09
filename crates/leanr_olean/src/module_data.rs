//! The decoded contents of one `.olean` module (oracle:
//! src/Lean/Environment.lean:109-129).

use std::sync::Arc;

use leanr_kernel::{ArcConstantInfo as ConstantInfo, Expr, Name, RecGuard};

use crate::{interp::Interp, raw, OleanError};

/// oracle: src/Lean/Setup.lean:25-32
#[derive(Debug, Clone)]
pub struct Import {
    pub module: Arc<Name>,
    pub import_all: bool,
    pub is_exported: bool,
    pub is_meta: bool,
}

/// Which companion part a byte buffer is, for [`ModuleData::parse_parts`].
///
/// The module system (pinned toolchain v4.32.0-rc1) can split one module
/// into a base `Foo.olean` plus `Foo.olean.server` and `Foo.olean.private`
/// companion parts (oracle: `OLeanLevel.adjustFileName`,
/// src/Lean/Environment.lean:1793-1796). The base part alone is a
/// self-contained region and carries the module's public constant subset;
/// the `.private` part carries the module's *full* constant set (oracle:
/// `mkModuleData`, Environment.lean:1843-1852 — the `.private` level folds
/// in every kernel constant, while lower levels are filtered to the exported
/// subset), stored with objects deduplicated against the earlier parts.
///
/// The kind is used only to pick the primary part (the base) for the
/// module's non-constant fields; pointer resolution is by logical address
/// range and does not depend on it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PartKind {
    /// The base `Foo.olean` (public/exported level).
    Base,
    /// The `Foo.olean.server` part (language-server extension state).
    Server,
    /// The `Foo.olean.private` part (full constant set).
    Private,
}

#[derive(Debug)]
pub struct ModuleData {
    pub is_module: bool,
    pub imports: Vec<Import>,
    pub const_names: Vec<Arc<Name>>,
    pub constants: Vec<ConstantInfo>,
    pub extra_const_names: Vec<Arc<Name>>,
    /// Environment-extension entries are validated by phase A but kept
    /// opaque (spec: interpreted by the elaborator in M4).
    pub num_entries: usize,
}

impl ModuleData {
    /// Decode a whole single-region `.olean` file. `bytes` is untrusted
    /// input; every failure mode is an `OleanError`, never a panic (see
    /// docs/THREAT_MODEL.md and the raw-module docs).
    ///
    /// This is the M1a single-file path and is unchanged: byte-for-byte the
    /// same as decoding one part with [`ModuleData::parse_parts`].
    pub fn parse(bytes: &[u8]) -> Result<ModuleData, OleanError> {
        let root = raw::parse_bytes(bytes)?;
        Interp::new().module_data(&root)
    }

    /// Decode a module split across its ordered companion parts, producing
    /// the module's FULL constant set (base plus `.olean.server`/
    /// `.olean.private`).
    ///
    /// All parts are mapped into one logical address space so a companion
    /// part's pointers into an earlier part's deduplicated objects resolve
    /// (oracle: `readModuleDataParts`, Environment.lean:1755-1763, reads each
    /// part against the accumulated regions of the prior parts). The parts
    /// should be given base-first, matching the oracle's load order
    /// (`readModuleDataPartsOfMod`, Environment.lean:2042-2055 loads
    /// `[base, server, private]`), though resolution itself is order-free.
    ///
    /// Constants from every part are merged into one constant map, preferring
    /// the most authoritative part (`.private` > `.server` > base) for each
    /// name. Rationale: the oracle picks ONE part per module for the kernel
    /// constant map — `mainModule?` (Environment.lean:1999-2003) is
    /// `getData? (if self.importAll then .private else .exported)`, so an
    /// `import all` consumer gets the `.private` part (the full, checkable
    /// constant set) while a plain importer deliberately gets the base
    /// (`.exported`) interface. The base part stores only that public
    /// *interface*: a public `def`/`theorem` whose body is not exposed is
    /// written as a bare **axiom** stub there (verified on the pinned
    /// toolchain — `bump`/`triv` are `axiom` in `ModPriv.olean` but the real
    /// `def`/`thm` in `ModPriv.olean.private`). leanr's consumer is a full
    /// fresh-check (replay needs checkable bodies), i.e. the `importAll`
    /// semantics, so `.private` wins here.
    ///
    /// A name therefore legitimately appears in several parts with DIFFERENT
    /// infos (axiom stub vs. full def). Note the oracle never *reconciles*
    /// such cross-part pairs — `mainModule?` picks exactly one part, so a
    /// module's parts never meet in its constant map (its `subsumesInfo`,
    /// Environment.lean:2209-2225, reconciles cross-MODULE duplicates only,
    /// and its arms would reject a def/axiom pair via `| _, _ => false`).
    /// The shadowed-duplicate guard below is therefore leanr's own
    /// conservative check, consistent with the oracle's one-part-per-module
    /// model: a shadowed duplicate must share `type` and `levelParams` with
    /// the kept version (the invariant every `subsumesInfo` arm also
    /// requires); a disagreement is real corruption and a decode error.
    ///
    /// The module's non-constant fields (`is_module`, `imports`,
    /// `num_entries`) are taken from the base part. Requires exactly one
    /// [`PartKind::Base`] part.
    pub fn parse_parts(parts: &[(PartKind, &[u8])]) -> Result<ModuleData, OleanError> {
        let base_positions: Vec<usize> = parts
            .iter()
            .enumerate()
            .filter(|(_, (k, _))| *k == PartKind::Base)
            .map(|(i, _)| i)
            .collect();
        let [base_idx] = base_positions[..] else {
            return Err(OleanError::BadShape {
                expected: "exactly one Base part in parse_parts",
            });
        };

        let byte_slices: Vec<&[u8]> = parts.iter().map(|(_, b)| *b).collect();
        let roots = raw::parse_parts_bytes(&byte_slices)?;

        // One shared interpreter: objects shared across parts decode to the
        // same `Arc<RawValue>` (see `raw::parse_parts_bytes`), and the
        // per-type memos then map them to a single kernel value.
        let mut interp = Interp::new();
        let mut modules: Vec<ModuleData> = roots
            .iter()
            .map(|r| interp.module_data(r))
            .collect::<Result<_, _>>()?;

        // Visit parts most-authoritative first so the checkable `.private`
        // version of a name wins over the base part's axiom stub. Ties keep
        // input order (stable sort).
        let authority = |k: PartKind| match k {
            PartKind::Private => 0,
            PartKind::Server => 1,
            PartKind::Base => 2,
        };
        let mut order: Vec<usize> = (0..modules.len()).collect();
        order.sort_by_key(|&i| authority(parts[i].0));

        let mut guard = RecGuard::new();
        let mut const_names: Vec<Arc<Name>> = Vec::new();
        let mut constants: Vec<ConstantInfo> = Vec::new();
        let mut seen: std::collections::HashMap<Arc<Name>, usize> =
            std::collections::HashMap::new();
        for &i in &order {
            for c in &modules[i].constants {
                let name = Arc::clone(c.name());
                match seen.get(&name) {
                    None => {
                        seen.insert(Arc::clone(&name), constants.len());
                        const_names.push(name);
                        constants.push(c.clone());
                    }
                    Some(&existing) => {
                        // Shadowed duplicate: the authoritative version is
                        // already kept. Conservative own-design guard (the
                        // oracle never compares cross-part duplicates; see
                        // the doc comment): it must share `type` +
                        // `levelParams` with the kept version; anything else
                        // is corruption.
                        let kept = constants[existing].constant_val();
                        let dup = c.constant_val();
                        let compatible = kept.level_params == dup.level_params
                            && Expr::structural_eq(&kept.ty, &dup.ty, &mut guard)
                                .map_err(|_| OleanError::DeepRecursion)?;
                        if !compatible {
                            return Err(OleanError::DuplicateConstant {
                                name: name.to_string(),
                            });
                        }
                    }
                }
            }
        }

        // Extra const names: union preserving first-seen (authoritative) order.
        let mut extra_seen: std::collections::HashSet<Arc<Name>> = std::collections::HashSet::new();
        let mut extra_const_names: Vec<Arc<Name>> = Vec::new();
        for &i in &order {
            for n in &modules[i].extra_const_names {
                if extra_seen.insert(Arc::clone(n)) {
                    extra_const_names.push(Arc::clone(n));
                }
            }
        }

        let base = &mut modules[base_idx];
        Ok(ModuleData {
            is_module: base.is_module,
            imports: std::mem::take(&mut base.imports),
            const_names,
            constants,
            extra_const_names,
            num_entries: base.num_entries,
        })
    }
}
