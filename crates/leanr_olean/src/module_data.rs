//! The decoded contents of one `.olean` module (oracle:
//! src/Lean/Environment.lean:109-129).

use std::sync::Arc;

use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{ArcConstantInfo, ConstantInfo, Expr, Name, RecGuard};

use crate::interp_id::InterpId;
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
    pub constants: Vec<ArcConstantInfo>,
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
        let mut constants: Vec<ArcConstantInfo> = Vec::new();
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

/// The id-native decoded module (term-bank phase 3): what `ModuleData`
/// becomes once the Arc decode path is deleted. Ids live in the
/// `&mut Store` handed to `parse`/`parse_parts` — the caller's
/// `Environment::store_mut()` in the check pipeline, or a standalone
/// `Store::persistent()` for inspection commands.
#[derive(Debug)]
pub struct ModuleDataId {
    pub is_module: bool,
    pub imports: Vec<Import>,
    pub const_names: Vec<NameId>,
    pub constants: Vec<ConstantInfo>,
    pub extra_const_names: Vec<NameId>,
    /// Environment-extension entries are validated by phase A but kept
    /// opaque (spec: interpreted by the elaborator in M4).
    pub num_entries: usize,
}

impl ModuleDataId {
    /// Decode a whole single-region `.olean` file directly into `st`.
    /// `bytes` is untrusted input; every failure mode is an
    /// `OleanError`, never a panic. A failed decode may leave
    /// already-interned rows in `st` — sound (interning is append-only
    /// and canonical; unreachable ids are inert) and decode failure is
    /// fatal for the run.
    pub fn parse(bytes: &[u8], st: &mut Store) -> Result<ModuleDataId, OleanError> {
        let root = raw::parse_bytes(bytes)?;
        InterpId::new(st).module_data(&root)
    }

    /// Decode a module split across its ordered companion parts — id-native
    /// twin of `ModuleData::parse_parts` (see its doc comment for the oracle
    /// rationale on part authority and the shadowed-duplicate guard;
    /// semantics are identical).
    pub fn parse_parts(
        parts: &[(PartKind, &[u8])],
        st: &mut Store,
    ) -> Result<ModuleDataId, OleanError> {
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

        // One shared interpreter: objects shared across parts decode to
        // the same id (memos keyed by raw node address, exactly like
        // the Arc version). The block scopes the &mut Store borrow so
        // `st` is usable for error rendering below.
        let mut modules: Vec<ModuleDataId> = {
            let mut interp = InterpId::new(st);
            roots
                .iter()
                .map(|r| interp.module_data(r))
                .collect::<Result<_, _>>()?
        };

        // Most-authoritative first: `.private` > `.server` > base.
        let authority = |k: PartKind| match k {
            PartKind::Private => 0,
            PartKind::Server => 1,
            PartKind::Base => 2,
        };
        let mut order: Vec<usize> = (0..modules.len()).collect();
        order.sort_by_key(|&i| authority(parts[i].0));

        let mut const_names: Vec<NameId> = Vec::new();
        let mut constants: Vec<ConstantInfo> = Vec::new();
        let mut seen: std::collections::HashMap<NameId, usize> = std::collections::HashMap::new();
        for &i in &order {
            for c in &modules[i].constants {
                let name = c.name();
                match seen.get(&name) {
                    None => {
                        seen.insert(name, constants.len());
                        const_names.push(name);
                        constants.push(c.clone());
                    }
                    Some(&existing) => {
                        // Shadowed duplicate must share `type` +
                        // `levelParams` with the kept version. By the
                        // interning invariant id equality IS the Arc
                        // version's guarded structural_eq, so this is
                        // plain `==` — no RecGuard, no DeepRecursion.
                        let kept = constants[existing].constant_val();
                        let dup = c.constant_val();
                        let compatible = kept.level_params == dup.level_params && kept.ty == dup.ty;
                        if !compatible {
                            return Err(OleanError::DuplicateConstant {
                                name: st.to_name(None, Some(name)).to_string(),
                            });
                        }
                    }
                }
            }
        }

        // Extra const names: union preserving first-seen order.
        let mut extra_seen: std::collections::HashSet<NameId> = std::collections::HashSet::new();
        let mut extra_const_names: Vec<NameId> = Vec::new();
        for &i in &order {
            for &n in &modules[i].extra_const_names {
                if extra_seen.insert(n) {
                    extra_const_names.push(n);
                }
            }
        }

        let base = &mut modules[base_idx];
        Ok(ModuleDataId {
            is_module: base.is_module,
            imports: std::mem::take(&mut base.imports),
            const_names,
            constants,
            extra_const_names,
            num_entries: base.num_entries,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanr_kernel::bank::NameId;
    use leanr_kernel::{ConstantInfo, Environment};
    use std::collections::HashMap;
    use std::path::PathBuf;

    fn fixture(name: &str) -> Vec<u8> {
        std::fs::read(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../../tests/fixtures")
                .join(name),
        )
        .unwrap()
    }

    /// Id-path mirror of `check_fixtures.rs`'s
    /// `modpriv_parts_replay_from_empty_env`: multi-region merge on the
    /// id path — `.private` wins over the base axiom stub, the private
    /// helper is present, and the merged set replays clean.
    #[test]
    fn modpriv_parts_id_decode_and_replay() {
        let base = fixture("ModPriv.olean");
        let server = fixture("ModPriv.olean.server");
        let private = fixture("ModPriv.olean.private");

        let mut env = Environment::default();
        let md = ModuleDataId::parse_parts(
            &[
                (PartKind::Base, &base),
                (PartKind::Server, &server),
                (PartKind::Private, &private),
            ],
            env.store_mut(),
        )
        .expect("parts decode");
        assert!(md.is_module);
        assert!(md.imports.is_empty());

        let render = |env: &Environment, n: NameId| env.store().to_name(None, Some(n)).to_string();
        assert!(
            md.constants
                .iter()
                .any(|c| render(&env, c.name()) == "_private.ModPriv.0.secret"),
            "private helper missing from merged constants"
        );
        let bump = md
            .constants
            .iter()
            .find(|c| render(&env, c.name()) == "bump")
            .expect("bump present");
        assert_eq!(
            bump.kind(),
            "def",
            "bump must be the private def, not an axiom stub"
        );

        let constants: HashMap<NameId, ConstantInfo> =
            md.constants.into_iter().map(|c| (c.name(), c)).collect();
        let stats = leanr_kernel::replay(&mut env, constants).expect("replays clean");
        assert!(
            stats.checked >= 5,
            "expected >= 5 checked, got {}",
            stats.checked
        );
        assert_eq!(stats.skipped_unsafe, 0);
    }

    #[test]
    fn parse_parts_requires_exactly_one_base() {
        let base = fixture("ModPriv.olean");
        let mut env = Environment::default();
        let err = ModuleDataId::parse_parts(&[(PartKind::Private, &base)], env.store_mut())
            .expect_err("no base part");
        assert!(matches!(err, OleanError::BadShape { .. }));
    }
}
