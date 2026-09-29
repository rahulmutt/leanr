//! Structure accessors — M4b-4a P1. Oracle: `Lean/Structure.lean`
//! (pinned v4.33.0-rc1). Additive and TCB-neutral: read-only views over
//! decoded `structureExt` rows. Where the oracle `panic!`s on a
//! non-structure (`getStructureInfo`), these return an empty answer
//! instead — `.olean` input is untrusted and the elaborator only ever
//! asks after an `is_structure` guard anyway.

use std::collections::{HashMap, HashSet};

use leanr_kernel::bank::NameId;
use leanr_olean::{StructureFieldInfo, StructureInfo};

use crate::MetaCtx;

/// Keyed by structure name. The oracle binary-searches per-module
/// sorted arrays (`getStructureInfo?`); a point-lookup map answers the
/// same question (names are unique per environment).
#[derive(Default)]
pub(crate) struct StructureTable {
    by_name: HashMap<NameId, StructureInfo>,
}

impl StructureTable {
    pub(crate) fn build(entries: &[StructureInfo]) -> Self {
        StructureTable {
            by_name: entries.iter().map(|i| (i.struct_name, i.clone())).collect(),
        }
    }
}

impl<'e> MetaCtx<'e> {
    /// oracle: `getStructureInfo?`.
    pub fn get_structure_info(&self, s: NameId) -> Option<&StructureInfo> {
        self.structures.by_name.get(&s)
    }

    /// oracle: `isStructure`.
    pub fn is_structure(&self, s: NameId) -> bool {
        self.structures.by_name.contains_key(&s)
    }

    /// oracle: `getStructureFields`, constructor order.
    pub fn get_structure_fields(&self, s: NameId) -> &[NameId] {
        self.get_structure_info(s).map_or(&[], |i| &i.field_names)
    }

    /// oracle: `getFieldInfo?`.
    pub fn get_field_info(&self, s: NameId, field: NameId) -> Option<&StructureFieldInfo> {
        self.get_structure_info(s)?
            .field_info
            .iter()
            .find(|f| f.field_name == field)
    }

    /// oracle: `getStructureSubobjects` — the subobject parents, in FIELD
    /// (constructor) order.
    pub fn get_structure_subobjects(&self, s: NameId) -> Vec<NameId> {
        self.get_structure_fields(s)
            .iter()
            .filter_map(|&f| self.get_field_info(s, f)?.subobject)
            .collect()
    }

    /// oracle: `findField?`.
    pub fn find_field(&self, s: NameId, field: NameId) -> Option<NameId> {
        if self.get_structure_fields(s).contains(&field) {
            return Some(s);
        }
        self.get_structure_subobjects(s)
            .into_iter()
            .find_map(|p| self.find_field(p, field))
    }

    /// oracle: `getPathToBaseStructure?` (`Structure.lean:338-354`).
    /// Subobject fields first, in `fieldInfo` order, then other parents in
    /// `extends` order, with a visited set shared across the whole search
    /// (the oracle's `StateM NameSet`; `<|>` does not roll it back).
    pub fn get_path_to_base_structure(&self, base: NameId, s: NameId) -> Option<Vec<NameId>> {
        let mut visited = HashSet::new();
        let mut path = Vec::new();
        self.path_go(base, s, &mut path, &mut visited)
            .then_some(path)
    }

    fn path_go(
        &self,
        base: NameId,
        s: NameId,
        path: &mut Vec<NameId>,
        visited: &mut HashSet<NameId>,
    ) -> bool {
        if base == s {
            return true;
        }
        if !visited.insert(s) {
            return false;
        }
        let Some(info) = self.get_structure_info(s) else {
            return false;
        };
        for f in &info.field_info {
            if let Some(parent) = f.subobject {
                path.push(f.proj_fn);
                if self.path_go(base, parent, path, visited) {
                    return true;
                }
                path.pop();
            }
        }
        for p in &info.parent_info {
            path.push(p.proj_fn);
            if self.path_go(base, p.struct_name, path, visited) {
                return true;
            }
            path.pop();
        }
        false
    }
}
