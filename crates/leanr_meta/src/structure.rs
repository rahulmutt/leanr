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
    /// oracle: `structureResolutionExt` (Structure.lean:421-422), "a mere
    /// cache". Sound because `structureExt` rows never change while a
    /// `MetaCtx` lives.
    resolution_orders: HashMap<NameId, Vec<NameId>>,
}

impl StructureTable {
    pub(crate) fn build(entries: &[StructureInfo]) -> Self {
        StructureTable {
            by_name: entries.iter().map(|i| (i.struct_name, i.clone())).collect(),
            resolution_orders: HashMap::new(),
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

    /// oracle: `getStructureResolutionOrder` (`Structure.lean:512-514`) --
    /// `computeStructureResolutionOrder structName (relaxed := true)`
    /// (`:452-460`), the C3 merge (`mergeStructureResolutionOrders`,
    /// `:462-492`) memoized as the oracle memoizes it. `None` only for a
    /// parent cycle, which well-formed data never has and the oracle
    /// would recurse on forever; see `find_field`'s doc.
    pub fn get_structure_resolution_order(&mut self, s: NameId) -> Option<Vec<NameId>> {
        self.resolution_order_go(s, &mut HashSet::new())
    }

    fn resolution_order_go(
        &mut self,
        s: NameId,
        in_progress: &mut HashSet<NameId>,
    ) -> Option<Vec<NameId>> {
        if let Some(o) = self.structures.resolution_orders.get(&s) {
            return Some(o.clone());
        }
        if !in_progress.insert(s) {
            return None;
        }
        // `getStructureParentInfo env structName |>.map (·.structName)`:
        // empty for a non-structure.
        let parent_names: Vec<NameId> = self.get_structure_info(s).map_or_else(Vec::new, |i| {
            i.parent_info.iter().map(|p| p.struct_name).collect()
        });
        let mut res_orders: Vec<Vec<NameId>> = Vec::with_capacity(parent_names.len() + 1);
        // `parentResOrders.insertIdx 0 parentNames |>.filter (!·.isEmpty)`.
        res_orders.push(parent_names.clone());
        for &p in &parent_names {
            res_orders.push(self.resolution_order_go(p, in_progress)?);
        }
        res_orders.retain(|o| !o.is_empty());
        let mut order = vec![s];
        while !res_orders.is_empty() {
            let name = select_parent(&res_orders);
            order.push(name);
            for o in res_orders.iter_mut() {
                o.retain(|&n| n != name);
            }
            res_orders.retain(|o| !o.is_empty());
        }
        in_progress.remove(&s);
        self.structures.resolution_orders.insert(s, order.clone());
        Some(order)
    }

    /// oracle: `findField?`. The oracle recurses with no cycle guard: a
    /// well-formed environment's subobject graph is acyclic. `structureExt`
    /// rows are untrusted, so a doctored cycle (`S2.toS1.subobject := S2`)
    /// would recurse until the stack overflows. `visited` cuts a revisit
    /// off with `None`, as `path_go` below does. On acyclic data that is
    /// no change: a structure revisited through a diamond was already
    /// searched in full and yielded `None` the first time.
    pub fn find_field(&self, s: NameId, field: NameId) -> Option<NameId> {
        self.find_field_go(s, field, &mut HashSet::new())
    }

    fn find_field_go(
        &self,
        s: NameId,
        field: NameId,
        visited: &mut HashSet<NameId>,
    ) -> Option<NameId> {
        if !visited.insert(s) {
            return None;
        }
        if self.get_structure_fields(s).contains(&field) {
            return Some(s);
        }
        self.get_structure_subobjects(s)
            .into_iter()
            .find_map(|p| self.find_field_go(p, field, visited))
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

/// oracle: `mergeStructureResolutionOrders.selectParent`
/// (`Structure.lean:494-505`), relaxed: for `n' = 0, 1, ...`, ignore the
/// last `n'` orders and take the first head that appears in no other
/// considered order's TAIL. Every order is nonempty (caller invariant).
/// The `good` flag only feeds the strict mode's conflict report, which
/// `getStructureResolutionOrder` never asks for.
fn select_parent(res_orders: &[Vec<NameId>]) -> NameId {
    for n_skip in 0..res_orders.len() {
        let hi = res_orders.len() - n_skip;
        for i in 0..hi {
            let parent = res_orders[i][0];
            let consistent = |o: &Vec<NameId>| o[1..].iter().all(|&n| n != parent);
            if res_orders[..i].iter().all(consistent)
                && res_orders[i + 1..hi].iter().all(consistent)
            {
                return parent;
            }
        }
    }
    res_orders[0][0]
}
