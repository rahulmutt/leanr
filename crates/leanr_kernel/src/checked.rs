//! The gated declaration table (`CheckedConstants`) and the `ConstSource`
//! seam the checker's `EnvView` consults. Spec:
//! docs/superpowers/specs/2026-07-10-m1-final-parallel-mathlib-design.md
//! (§Components, §Key enabling observation). `CheckedConstants` is
//! populated in Task 2; this task only introduces the enum so `EnvView`
//! can be generalized without a behavior change.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::bank::NameId;
use crate::ConstantInfo;

/// Where an `EnvView` resolves a `NameId` to a `ConstantInfo`.
/// `Plain` is the sequential environment's plain map (identical behavior
/// to the pre-refactor `&HashMap`); `Gated` is the parallel driver's
/// admitted-flag-gated table (Task 2).
#[derive(Clone, Copy)]
pub enum ConstSource<'a> {
    Plain(&'a HashMap<NameId, ConstantInfo>),
    Gated(&'a CheckedConstants),
}

impl<'a> ConstSource<'a> {
    pub fn get(&self, n: NameId) -> Option<&'a ConstantInfo> {
        match self {
            ConstSource::Plain(m) => m.get(&n),
            ConstSource::Gated(c) => c.get(n),
        }
    }
}

/// The parallel driver's declaration table: every decoded constant of the
/// check closure, each gated by an admitted flag. The `map` is immutable
/// after `new`; only the flags flip (false -> true, once). `Sync` by
/// construction (std atomics), so `&CheckedConstants` crosses threads.
/// A `get` returns an entry only once its flag is set, so a checker
/// consulting it (via `ConstSource::Gated`) sees exactly the admitted
/// prefix — spec §Key enabling observation.
pub struct CheckedConstants {
    map: HashMap<NameId, ConstantInfo>,
    admitted: HashMap<NameId, AtomicBool>,
}

impl CheckedConstants {
    pub fn new(map: HashMap<NameId, ConstantInfo>) -> CheckedConstants {
        let admitted = map.keys().map(|&n| (n, AtomicBool::new(false))).collect();
        CheckedConstants { map, admitted }
    }

    /// Admitted-gated lookup (`Acquire` pairs with `admit`'s `Release`).
    pub fn get(&self, n: NameId) -> Option<&ConstantInfo> {
        match self.admitted.get(&n) {
            Some(flag) if flag.load(Ordering::Acquire) => self.map.get(&n),
            _ => None,
        }
    }

    /// Ungated lookup — the decoded constant regardless of admission.
    /// Used by the dependency pass and the decoded-vs-regenerated compare.
    pub fn get_decoded(&self, n: NameId) -> Option<&ConstantInfo> {
        self.map.get(&n)
    }

    pub fn contains(&self, n: NameId) -> bool {
        self.map.contains_key(&n)
    }

    /// Set `n`'s admitted flag. A name not in the table is a no-op (the
    /// caller only ever admits names it took from the table). `&self`:
    /// the flag is the only mutable state and it is atomic.
    pub fn admit(&self, n: NameId) {
        if let Some(flag) = self.admitted.get(&n) {
            flag.store(true, Ordering::Release);
        }
    }

    pub fn iter_decoded(&self) -> impl Iterator<Item = (&NameId, &ConstantInfo)> {
        self.map.iter()
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

const _: fn() = || {
    fn assert_sync<T: Sync>() {}
    assert_sync::<CheckedConstants>();
};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bank::Store;
    use crate::Name;
    use std::sync::Arc;

    fn nm(part: &str) -> Arc<Name> {
        Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: part.to_string(),
        })
    }

    // Build a table with two axioms `A`, `B` interned into a persistent
    // store, plus a third name `Z` interned into the same store but never
    // inserted into the table's map (used as an "unknown to this table"
    // id). `NameId`s are only meaningful relative to the store that
    // interned them, so `Z` is drawn from the same store as `A`/`B` rather
    // than a second, independent store — two fresh persistent stores would
    // otherwise assign the same low-level id to their first interned name,
    // making `Z` collide with `A` instead of being genuinely absent.
    fn table() -> (CheckedConstants, NameId, NameId, NameId) {
        let mut st = Store::persistent();
        let a = st.intern_name(None, &nm("A")).unwrap().unwrap();
        let b = st.intern_name(None, &nm("B")).unwrap().unwrap();
        let z = st.intern_name(None, &nm("Z")).unwrap().unwrap();
        let zero = st.level_zero(None).unwrap();
        let ty = st.expr_sort(None, zero).unwrap();
        let mk = |n: NameId| {
            ConstantInfo::Axiom(crate::AxiomVal {
                val: crate::ConstantVal {
                    name: n,
                    level_params: vec![],
                    ty,
                },
                is_unsafe: false,
            })
        };
        let mut map = std::collections::HashMap::new();
        map.insert(a, mk(a));
        map.insert(b, mk(b));
        (CheckedConstants::new(map), a, b, z)
    }

    #[test]
    fn unadmitted_is_invisible_to_gated_get() {
        let (t, a, _b, _z) = table();
        assert!(t.get(a).is_none());
        assert!(t.get_decoded(a).is_some());
        assert!(t.contains(a));
    }

    #[test]
    fn admit_makes_gated_get_visible() {
        let (t, a, b, _z) = table();
        t.admit(a);
        assert!(t.get(a).is_some());
        assert!(t.get(b).is_none());
    }

    #[test]
    fn unknown_name_never_visible() {
        let (t, _a, _b, z) = table();
        assert!(t.get(z).is_none());
        t.admit(z); // no-op, must not panic
        assert!(t.get(z).is_none());
    }
}
