//! Structural interning (hash-consing) for `Expr`/`Level`.
//!
//! A *transient* batch canonicalizer: build an `Interner`, rewrite the
//! decoded constants through it, then drop it. Structurally-identical
//! subterms collapse to one shared `Arc`, so the resulting `Arc` graph
//! (and the `Environment` built from it) holds each distinct subterm once.
//! No global state, no `Weak` refs, no hot-path cost (see
//! docs/superpowers/specs/2026-07-06-expr-hash-consing-design.md).
//!
//! Soundness: interning only ever replaces an `Arc<Expr>`/`Arc<Level>` with
//! a structurally-identical one. The kernel decides types by
//! `structural_eq`/`is_def_eq` (value comparison; `Arc::ptr_eq` is only a
//! fast path), so no verdict can change. Bucket comparison uses the
//! existing `structural_eq`, which compares every field (binder names,
//! `BinderInfo`, `non_dep`, `KVMap`), so merged nodes are fully identical.

use crate::{KernelError, Level, RecGuard};
use std::collections::HashMap;
use std::sync::Arc;

// `Interner` and its methods are only reachable from `#[cfg(test)]` until
// Task 3 wires up `intern_constants` as the crate's public entry point (see
// lib.rs); `allow(dead_code)` here is temporary scaffolding removed in Task 3.
#[derive(Default)]
#[allow(dead_code)]
pub struct Interner {
    /// Canonical levels, bucketed by `Level::hash_val`.
    levels: HashMap<u64, Vec<Arc<Level>>>,
    /// Input-`Arc`-address → canonical level, so a shared input subtree is
    /// interned once. Keys are live for the pass's lifetime only.
    level_memo: HashMap<usize, Arc<Level>>,
    // Expr fields added in Task 2.
}

#[allow(dead_code)]
impl Interner {
    pub fn new() -> Interner {
        Interner::default()
    }

    /// Canonicalize a level bottom-up. Returns the shared canonical `Arc`
    /// for `l`'s structural value.
    pub fn intern_level(
        &mut self,
        l: &Arc<Level>,
        g: &mut RecGuard,
    ) -> Result<Arc<Level>, KernelError> {
        let key = Arc::as_ptr(l) as usize;
        if let Some(c) = self.level_memo.get(&key) {
            return Ok(Arc::clone(c));
        }
        let canon = g.enter(|g| {
            // Rebuild with canonical children first (bottom-up).
            let rebuilt: Arc<Level> = match l.as_ref() {
                Level::Zero | Level::Param(_) | Level::MVar(_) => Arc::clone(l),
                Level::Succ(a) => Arc::new(Level::Succ(self.intern_level(a, g)?)),
                Level::Max(a, b) => Arc::new(Level::Max(
                    self.intern_level(a, g)?,
                    self.intern_level(b, g)?,
                )),
                Level::IMax(a, b) => Arc::new(Level::IMax(
                    self.intern_level(a, g)?,
                    self.intern_level(b, g)?,
                )),
            };
            let h = Level::hash_val(&rebuilt, g)?;
            let bucket = self.levels.entry(h).or_default();
            for existing in bucket.iter() {
                // With canonical children this short-circuits on ptr_eq.
                if Level::structural_eq(existing, &rebuilt, g)? {
                    return Ok(Arc::clone(existing));
                }
            }
            bucket.push(Arc::clone(&rebuilt));
            Ok(rebuilt)
        })?;
        self.level_memo.insert(key, Arc::clone(&canon));
        Ok(canon)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Level, RecGuard};
    use std::sync::Arc;

    fn name(s: &str) -> Arc<crate::Name> {
        Arc::new(crate::Name::Str {
            parent: Arc::new(crate::Name::Anonymous),
            part: s.to_string(),
        })
    }

    #[test]
    fn level_merges_structurally_equal_distinct_pointers() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        // Two independently-built `Succ Zero`s — structurally equal, distinct Arcs.
        let a = Arc::new(Level::Succ(Arc::new(Level::Zero)));
        let b = Arc::new(Level::Succ(Arc::new(Level::Zero)));
        assert!(!Arc::ptr_eq(&a, &b));
        let ca = it.intern_level(&a, &mut g).unwrap();
        let cb = it.intern_level(&b, &mut g).unwrap();
        assert!(
            Arc::ptr_eq(&ca, &cb),
            "equal levels must share one canonical Arc"
        );
        assert!(Level::structural_eq(&a, &ca, &mut g).unwrap());
    }

    #[test]
    fn level_distinct_params_not_merged() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        let a = Arc::new(Level::Param(name("u")));
        let b = Arc::new(Level::Param(name("v")));
        let ca = it.intern_level(&a, &mut g).unwrap();
        let cb = it.intern_level(&b, &mut g).unwrap();
        assert!(!Arc::ptr_eq(&ca, &cb));
    }

    #[test]
    fn level_idempotent() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        let a = Arc::new(Level::Succ(Arc::new(Level::Zero)));
        let ca = it.intern_level(&a, &mut g).unwrap();
        let cca = it.intern_level(&ca, &mut g).unwrap();
        assert!(
            Arc::ptr_eq(&ca, &cca),
            "interning a canonical level is a no-op"
        );
    }
}
