//! Which local instances are in scope.
//!
//! oracle: `LocalInstance` (`MetavarContext.lean:268-273`) — a
//! `className` and an `fvar`, nothing else. The oracle keeps them in a
//! `LocalInstances := Array LocalInstance` threaded through
//! `Meta.Context` and stored on every `MetavarDecl` (`:320`), and it is
//! deliberately NOT part of the `LocalContext` itself: the kernel does
//! not care about instances (`:265-267`), so they live one layer up.
//!
//! # Why this is a separate module
//!
//! `metactx.rs` is already long, and the scoping rule here is the whole
//! subtlety of the slice: this stack is SPARSE where every other
//! parallel index on `MetaCtx` is in lockstep with `lctx.decls`. Keeping
//! the rule in one screen is worth a file.
//!
//! # The scoping rule
//!
//! `MetaCtx::local_names` (`metactx.rs:80`) has exactly one entry per
//! `push_local_decl`/`push_let_decl` call, so `lctx_restore(cp)`
//! truncates it to `cp` and a `debug_assert` keeps the two honest. This
//! stack cannot do that: only a CLASS-TYPED declaration produces an
//! entry, so `entries.len()` bears no relation to `lctx.save()`. Each
//! entry therefore records the `lctx` depth it was pushed at — which is
//! the declaration's own index in `lctx.decls` — and `truncate_to` pops
//! while that depth is `>= checkpoint`. Entries are pushed in
//! increasing depth order (declarations only ever append), so popping
//! from the back terminates at the first survivor.
//!
//! Doing it this way keeps `lctx_checkpoint`'s `usize` return type, so
//! no caller of the checkpoint/restore pair changes.
//!
//! # Dedup is vacuous here
//!
//! `withLocalInstancesImp` (`Basic.lean:1937-1949`) guards against
//! adding the same local instance twice, keyed on `fvarId`. That guard
//! exists for `withLocalInstances`, which RE-registers already-declared
//! decls. leanr's producers are the push chokepoints, which mint a fresh
//! `fvar_gen` id every time, so no fvar can be registered twice and the
//! guard has nothing to guard. Named rather than silently omitted; a
//! future port of `withExistingLocalDecls` (`Basic.lean:1955-1959`)
//! would need it.

use leanr_kernel::bank::{ExprId, NameId};

/// oracle: `LocalInstance` (`MetavarContext.lean:268-273`), plus the
/// scope bookkeeping leanr needs because its local context is a
/// mutate-in-place stack rather than a persistent structure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LocalInstance {
    pub class_name: NameId,
    pub fvar: ExprId,
    /// The `lctx` depth this entry was pushed at — i.e. the index of its
    /// own declaration in `lctx.decls`. Read only by `truncate_to`. Not
    /// part of the oracle's record: the oracle's `LocalInstances` is a
    /// persistent array captured by `withReader`, so scope exit restores
    /// it for free.
    pub at_depth: usize,
}

/// The in-scope local instances, innermost last.
#[derive(Clone, Debug, Default)]
pub(crate) struct LocalInstanceStack {
    entries: Vec<LocalInstance>,
}

impl LocalInstanceStack {
    /// No producer yet (Task 4 installs entries at the push chokepoints);
    /// exercised today only by this module's own tests.
    #[allow(dead_code)]
    pub(crate) fn push(&mut self, class_name: NameId, fvar: ExprId, at_depth: usize) {
        debug_assert!(
            self.entries.last().is_none_or(|e| e.at_depth <= at_depth),
            "local instances must be pushed in non-decreasing depth order; \
             `truncate_to` pops from the back and relies on it"
        );
        self.entries.push(LocalInstance {
            class_name,
            fvar,
            at_depth,
        });
    }

    /// Drop every entry whose declaration is at or above `depth` — the
    /// counterpart of `LocalContext::restore(depth)`.
    pub(crate) fn truncate_to(&mut self, depth: usize) {
        while self.entries.last().is_some_and(|e| e.at_depth >= depth) {
            self.entries.pop();
        }
    }

    /// No consumer yet (Task 6's `get_instances`); exercised today only
    /// by this module's own tests.
    #[allow(dead_code)]
    pub(crate) fn entries(&self) -> &[LocalInstance] {
        &self.entries
    }

    /// Install a saved set wholesale — `MetaCtx::install_lctx`'s half of
    /// the snapshot swap (Task 5). No caller yet.
    #[allow(dead_code)]
    pub(crate) fn replace(&mut self, entries: Vec<LocalInstance>) {
        self.entries = entries;
    }

    /// The other half of the Task 5 snapshot swap: capture the current
    /// set before `replace`-ing it with a saved one. No caller yet.
    #[allow(dead_code)]
    pub(crate) fn to_vec(&self) -> Vec<LocalInstance> {
        self.entries.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanr_kernel::bank::NameId;

    fn nid(i: u32) -> NameId {
        NameId::from_index(i, false).expect("a small index is a valid NameId")
    }
    fn eid(i: u32) -> ExprId {
        ExprId::from_index(i, true).expect("a small index is a valid ExprId")
    }

    /// Truncation is by RECORDED DEPTH, not by index. The stack is
    /// sparse — only class-typed declarations produce an entry — so an
    /// index-based `truncate(checkpoint)` drops the wrong entries
    /// whenever a non-class declaration sits between two instances,
    /// which is the ordinary case (`fun (n : Nat) [inst : C n] => …`).
    #[test]
    fn truncate_to_pops_by_recorded_depth_not_by_index() {
        let mut s = LocalInstanceStack::default();
        // lctx depths 0..5, with instances only at 1 and 4 — depths 0,
        // 2, 3 are ordinary non-class binders that push nothing here.
        s.push(nid(10), eid(1), 1);
        s.push(nid(11), eid(4), 4);
        assert_eq!(s.entries().len(), 2);

        // Restoring to depth 5 keeps both: neither was pushed at or
        // after 5.
        s.truncate_to(5);
        assert_eq!(s.entries().len(), 2, "nothing was pushed at depth >= 5");

        // Restoring to depth 4 drops exactly the one pushed AT depth 4.
        s.truncate_to(4);
        assert_eq!(
            s.entries().iter().map(|e| e.fvar).collect::<Vec<_>>(),
            vec![eid(1)],
            "the entry pushed at depth 4 is out of scope once lctx is \
             restored to 4; the one at depth 1 is still in scope. An \
             index-based truncate(4) would have kept BOTH, because \
             there are only 2 entries."
        );

        s.truncate_to(0);
        assert!(
            s.entries().is_empty(),
            "restoring to top level clears the stack"
        );
    }

    /// `truncate_to` must pop EVERY entry at or above the depth, not
    /// just the last one.
    #[test]
    fn truncate_to_pops_all_entries_at_or_above_the_depth() {
        let mut s = LocalInstanceStack::default();
        s.push(nid(10), eid(1), 1);
        s.push(nid(11), eid(2), 2);
        s.push(nid(12), eid(3), 3);
        s.truncate_to(2);
        assert_eq!(
            s.entries().iter().map(|e| e.fvar).collect::<Vec<_>>(),
            vec![eid(1)],
            "both the depth-2 and depth-3 entries are out of scope"
        );
    }
}
