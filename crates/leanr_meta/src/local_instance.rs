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
//!
//! # An inherited circularity, named rather than resolved
//!
//! `isClassExpensive?` runs whnf, and whnf depends indirectly on the set
//! of local instances being computed. The oracle says so in as many
//! words (`Basic.lean:1402-1406`). leanr inherits it exactly, and it
//! surfaces a second time in `get_instances`'
//! `local_instance_candidate`, whose telescope installs further local
//! instances while computing one candidate's `synthOrder`. Both
//! terminate — but NOT because either loop is locally finite
//! (`instimplicit_binder_positions`'s own docstring in `instances.rs`
//! is explicit that its telescope's termination is "NOT simply 'the
//! telescope is finite'"): both `is_class_expensive`'s whnf and this
//! telescope's whnf ride the same `whnf -> smart unfolding -> synth_pending ->
//! synth_instance -> get_instances` cycle that `get_instances`' own
//! re-entrancy note traces, and inherit that cycle's bounds —
//! `MAX_SYNTH_PENDING_DEPTH` (`whnf.rs:138`), `synth_instance`'s
//! `guarded` bump (`synth.rs:1645`), and the step budget
//! (`metactx.rs:1142-1148`). Being bounded is not the same as being
//! "resolved", and a future change that makes `is_class` consult the
//! instance table would close the loop for real.
//!
//! One further, deliberate difference from the oracle belongs in this
//! same note. The oracle's own EXPENSIVE-path telescope
//! (`forallTelescopeReducingAuxAux`, `Basic.lean:1453-1488`) reaches
//! the non-forall-tail arm (`| _ =>`, `:1474-1487`) and there installs
//! the peeled binders' own local instances via `withNewLocalInstancesImp`
//! (defined `:1407-1420`) at the call site `:1477`, BEFORE its own
//! `whnf` call on that tail at `:1479` — so those binders' own local
//! instances ARE in scope for that `whnf`, which is exactly the
//! self-reference `Basic.lean:1402-1406` documents. (The same function
//! also calls `withNewLocalInstancesImp` earlier, at `:1472`, but that
//! call sits in the `.forallE` arm's `else` branch — taken only when
//! `fvarsSizeLtMaxFVars` is `false` — and `isClassExpensive?`
//! (`:1520-1522`) always passes `maxFVars? := none`, for which
//! `fvarsSizeLtMaxFVars` (`:1395-1398`) is unconditionally `true`, so
//! that branch is dead on this call path; `:1477`/`:1479` is the
//! install/whnf pair that actually executes.) leanr's
//! `MetaCtx::is_class_expensive` (`metactx.rs`) does NOT reproduce any
//! of this: it walks the `Forall` spine structurally, calling `whnf`
//! on each successive `body` without ever opening a binder or
//! installing anything, so those `whnf` calls never see instances the
//! binders being walked past would have contributed. Recorded here as
//! a known, deliberate difference rather than left for a future reader
//! to rediscover — closing it would mean `is_class_expensive` opening
//! binders the way `local_instance_candidate`'s own telescope
//! (`instances.rs`'s `instimplicit_binder_positions`) already does,
//! which this slice does not attempt.
//!
//! # Seams this slice does NOT close
//!
//! * `"type class instance expected"` — the oracle throws when a goal's
//!   `isClass?` is `none` (`SynthInstance.lean:207-208`); leanr's
//!   `get_instances` returns candidates regardless. PRE-EXISTING, and
//!   deliberately left: closing it here would put corpus movement from
//!   an unrelated fix inside this slice's neutrality gate, which is the
//!   whole approval argument for a non-additive change. Explicitly
//!   unowned.
//! * `scoped instance` namespace activation — unchanged, still unowned
//!   (`instances.rs`'s own "Scope: `scoped instance` activation only"
//!   section).
//! * erasure / private-instance filtering — unchanged, still unowned.
//!   Note these filters live in `getInstances`' `.const` arm
//!   (`SynthInstance.lean:216-228`) and so do not apply to locals at
//!   all, which is faithful rather than a gap.
//! * `withNewMCtxDepth`'s depth machinery does not reach local
//!   instances: they are fvars, not metavariables. Recorded as a
//!   NON-interaction so a later reader does not go looking for one.

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
    /// Called from `MetaCtx::install_local_instance_for` (Task 4), at
    /// the two push chokepoints (`push_local_decl`/`push_let_decl`).
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

    /// No production consumer: task 6's `get_instances` needs an OWNED
    /// snapshot ([`LocalInstanceStack::to_vec`]) because it calls back
    /// into `&mut self` for each candidate while iterating. Exercised
    /// today only by tests, hence the allow.
    #[allow(dead_code)]
    pub(crate) fn entries(&self) -> &[LocalInstance] {
        &self.entries
    }

    /// Install a saved set wholesale — `MetaCtx::install_lctx`'s half of
    /// the snapshot swap (Task 5).
    pub(crate) fn replace(&mut self, entries: Vec<LocalInstance>) {
        self.entries = entries;
    }

    /// The other half of the Task 5 snapshot swap: capture the current
    /// set before `replace`-ing it with a saved one. Called by
    /// `MetaCtx::current_lctx`, which snapshots the ambient instances
    /// alongside `lctx`/`local_names`.
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
