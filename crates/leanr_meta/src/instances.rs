//! The instance table B5's tabled resolution driver queries:
//! [`Instance`], [`InstanceTable`], [`MetaCtx::get_instances`],
//! [`MetaCtx::default_instances`].
//!
//! oracle: `Lean.Meta.SynthInstance.getInstances`
//! (`Lean/Meta/SynthInstance.lean:201-241`) and
//! `Lean.Meta.{getDefaultInstances,getDefaultInstancesPriorities}`
//! (`Lean/Meta/Instances.lean:385-436`), pinned toolchain
//! `leanprover/lean4:v4.33.0-rc1`.
//!
//! # `val`'s level params are NOT refreshed here (named seam — owned by B5)
//!
//! **Read this before consuming `Instance::val`.** `getInstances`'s own
//! decode step (`SynthInstance.lean:222-226`) does not hand back `e.val`
//! verbatim:
//! ```text
//! val := e.val.updateConst! (← us.mapM (fun _ => mkFreshLevelMVar))
//! ```
//! i.e. for a universe-polymorphic instance, EVERY universe argument of
//! the decoded `Const` is replaced by a FRESH level metavariable before
//! the candidate is ever handed to `tryResolve`. `Instance::val` below is
//! `e.val` copied verbatim from the decoded `InstanceEntry`
//! (`InstanceTable::build`, the `val: e.val` field below) —
//! `mkConstWithLevelParams declName`, i.e. a `Const` still carrying the
//! DECLARATION's own RIGID `Level.param`s, not fresh mvars. If a
//! synthesis driver unifies the goal's levels against `Instance::val` as
//! stored here without first performing this refresh, a
//! universe-polymorphic instance's levels are rigid params rather than
//! mvars: unification against the goal's (typically concrete-or-mvar)
//! levels will spuriously FAIL for the common case, or — in the unlucky
//! case where a param name happens to satisfy defeq some other way —
//! could "succeed" for the wrong reason. This is the one step of
//! `getInstances` this table does not transcribe.
//!
//! It is intentionally NOT implemented here: minting fresh level mvars
//! needs a live `mctx` (to allocate them into), which this
//! table-construction code does not have — `InstanceTable::build` runs
//! once, off a bare `EnvView`, with no `MetaCtx` in scope at all — and
//! which only a query-time caller holds. **B5 owns implementing this
//! refresh**: once per candidate, immediately after reading
//! `Instance::val` out of `get_instances`'s result and before attempting
//! to unify or apply it, B5 must replace each of `val`'s universe
//! arguments with a freshly-minted level mvar, exactly as
//! `SynthInstance.lean:222-226` does.
//!
//! # `synth_order`: read, never recomputed (controller decision)
//!
//! The design/plan text for this task described `synth_order` as a
//! transcription target of `Lean.Meta.computeSynthOrder`
//! (`Instances.lean:150-...`), computed HERE at table-construction time.
//! A controller decision (recorded on the branch, overriding both the
//! task brief and that Global Constraint's literal wording) supersedes
//! that: the toolchain already runs `computeSynthOrder` once, at
//! registration, and serializes the result into `InstanceEntry.synthOrder`
//! (`Instances.lean:52`, field 4) — PR-A decodes it verbatim into
//! `leanr_olean::InstanceEntry::synth_order` (verified empirically there:
//! `instAddProd` → `[2, 3]`, plain instances → `[]`, the two
//! `extends`-forwarders → `[1]`). `InstanceTable::build` below therefore
//! just COPIES `e.synth_order` into `Instance::synth_order` — no
//! `compute_synth_order` function exists in this crate, and none should
//! be added; re-deriving it here would be redundant with, and could
//! silently drift from, the toolchain's own already-serialized answer.
//!
//! # Scope: global instances only (named seam)
//!
//! `instanceExtension` is a `SimpleScopedEnvExtension`
//! (`Instances.lean:95-102`), so a `scoped instance` can in principle
//! produce an `InstanceEntry` whose `scope` is `EntryScope::Scoped(ns)`
//! (`leanr_olean::EntryScope`) rather than `Global` — visible only while
//! `ns` is `open`. This crate has no namespace-open-tracking model
//! (there is no "which scopes are currently active" state anywhere in
//! `MetaCtx`), so `InstanceTable::build` filters to `Global`-scope
//! entries only, exactly mirroring `metactx.rs`'s own precedent for
//! `ReducibilityEntry` (`MetaCtx::new`, the `reducibility` filter a few
//! lines above the instance-table construction call: "scoped ...
//! entries require the M3b3-style activation model, out of scope ...;
//! revisit when a corpus divergence implicates one"). `Instances.olean`
//! (this task's fixture) declares no `scoped instance`, so this seam is
//! not exercised either way by the fixture.
//!
//! **Ownership**: closing this gap needs the same M3b3-style
//! namespace-open-tracking/activation model `MetaCtx::new`'s own
//! `ReducibilityEntry` comment already defers — no task in this plan
//! owns building that model, so this stays an explicitly unowned seam for
//! M4b/future work, revisited if a corpus divergence ever implicates a
//! `scoped instance` — same unowned-seam treatment as the
//! erasure/private-instance seam documented further below.
//!
//! # `global_name: None` (named seam, not a silent skip)
//!
//! `addInstance` (`Instances.lean:283-304`) is the ONLY producer of a
//! persisted `instanceExtension` entry, and it unconditionally sets
//! `globalName? := declName` (line 304) — a `some`. A LOCAL instance
//! (introduced by a hypothesis in the local context, e.g. inside a
//! tactic block) is a completely different mechanism
//! (`getLocalInstances`/`LocalInstance`, `SynthInstance.lean:204,
//! 230-239`) that never touches `instanceExtension` and is never
//! serialized to `.olean` at all — `getInstances` appends those
//! separately, at query time, from the CALLER's local context, which is
//! exactly what a future B5 task must do from `MetaCtx::lctx`, not from
//! this table. So every `InstanceEntry` this crate ever decodes from a
//! real `.olean` has `global_name = Some(_)`, and `global_name: None`
//! is reachable ONLY via adversarial/malformed bytes (Global
//! Constraints: `.olean` bytes are untrusted). Since there is then no
//! `Name` to resolve a `ty` from (`EnvView::get` needs one) and no other
//! source for the instance's declared type, `InstanceTable::build`
//! drops such an entry from the table — documented here as the named
//! seam it is, not a silently-absorbed one: dropping a candidate is
//! incompleteness only (`get_instances` simply never offers it; the
//! kernel independently re-checks whatever IS synthesized), never a
//! wrong verdict.
//!
//! # Unresolvable `global_name` (named seam)
//!
//! A `global_name = Some(n)` whose `n` does not resolve via
//! `EnvView::get` is the SAME untrusted-bytes posture: every real
//! `instanceExtension` entry names a constant declared in the very
//! module that also declares the instance, so this cannot happen for
//! genuine toolchain output. `InstanceTable::build` drops the entry
//! rather than panicking or fabricating a `ty` — same incompleteness-only
//! reasoning as the `global_name: None` case above.
//!
//! # Erasure / private-instance filtering (named seam — DIVERGENT-ANSWER risk, unowned)
//!
//! `getInstances` (`SynthInstance.lean:215-223`) filters its
//! `getUnify` result against two RUNTIME (not `.olean`-decoded) sources
//! before returning: `getErasedInstances` (the `attribute [-instance]`
//! erasure set, `Instances.lean:359-360`, itself read off the SAME
//! `instanceExtension` state's `.erased : PHashSet Name` field,
//! `Instances.lean:78-88`) and a private-instance-leak check
//! (`env.isExporting && !env.contains constName`). Neither has any
//! decoded representation in `leanr_olean::InstanceEntry` — PR-A decodes
//! only the `InstanceEntry` ADD side of this extension, never its erase
//! side, and there is no `.olean`-level "is this constant private /
//! exporting" flag consumed here either. `get_instances` below therefore
//! never filters against either: an erased or private-and-leaking
//! instance name can still surface as a candidate.
//!
//! **This is NOT merely incompleteness — it is a divergent-answer risk.**
//! Synthesis returns the FIRST successful candidate it tries (`generate`'s
//! back-to-front walk, `SynthInstance.lean:589-621`), so an extra
//! candidate that the oracle itself would have filtered out (an
//! `attribute [-instance]`-erased instance, or a private one that would
//! have been rejected by the exporting check) can be tried, SUCCEED, and
//! be returned as THE synthesis answer where the oracle would have
//! skipped it and picked a different instance (or none at all). That is a
//! silently DIFFERENT answer from the oracle's, not just a dropped or
//! incomplete one. The kernel independently re-checking the resulting
//! term still guarantees no UNSOUND term is ever accepted, but this
//! project's constraint is "never a silent wrong answer", and this seam
//! can violate that constraint at the synthesis layer even while kernel
//! soundness holds.
//!
//! **Ownership**: closing this gap needs a new `.olean` decode —
//! `leanr_olean` would have to decode `Instances.erased` (a
//! `PHashSet Name`) and, separately, a private/exporting flag per
//! constant, before `get_instances` here could filter on either. No task
//! in this plan owns building that decoder; it is PR-A-shaped work this
//! plan does not contain, and is explicitly left as an unowned seam for
//! M4b/future work rather than silently deferred. Not exercised by
//! `Instances.lean` (no `attribute [-instance]`, no private/exporting
//! distinction in the fixture) — no test in this module currently
//! observes the gap.
//!
//! # `get_instances` ordering (source wins over the brief's paraphrase)
//!
//! The task brief describes the required order as "priority desc, then
//! registration order". Reading the actual oracle shows that is not
//! quite right — recorded here as the disagreement the task materials
//! ask for:
//!
//! 1. `getInstances` builds `result := globalInstances.getUnify type`
//!    (`SynthInstance.lean:210-211`) — B1's own `DiscrTree::get_match_keys`
//!    transcribes exactly this `getUnify`, so `result`'s order IS this
//!    crate's `get_match_keys` output order (wildcard-before-specific,
//!    matching the oracle's own `getUnify.process` order —
//!    `discr_tree.rs`'s module doc, "Match order: wildcard before
//!    specific (oracle order)" — plus deterministic sibling/insertion
//!    order).
//! 2. `result := result.insertionSort fun e1 e2 => e1.priority < e2.priority`
//!    (`SynthInstance.lean:212-214`) — a STABLE sort, ASCENDING by
//!    priority (ties keep their step-1 relative order).
//! 3. The consumer, `generate` (`SynthInstance.lean:589-621`), does NOT
//!    walk this array front-to-back: a `GeneratorNode`'s
//!    `currInstanceIdx` starts at `instances.size`
//!    (`SynthInstance.lean:254`) and `generate` reads `instances[idx]!`
//!    for `idx := currInstanceIdx - 1`, decrementing — i.e. it reads the
//!    array BACK-TO-FRONT, last element first.
//!
//! Composing 2 and 3: the actual resolution order is the REVERSE of the
//! step-2 ascending-stable-sorted array. Reversing an ascending-stable
//! sort does give priority-DESCENDING as the primary key (correct, and
//! what the brief says) — but for a TIE, reversing also reverses the
//! tied elements' own relative order, so ties resolve in the REVERSE of
//! `getUnify`'s own traversal order, not the forward "registration
//! order" the brief's paraphrase suggests. `get_instances` below
//! reproduces this exactly — stable-sort ascending by priority, then
//! reverse the whole vector — rather than writing a from-scratch
//! `(priority desc, index desc)` comparator, so it is correct by
//! construction rather than by a second, independently-checked
//! derivation. Not observable against `Instances.olean` (every instance
//! there has the same, default priority and there is at most one
//! instance per class/type pair — no ties, no multi-candidate query),
//! so this module's own `#[cfg(test)]` builds a synthetic tied scenario
//! to pin it (`get_instances_orders_by_priority_desc_then_reverse_of_ties`).
//!
//! Local instances (`SynthInstance.lean:230-239`, pushed onto the END of
//! `result` AFTER the sort above, with no further sort) are out of
//! scope for this table (see the `global_name: None` seam above) and so
//! is the `isClass?`/`forallTelescopeReducing` goal-telescoping
//! `getInstances` itself does up front (`SynthInstance.lean:205-206`) —
//! `get_instances` here takes an already-telescoped class application,
//! matching every other B2/B1 query-side helper's contract; a future B5
//! task owns stripping any leading binders off an actual synthesis
//! goal before calling this.
//!
//! # Default instances: read order, not re-sorted here
//!
//! `getDefaultInstances` (`Instances.lean:432-436`) returns the raw,
//! UNSORTED-by-priority per-class list; the toolchain's own priority
//! ordering happens one layer up, in `synthesizeUsingDefault`
//! (`Lean/Elab/SyntheticMVars.lean:213-221`): iterate DISTINCT priority
//! values descending (`getDefaultInstancesPriorities`'s `PrioritySet`,
//! a `TreeSet` ordered by `compare y x` — i.e. descending,
//! `Instances.lean:383`), and at each priority, filter+walk the
//! per-class list in ITS OWN stored order. That stored order is itself
//! the REVERSE of registration: `addDefaultInstanceEntry`
//! (`Instances.lean:390-394`) CONS-prepends every new entry onto its
//! class's list (`(e.instanceName, e.priority) :: insts`), so the
//! most-recently-registered entry for a class is always at the head.
//! `default_instances` below reproduces exactly that stored order (not
//! a priority sort — the brief's own signature gives no ordering
//! requirement, and re-sorting here would diverge from what
//! `getDefaultInstances` itself actually returns) by reversing the
//! WHOLE flat `defaults` vec (registration order) before filtering by
//! class — reversing-then-filtering reproduces cons-prepend's per-class
//! ordering exactly, for the same "reverse of a stable-ordered sequence
//! preserves the subsequence's own reversal" reason `get_instances`
//! relies on above.
//!
//! `getDefaultInstances` (`Instances.lean:432-436`) also applies its OWN
//! private-instance filter that is separate from, and not modeled by, the
//! erasure/private seam documented above:
//! ```text
//! if env.isExporting then
//!   -- private instances must not leak into public scope
//!   return insts.filter fun (n, _) => env.contains n
//! else
//!   return insts
//! ```
//! i.e. when the environment is in "exporting" mode, a default-instance
//! entry whose declared name is not itself visible/contained in the
//! current environment is dropped. `default_instances` below does not
//! model this at all — no `isExporting`/`contains` check anywhere in this
//! table or method — same unowned, PR-A-shaped-decoder gap as the
//! erasure/private seam above (this crate has no decoded "is this
//! constant private / is the environment exporting" state to check
//! against), not yet exercised by `Instances.olean`.
//!
//! # Landed ahead of its consumer
//!
//! `get_instances`/`default_instances`/`instance_named` are `pub(crate)`
//! per this task's own interface spec (not part of `leanr_meta`'s
//! external API), and PR-B's tabled resolution driver (task B5) — the
//! real, non-test call site — has not landed yet. Until it does, every
//! item in this module (and, transitively through `get_instances` ->
//! `discr_get_match`, every item in `discr_path.rs` too — see that
//! module's own updated doc) is reachable only from this module's own
//! `#[cfg(test)]` tests, exactly the situation `discr_path.rs` was in
//! before this task landed (its own now-removed blanket
//! `#![allow(dead_code)]`). `#![allow(dead_code)]` below is scoped to
//! this one module (an inner attribute on the `instances` module, not
//! the whole crate) and should be removed once B5 wires this table in.

use std::collections::HashMap;

use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::EnvView;
use leanr_olean::{DefaultInstanceEntry, EntryScope, InstanceEntry};

use crate::discr_tree::DiscrTree;
use crate::{MetaCtx, MetaError};

/// One resolvable instance candidate. oracle:
/// `Lean.Meta.SynthInstance.Instance` (`SynthInstance.lean:40-43`) plus
/// the extra `ty`/`priority`/`global_name` fields this table caches
/// alongside it (the oracle recomputes an instance's type on demand via
/// `inferType`; storing it here avoids a `MetaCtx::infer_type` call per
/// candidate per query since `Instance::ty` is available for free at
/// table-construction time, off `ConstantVal.ty` — see
/// `InstanceTable::build`).
#[derive(Debug, Clone)]
pub(crate) struct Instance {
    pub val: ExprId,
    /// The instance's DECLARED type (`ConstantVal.ty`), still carrying
    /// the declaration's own rigid `Level.param`s.
    ///
    /// Narrowed from this module's former blanket
    /// `#![allow(dead_code)]` (removed by task B5): B5's `get_subgoals`
    /// deliberately does NOT read this cache -- it transcribes the
    /// oracle's own `inferType instVal` (`SynthInstance.lean:349`)
    /// against the LEVEL-REFRESHED `val`, which is the only spelling
    /// that gets the fresh universe metavariables into the telescoped
    /// type. Reading `ty` there instead would additionally require
    /// re-running `instantiate_level_params` with those same fresh
    /// levels, i.e. redoing by hand exactly what `infer_const` already
    /// does. Kept (it is free at table-construction time) for the
    /// elaborator-layer consumers that will want a candidate's declared
    /// type without a live `mctx` -- `synthesizeUsingDefault`
    /// (`Elab/SyntheticMVars.lean:213-221`) and instance diagnostics.
    /// Owner: M4b.
    #[allow(dead_code)]
    pub ty: ExprId,
    pub priority: usize,
    pub synth_order: Vec<usize>,
    /// Narrowed from this module's former blanket
    /// `#![allow(dead_code)]` (removed by task B5): the resolution
    /// driver identifies a candidate by its `val` (the `Const` it
    /// applies), never by name -- the oracle only reads `declName` off
    /// `inst.val.getAppFn` for DIAGNOSTICS (`recordInstance`,
    /// `SynthInstance.lean:347-348`, gated on `isDiagnosticsEnabled`),
    /// which this crate has no channel for. Read today only by
    /// `#[cfg(test)]` assertions and by `InstanceTable::by_name`'s own
    /// keying; owner of the real consumer (instance diagnostics /
    /// erasure filtering, this module's own erasure seam): M4b.
    #[allow(dead_code)]
    pub global_name: Option<NameId>,
}

/// The whole-table analogue of `Lean.Meta.Instances`
/// (`Instances.lean:76-80`): a discrimination tree keyed the same way
/// (`discrTree`), plus an auxiliary name-indexed lookup (`instanceNames`
/// there; `by_name` here) this crate's test/diagnostic code uses to find
/// one instance by its declaration name without a full discr-tree query.
/// `defaults` is the flat, unwrapped analogue of
/// `Lean.Meta.DefaultInstances.defaultInstances`
/// (`Instances.lean:385-386`, there a `NameMap (List (Name × Nat))`;
/// here a plain `Vec` filtered by [`MetaCtx::default_instances`] at read
/// time — see that method's doc for why grouping eagerly here would
/// have to reproduce the SAME cons-prepend order anyway, so there is no
/// win to precomputing it). No `erased` field: see this module's own
/// doc on erasure filtering — nothing here ever populates or consults
/// one.
///
/// **Divergence from the oracle's `insertVal` (owned by B1, not this
/// task)**: `DiscrTree::insert` (`discr_tree.rs`) unconditionally pushes
/// onto a node's value vec. The oracle's `insertVal`
/// (`DiscrTree/Basic.lean:139-150`) instead REPLACES the first `vs[i]`
/// with `v == vs[i]`, where `InstanceEntry`'s `BEq` compares only
/// `.val` (`e₁.val == e₂.val`, `Instances.lean:66-67`). So re-registering
/// an instance under the same `val` (e.g. `attribute [instance 100] foo`
/// changing only `foo`'s priority) yields ONE entry in Lean's tree but
/// TWO entries here — the stale one keeps its old priority, and
/// [`InstanceTable::get_by_name`]'s `by_name` map (last-write-wins, a
/// plain `HashMap::insert`) then disagrees with what `tree` returns. The
/// fix belongs to B1's `DiscrTree::insert`, not here — see that module's
/// own doc — but `InstanceTable::build` is the first consumer where
/// duplicate values become semantically possible, hence the note here.
#[derive(Default)]
pub(crate) struct InstanceTable {
    tree: DiscrTree<Instance>,
    /// See [`InstanceTable::get_by_name`] for the allow's rationale.
    #[allow(dead_code)]
    by_name: HashMap<NameId, Instance>,
    /// See [`MetaCtx::default_instances`] for the allow's rationale.
    #[allow(dead_code)]
    defaults: Vec<(NameId, NameId, usize)>,
}

impl InstanceTable {
    /// Build the whole table once, from one module's decoded
    /// `instanceExtension`/`defaultInstanceExtension` entries. Called
    /// exactly once, from `MetaCtx::new` (`metactx.rs`) — never
    /// per-query (Global Constraints: `synth_order` computed/read once
    /// at registration, never recomputed).
    pub(crate) fn build(
        view: EnvView,
        instances: &[InstanceEntry],
        default_instances: &[DefaultInstanceEntry],
    ) -> InstanceTable {
        let mut tree = DiscrTree::default();
        let mut by_name = HashMap::new();
        for e in instances {
            // Global-only (named seam, module doc: no namespace-open
            // tracking exists here, same posture as `MetaCtx::new`'s
            // own `ReducibilityEntry` filter).
            if !matches!(e.scope, EntryScope::Global) {
                continue;
            }
            // `global_name: None` / unresolvable name (named seams,
            // module doc): drop, never panic or fabricate a `ty`.
            let Some(name) = e.global_name else {
                continue;
            };
            let Some(info) = view.get(name) else {
                continue;
            };
            let inst = Instance {
                // `val: e.val` verbatim — level params NOT refreshed to
                // fresh mvars here; see module doc's "`val`'s level
                // params are NOT refreshed here" seam (owned by B5).
                val: e.val,
                ty: info.constant_val().ty,
                priority: e.priority,
                synth_order: e.synth_order.clone(),
                global_name: Some(name),
            };
            tree.insert(&e.keys, inst.clone());
            by_name.insert(name, inst);
        }
        let defaults = default_instances
            .iter()
            .map(|d| (d.class_name, d.instance_name, d.priority))
            .collect();
        InstanceTable {
            tree,
            by_name,
            defaults,
        }
    }

    /// Narrowed from this module's former blanket
    /// `#![allow(dead_code)]` (removed by task B5): the name-indexed
    /// half of the table (mirroring the real `Instances.instanceNames`,
    /// `Instances.lean:78`) is not on B5's resolution path at all --
    /// that path is `get_instances` -> discrimination tree. Its only
    /// callers are `#[cfg(test)]` (`test_support::instance_named`) and
    /// the elaborator-layer instance diagnostics that will want a
    /// by-name lookup. Owner: M4b.
    #[allow(dead_code)]
    pub(crate) fn get_by_name(&self, name: NameId) -> Option<&Instance> {
        self.by_name.get(&name)
    }
}

impl<'e> MetaCtx<'e> {
    /// `discr_get_match` on `goal`, sorted into the oracle's actual
    /// `getInstances` resolution order — see this module's doc for the
    /// full derivation (priority descending; ties broken by the REVERSE
    /// of `getUnify`'s own traversal order, not forward registration
    /// order).
    ///
    /// **Consumption contract for callers (B5): element 0 is the FIRST
    /// candidate to try — consume this result FRONT-TO-BACK.** This is
    /// the opposite direction from the oracle's own array, which
    /// `generate` reads BACK-TO-FRONT (see the module doc's derivation);
    /// the whole point of composing the stable-ascending sort with a
    /// `reverse()` here is to undo that back-to-front reading so this
    /// method's result is already in try-order. Do not re-reverse it.
    ///
    /// Swaps `self.instances` out via `mem::take` before calling
    /// `discr_get_match` (same idiom as `defeq.rs`/`level.rs`'s own
    /// `mem::take(&mut self.postponed)`): `discr_get_match(&mut self,
    /// tree: &DiscrTree<V>, ..)` needs both a mutable borrow of `self`
    /// (to run `mk_path`) and an immutable borrow of `self.instances.tree`
    /// alive for its whole call — `self.discr_get_match(&self.instances.tree,
    /// ..)` cannot borrow-check directly (the mutable receiver borrow and
    /// the argument's borrow of a part of the same `self` conflict), so
    /// the table is temporarily taken out of `self` (replaced by
    /// `InstanceTable::default()`, an empty table, for the duration of
    /// the call) and put back immediately after.
    pub(crate) fn get_instances(&mut self, goal: ExprId) -> Result<Vec<Instance>, MetaError> {
        // INVARIANT (re-entrancy): `self.instances` is `InstanceTable::default()`
        // (empty) for the whole duration of the `discr_get_match` call
        // below. Harmless today because `mk_path`/`whnf` never consult
        // the instance table, so nothing reachable from
        // `discr_get_match` can observe the table being briefly taken.
        // If a future change makes path construction (or anything else
        // `discr_get_match` transitively calls) re-entrant into instance
        // lookup, a nested `get_instances` call here would silently see
        // this now-empty placeholder table and report "no instances"
        // rather than erroring — there is no assertion below that would
        // catch that, so a future change widening what `discr_get_match`
        // touches must re-check this invariant by inspection.
        let table = std::mem::take(&mut self.instances);
        let result: Result<Vec<Instance>, MetaError> = self
            .discr_get_match(&table.tree, goal)
            .map(|v| v.into_iter().cloned().collect());
        self.instances = table;
        let mut found = result?;
        // oracle: `insertionSort (·.priority < ·.priority)` (ascending,
        // stable) then `generate`'s back-to-front consumption — see
        // this module's doc for why "stable-ascending-sort, then
        // reverse the whole vector" is the exact (not approximate)
        // transcription of that composition.
        found.sort_by_key(|i| i.priority);
        found.reverse();
        Ok(found)
    }

    /// Find one instance by its declaration name. Not part of the
    /// brief's stated interface (only `get_instances`/`default_instances`
    /// are) — added because `InstanceTable::by_name` mirrors a REAL
    /// oracle field (`Instances.instanceNames`, `Instances.lean:78`),
    /// and this crate's own tests need a name-targeted lookup (the
    /// task's own Step-1 test, `parametrized_instance_has_two_synth_subgoals`)
    /// without hand-constructing a discrimination-tree query for a
    /// parametrized instance's own (metavariable-shaped) type.
    /// See [`InstanceTable::get_by_name`] for the allow's rationale.
    #[allow(dead_code)]
    pub(crate) fn instance_named(&self, name: NameId) -> Option<&Instance> {
        self.instances.get_by_name(name)
    }

    /// The per-class default-instance list, in the SAME order
    /// `Lean.Meta.getDefaultInstances` itself returns (most-recently
    /// -registered first) — see this module's doc for why that is NOT a
    /// priority sort.
    /// Narrowed from this module's former blanket
    /// `#![allow(dead_code)]` (removed by task B5): default instances
    /// are consumed one layer ABOVE synthesis, by `synthesizeUsingDefault`
    /// (`Elab/SyntheticMVars.lean:213-221`), never by
    /// `SynthInstance.main` itself -- so B5's driver correctly has no
    /// call to this, and no task in this plan builds that elaborator
    /// layer. Owner: M4b.
    #[allow(dead_code)]
    pub(crate) fn default_instances(&self, class: NameId) -> Vec<(NameId, usize)> {
        self.instances
            .defaults
            .iter()
            .rev()
            .filter(|(c, _, _)| *c == class)
            .map(|(_, inst, prio)| (*inst, *prio))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanr_olean::DiscrKey;

    use crate::test_support::{
        const_named, instance_named, parse_goal, render_name, with_instances_ctx,
    };

    /// Step-1 brief test: the goal `Add N` must turn up `instAddN`.
    #[test]
    fn instance_table_finds_add_n() {
        with_instances_ctx(|ctx| {
            let goal = parse_goal(ctx, "Add N");
            let found = ctx.get_instances(goal).expect("get_instances");
            assert!(
                found
                    .iter()
                    .any(|i| i.global_name.map(|n| render_name(ctx, n))
                        == Some("instAddN".to_string())),
                "found: {:?}",
                found
                    .iter()
                    .map(|i| i.global_name.map(|n| render_name(ctx, n)))
                    .collect::<Vec<_>>()
            );
        });
    }

    /// Step-1 brief test: `instAddProd {a b} [Add a] [Add b] : Add (Prod
    /// a b)` decodes with two synthesis subgoals (PR-A's own confirmed
    /// pin: `synth_order == [2, 3]`; asserting `.len() == 2` here is the
    /// brief's own, slightly weaker, framing — kept as specified).
    #[test]
    fn parametrized_instance_has_two_synth_subgoals() {
        with_instances_ctx(|ctx| {
            let inst = instance_named(ctx, "instAddProd").expect("instAddProd registered");
            assert_eq!(
                inst.synth_order.len(),
                2,
                "synth_order: {:?}",
                inst.synth_order
            );
            assert_eq!(inst.synth_order, vec![2, 3]);
        });
    }

    /// `default_instances` finds `instOfNN` (`@[default_instance]`) under
    /// its class `OfN`.
    #[test]
    fn default_instances_finds_the_default_instance() {
        with_instances_ctx(|ctx| {
            let of_n = const_named(ctx, "OfN");
            let of_n_name = if let leanr_kernel::bank::terms::Node::Const {
                name: Some(n), ..
            } = ctx.node(of_n)
            {
                n
            } else {
                panic!("OfN is not a bare const")
            };
            let defaults = ctx.default_instances(of_n_name);
            let names: Vec<String> = defaults.iter().map(|(n, _)| render_name(ctx, *n)).collect();
            assert!(
                names.contains(&"instOfNN".to_string()),
                "default_instances(OfN): {names:?}"
            );
        });
    }

    /// `get_instances`'s ordering pin (task-mandated: a bare "contains"
    /// check doesn't cover it). `Instances.olean` has no priority ties,
    /// so this builds a synthetic 4-instance scenario directly (this
    /// module's own `#[cfg(test)]`, so `InstanceTable`'s private fields
    /// are reachable) and checks the exact output order: priority
    /// descending, ties broken by the REVERSE of insertion/traversal
    /// order (see the module doc's derivation).
    #[test]
    fn get_instances_orders_by_priority_desc_then_reverse_of_ties() {
        with_instances_ctx(|ctx| {
            let filler = const_named(ctx, "Add");
            let mk = |idx: u32, priority: usize| Instance {
                val: filler,
                ty: filler,
                priority,
                synth_order: Vec::new(),
                global_name: Some(NameId::from_index(idx, false).unwrap()),
            };
            // Insertion order: idx0(prio 5), idx1(prio 10), idx2(prio 10),
            // idx3(prio 1) -- all under one root Star key so a single
            // concrete-headed query matches all four
            // (`root_star_bucket_matches_any_concrete_query`,
            // `discr_tree.rs`, is the same shape).
            let mut tree = DiscrTree::default();
            tree.insert(&[DiscrKey::Star], mk(0, 5));
            tree.insert(&[DiscrKey::Star], mk(1, 10));
            tree.insert(&[DiscrKey::Star], mk(2, 10));
            tree.insert(&[DiscrKey::Star], mk(3, 1));
            ctx.instances = InstanceTable {
                tree,
                by_name: HashMap::new(),
                defaults: Vec::new(),
            };

            let goal = const_named(ctx, "Add"); // bare `Add`: mk_path => [Const Add 0]
            let found = ctx.get_instances(goal).expect("get_instances");
            let idxs: Vec<u32> = found
                .iter()
                .map(|i| i.global_name.expect("global_name").index() as u32)
                .collect();
            // priority-desc: idx1/idx2 (prio 10) before idx0 (prio 5)
            // before idx3 (prio 1); within the idx1/idx2 tie, REVERSE of
            // insertion order (idx2 inserted after idx1) => idx2 first.
            assert_eq!(idxs, vec![2, 1, 0, 3], "found: {found:?}");
        });
    }
}
