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
//! # `global_name: None` — two sources, only one of them adversarial
//!
//! **A local instance (legitimate).** `get_instances` constructs a
//! candidate directly for every in-scope local instance
//! (oracle: `getInstances` :230-237), whose `val` is an fvar and which
//! has no declaration name at all. These never pass through
//! `InstanceTable::build` and are never serialized — `addInstance`
//! (`Instances.lean:283-304`) is the only producer of a persisted
//! `instanceExtension` entry and always sets `globalName? := declName`.
//! So `global_name: None` on a candidate returned by `get_instances`
//! means "local", and any reader that treats it as malformed input is
//! wrong.
//!
//! **A malformed decode (adversarial).** Inside `InstanceTable::build`,
//! reading `global_name = None` off `.olean` bytes still means exactly
//! what it meant before: there is no `Name` to resolve a `ty` from
//! (`EnvView::get` needs one) and no other source for the instance's
//! declared type, so `build` drops the entry. Dropping a candidate is
//! incompleteness only (`get_instances` simply never offers it; the
//! kernel independently re-checks whatever IS synthesized), never a
//! wrong verdict. Global Constraints: `.olean` bytes are untrusted.
//!
//! The distinction is by CONSTRUCTION SITE, not by inspection: nothing
//! about a `None` tells you which it was. Readers must therefore not
//! infer "malformed" from `global_name.is_none()`.
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
//! Local instances (`SynthInstance.lean:230-239`) are pushed onto the
//! END of `result` AFTER the sort above, with no further sort — i.e.
//! `generate`, reading back-to-front, reaches them FIRST. They are not
//! part of this TABLE (they never touch `instanceExtension` — see the
//! `global_name: None` seam above); `get_instances` appends them at
//! query time off `MetaCtx::local_instances`, between the sort and the
//! reverse, so they come out ahead of every global. Still out of scope
//! here is the `isClass?`/`forallTelescopeReducing` goal-telescoping
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
//! # Dead-code allow, narrowed
//!
//! PR-B's tabled resolution driver (task B5) has landed and is the real,
//! non-test call site for this module: `get_instances` is on `synth.rs`'s
//! resolution path (transitively through `discr_get_match`, every item
//! in `discr_path.rs` too — see that module's own doc), so the blanket
//! `#![allow(dead_code)]` this module used to carry is gone. What
//! remains is six narrow, per-item allows, each with its own oracle
//! citation and owning task, for the items B5 does NOT put on the
//! resolution path: `Instance::ty`/`Instance::global_name`,
//! `InstanceTable::{by_name, get_by_name}` + `MetaCtx::instance_named`
//! (the name-indexed half of the table), and
//! `InstanceTable::defaults` + `MetaCtx::default_instances` (default
//! instances are consumed one layer above synthesis, by
//! `synthesizeUsingDefault`, not by `SynthInstance.main`). Each allow
//! site below carries its own reasoning; none of them is a stand-in for
//! the removed blanket allow.

use std::collections::HashMap;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::{instantiate_rev, BinderInfo, EnvView};
use leanr_olean::{ClassEntry, DefaultInstanceEntry, EntryScope, InstanceEntry};

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
    /// Read by [`MetaCtx::default_instances`] (per-class) and, since
    /// M4b-3 P3 task 4, by [`MetaCtx::default_instance_priorities`]
    /// (global) — the latter is genuinely `pub`, so the field no longer
    /// needs the `#[allow(dead_code)]` its sibling `by_name` still does.
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
        // oracle: `getInstances` resolves the goal's class name
        // (`SynthInstance.lean:205-209`) BEFORE it touches the global
        // index (:210), and this transcription keeps that order for a
        // second reason of its own: the `mem::take` below leaves
        // `self.instances` EMPTY for the duration of `discr_get_match`,
        // and `is_class` can REDUCE (its expensive path runs whnf under
        // `Reducible`; even its "quick" path answers `.undef`, i.e.
        // falls through to that path, for any definition-headed type
        // under the ambient transparency). Calling it up here puts
        // whatever it reduces strictly OUTSIDE that window, which the
        // note on the window below shows is load-bearing rather than
        // tidy: a whnf inside the window CAN re-enter `get_instances`.
        // The faithful order and the safe order are the same order,
        // which is worth not re-deriving later.
        //
        // `is_class` swallows its own errors to `None`
        // (`metactx.rs:1256-1262`, the oracle's `try … catch _ =>
        // return none`, `Basic.lean:1542-1543`), so a step-budget
        // exhaustion or a loose bvar inside THAT whnf silently drops
        // every LOCAL candidate here while still returning the globals
        // — incompleteness, never a wrong candidate, but a failure this
        // function cannot see.
        //
        // Two deliberate differences from the oracle at this point, both
        // pre-existing (see the module doc): this takes an
        // ALREADY-telescoped class application, so there is no
        // `forallTelescopeReducing` here — and hence no need for the
        // oracle's own "read `localInstances` before the telescope
        // updates them" precaution (:203-204); and a goal that is not a
        // class is `None` here rather than the oracle's hard error
        // (:207). `None` only suppresses the local half below — the
        // global lookup is unchanged, so no existing caller's result
        // moves.
        //
        // SEAM (unowned): nothing downstream raises that error either.
        // `mk_generator_node` (`synth.rs:2358-2367`) returns `Ok(None)`
        // on an empty candidate list, where the oracle throws "type
        // class instance expected" (:207) — so a non-class synthesis
        // goal is reported as "no instance found" rather than as the
        // malformed goal it is. Diagnostic quality only, never a wrong
        // verdict; no task in the local-instances slice owns it (task
        // 10's own seam note leaves the same divergence alone for the
        // same reason).
        let class_name = self.is_class(goal)?;

        // INVARIANT (re-entrancy): `self.instances` is `InstanceTable::default()`
        // (empty) for the whole duration of the `discr_get_match` call
        // below.
        //
        // This window is REACHABLE from instance lookup, contrary to
        // what this comment claimed before the local-instances slice
        // ("harmless, `mk_path`/`whnf` never consult the instance
        // table"). Traced hop by hop:
        //
        //   `discr_get_match` -> `mk_path` -> `mk_path_aux` ->
        //   `push_args_aux` (`discr_path.rs:462,471`) ->
        //   `param_binder_infos` (`:527`) -> `self.whnf(ty)` (`:538`;
        //   `is_type`/`is_proof` reach `whnf_default` the same way) ->
        //   `unfold_definition`'s smart-unfolding channel
        //   (`whnf.rs:2698,2731`) -> `smart_unfolding_reduce` (`:1454`)
        //   -> `sunfold_go_match_body` (`:1721`) -> `synth_pending`
        //   (`:1740`, `:1380`) -> `synth_instance` (`:1434`;
        //   `synth.rs:1644`) -> `mk_generator_node` (`synth.rs:2358`)
        //   -> `get_instances` (`synth.rs:2365`).
        //
        // CONSEQUENCE: a `get_instances` entered through that chain
        // while this window is open takes an ALREADY-EMPTY table, finds
        // no global candidates, and answers "no instances" without
        // erroring — silent incompleteness at the synthesis layer.
        // (Its LOCAL half is unaffected: locals come off
        // `MetaCtx::local_instances`, never off this table.) Nothing
        // asserts against it and no committed test constructs the
        // nesting, so it is a latent hazard rather than an observed
        // failure. It PREDATES this slice — both the take and the false
        // "harmless" claim were already here — and is deliberately left
        // in place (ruling R9): closing it changes how the GLOBAL
        // lookup path holds its table, and that behavior change must
        // not land inside this slice's corpus-neutrality gate.
        // Recorded here as the named seam it is.
        //
        // It terminates rather than looping: `synth_pending` is capped
        // by `MAX_SYNTH_PENDING_DEPTH` (`whnf.rs:138`, checked at
        // `:1417`), `synth_instance` bumps `guarded` (`synth.rs:1645`),
        // and `step()` (`metactx.rs:1142-1148`) bounds the whole thing.
        //
        // WHAT THIS BUYS THE CODE BELOW: `is_class` above, and
        // `local_instance_candidate` further down (which whnfs a
        // candidate's telescope, and whose `push_local_decl` runs
        // `is_class` again per binder), both sit OUTSIDE this window,
        // so a nested lookup entered from either sees the FULL table.
        // That placement is load-bearing, not stylistic; their
        // telescopes ride the same cycle and inherit the same bounds.
        // NO test pins the placement, because moving `is_class` inside
        // still answers correctly for the OUTER query — only a nested
        // inner query would be degraded, and nothing in the tests
        // constructs one. Guarded by this comment and by review.
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
        // oracle: :236-237 — the locals are appended to the END of the
        // ascending array, i.e. `generate` reaches them FIRST. With the
        // sort-then-reverse transcription above they therefore go on
        // AFTER the sort and BEFORE the reverse. Appending before the
        // sort would instead file them among the globals at whatever
        // placeholder priority they carry
        // (`a_local_instance_is_tried_before_every_global`).
        //
        // In `localInstances` order (outermost first), so the reverse
        // below leaves the INNERMOST binder's instance first — the
        // oracle's own shadowing order
        // (`the_innermost_local_instance_is_tried_first`).
        if let Some(class_name) = class_name {
            // Snapshot before the loop, not iterated live:
            // `local_instance_candidate` telescopes each candidate's
            // type through `push_local_decl`, which INSTALLS local
            // instances of its own (and `lctx_restore` then removes
            // them), so the live stack is a moving target here — the
            // same hazard the oracle's `:203-204` guards against.
            for li in self.local_instances.to_vec() {
                // oracle: `if linst.className == className` (:231) —
                // exact name equality, never defeq.
                if li.class_name != class_name {
                    continue;
                }
                found.push(self.local_instance_candidate(li.fvar)?);
            }
        }
        found.reverse();
        Ok(found)
    }

    /// oracle: `getInstances` :231-238 — a local instance's candidate
    /// record. Unlike a global's, its `synthOrder` is computed HERE, at
    /// query time, rather than read off the instance extension:
    /// telescope the fvar's own type (`forallTelescopeReducing (←
    /// inferType linst.fvar)`) and collect the positions whose binder
    /// info is instance-implicit.
    ///
    /// `global_name` is `None`, and legitimately so — not the
    /// malformed-bytes case this module's doc describes for a GLOBAL
    /// entry: the oracle's own local record is `{ val := linst.fvar,
    /// synthOrder }` (:237), a bare fvar with no declaration name
    /// anywhere in it.
    ///
    /// `priority` has no oracle counterpart at all: `LocalInstance`
    /// (`MetavarContext.lean:268-273`) carries a `className` and an
    /// `fvar`, nothing else, and the record pushed at :237 carries no
    /// priority either. `0` is therefore a placeholder, never a
    /// transcription — no ordering reads it today, since
    /// `get_instances` appends locals AFTER its sort. It is
    /// deliberately the LOWEST value rather than the highest: were a
    /// future edit to move that append before the sort, a
    /// highest-priority placeholder would silently keep the locals in
    /// front and hide the mistake, while `0` makes it observable.
    fn local_instance_candidate(&mut self, fvar: ExprId) -> Result<Instance, MetaError> {
        let ty = self.infer_type(fvar)?;
        let cp = self.lctx_checkpoint();
        let synth_order = self.instimplicit_binder_positions(ty);
        // Restored unconditionally, error path included — the
        // `is_def_eq_binding_shallow`/`_body` split idiom
        // (`defeq.rs:357-365`). The telescope's fvars, and the local
        // instances `push_local_decl` installed for the
        // instance-implicit ones, must not outlive this call even when
        // a binder's type fails to reduce
        // (`building_a_local_candidate_restores_the_context`).
        self.lctx_restore(cp);
        Ok(Instance {
            val: fvar,
            ty,
            priority: 0,
            synth_order: synth_order?,
            global_name: None,
        })
    }

    /// The telescope half of [`MetaCtx::local_instance_candidate`]: the
    /// positions of `ty`'s instance-implicit binders. Leaves its fvars
    /// in `lctx` — the caller restores.
    ///
    /// The telescope really OPENS each binder, `forall_bounded_telescope`
    /// -style (`assign.rs:614-648`), rather than walking the `Forall`
    /// spine structurally: a later binder's type may mention an earlier
    /// one, so each domain is `instantiate_rev`'d against the fvars
    /// pushed so far before it is declared — the oracle's own
    /// `d.instantiateRevRange j fvars.size fvars`
    /// (`Basic.lean:1461`, inside `forallTelescopeReducingAuxAux`).
    /// Pushing a domain raw would declare `Add #0` — a decl whose type
    /// carries a LOOSE BVAR — into the local context, which every path
    /// that later reduces that type rejects outright
    /// (`whnf.rs:239-246`). The non-forall tail is instantiated the
    /// same way before it is whnf'd, matching the oracle's own
    /// `type.instantiateRevRange` on that arm (`Basic.lean:1473`).
    ///
    /// `push_local_decl` INSTALLS a local instance for each class-typed
    /// binder (task 4's chokepoint), so this recursion re-enters the
    /// very set `get_instances` is iterating — which is exactly the
    /// oracle's behavior, `forallTelescopeReducing` installing through
    /// `withNewLocalInstancesImp` (`Basic.lean:1472`), and the
    /// self-reference `Basic.lean:1402-1406` acknowledges. It is
    /// invisible to the caller because `get_instances` iterates a
    /// SNAPSHOT and this call is bracketed by `lctx_restore`.
    ///
    /// Termination is NOT simply "the telescope is finite". The `whnf`
    /// below, and the `is_class` each `push_local_decl` runs, both sit
    /// on the `whnf -> smart unfolding -> synth_pending ->
    /// synth_instance -> get_instances` cycle traced in
    /// `get_instances`' own re-entrancy note, so this can re-enter
    /// instance lookup and reach here again. What bounds it is that
    /// cycle's own bounds: `MAX_SYNTH_PENDING_DEPTH` (`whnf.rs:138`),
    /// `synth_instance`'s `guarded` bump (`synth.rs:1645`), and the
    /// step budget (`metactx.rs:1142-1148`). Each such re-entry does
    /// see the full instance table, because this method runs outside
    /// `get_instances`' `mem::take` window.
    fn instimplicit_binder_positions(&mut self, ty: ExprId) -> Result<Vec<usize>, MetaError> {
        let mut synth_order = Vec::new();
        let mut xs: Vec<ExprId> = Vec::new();
        let mut cur = ty;
        let mut i = 0usize;
        loop {
            let t = if matches!(self.node(cur), Node::Forall { .. }) {
                cur
            } else {
                let closed = instantiate_rev(
                    self.scratch,
                    Some(self.view.store),
                    cur,
                    &xs,
                    &mut self.guard,
                )?;
                self.whnf(closed)?
            };
            let Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = self.node(t)
            else {
                break;
            };
            // oracle: `if (← getFVarLocalDecl x).binderInfo ==
            // .instImplicit then order := order.push i` (:234-236) —
            // the index is over the WHOLE telescope, not over the
            // instance-implicit binders alone.
            if binder_info == BinderInfo::InstImplicit {
                synth_order.push(i);
            }
            let d = instantiate_rev(
                self.scratch,
                Some(self.view.store),
                binder_type,
                &xs,
                &mut self.guard,
            )?;
            let fvar = self.push_local_decl(binder_name, d, binder_info)?;
            xs.push(fvar);
            cur = body;
            i += 1;
        }
        Ok(synth_order)
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

    /// oracle: `getDefaultInstancesPriorities` (`Instances.lean:429-430`)
    /// — the GLOBAL priority set across every class, DESCENDING and
    /// distinct (`PrioritySet := Std.TreeSet Nat (fun x y => compare y x)`,
    /// `Instances.lean:383`). `synthesizeUsingDefault`
    /// (`SyntheticMVars.lean:215-221`) walks it outermost, trying every
    /// pending mvar at one priority before dropping to the next.
    ///
    /// New rather than derived: `default_instances`/`default_instances_of`
    /// are per-class, and the priority walk is not.
    pub fn default_instance_priorities(&self) -> Vec<usize> {
        let mut prios: Vec<usize> = self.instances.defaults.iter().map(|(_, _, p)| *p).collect();
        prios.sort_unstable();
        prios.dedup();
        prios.reverse();
        prios
    }
}

/// The decoded `Lean.classExtension` state. oracle: `ClassState`
/// (`Class.lean:41-45`) — two maps keyed by class name, built once from
/// the module's entries by `ClassState.addEntry` (`Class.lean:49-52`).
///
/// Built once, from `MetaCtx::new`, exactly like [`InstanceTable`] just
/// above; never per-query. Last-write-wins on a duplicate name, matching
/// `SMap.insert` and the same untrusted-input posture
/// `MetaCtx::new`'s `projection_fns` map documents: a real `.olean`
/// never registers a class twice, so a collision is reachable only via
/// adversarial bytes and must not panic.
#[derive(Default)]
pub(crate) struct ClassTable {
    out_params: HashMap<NameId, Vec<usize>>,
    out_level_params: HashMap<NameId, Vec<usize>>,
}

impl ClassTable {
    pub(crate) fn build(entries: &[ClassEntry]) -> ClassTable {
        let mut out_params = HashMap::new();
        let mut out_level_params = HashMap::new();
        for e in entries {
            out_params.insert(e.name, e.out_params.clone());
            out_level_params.insert(e.name, e.out_level_params.clone());
        }
        ClassTable {
            out_params,
            out_level_params,
        }
    }

    pub(crate) fn out_params(&self, class_name: NameId) -> Option<&[usize]> {
        self.out_params.get(&class_name).map(|v| v.as_slice())
    }

    /// Is `class_name` a registered type class? oracle:
    /// `isClass env declName` (`Basic.lean:1512`), reading the same
    /// `classExtension` this table is built from.
    ///
    /// Membership is `out_params(..).is_some()`, not "has output
    /// parameters": every class gets a `classExtension` entry whether or
    /// not it declares any, and a class with none has an entry with an
    /// EMPTY slice. Reading emptiness as absence would make every
    /// ordinary class invisible.
    ///
    /// Called from `MetaCtx::is_class_quick_const`/`is_class_expensive`
    /// (Task 4's `MetaCtx::is_class` wiring), which `get_instances`
    /// (Task 6) is now itself a caller of.
    pub(crate) fn is_class_name(&self, class_name: NameId) -> bool {
        self.out_params(class_name).is_some()
    }

    pub(crate) fn out_level_params(&self, class_name: NameId) -> Option<&[usize]> {
        self.out_level_params.get(&class_name).map(|v| v.as_slice())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanr_olean::DiscrKey;

    use crate::test_support::{
        class_app, const_named, instance_named, parametrized_instance_type, parse_goal,
        render_name, with_class_ctx, with_instances_ctx,
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

    /// oracle: `getDefaultInstancesPriorities` (`Instances.lean:429-430`)
    /// — the GLOBAL set of default-instance priorities, DESCENDING and
    /// distinct, across every class (`PrioritySet := Std.TreeSet Nat
    /// (fun x y => compare y x)`, `Instances.lean:383`).
    /// `default_instances` is per-class and cannot produce it, which is
    /// why this is a new accessor rather than a forwarder.
    ///
    /// Builds a SYNTHETIC `defaults` table rather than reading
    /// `Instances.olean`'s (fix round 1, review Important 1).
    /// The FIXTURE — `tests/fixtures/Instances.lean:88`, NOT the
    /// toolchain's `Lean/Meta/Instances.lean` that every other
    /// `Instances.lean:NNN` citation in this file means — declares
    /// exactly ONE `@[default_instance]` (`instOfNN`),
    /// so the fixture yields a one-element vec, against which the task
    /// brief's sketched assertion — re-applying the implementation's own
    /// `sort_unstable`/`dedup`/`reverse` to a clone and comparing — was
    /// vacuous: it passes for any implementation ending in those three
    /// calls, and for `Vec::new()`. This instead pins the exact expected
    /// vector over a table with two distinct priorities, a DUPLICATE
    /// (which only `dedup` removes), an out-of-registration-order entry
    /// (which only `sort`+`reverse` fixes), and TWO CLASSES (so a
    /// per-class implementation cannot pass). Same "assign a synthetic
    /// `InstanceTable` directly" idiom as
    /// `get_instances_orders_by_priority_desc_then_reverse_of_ties`
    /// below — this module's own `#[cfg(test)]`, so the private fields
    /// are reachable.
    #[test]
    fn default_instance_priorities_are_descending_and_distinct() {
        with_instances_ctx(|ctx| {
            let class_a = NameId::from_index(0, false).unwrap();
            let class_b = NameId::from_index(1, false).unwrap();
            let inst = |idx: u32| NameId::from_index(idx, false).unwrap();
            // (class, instance, priority), in REGISTRATION order:
            // deliberately neither sorted nor distinct, and spread over
            // two classes.
            ctx.instances = InstanceTable {
                tree: DiscrTree::default(),
                by_name: HashMap::new(),
                defaults: vec![
                    (class_a, inst(10), 100),
                    (class_b, inst(11), 1000),
                    (class_a, inst(12), 500),
                    // duplicate of the first priority, under the OTHER
                    // class: distinctness is global, not per-class.
                    (class_b, inst(13), 100),
                ],
            };

            assert_eq!(
                ctx.default_instance_priorities(),
                vec![1000, 500, 100],
                "descending and distinct, across every class"
            );
        });
    }

    /// oracle: `getOutParamPositions?` / `getOutLevelParamPositions?` /
    /// `hasOutParams` (`Class.lean:81-82,91-92,85-88`). `Add` is a class with no
    /// output parameters, so it is PRESENT with an empty array — the
    /// oracle's `isClass` is exactly "present in this map"
    /// (`Class.lean:77-78`), and collapsing "absent" into "no out
    /// params" would lose that distinction. `instAddN` (an *instance*,
    /// not a class) stands for a name that is not a class at all: it
    /// must read back `None`, not `Some(&[])`, or the two directions of
    /// the `isClass` distinction are not both covered.
    #[test]
    fn class_table_reads_out_param_positions() {
        with_instances_ctx(|ctx| {
            let op_expr = const_named(ctx, "Op");
            let op = if let leanr_kernel::bank::terms::Node::Const { name: Some(n), .. } =
                ctx.node(op_expr)
            {
                n
            } else {
                panic!("Op is not a bare const")
            };
            let add_expr = const_named(ctx, "Add");
            let add = if let leanr_kernel::bank::terms::Node::Const { name: Some(n), .. } =
                ctx.node(add_expr)
            {
                n
            } else {
                panic!("Add is not a bare const")
            };
            let lvl_expr = const_named(ctx, "Lvl");
            let lvl = if let leanr_kernel::bank::terms::Node::Const { name: Some(n), .. } =
                ctx.node(lvl_expr)
            {
                n
            } else {
                panic!("Lvl is not a bare const")
            };
            let inst_add_n_expr = const_named(ctx, "instAddN");
            let inst_add_n =
                if let leanr_kernel::bank::terms::Node::Const { name: Some(n), .. } =
                    ctx.node(inst_add_n_expr)
                {
                    n
                } else {
                    panic!("instAddN is not a bare const")
                };

            assert_eq!(ctx.get_out_param_positions(op), Some(&[2usize][..]));
            assert_eq!(ctx.get_out_level_param_positions(op), Some(&[][..]));
            assert!(ctx.has_out_params(op));

            assert_eq!(ctx.get_out_param_positions(add), Some(&[][..]));
            assert!(
                !ctx.has_out_params(add),
                "Add has no out params but IS a class"
            );

            assert_eq!(ctx.get_out_param_positions(lvl), Some(&[1usize][..]));
            assert_eq!(ctx.get_out_level_param_positions(lvl), Some(&[1usize][..]));

            // The "absent" direction of the oracle's `isClass` distinction:
            // `instAddN` is a real declared constant in this fixture (an
            // *instance*, not a class), so it must read back `None` — not
            // `Some(&[])`, which is `Add`'s own (present-but-empty) answer
            // just above. Collapsing this to `Some(&[])` (e.g. via an
            // `unwrap_or(&[])`-shaped bug) would silently claim every
            // non-class name is a class with no output parameters.
            assert_eq!(ctx.get_out_param_positions(inst_add_n), None);
            assert!(
                !ctx.has_out_params(inst_add_n),
                "a non-class has no out params either, via the None arm"
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

    /// `N -> Add N` — the shape a parametrized local instance's
    /// conclusion takes (`is_class_looks_through_forall_binders`'s own
    /// doc comment). `add` is `Add`'s `NameId`, as handed back by
    /// [`with_class_ctx`], so the constant this builds is the SAME name
    /// registered in the synthetic `ClassTable`, not a freshly-reinterned
    /// lookalike. Built from [`class_app`]'s `Add N`, promoted to
    /// `test_support` (task 4, ruling R7) since task 4's `metactx.rs`
    /// tests need that same application on its own, without the arrow.
    fn arrow_to_class(ctx: &mut MetaCtx, add: NameId) -> ExprId {
        let add_n = class_app(ctx, add);
        let n = const_named(ctx, "N");
        ctx.mk_arrow(n, add_n).expect("N -> Add N")
    }

    /// `isClassQuick?`'s `.forallE` arm recurses into the BODY
    /// (`Basic.lean:1366`): `{a : Type} → [Add a] → Add (Prod a a)` is a
    /// class, because its conclusion is. This is the shape a
    /// parametrized local instance has, so getting it wrong makes every
    /// such binder invisible.
    #[test]
    fn is_class_looks_through_forall_binders() {
        with_class_ctx(|ctx, add| {
            let ty = arrow_to_class(ctx, add);
            assert_eq!(
                ctx.is_class(ty).expect("is_class"),
                Some(add),
                "a forall whose conclusion is a class IS a class"
            );
        });
    }

    /// A non-class head constant is NOT a class, however class-shaped it
    /// looks. Kills a `is_class` that reports the head constant of any
    /// application without consulting the class table.
    #[test]
    fn is_class_rejects_a_non_class_head() {
        with_class_ctx(|ctx, _add| {
            let n = const_named(ctx, "N");
            assert_eq!(
                ctx.is_class(n).expect("is_class"),
                None,
                "`N` is a type, not a class — a constant-true is_class \
                 would register every binder as a local instance"
            );
        });
    }

    /// `isClassQuick?`'s `.sort`/`.lam`/`.lit`/`.fvar`/`.bvar` arms
    /// return `.none` OUTRIGHT (`Basic.lean:1359-1363`) — they never
    /// reach the expensive path. A port that fell through to
    /// `isClassExpensive?` here would run whnf on shapes the oracle
    /// never whnfs. Checked two ways: the `Option` result (must be
    /// `None`) AND the step counter (must not move) — `None` alone does
    /// NOT discriminate this, because the expensive path's `whnf` on a
    /// bare `Sort` is a no-op that also answers `None` (see the commit
    /// message's mutation-measurement note).
    #[test]
    fn is_class_rejects_a_sort_without_reducing() {
        with_class_ctx(|ctx, _add| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            let steps_before = ctx.steps();
            assert_eq!(ctx.is_class(sort0).expect("is_class"), None);
            assert_eq!(
                ctx.steps(),
                steps_before,
                "a bare Sort must never reach whnf — is_class_quick's Sort \
                 arm has to answer .none outright, not .undef"
            );
        });
    }

    /// Review round 1, I2: Ruling R5's decisive discriminator. `N` here
    /// is a REAL registered `inductive` (`Instances.lean`'s own
    /// `inductive N where ...`, via `with_instances_ctx`'s fixture
    /// replay) — unlike `is_class_rejects_a_non_class_head`'s `N`, which
    /// lives in `with_class_ctx`'s minimal empty environment and so is
    /// merely an UNKNOWN constant to `EnvView::get`, not a known
    /// non-`defnInfo` one. That gap means the non-class-head test alone
    /// cannot tell the brief's original (wrong) sketch —
    /// `is_class_quick_const` answering `.undef` for EVERY non-class
    /// constant — apart from Ruling R5's correct reading: under the
    /// wrong sketch, `N` would still whnf-reduce to itself (an inductive
    /// never unfolds) and still answer `None` from `is_class_expensive`,
    /// so the `Option` result is identical either way — the exact
    /// `is_class_rejects_a_sort_without_reducing`-shaped gap. The step
    /// counter closes it: the oracle's `getConstTemp?` answers `some
    /// (.inductInfo ..)` for `N`, not a `.defnInfo`, so
    /// `isClassQuickConst?` must answer `.none` OUTRIGHT, no whnf ever
    /// called.
    #[test]
    fn is_class_rejects_a_real_inductive_without_reducing() {
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let steps_before = ctx.steps();
            assert_eq!(ctx.is_class(n).expect("is_class"), None);
            assert_eq!(
                ctx.steps(),
                steps_before,
                "a known inductive must answer `.none` from \
                 is_class_quick_const's `getConstTemp?` arm directly, \
                 never reach the expensive whnf path"
            );
        });
    }

    /// Review round 1, I2's companion: the `Defn` arm's OTHER half.
    /// `Unit` (`Instances.lean`'s `abbrev Unit : Type := PUnit`, i.e.
    /// `@[reducible] def Unit : Type := PUnit`) is a non-class
    /// definition that genuinely reaches `is_class_expensive` and
    /// reduces there — `steps()` MUST move, unlike the inductive test
    /// just above. This is `is_class_expensive`'s first exercise from
    /// any test in this task: under the ambient `Default` transparency
    /// `with_instances_ctx` builds, `getDefInfoTemp`'s `.default` arm is
    /// unconditional, so `is_class_quick_const` answers `.undef` for
    /// `Unit` regardless of its own `@[reducible]` attribute; inside
    /// `is_class_expensive`'s own `withReducible` bump, THAT attribute
    /// is what lets `whnf` delta-unfold `Unit` to `PUnit`. `PUnit`'s
    /// head is not a registered class either, so the final answer is
    /// still `None` — the discriminator here is that it got there BY
    /// REDUCING, not by stopping short the way `N` does above.
    #[test]
    fn is_class_reduces_a_reducible_non_class_def() {
        with_instances_ctx(|ctx| {
            let unit = const_named(ctx, "Unit");
            let steps_before = ctx.steps();
            assert_eq!(ctx.is_class(unit).expect("is_class"), None);
            assert!(
                ctx.steps() > steps_before,
                "`Unit` is `@[reducible]` and must reach is_class_expensive's \
                 whnf and actually unfold, not stop at is_class_quick \
                 (steps before: {steps_before}, after: {})",
                ctx.steps()
            );
        });
    }

    /// A local instance is offered as a candidate. oracle:
    /// `getInstances` `:236-237`.
    ///
    /// Fixture note: this and every test below run over
    /// `with_instances_ctx`, NOT the synthetic `with_class_ctx` the task
    /// brief sketched. `get_instances` starts by building a
    /// discrimination-tree PATH for the goal, which resolves the goal's
    /// head constant in the environment (`Infer("unknown constant
    /// 'Add'")` otherwise) — so a query needs a replayed environment,
    /// not a hand-built one-entry `ClassTable`. `Instances.olean` has a
    /// real `class Add`, a real `class Mul`, and real global instances,
    /// which is also what lets the ordering test below measure a local
    /// against a genuine global rather than a synthetic one.
    #[test]
    fn a_local_instance_is_offered_as_a_candidate() {
        with_instances_ctx(|ctx| {
            let add_n = parse_goal(ctx, "Add N");
            let cp = ctx.lctx_checkpoint();
            let inst = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push");
            let found = ctx.get_instances(add_n).expect("get_instances");
            let li = found
                .iter()
                .find(|i| i.val == inst)
                .expect("the in-scope local instance must be a candidate");
            assert!(
                li.global_name.is_none(),
                "a local instance has no declaration name — the oracle's own \
                 record is `{{ val := linst.fvar, synthOrder }}` (:237)"
            );
            assert_eq!(
                li.ty, add_n,
                "a local candidate's `ty` is the fvar's own inferred type"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// A local instance is tried BEFORE every global. oracle: appended
    /// to the end of the ascending array (:230-237), consumed
    /// back-to-front by `generate` — which this crate transcribes as
    /// sort-ascending-then-reverse (see the module doc), so the append
    /// must land between the sort and the reverse.
    ///
    /// This is the slice's most mutable line: appending before the sort
    /// files the local at its placeholder priority among the globals
    /// instead of ahead of all of them (`instAddN` carries the oracle's
    /// default priority, `1000`, so it would win that comparison).
    #[test]
    fn a_local_instance_is_tried_before_every_global() {
        with_instances_ctx(|ctx| {
            let add_n = parse_goal(ctx, "Add N");
            let cp = ctx.lctx_checkpoint();
            let local = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push");
            let found = ctx.get_instances(add_n).expect("get_instances");
            let li = found
                .iter()
                .position(|i| i.val == local)
                .expect("local present");
            let gi = found
                .iter()
                .position(|i| i.global_name.map(|n| render_name(ctx, n)) == Some("instAddN".into()))
                .expect("instAddN present");
            assert!(
                li < gi,
                "local at {li}, instAddN at {gi}: locals are consumed first, \
                 so they must come first in this vector"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// The INNERMOST local instance is tried first, and both locals
    /// still come ahead of every global. oracle: the locals are pushed
    /// in `localInstances` order (outermost first, `:236-237`) onto an
    /// array `generate` reads back-to-front, so the innermost binder
    /// wins — shadowing an outer instance the way scoping demands.
    ///
    /// Not named by the task's own mutation table: an implementation
    /// that reversed only the local segment, or that walked the
    /// snapshot backwards, would still put "a local" first and pass the
    /// test above.
    #[test]
    fn the_innermost_local_instance_is_tried_first() {
        with_instances_ctx(|ctx| {
            let add_n = parse_goal(ctx, "Add N");
            let cp = ctx.lctx_checkpoint();
            let outer = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push outer");
            let inner = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push inner");
            let found = ctx.get_instances(add_n).expect("get_instances");
            let heads: Vec<ExprId> = found.iter().take(2).map(|i| i.val).collect();
            assert_eq!(
                heads,
                vec![inner, outer],
                "innermost local first, then the outer one, then the globals"
            );
            assert!(
                found.len() > 2,
                "the globals must still be there behind them: {found:?}"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// An out-of-scope local instance is not a candidate.
    #[test]
    fn a_closed_binders_instance_is_not_offered() {
        with_instances_ctx(|ctx| {
            let add_n = parse_goal(ctx, "Add N");
            let cp = ctx.lctx_checkpoint();
            let inst = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push");
            ctx.lctx_restore(cp);
            let found = ctx.get_instances(add_n).expect("get_instances");
            assert!(
                found.iter().all(|i| i.val != inst),
                "the binder is closed: its instance left scope with it"
            );
        });
    }

    /// A local instance of a DIFFERENT class is not offered. oracle:
    /// `if linst.className == className` (:231) — exact name equality,
    /// never defeq. `Mul N` and `Add N` are two real, distinct classes
    /// of `Instances.olean`, applied to the same type.
    #[test]
    fn a_local_instance_of_another_class_is_not_offered() {
        with_instances_ctx(|ctx| {
            let mul_n = parse_goal(ctx, "Mul N");
            let add_n = parse_goal(ctx, "Add N");
            let cp = ctx.lctx_checkpoint();
            let inst = ctx
                .push_local_decl(None, mul_n, BinderInfo::InstImplicit)
                .expect("push");
            let found = ctx.get_instances(add_n).expect("get_instances");
            assert!(
                found.iter().all(|i| i.val != inst),
                "a `Mul N` in scope is not a candidate for an `Add N` goal"
            );
            // ... and it IS one for its own class, so the guard above is
            // rejecting on the class name rather than on locals wholesale.
            let for_mul = ctx.get_instances(mul_n).expect("get_instances");
            assert!(
                for_mul.iter().any(|i| i.val == inst),
                "the same local IS a candidate for `Mul N`"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// A local's `synth_order` is read off the INSTANCE-IMPLICIT binders
    /// of its own type. oracle: :231-238 — computed at QUERY time, from
    /// the fvar's own inferred type, where a global's is precomputed by
    /// the instance extension.
    #[test]
    fn a_local_instances_synth_order_comes_from_its_instimplicit_binders() {
        with_instances_ctx(|ctx| {
            // `{a : Type} → [Add a] → Add (Prod a a)`: binder 0 is
            // implicit, binder 1 is instance-implicit.
            let ty = parametrized_instance_type(ctx);
            let goal = parse_goal(ctx, "Add (Prod N N)");
            let cp = ctx.lctx_checkpoint();
            let inst = ctx
                .push_local_decl(None, ty, BinderInfo::InstImplicit)
                .expect("push");
            let found = ctx.get_instances(goal).expect("get_instances");
            let li = found.iter().find(|i| i.val == inst).expect("local present");
            assert_eq!(
                li.synth_order,
                vec![1],
                "only binder 1 is instance-implicit; an empty synth_order \
                 would make the search never solve the subgoal"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// Controller ruling R8: the telescope really OPENS each binder, so
    /// every decl it pushes has a CLOSED type. The task brief's own
    /// sketch declared each domain RAW, which puts `Add #0` — a type
    /// carrying a loose bvar — into the local context for the whole
    /// duration of the telescope.
    ///
    /// Nothing `get_instances` itself returns can see that (`is_class`
    /// answers off the head constant without reducing, so this
    /// fixture's `synth_order` comes out `[1]` either way, and
    /// `is_class` swallows the error a reduction WOULD raise), which is
    /// exactly why this test reaches under `local_instance_candidate`
    /// to the telescope itself and inspects the local context before it
    /// is restored: the defect is a malformed `lctx`, not a wrong
    /// answer. Every consumer that later reduces such a type — whnf
    /// rejects a loose bvar outright, `whnf.rs:239-246` — is the real
    /// exposure.
    #[test]
    fn the_telescope_declares_each_binder_with_a_closed_type() {
        with_instances_ctx(|ctx| {
            // `{a : Type} → [Add a] → Add (Prod a a)`: binder 1's
            // domain MENTIONS binder 0.
            let ty = parametrized_instance_type(ctx);
            let cp = ctx.lctx_checkpoint();
            let order = ctx.instimplicit_binder_positions(ty).expect("telescope");
            assert_eq!(order, vec![1], "binder 1 is the instance-implicit one");
            let pushed: Vec<ExprId> = ctx.local_names[cp..].iter().map(|(_, f)| *f).collect();
            assert_eq!(pushed.len(), 2, "both binders were opened");
            for (i, fvar) in pushed.into_iter().enumerate() {
                let Node::FVar { id: Some(id) } = ctx.node(fvar) else {
                    panic!("push_local_decl returned a non-fvar")
                };
                let decl_ty = ctx.lctx.get(id).expect("declared").ty;
                assert_eq!(
                    ctx.data(decl_ty).loose_bvar_range(),
                    0,
                    "binder {i} was declared with a type carrying a loose \
                     bvar — the telescope substituted no fvar for the \
                     binder it opened before it"
                );
            }
            ctx.lctx_restore(cp);
        });
    }

    /// Telescoping a parametrized local instance leaves NOTHING behind:
    /// neither the binders it opened nor the local instances
    /// `push_local_decl` installed for the instance-implicit ones.
    ///
    /// Ruling R8's companion. The telescope really opens each binder,
    /// and `push_local_decl` is itself a local-instance PRODUCER (the
    /// oracle's own telescope installs too — `Basic.lean:1472`'s
    /// `withNewLocalInstancesImp`), so a missing `lctx_restore` would
    /// leave a `get_instances` QUERY mutating the ambient context and
    /// growing the local-instance set on every call. Not named by the
    /// task's own mutation table.
    #[test]
    fn building_a_local_candidate_restores_the_context() {
        with_instances_ctx(|ctx| {
            let ty = parametrized_instance_type(ctx);
            let goal = parse_goal(ctx, "Add (Prod N N)");
            let cp = ctx.lctx_checkpoint();
            ctx.push_local_decl(None, ty, BinderInfo::InstImplicit)
                .expect("push");
            let depth_before = ctx.lctx_checkpoint();
            let instances_before = ctx.local_instances.entries().len();
            ctx.get_instances(goal).expect("get_instances");
            assert_eq!(
                ctx.lctx_checkpoint(),
                depth_before,
                "the telescope's binders must not outlive the query"
            );
            assert_eq!(
                ctx.local_instances.entries().len(),
                instances_before,
                "nor the local instances those binders installed"
            );
            ctx.lctx_restore(cp);
        });
    }
}
