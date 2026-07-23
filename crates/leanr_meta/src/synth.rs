//! Tabled type-class-synthesis engine: table state, table keys, and
//! waiter/answer bookkeeping (task B4) -- DATA STRUCTURES + TABLE
//! MECHANICS ONLY. The resolution driver (an oracle `synth`/`generate`/
//! `consume`/`resume`-equivalent, `synth_instance`) is task B5's; no
//! function in this module drives resolution, opens a subgoal on its
//! own initiative, or calls anything B5 owns.
//!
//! oracle: `Lean.Meta.SynthInstance` (`SynthInstance.lean`), toolchain
//! leanprover/lean4:v4.33.0-rc1 -- specifically `Instance`/`GeneratorNode`
//! (:40-52), `ConsumerNode` (:54-59), `Waiter` (:61-66), the `MkTableKey`
//! namespace and `mkTableKey` (:92-199), `Answer`/`TableEntry` (:232-239),
//! and `SynthInstance.State` (:244-254) -- plus `Lean.Meta.
//! AbstractMVarsResult` (`Meta/Basic.lean:338-346`), which `Answer.result`
//! is typed by.
//!
//! # `GoalKey`: a hash-consed `ExprId`, not a hand-rolled digest
//!
//! The oracle's own table is `Std.HashMap Expr TableEntry`
//! (`State.tableEntries`, :246) -- the NORMALIZED EXPRESSION itself,
//! compared/hashed via `Expr`'s structural `BEq`/`Hashable`, is the key;
//! Lean never reduces it to a separate integer digest. This crate's
//! `ExprId` already IS a hash-consed structural identity: two
//! structurally-equal expressions interned against the same `Store` are
//! literally the same id (`bank/mod.rs`'s dedup table, `term_intern_row`).
//! `GoalKey` below wraps `ExprId` directly for exactly this reason --
//! it is the precise transcription of "the normalized `Expr` is the
//! key", not an approximation of it, and it is STRICTLY safer than the
//! task brief's own "hash of the goal, hashed structurally" phrasing: a
//! hand-rolled `u64` digest can collide two DIFFERENT goals (the exact
//! vacuity risk this task's own negative test,
//! `different_goals_produce_different_keys`, exists to catch), where
//! reusing the bank's own dedup table costs nothing extra (the interning
//! calls that BUILD the normalized expression already perform the
//! structural comparison that would otherwise have to be redone by a
//! hasher) and -- scoped precisely to the ID REPRESENTATION, not to key
//! collisions in general (Minor 7, review round 1) -- has zero collision
//! risk BY CONSTRUCTION for that representation step: hash-consing
//! itself never conflates two structurally-different trees, full stop.
//! It does NOT make the `_tc.<idx>` NAMING SCHEME collision-free: a goal
//! that genuinely mentions a real fvar or level-param already named
//! `` _tc.0 `` (however unlikely in practice) normalizes to the exact
//! same tree as one whose canonical rename minted that same name, and
//! the two collide. This is not a bug to fix here -- it is ORACLE-
//! IDENTICAL (the real `mkTableKey` mints the literal, unqualified name
//! `` Name.mkNum `_tc idx ``, `:156`, with no freshness check against
//! names already present in `e`, so the real Lean has the exact same
//! exposure) -- just a claim this doc must not overstate.
//!
//! # `normalize_goal_key` / `mkTableKey`
//!
//! oracle: `mkTableKey` (:196-199) delegates to the `MkTableKey`
//! namespace's `normExpr`/`normLevel` (:92-160), run over a `StateM`
//! threading one `MkTableKey.State { nextIdx, lmap, emap, mctx }`
//! (:98-102) -- ONE `nextIdx` counter shared by BOTH maps, so a goal's
//! canonical key numbers EVERY metavariable (level or expr) it mentions,
//! in a single first-occurrence order across the whole interleaved walk
//! (the module doc a few lines above `MkTableKey`, :78-90, gives the
//! worked example: `f ?m ?m ?n` normalizes to `f _tc.0 _tc.0 _tc.1`,
//! same mvar reusing its FIRST index on every later occurrence). Both
//! `normLevel`/`normExpr` gate renaming on assignability, but via TWO
//! DIFFERENT oracle functions that must not be conflated with each
//! other or with `assign.rs`'s own check of a similar name:
//! `normLevel`'s inline check (`getLevelDepth mvarId != mctx.depth`,
//! :119) and `normExpr`'s call to the PUBLIC `MVarId.isAssignable`
//! (`MetavarContext.lean:483-486`: `decl.depth == mctx.depth`) are both
//! DEPTH-ONLY. Neither is `ExprDefEq.lean:1731-1734`'s PRIVATE
//! `isAssignable` (`isReadOnlyOrSyntheticOpaque`) -- the different
//! function `assign.rs::unassigned_mvar_id` correctly transcribes, for a
//! DIFFERENT purpose (occurs-check-time assignment safety during
//! unification, not table keying). Under the real oracle, a
//! `MVarKind.syntheticOpaque` mvar IS renamed by `mkTableKey`: kind plays
//! no role in `MVarId.isAssignable` at all, only depth does. This crate
//! has no per-mvar depth model whatsoever (`MVarDecl`, `mvar_ctx.rs`,
//! carries no depth field; `level.rs`/`assign.rs`'s own module docs
//! record every such collapse as the standing tier-1 seam: "every
//! declared mvar is mutually assignable, single flat mctx depth"), so
//! under that collapse `decl.depth == mctx.depth` /
//! `getLevelDepth mvarId != mctx.depth` are always (respectively)
//! true/false for any DECLARED mvar -- both walks below collapse the
//! check to "always assignable" for every declared mvar, KIND INCLUDED:
//! `norm_expr_body`'s mvar arm does not special-case
//! `MVarKind::SyntheticOpaque` (it IS renamed, same as any other
//! declared mvar), deliberately NOT mirroring
//! `assign.rs::unassigned_mvar_id`'s kind check, because that check
//! answers a different oracle question than this one does.
//!
//! `mkTableKey`'s own doc (:195) states it "assumes `e` does not contain
//! assigned metavariables" -- callers (`mkTableKeyFor`, :262-266) run
//! `instantiateMVars` first. `instantiate_mvars` (this crate's own
//! transcription, `assign.rs:1173-1179`) resolves every ASSIGNED EXPR
//! mvar recursively but -- see its own doc comment's arm list -- never
//! descends into a `Sort`/`Const` node's LEVEL at all, so an assigned
//! LEVEL mvar embedded there is left untouched by that pass. Rather than
//! bolt on a second, separate level-mvar-instantiation pre-pass (which
//! would just be `level.rs::instantiate_level_mvars` inlined a second
//! time, and that helper is private to `level.rs` besides),
//! `normalize_goal_key` below still calls `instantiate_mvars` once (to
//! satisfy `mkTableKey`'s stated precondition for the EXPR side), and
//! folds the LEVEL side's "resolve-assigned-then-rename-unassigned"
//! into `KeyNormalizer::norm_level` itself: an assigned level mvar is
//! resolved to its (recursively normalized) assignment FIRST, and only
//! an mvar confirmed unassigned after that is ever canonically renamed --
//! net effect identical to the oracle's own composed
//! `instantiateMVars ∘ mkTableKey` pipeline, just recomposed to work
//! around where this crate's own `instantiate_mvars` stops short.
//!
//! **The correctness property this buys**: two goals that are
//! α-equivalent up to metavariable identity (same shape, mvars renamed)
//! normalize to literally the same `ExprId` -- both walks visit their
//! respective mvars in the same first-occurrence positions and mint the
//! same `_tc.<idx>` canonical name at each, so the two resulting
//! expression TREES are structurally identical and hash-cons to one id.
//! This is exactly what lets tabled resolution terminate on a cyclic
//! instance graph (B5's concern): a goal reached a second time via a
//! different derivation, but the same shape up to mvar renaming, looks
//! up the SAME table entry instead of spawning a second, unbounded
//! search. Two goals that are genuinely different (different head,
//! different structure, or the same shape with a non-mvar subterm that
//! differs) normalize to different trees and never collide --
//! `different_goals_produce_different_keys` below pins this directly,
//! since a key function that always returns one constant would
//! otherwise pass the stability test alone vacuously.
//!
//! # `Answer`: confirmed against source (brief's guess corrected)
//!
//! oracle (:232-236, verbatim):
//! ```text
//! structure Answer where
//!   result     : AbstractMVarsResult
//!   resultType : Expr
//!   size       : Nat
//! ```
//! The task brief guessed `{ val: ExprId, assignments: <snapshot-like>
//! }` -- a resolved term plus the mvar assignments that produced it.
//! The oracle carries something different in kind, not just in name:
//! `result` is not a bare term at all, it is the term ABSTRACTED over
//! every (assignable, current-depth) metavariable it mentions
//! (`AbstractMVarsResult`, `Meta/Basic.lean:338-343`: `paramNames` --
//! fresh universe-param names substituted for abstracted level mvars;
//! `mvars` -- the original mvar expressions that got lambda-abstracted
//! away, in abstraction order; `expr` -- `fun (m_1:A_1)..(m_k:A_k) =>
//! e'`), which is what makes one answer, once found, replayable against
//! every DIFFERENT waiting consumer's own (different) `MetavarContext`
//! (`tryAnswer`, :423-429, reopens it fresh via `openAbstractMVarsResult`,
//! `Meta/Basic.lean:424-429`, per use) without re-solving -- there is no
//! `MetaSnapshot`-shaped "assignments" field anywhere in the oracle's
//! `Answer`; the abstraction itself is precisely what makes an answer
//! assignment-context-independent. `resultType` is a cached `inferType`
//! of `result.expr`, consulted only by `isNewAnswer`'s cheap dedup check
//! (`!=`, not `isDefEq` -- SynthInstance.lean:445-449, with the oracle's
//! own comment there noting `isDefEq` would be "too expensive") so a
//! second, structurally distinct solution to the same goal is not
//! needlessly re-tried by a future waiter. `size` is the running
//! instance-size budget counter (`cNode.size + 1` at the point the
//! answer completes, :457) checked in `addAnswer` against
//! `synthInstance.maxSize` (default 128, :24-27) -- confirmed present,
//! matching the brief's own hint that `Answer` "may hold ... a
//! size/`numMVars`". `AbstractMVarsResult` is reproduced below as
//! [`AbstractMVarsResult`] (its `num_mvars` mirrors
//! `AbstractMVarsResult.numMVars`, `Meta/Basic.lean:345-346` --
//! `mvars.size`) purely as a DATA SHAPE: the actual `abstractMVars`
//! transform (`Meta/AbstractMVars.lean:60-113`, a full expr-abstraction
//! algorithm in the same family as `mk_lambda_fvars`/`abstract_fvars`)
//! and `openAbstractMVarsResult` (`Meta/Basic.lean:424-429`) are NOT
//! implemented here -- **named seam, owned by B5**: both are only ever
//! invoked from `mkAnswer`/`tryAnswer` (:453-459, :423-429), which are
//! only ever invoked from `addAnswer`/`consume`, all four RESOLUTION-
//! DRIVER functions, not table mechanics. Nothing in this module ever
//! constructs a real (non-placeholder) `Answer`.
//!
//! # `TableEntry`: confirmed against source (brief's guess corrected)
//!
//! oracle (:238-239, verbatim): `structure TableEntry where waiters :
//! Array Waiter; answers : Array Answer := #[]` -- exactly two fields.
//! The brief additionally guessed a `complete: bool`. There is no such
//! field, or concept, in the oracle: a generator node's search being
//! "done" is never tracked as a boolean anywhere on its table entry --
//! it falls out implicitly from `GeneratorNode.currInstanceIdx`
//! reaching `0`, at which point `generate` (:589-593) pops that node off
//! `State.generatorStack` (:246) and it is simply never visited again;
//! the corresponding `TableEntry` itself is never touched or flagged.
//! [`TableEntry`] below is therefore the oracle's exact two fields, no
//! more: adding an untested, unused third field on the strength of the
//! brief's guess alone -- when the oracle manages the identical
//! information a different way, and the eventual driver
//! (`SynthState.generators` emptying, or not, for a given key) may end
//! up tracking it that way too -- would be inventing state this task
//! cannot exercise or validate. If B5's own control flow needs an
//! explicit per-entry "no more generator work pending" signal that
//! `SynthState.generators`'s own membership doesn't already give it for
//! free, adding the field back is a one-line change B5 can make when it
//! knows what it actually needs.
//!
//! # `GeneratorNode` / `ConsumerNode`: brief's shape kept; oracle's
//! extra fields recorded as named seams, not added
//!
//! oracle `GeneratorNode` (:47-52): `mvar : Expr; key : Expr; mctx :
//! MetavarContext; instances : Array Instance; currInstanceIdx : Nat;
//! typeHasMVars : Bool`. oracle `ConsumerNode` (:54-59): `mvar : Expr;
//! key : Expr; mctx : MetavarContext; subgoals : List Expr; size : Nat`.
//! Both oracle nodes carry a per-node `mctx : MetavarContext` SNAPSHOT
//! (the state to resume search under) and `ConsumerNode` separately
//! carries `size` (the running instance-size budget, distinct from
//! `Answer.size` above -- this one is "size accumulated by subgoals
//! solved SO FAR on this consumer", `Answer.size` is that same count
//! `+1` once the LAST subgoal is solved and the answer materializes,
//! :457). Neither field appears in the brief's stated shape for either
//! struct, and [`GeneratorNode`]/[`ConsumerNode`] below deliberately do
//! NOT add them: unlike `Answer`/`TableEntry` above (where the brief's
//! guess was outright wrong about what the field IS), here the brief's
//! omission is a genuine open question about REPRESENTATION, not
//! content -- how a driver should thread a per-node mctx snapshot
//! (`MetaSnapshot`, `metactx.rs`, itself `pub(crate)` with private
//! fields) through an arena of nodes is a resolution-driver design
//! decision (own it by cloning a full snapshot per node? intern
//! snapshots into a side table and store an index? something else?)
//! that only the code actually doing the threading -- B5's `generate`/
//! `consume`/`resume` analogues -- is positioned to make correctly; B4
//! guessing at it here, unexercised by any test in this task, would be
//! speculative scaffolding, not a confirmed data shape. Recorded here
//! as the named seam it is: **B5 must add an `mctx` field to both
//! structs (and a `size` field to `ConsumerNode`) before the driver can
//! be correct** -- the two-argument `Consumer(usize)` design below
//! (next paragraph) already establishes the "index into an arena,
//! rather than embed by value" idiom B5's own `mctx` field is likely to
//! want to follow.
//!
//! **Minor 6 (review round 1):** `GeneratorNode.typeHasMVars` (:52, :58,
//! :253: `mvarType.hasMVar`) is a THIRD missing field, distinct from
//! `mctx`/`size` above and not previously named as a seam anywhere but
//! this struct's own field-list doc -- adding it here too. It is not
//! cosmetic: `generate` (:589-624) reads it to decide whether the
//! canonical-instances short-circuit (:600-624, gated on
//! `backward.synthInstance.canonInstances`) is even eligible for this
//! generator at all -- `unless gNode.typeHasMVars do ...` (:602) skips
//! the whole "stop early, we already have one metavariable-free answer"
//! optimization whenever the goal's own type still mentions a
//! metavariable, since a canonical-looking answer found against an
//! not-yet-fully-elaborated type isn't actually guaranteed unique.
//! Missing this field changes how MANY answers a generator produces
//! (functionally: it forces the "always search fully, never
//! short-circuit" behavior for every generator, since B5 will have
//! nothing to read for `typeHasMVars` either way) -- a real behavioral
//! gap for B5 to close alongside `mctx`, not a data-shape footnote.
//!
//! # `Waiter`: an index into an arena, not the oracle's by-value embed
//!
//! oracle `Waiter` (:61-66) is `| consumerNode : ConsumerNode → Waiter |
//! root`  -- it embeds the FULL `ConsumerNode` value directly, and
//! `wakeUp` (:422-434) pushes `(cNode, answer)` PAIRS onto a
//! `resumeStack : Array (ConsumerNode × Answer)` (`State.resumeStack`,
//! :245). The brief's stated shape instead is `enum Waiter { Consumer
//! (usize), Root }` -- an INDEX into an arena, not an embedded value.
//! This is a deliberate, Rust-idiomatic re-representation (this
//! module's own `consumers: Vec<ConsumerNode>` on [`SynthState`] IS that
//! arena) rather than a mistranscription of the oracle's shape: cloning
//! a whole `ConsumerNode` (which itself would need to carry a full
//! `mctx` snapshot, per the previous section) into every `Waiter` that
//! references it is exactly the kind of duplication an index avoids, and
//! Rust's ownership rules make a self-referential "value embeds a
//! pointer to a sibling value" structure like the oracle's own painful
//! to express directly anyway. Kept as specified (index, not embed);
//! recorded here rather than silently treated as equivalent. Two
//! consequences of the re-representation, both left as named seams for
//! B5 (no table-mechanics function in this module needs to resolve
//! them): (1) the oracle's `resumeStack` pairs a WOKEN consumer with the
//! SPECIFIC `Answer` that woke it (`resume`, :635-651, reads that exact
//! pair back off the stack); a `Waiter::Consumer(usize)` alone does not
//! carry which answer woke it, so `SynthState` below has no
//! `resumeStack`-equivalent field at all -- B5 owns adding one (e.g. a
//! `Vec<(usize, Answer)>`) when it implements `resume`'s analogue. (2)
//! the oracle's root case (`wakeUp`'s `.root` arm, :424-430) sets
//! `State.result?` directly when a level-mvar-free answer reaches it;
//! `SynthState` below has no `result` field either, for the same
//! "B5's driver decides how to surface it" reason.
//!
//! **(3) -- a HARD REQUIREMENT for B5, not just a note (review round 1,
//! Important 3):** the oracle's `Waiter.consumerNode` embeds an
//! IMMUTABLE SNAPSHOT of the consumer as it was at the moment it started
//! waiting -- `consume` (:534-579) builds that snapshot once, at
//! `waiter := Waiter.consumerNode cNode` (:553), from a `cNode` whose
//! `subgoals` still has its ORIGINAL (not-yet-advanced) head; when an
//! answer later arrives, `resume` (:635-651) does NOT mutate that
//! snapshot in place -- it builds a WHOLE NEW `ConsumerNode` with
//! `subgoals := rest` (:650) and feeds that fresh node to `consume`
//! again. The old, waited-on snapshot is never touched again. This
//! module's own re-representation combines TWO choices that are each
//! individually fine but JOINTLY dangerous: `Waiter::Consumer(usize)` is
//! an INDEX into `SynthState::consumers` rather than an embedded
//! snapshot, AND `ConsumerNode.next` (below) is documented (see that
//! field's own doc) as a CURSOR meant to be ADVANCED IN PLACE as
//! subgoals are solved. Put those together and a driver that advances
//! `next` in place on `consumers[i]` corrupts every OUTSTANDING
//! `Waiter::Consumer(i)` still waiting on that slot's ORIGINAL position:
//! when it is finally woken, it resumes from wherever `next` has since
//! reached, not from where it actually started waiting -- silently
//! propagating an answer to the WRONG subgoal (a wrong-answer bug, not
//! merely a perf/incompleteness one, unlike every other seam recorded in
//! this module's doc). **Binding constraint for B5**: EITHER (a)
//! `SynthState::consumers` must be APPEND-ONLY -- a driver may push new
//! `ConsumerNode`s but must never mutate a slot that any outstanding
//! `Waiter::Consumer` still points at (advancing to the next subgoal
//! means pushing a NEW node and handing out a NEW index, mirroring the
//! oracle's own "build a new node" discipline above), OR (b) the
//! resume-position cursor must live ON THE WAITER itself (e.g.
//! `Waiter::Consumer { node: usize, next: usize }`) rather than inside
//! the mutable arena slot, so a stale waiter's own recorded position
//! cannot be overwritten by a later advance of the same slot. This
//! module's own table-mechanics functions (`new_entry`/`add_waiter`/
//! `add_answer`) never advance `next` themselves, so nothing in THIS
//! task violates the constraint -- it binds only the driver B5 writes.
//!
//! # Landed ahead of its consumer
//!
//! Every item in this module is `pub(crate)` and reachable only from
//! this module's own `#[cfg(test)]` tests until B5's driver lands and
//! calls into it -- the same "table mechanics land before the driver
//! that drives them" posture `instances.rs`'s own module doc records for
//! itself (search that module's own final section, "Landed ahead of its
//! consumer"). `#![allow(dead_code)]` below is scoped to this module
//! alone (an inner attribute, not a crate-wide one) and is a SEPARATE
//! allow from `instances.rs`'s own -- neither module's allow should be
//! used to cover for the other; both are removed independently once B5
//! wires each one in.
#![allow(dead_code)]

use std::collections::HashMap;

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, LevelsId, NameId};
use leanr_kernel::{Nat, MAX_REC_DEPTH};

use crate::instances::Instance;
use crate::{LMVarId, MVarId, MetaCtx, MetaError};

/// Stack-growth constants for [`KeyNormalizer`]'s own depth guard --
/// restated from `metactx.rs::{RED_ZONE,STACK_CHUNK}` (private there),
/// the exact same values, the same "restate rather than expose"
/// idiom `metactx.rs` itself uses for `tc.rs`'s own constants (see that
/// module's doc comment on the pair). `KeyNormalizer` cannot reuse
/// `MetaCtx::guarded` directly: that method's closure is `FnOnce(&mut
/// MetaCtx) -> ..`, with no way to also thread `KeyNormalizer`'s own
/// `next_idx`/`lmap`/`emap` scratch state through it, so this is a
/// second, tiny copy of the same three-line body instead
/// (`stacker::maybe_grow` around a depth-checked call), not a shared
/// helper.
const RED_ZONE: usize = 128 * 1024;
const STACK_CHUNK: usize = 4 * 1024 * 1024;

// =======================================================================
// GoalKey / normalize_goal_key / mkTableKey
// =======================================================================

/// A table key: a normalized goal expression, up to metavariable
/// renaming. See this module's own doc for why this wraps a
/// hash-consed `ExprId` directly rather than a hand-rolled digest.
/// oracle: the key half of `Std.HashMap Expr TableEntry`
/// (`SynthInstance.lean:246`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct GoalKey(ExprId);

impl GoalKey {
    /// Table-mechanics tests only: a synthetic key that needs no
    /// `MetaCtx`/`Store` at all (`ExprId::from_index`, the same bare
    /// bit-pattern constructor `instances.rs`'s own
    /// `get_instances_orders_by_priority_desc_then_reverse_of_ties`
    /// test uses for `NameId::from_index`). Two different `idx`s are
    /// guaranteed distinct keys; this constructor makes no other claim
    /// (in particular it is NOT a stand-in for a real
    /// `normalize_goal_key` result -- `table_key_is_stable_up_to_mvar_
    /// renaming` and `different_goals_produce_different_keys` below
    /// exercise that function directly, over a real `MetaCtx`).
    #[cfg(test)]
    pub(crate) fn for_test(idx: u32) -> GoalKey {
        GoalKey(ExprId::from_index(idx, true).expect("small test index fits"))
    }
}

/// Per-call scratch state for [`MetaCtx::normalize_goal_key`]'s
/// structural walk. oracle: `MkTableKey.State`
/// (`SynthInstance.lean:98-102`: `nextIdx`, `lmap : HashMap LMVarId
/// Level`, `emap : HashMap MVarId Expr`, plus `mctx` -- threaded here as
/// `ctx: &mut MetaCtx` instead of a copy, since this walk never needs to
/// swap `mctx`s mid-traversal the way the driver's own `withMCtx` calls
/// do). ONE `next_idx` counter shared by both maps -- see this module's
/// doc for why that single interleaved numbering (not two independent
/// per-kind counters) is exactly what the oracle's own worked example
/// (`f ?m ?m ?n` -> `f _tc.0 _tc.0 _tc.1`) requires.
struct KeyNormalizer<'a, 'e> {
    ctx: &'a mut MetaCtx<'e>,
    next_idx: u64,
    lmap: HashMap<LMVarId, LevelId>,
    emap: HashMap<MVarId, ExprId>,
    /// `` `_tc `` interned once per call, reused for every fresh index
    /// this call mints (oracle: `` Name.mkNum `_tc s.nextIdx ``,
    /// :123, :169).
    tc_prefix: NameId,
    depth: u32,
}

impl<'a, 'e> KeyNormalizer<'a, 'e> {
    fn new(ctx: &'a mut MetaCtx<'e>) -> Result<KeyNormalizer<'a, 'e>, MetaError> {
        let base = Some(ctx.view.store);
        let s = ctx.scratch.intern_str(base, "_tc")?;
        let tc_prefix = ctx.scratch.name_str(base, None, s)?;
        Ok(KeyNormalizer {
            ctx,
            next_idx: 0,
            lmap: HashMap::new(),
            emap: HashMap::new(),
            tc_prefix,
            depth: 0,
        })
    }

    /// `MetaCtx::guarded`'s exact body (`metactx.rs:335-346`), restated
    /// against `Self` instead of `MetaCtx` -- see the module-level
    /// `RED_ZONE`/`STACK_CHUNK` doc comment for why this can't just
    /// call that method directly.
    fn guarded<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<R, MetaError>,
    ) -> Result<R, MetaError> {
        if self.depth >= MAX_REC_DEPTH {
            return Err(MetaError::DepthBudgetExhausted);
        }
        self.depth += 1;
        let r = stacker::maybe_grow(RED_ZONE, STACK_CHUNK, || f(self));
        self.depth -= 1;
        r
    }

    /// Mint the next `_tc.<idx>` name (oracle: the `nextIdx`-bump arm
    /// shared by `MkTableKey.normLevel`/`normExpr`, :123-125, :169-171).
    fn fresh_tc_name(&mut self) -> Result<NameId, MetaError> {
        let base = Some(self.ctx.view.store);
        let idx = self.next_idx;
        self.next_idx += 1;
        let idx_id = self.ctx.scratch.intern_nat(base, &Nat::from(idx))?;
        Ok(self
            .ctx
            .scratch
            .name_num(base, Some(self.tc_prefix), idx_id)?)
    }

    /// oracle: `MkTableKey.normLevel` (`SynthInstance.lean:114-127`).
    fn norm_level(&mut self, l: LevelId) -> Result<LevelId, MetaError> {
        self.ctx.step()?;
        let base = Some(self.ctx.view.store);
        // oracle: `if !u.hasMVar then return u` (:116) -- level flags
        // bit 1 is exactly `hasLevelMVar` (`bank/mod.rs::level_flags`).
        if self.ctx.scratch.level_flags(base, l) & 0b10 == 0 {
            return Ok(l);
        }
        self.guarded(|nz| nz.norm_level_body(l))
    }

    fn norm_level_body(&mut self, l: LevelId) -> Result<LevelId, MetaError> {
        let base = Some(self.ctx.view.store);
        match *self.ctx.scratch.level_row(base, l) {
            LevelRow::Zero | LevelRow::Param(_) => Ok(l),
            LevelRow::MVar(name) => {
                // Anonymous level mvars carry no `LMVarId` to key
                // `lmap`/`level_assignment` on; oracle's own
                // `Level.mvar` leaf is likewise just returned as-is by
                // every arm that doesn't match a NAMED mvar it can look
                // up (there is no unnamed-mvar case in the oracle at
                // all -- every `LMVarId` the elaborator mints carries a
                // name -- so this is defensive, not a modeled seam).
                let Some(name) = name else { return Ok(l) };
                let lid = LMVarId(name);
                // Resolve an ASSIGNED mvar first (folding in what this
                // crate's own `instantiate_mvars` does not cover for
                // levels -- see the module doc); only an mvar confirmed
                // UNASSIGNED after that is ever renamed, matching
                // `mkTableKey`'s stated precondition.
                if let Some(v) = self.ctx.mctx.level_assignment(lid) {
                    return self.norm_level(v);
                }
                if let Some(&renamed) = self.lmap.get(&lid) {
                    return Ok(renamed);
                }
                let pname = self.fresh_tc_name()?;
                let renamed = self.ctx.scratch.level_param(base, Some(pname))?;
                self.lmap.insert(lid, renamed);
                Ok(renamed)
            }
            LevelRow::Succ(a) => {
                let a2 = self.norm_level(a)?;
                if a2 == a {
                    Ok(l)
                } else {
                    Ok(self.ctx.scratch.level_succ(base, a2)?)
                }
            }
            LevelRow::Max(a, b) => {
                let a2 = self.norm_level(a)?;
                let b2 = self.norm_level(b)?;
                if a2 == a && b2 == b {
                    Ok(l)
                } else {
                    Ok(self.ctx.scratch.level_max(base, a2, b2)?)
                }
            }
            LevelRow::IMax(a, b) => {
                let a2 = self.norm_level(a)?;
                let b2 = self.norm_level(b)?;
                if a2 == a && b2 == b {
                    Ok(l)
                } else {
                    Ok(self.ctx.scratch.level_imax(base, a2, b2)?)
                }
            }
        }
    }

    /// oracle: `MkTableKey.normExpr` (`SynthInstance.lean:129-160`).
    fn norm_expr(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        self.ctx.step()?;
        // oracle: `if !e.hasMVar then pure e` (:131) -- `hasMVar` is
        // `hasExprMVar || hasLevelMVar` (`Expr.hasMVar`); by the time
        // this walk runs, `instantiate_mvars` has already resolved every
        // ASSIGNED expr mvar (see `normalize_goal_key` below), so the
        // only expr mvars this bit can still see are genuinely
        // unassigned ones still needing a canonical rename.
        let d = self.ctx.data(e);
        if !d.has_expr_mvar() && !d.has_level_mvar() {
            return Ok(e);
        }
        self.guarded(|nz| nz.norm_expr_body(e))
    }

    fn norm_expr_body(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let base = Some(self.ctx.view.store);
        match self.ctx.node(e) {
            Node::MVar { id: Some(id) } => {
                let mid = MVarId(id);
                // Minor 5 (review round 1): resolve an ALREADY-ASSIGNED
                // mvar first, symmetric with `norm_level_body`'s own
                // `level_assignment` check just above. This arm's
                // precondition ("no assigned expr mvar reaches here") is
                // otherwise enforced only by the caller having already
                // run `instantiate_mvars` (`normalize_goal_key` below) --
                // a comment-enforced invariant, not a code-enforced one;
                // this one line makes the arm correct standalone too,
                // matching `mkTableKey`'s own doc-stated precondition
                // defensively rather than assuming every future caller
                // honors it.
                if let Some(v) = self.ctx.mctx.assignment(mid) {
                    return self.norm_expr(v);
                }
                // oracle: `if !(← mvarId.isAssignable) then return e`
                // (:151-152) -- `MVarId.isAssignable`
                // (`MetavarContext.lean:483-486`) is DEPTH-ONLY (`decl.depth
                // == mctx.depth`), a different function from
                // `assign.rs::unassigned_mvar_id`'s `isReadOnlyOrSyntheticOpaque`
                // check (see this module's own doc for why the two must not
                // be conflated). Under this crate's flat-depth collapse
                // (no per-mvar depth model at all, `mvar_ctx.rs`) that
                // depth check is always true for any DECLARED mvar,
                // `MVarKind` included -- a syntheticOpaque mvar IS renamed
                // here, matching the real `mkTableKey`. `None` (no
                // declaration at all) is the one genuine "not assignable"
                // case left: not a mvar this crate's `MetavarContext` knows
                // about, so nothing to rename by.
                let assignable = self.ctx.mctx.decl(mid).is_some();
                if !assignable {
                    return Ok(e);
                }
                if let Some(&renamed) = self.emap.get(&mid) {
                    return Ok(renamed);
                }
                let name = self.fresh_tc_name()?;
                let renamed = self.ctx.scratch.expr_fvar(base, Some(name))?;
                self.emap.insert(mid, renamed);
                Ok(renamed)
            }
            // Anonymous mvar: no `MVarId` to rename by; left as itself
            // (same defensive posture as `norm_level_body`'s anonymous
            // level-mvar arm above).
            Node::MVar { id: None } => Ok(e),
            Node::Sort { level } => {
                let l2 = self.norm_level(level)?;
                if l2 == level {
                    Ok(e)
                } else {
                    Ok(self.ctx.scratch.expr_sort(base, l2)?)
                }
            }
            Node::Const { name, levels } => {
                let list = self.ctx.scratch.level_list_at(base, levels).to_vec();
                let mut changed = false;
                let mut new_list = Vec::with_capacity(list.len());
                for lv in list {
                    let lv2 = self.norm_level(lv)?;
                    changed |= lv2 != lv;
                    new_list.push(lv2);
                }
                if !changed {
                    Ok(e)
                } else {
                    let levels2: LevelsId = self.ctx.scratch.intern_level_list(base, &new_list)?;
                    Ok(self.ctx.scratch.expr_const(base, name, levels2)?)
                }
            }
            Node::App { f, arg } => {
                let f2 = self.norm_expr(f)?;
                let a2 = self.norm_expr(arg)?;
                if f2 == f && a2 == arg {
                    Ok(e)
                } else {
                    Ok(self.ctx.scratch.expr_app(base, f2, a2)?)
                }
            }
            Node::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.norm_expr(binder_type)?;
                let b2 = self.norm_expr(body)?;
                if t2 == binder_type && b2 == body {
                    Ok(e)
                } else {
                    Ok(self
                        .ctx
                        .scratch
                        .expr_lam(base, binder_name, t2, b2, binder_info)?)
                }
            }
            Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let t2 = self.norm_expr(binder_type)?;
                let b2 = self.norm_expr(body)?;
                if t2 == binder_type && b2 == body {
                    Ok(e)
                } else {
                    Ok(self
                        .ctx
                        .scratch
                        .expr_forall(base, binder_name, t2, b2, binder_info)?)
                }
            }
            Node::LetE {
                decl_name,
                ty,
                value,
                body,
                non_dep,
            } => {
                let t2 = self.norm_expr(ty)?;
                let v2 = self.norm_expr(value)?;
                let b2 = self.norm_expr(body)?;
                if t2 == ty && v2 == value && b2 == body {
                    Ok(e)
                } else {
                    Ok(self
                        .ctx
                        .scratch
                        .expr_let(base, decl_name, t2, v2, b2, non_dep)?)
                }
            }
            Node::MData { data, expr } => {
                let e2 = self.norm_expr(expr)?;
                if e2 == expr {
                    Ok(e)
                } else {
                    Ok(self.ctx.scratch.expr_mdata(base, data, e2)?)
                }
            }
            Node::Proj {
                type_name,
                idx,
                structure,
            } => {
                let s2 = self.norm_expr(structure)?;
                if s2 == structure {
                    Ok(e)
                } else {
                    Ok(self
                        .ctx
                        .scratch
                        .expr_proj(base, type_name, &Nat::from(idx as u64), s2)?)
                }
            }
            Node::ProjBig {
                type_name,
                idx,
                structure,
            } => {
                let idxn = self.ctx.scratch.nat_at(base, idx).clone();
                let s2 = self.norm_expr(structure)?;
                if s2 == structure {
                    Ok(e)
                } else {
                    Ok(self.ctx.scratch.expr_proj(base, type_name, &idxn, s2)?)
                }
            }
            // BVar/BVarBig/FVar/LitNat/LitStr: none of these shapes can
            // carry an expr mvar or a level (same catch-all as
            // `instantiate_mvars_body`'s own, `assign.rs:1299-1302`).
            _ => Ok(e),
        }
    }
}

impl<'e> MetaCtx<'e> {
    /// Compute `goal`'s table key. oracle: `mkTableKeyFor`
    /// (`SynthInstance.lean:262-266`) composed with `mkTableKey`
    /// (:196-199) -- see this module's own doc for the exact
    /// correspondence (and the one place this composition had to be
    /// re-shaped around this crate's `instantiate_mvars` not covering
    /// levels). `goal` here is expected to already be the metavariable's
    /// TYPE (what `mkTableKeyFor` passes, having already called
    /// `inferType mvar` itself) -- this function does not call
    /// `infer_type` or telescope anything on its own.
    pub(crate) fn normalize_goal_key(&mut self, goal: ExprId) -> Result<GoalKey, MetaError> {
        let goal = self.instantiate_mvars(goal)?;
        let mut nz = KeyNormalizer::new(self)?;
        let normalized = nz.norm_expr(goal)?;
        Ok(GoalKey(normalized))
    }
}

// =======================================================================
// AbstractMVarsResult / Answer / TableEntry / Waiter / GeneratorNode /
// ConsumerNode / SynthState
// =======================================================================

/// oracle: `Lean.Meta.AbstractMVarsResult` (`Meta/Basic.lean:338-343`).
/// A DATA SHAPE only -- see this module's doc ("`Answer`: confirmed
/// against source") for why the actual `abstractMVars`/
/// `openAbstractMVarsResult` algorithms are a named seam owned by B5,
/// not built here.
#[derive(Debug, Clone)]
pub(crate) struct AbstractMVarsResult {
    pub param_names: Vec<NameId>,
    pub mvars: Vec<ExprId>,
    pub expr: ExprId,
}

impl AbstractMVarsResult {
    /// oracle: `AbstractMVarsResult.numMVars` (`Meta/Basic.lean:345-346`
    /// -- `mvars.size`).
    pub(crate) fn num_mvars(&self) -> usize {
        self.mvars.len()
    }
}

/// oracle: `Lean.Meta.SynthInstance.Answer` (`SynthInstance.lean:
/// 232-236`). See this module's doc for the full field-by-field
/// confirmation against source (the brief's own guess at this struct's
/// shape was wrong, not just incomplete).
#[derive(Debug, Clone)]
pub(crate) struct Answer {
    pub result: AbstractMVarsResult,
    pub result_type: ExprId,
    pub size: usize,
}

impl Answer {
    /// Table-mechanics tests only: a placeholder `Answer` whose CONTENT
    /// is never inspected by anything in this module except
    /// `SynthState::add_answer`'s `result_type` dedup check (which a
    /// single-answer test never reaches) -- synthetic ids
    /// (`ExprId::from_index`), no `Store`/`MetaCtx` needed, mirroring
    /// `GoalKey::for_test`'s own reasoning.
    #[cfg(test)]
    pub(crate) fn for_test() -> Answer {
        let placeholder = ExprId::from_index(0, true).expect("small test index fits");
        Answer {
            result: AbstractMVarsResult {
                param_names: Vec::new(),
                mvars: Vec::new(),
                expr: placeholder,
            },
            result_type: placeholder,
            size: 0,
        }
    }
}

/// oracle: `Lean.Meta.SynthInstance.TableEntry` (`SynthInstance.lean:
/// 238-239`) -- exactly its two fields; see this module's doc
/// ("`TableEntry`: confirmed against source") for why the brief's third
/// guessed field (`complete: bool`) is not reproduced here.
#[derive(Debug, Clone, Default)]
pub(crate) struct TableEntry {
    pub answers: Vec<Answer>,
    pub waiters: Vec<Waiter>,
}

/// oracle: `Lean.Meta.SynthInstance.Waiter` (`SynthInstance.lean:
/// 61-66) -- re-represented as an index into `SynthState::consumers`
/// rather than embedding a `ConsumerNode` by value; see this module's
/// doc ("`Waiter`: an index into an arena...") for the full rationale
/// and the seams this re-representation leaves for B5.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Waiter {
    Consumer(usize),
    Root,
}

/// oracle: `Lean.Meta.SynthInstance.GeneratorNode` (`SynthInstance.lean:
/// 47-52`). See this module's doc ("`GeneratorNode` / `ConsumerNode`")
/// for the oracle's `mctx`/`typeHasMVars` fields this struct does not
/// (yet) carry -- a named seam, not an oversight. `goal` here is the
/// oracle's `mvar : Expr` field (the metavariable expression this node
/// is trying to resolve, kept under the brief's own field name for
/// interface continuity with B5's expected shape); `key` is
/// `normalize_goal_key` of that mvar's TYPE (oracle: `key = mkTableKey
/// mctx mvarType`, `mkGeneratorNode?`, :267-278); `remaining` is the
/// REMAINING (not-yet-tried) candidates, a shrinking `Vec` standing in
/// for the oracle's `instances : Array Instance` paired with a separate
/// `currInstanceIdx : Nat` cursor into it (this crate's own re-
/// representation -- popping the front as instances are tried, rather
/// than indexing back-to-front, per `get_instances`'s own module doc:
/// its result is already delivered in TRY order, front-to-back).
pub(crate) struct GeneratorNode {
    pub goal: ExprId,
    pub key: GoalKey,
    pub remaining: Vec<Instance>,
}

/// oracle: `Lean.Meta.SynthInstance.ConsumerNode` (`SynthInstance.lean:
/// 54-59`). See this module's doc for the oracle's `mctx`/`size` fields
/// this struct does not (yet) carry. `mvar : MVarId` (tighter than the
/// oracle's bare `Expr` -- every `ConsumerNode.mvar` the oracle ever
/// constructs IS an `Expr.mvar` reference, `SynthInstance.lean:453` /
/// `:602` construct it that way; `MVarId` names that identity precisely,
/// matching this crate's own idiom elsewhere of using a typed id instead
/// of a bare `Expr` wherever the shape is statically known to be an
/// mvar reference). `next` is a cursor index into `subgoals`, standing
/// in for the oracle's own `subgoals : List Expr` head/tail consumption
/// (`consume`'s `mvar :: _` pattern match, :550-552) -- an index avoids
/// repeatedly reallocating/shifting a `Vec`'s front, at the cost of
/// `subgoals` here being the FULL original list rather than shrinking.
/// **B5: see this module's doc ("`Waiter`: an index into an arena...",
/// point (3)) for a HARD constraint on how `next` may be advanced once
/// `Waiter::Consumer(usize)` indexes into a mutable arena of these** --
/// advancing it in place on an already-waited-on slot is a wrong-answer
/// bug, not just a perf one.
pub(crate) struct ConsumerNode {
    pub key: GoalKey,
    pub mvar: MVarId,
    pub subgoals: Vec<ExprId>,
    pub next: usize,
}

/// oracle: `Lean.Meta.SynthInstance.State` (`SynthInstance.lean:
/// 244-254`). See this module's doc ("`Waiter`: an index into an
/// arena...") for why this struct has no `result?`/`resumeStack`
/// analogue -- both are named seams for B5, not part of the table
/// mechanics this task builds. `step` is a synthesis-iteration counter
/// (this crate's determinism convention -- Global Constraints: "a
/// deterministic step counter, never `maxHeartbeats`" -- scoped to the
/// synthesis loop specifically, distinct from `MetaCtx`'s own `steps`
/// field, which every OTHER traversal in this crate already consumes);
/// nothing in this module's table mechanics loops, so nothing here ever
/// increments it -- B5 owns bumping it once per iteration of its own
/// resolution loop, the same role `checkSystem`'s per-iteration budget
/// check plays in the oracle (:191-193).
#[derive(Default)]
pub(crate) struct SynthState {
    pub answers: HashMap<GoalKey, TableEntry>,
    pub generators: Vec<GeneratorNode>,
    pub consumers: Vec<ConsumerNode>,
    pub step: u64,
}

impl SynthState {
    /// Register a brand-new, waiter-less table entry for `key`. oracle:
    /// the `tableEntries.insert key entry` half of `newSubgoal`
    /// (`SynthInstance.lean:279-287`), factored apart from waiter-
    /// seeding (`add_waiter` below) so B5 can compose them however its
    /// own `newSubgoal` analogue needs to -- the oracle's own
    /// `newSubgoal` always inserts ONE brand-new entry pre-seeded with
    /// exactly the ONE waiter that triggered it, in a single call; this
    /// crate splits that into two primitives instead of hard-coding
    /// that one caller's shape. Unconditional insert, like the oracle's
    /// own blind `.insert` (:286) -- the caller is responsible for
    /// having already checked (via an equivalent of `findEntry?`,
    /// :288-289) that `key` has no entry yet; calling this on an
    /// already-registered key silently discards its existing
    /// answers/waiters, exactly as a second `tableEntries.insert` would.
    pub(crate) fn new_entry(&mut self, key: GoalKey) {
        self.answers.insert(key, TableEntry::default());
    }

    /// Register `waiter` on `key`'s entry. Panics if `key` has no entry
    /// yet -- every entry must exist (via `new_entry`) before a waiter
    /// can be added to it; this is an internal-invariant violation (a
    /// caller bug), not adversarial/untrusted data, the same "only ever
    /// produced by our own code" posture `bank/terms.rs::tag_of`
    /// documents for its own internal-shape panic.
    pub(crate) fn add_waiter(&mut self, key: &GoalKey, waiter: Waiter) {
        self.answers
            .get_mut(key)
            .expect("add_waiter: no table entry for key -- caller must new_entry first")
            .waiters
            .push(waiter);
    }

    /// Record `answer` against `key`'s entry and report which waiters
    /// need to be woken. oracle: `addAnswer`'s table-touching half
    /// (`SynthInstance.lean:436-449`) -- the dedup check (`isNewAnswer`,
    /// :445-449) plus storing the answer and reading back the waiter
    /// list; ACTUALLY waking a waiter (`wakeUp`, :422-434 -- pushing
    /// onto a resume stack, or setting a root result) is resolution-
    /// driver work this function does not do, by design: it hands the
    /// woken [`Waiter`]s back to the caller (B5) to act on, which is
    /// exactly the table-mechanics/driver split this task draws.
    ///
    /// Dedups exactly like the oracle: an answer whose `result_type`
    /// structurally matches (`ExprId` equality -- this crate's
    /// hash-consed analogue of the oracle's own `Expr` `!=`; see
    /// `GoalKey`'s own doc for why hash-consed id equality is an exact,
    /// not approximate, transcription of that comparison) an answer
    /// ALREADY stored for this key is not stored again and wakes
    /// nobody. Panics if `key` has no entry yet, for the same reason
    /// `add_waiter` does.
    pub(crate) fn add_answer(&mut self, key: &GoalKey, answer: Answer) -> Vec<Waiter> {
        let entry = self
            .answers
            .get_mut(key)
            .expect("add_answer: no table entry for key -- caller must new_entry first");
        // oracle: `isNewAnswer` (:441-444) -- and its own comment there,
        // restated: "isDefEq here is too expensive"; a plain structural
        // mismatch check is the exact (not approximate) transcription
        // via this crate's hash-consed `ExprId` equality.
        let is_new = entry
            .answers
            .iter()
            .all(|old| old.result_type != answer.result_type);
        if !is_new {
            return Vec::new();
        }
        entry.answers.push(answer);
        entry.waiters.clone()
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;
    use crate::test_support::{const_named, fresh_mvar, with_instances_ctx};
    use leanr_kernel::bank::ExprId;

    /// Build `Type` (`Sort (succ Level.zero)`) as an mvar's type -- the
    /// brief's suggested `fresh_mvar_typed("Type")` helper, inlined here
    /// rather than promoted to `test_support` since this task's own
    /// tests are its only caller.
    fn type_sort(ctx: &mut MetaCtx) -> ExprId {
        let z = ctx.scratch.level_zero(Some(ctx.view.store)).expect("zero");
        let s = ctx
            .scratch
            .level_succ(Some(ctx.view.store), z)
            .expect("succ");
        ctx.scratch
            .expr_sort(Some(ctx.view.store), s)
            .expect("sort")
    }

    /// Mint a fresh, declared (but unassigned) LEVEL metavariable --
    /// this module's own tests are the only caller needing one (`norm_level`
    /// was otherwise entirely untested, minor 4), so this is inlined here
    /// rather than promoted to `test_support`, mirroring `type_sort`/
    /// `goal_add` above. Same "fixed prefix + monotone counter" idiom as
    /// `test_support::fresh_mvar` (and `level.rs::fresh_level_mvar`'s own
    /// production-code counterpart), scoped to the whole test binary since
    /// there is no production-code counter field to reuse for this
    /// test-only need.
    fn fresh_level_mvar_for_test(ctx: &mut MetaCtx) -> LevelId {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let idx = COUNTER.fetch_add(1, Ordering::Relaxed);
        let base = Some(ctx.view.store);
        let prefix_str = ctx
            .scratch
            .intern_str(base, "_leanr_test_lvl_mvar")
            .expect("intern");
        let prefix = ctx.scratch.name_str(base, None, prefix_str).expect("name");
        let idx_id = ctx.scratch.intern_nat(base, &Nat::from(idx)).expect("nat");
        let name = ctx
            .scratch
            .name_num(base, Some(prefix), idx_id)
            .expect("name");
        ctx.mctx_mut().declare_level(LMVarId(name));
        ctx.scratch
            .level_mvar(base, Some(name))
            .expect("level mvar")
    }

    /// Build the canonical `` _tc.<idx> `` name the normalizer would mint
    /// for the `idx`-th fresh metavariable it renames (oracle: `Name.mkNum
    /// \`_tc idx`, `SynthInstance.lean:123`/`:169`) -- used by tests that
    /// pin the EXACT normalized shape by hand rather than only comparing
    /// two calls to `normalize_goal_key` against each other.
    fn tc_name(ctx: &mut MetaCtx, idx: u64) -> NameId {
        let base = Some(ctx.view.store);
        let s = ctx.scratch.intern_str(base, "_tc").expect("intern");
        let prefix = ctx.scratch.name_str(base, None, s).expect("name");
        let idx_id = ctx.scratch.intern_nat(base, &Nat::from(idx)).expect("nat");
        ctx.scratch
            .name_num(base, Some(prefix), idx_id)
            .expect("name")
    }

    /// Build `Add arg1 .. argn` over already-constructed argument
    /// expressions (the brief's suggested `parse_goal_with`, inlined for
    /// the same reason as `type_sort` above; `test_support::parse_goal`
    /// only supports bare-constant-token specs, not embedding an
    /// already-built mvar reference as an argument).
    fn goal_add(ctx: &mut MetaCtx, args: &[ExprId]) -> ExprId {
        let head = const_named(ctx, "Add");
        ctx.mk_app_spine(head, args).expect("mk_app_spine")
    }

    /// Step-1 brief test: two goals `Add ?a` with different mvar
    /// identities normalize to the same key.
    #[test]
    fn table_key_is_stable_up_to_mvar_renaming() {
        with_instances_ctx(|ctx| {
            let ty = type_sort(ctx);
            let (m1, _) = fresh_mvar(ctx, ty);
            let (m2, _) = fresh_mvar(ctx, ty);
            let g1 = goal_add(ctx, &[m1]);
            let g2 = goal_add(ctx, &[m2]);
            assert_eq!(
                ctx.normalize_goal_key(g1).unwrap(),
                ctx.normalize_goal_key(g2).unwrap()
            );
        });
    }

    /// Negative counterpart to the stability test above: a key function
    /// that always returned one constant would pass that test vacuously,
    /// so this pins that two GENUINELY different goals (different head
    /// constants, no mvar renaming involved at all) must not collide.
    /// NOTE (review round 1): both goals here are bare `Expr.const`s with
    /// NO metavariable at all, so `norm_expr`'s `!e.hasMVar` early-exit
    /// (`:438-449` above) returns immediately for both -- this test
    /// exercises ONLY that early-exit path, never the counter-minting
    /// body (`norm_expr_body`/`norm_level_body`). It rules out a `fn
    /// key(_) -> CONST` stub but says nothing about the counter
    /// discipline; see `distinct_mvars_are_not_collapsed_together` below
    /// for the test that actually guards THAT property.
    #[test]
    fn different_goals_produce_different_keys() {
        with_instances_ctx(|ctx| {
            let g1 = const_named(ctx, "Add");
            let g2 = const_named(ctx, "Mul");
            assert_ne!(
                ctx.normalize_goal_key(g1).unwrap(),
                ctx.normalize_goal_key(g2).unwrap()
            );
        });
    }

    /// The counter-discipline negative test (review round 1, Important 2):
    /// none of the other tests in this module can fail against a
    /// normalizer that mints `_tc.0` for EVERY unassigned mvar and never
    /// bumps `next_idx` at all -- that "collapse everything" bug still
    /// passes `table_key_is_stable_up_to_mvar_renaming` (both goals still
    /// key identically, just for the wrong reason) and
    /// `repeated_mvar_occurrence_reuses_its_canonical_index` (`Add ?a ?a`
    /// collapsing every occurrence to `_tc.0` is indistinguishable from
    /// correctly reusing `?a`'s own first-occurrence index, since there is
    /// only ONE mvar in that goal anyway). This test uses TWO DISTINCT
    /// mvars (`?a`, `?b`) against the SAME mvar repeated (`?a`, `?a`) --
    /// the collapse-everything bug maps both to `Add _tc.0 _tc.0`,
    /// merging two genuinely different goals into one table entry (the
    /// exact collision failure mode this task's counter discipline
    /// exists to prevent); the correct normalizer maps them to `Add
    /// _tc.0 _tc.1` and `Add _tc.0 _tc.0` respectively, which must differ.
    /// Confirmed as real RED against that exact bug (see the task-B4
    /// report's "Fix round 1" section for the injected-bug run).
    #[test]
    fn distinct_mvars_are_not_collapsed_together() {
        with_instances_ctx(|ctx| {
            let ty = type_sort(ctx);
            let (m1, _) = fresh_mvar(ctx, ty);
            let (m2, _) = fresh_mvar(ctx, ty);
            let g_distinct = goal_add(ctx, &[m1, m2]);
            let g_repeated = goal_add(ctx, &[m1, m1]);
            assert_ne!(
                ctx.normalize_goal_key(g_distinct).unwrap(),
                ctx.normalize_goal_key(g_repeated).unwrap()
            );
        });
    }

    /// Pins the oracle's own worked example (this module's doc,
    /// `SynthInstance.lean:78-90`'s comment): a metavariable occurring
    /// MORE THAN ONCE in a goal must reuse its FIRST canonical index at
    /// every later occurrence, not mint a fresh one each time --
    /// `Add ?a ?a` and `Add ?b ?b` (two different fresh mvars, each used
    /// twice) must still key identically.
    #[test]
    fn repeated_mvar_occurrence_reuses_its_canonical_index() {
        with_instances_ctx(|ctx| {
            let ty = type_sort(ctx);
            let (m1, _) = fresh_mvar(ctx, ty);
            let (m2, _) = fresh_mvar(ctx, ty);
            let g1 = goal_add(ctx, &[m1, m1]);
            let g2 = goal_add(ctx, &[m2, m2]);
            assert_eq!(
                ctx.normalize_goal_key(g1).unwrap(),
                ctx.normalize_goal_key(g2).unwrap()
            );
        });
    }

    /// Minor 4 (review round 1): `norm_level`/`norm_level_body` were
    /// entirely untested -- no prior test constructed a level mvar at
    /// all. Pins the ONE `next_idx` counter's shared-interleaving claim
    /// (module doc, "one shared `next_idx` counter across both level and
    /// expr mvars") directly, by building the EXACT expected normalized
    /// tree by hand (via [`tc_name`]) rather than only comparing two
    /// `normalize_goal_key` calls against each other: goal `(Sort ?u)
    /// ?a` (an `App` whose function position is a `Sort` of an
    /// unassigned level mvar, applied to an unassigned expr mvar) visits
    /// the level mvar FIRST (it's in function position) and must mint
    /// `_tc.0` for it; the expr mvar, visited second, must then mint
    /// `_tc.1` -- NOT `_tc.0` again, which is exactly what two
    /// independent per-kind counters (rather than one shared one) would
    /// produce.
    #[test]
    fn level_mvar_and_expr_mvar_share_one_counter() {
        with_instances_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let u = fresh_level_mvar_for_test(ctx);
            let sort_u = ctx.scratch.expr_sort(base, u).expect("sort");
            let ty = type_sort(ctx);
            let (m_a, _) = fresh_mvar(ctx, ty);
            let goal = ctx.scratch.expr_app(base, sort_u, m_a).expect("app");

            let key = ctx.normalize_goal_key(goal).unwrap();

            let name0 = tc_name(ctx, 0);
            let name1 = tc_name(ctx, 1);
            let base = Some(ctx.view.store);
            let expected_level = ctx.scratch.level_param(base, Some(name0)).expect("param");
            let expected_sort = ctx.scratch.expr_sort(base, expected_level).expect("sort");
            let expected_fvar = ctx.scratch.expr_fvar(base, Some(name1)).expect("fvar");
            let expected = ctx
                .scratch
                .expr_app(base, expected_sort, expected_fvar)
                .expect("app");

            assert_eq!(key, GoalKey(expected));
        });
    }

    /// Companion to the shared-counter test above: an ASSIGNED level
    /// mvar must be resolved to its (recursively normalized) assignment
    /// FIRST, and that resolution must NOT consume a `next_idx` slot --
    /// `norm_level_body`'s `LevelRow::MVar` arm's `level_assignment`
    /// check (this task's own "one deliberate recomposition", module
    /// doc). Goal `(Sort ?u_assigned) ?a` with `?u_assigned := Level.zero`
    /// must normalize to `(Sort Level.zero) _tc.0` -- the expr mvar
    /// getting index `0`, not `1`, is exactly what proves the assigned
    /// level mvar minted no canonical name of its own.
    #[test]
    fn assigned_level_mvar_resolves_without_consuming_a_counter_index() {
        with_instances_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let u = fresh_level_mvar_for_test(ctx);
            let zero = ctx.scratch.level_zero(base).expect("zero");
            // `u` is a `LevelId`, not an `ExprId` -- assign it directly
            // via its `LMVarId`, mirroring `level.rs::tests`' own idiom
            // for building an already-assigned level mvar fixture.
            let lmvar_id = match *ctx.scratch.level_row(base, u) {
                LevelRow::MVar(Some(name)) => LMVarId(name),
                _ => unreachable!("fresh_level_mvar_for_test always builds a named level mvar"),
            };
            ctx.mctx_mut()
                .assign_level(lmvar_id, zero)
                .expect("assigning a fresh level mvar cannot fail");
            let sort_u = ctx.scratch.expr_sort(base, u).expect("sort");
            let ty = type_sort(ctx);
            let (m_a, _) = fresh_mvar(ctx, ty);
            let goal = ctx.scratch.expr_app(base, sort_u, m_a).expect("app");

            let key = ctx.normalize_goal_key(goal).unwrap();

            let name0 = tc_name(ctx, 0);
            let base = Some(ctx.view.store);
            let expected_sort = ctx.scratch.expr_sort(base, zero).expect("sort");
            let expected_fvar = ctx.scratch.expr_fvar(base, Some(name0)).expect("fvar");
            let expected = ctx
                .scratch
                .expr_app(base, expected_sort, expected_fvar)
                .expect("app");

            assert_eq!(key, GoalKey(expected));
        });
    }

    /// Step-1 brief test: pure table mechanics, no `MetaCtx` at all.
    #[test]
    fn adding_answer_wakes_waiters() {
        let mut st = SynthState::default();
        let key = GoalKey::for_test(1);
        st.new_entry(key);
        st.add_waiter(&key, Waiter::Root);
        let woken = st.add_answer(&key, Answer::for_test());
        assert_eq!(woken, vec![Waiter::Root]);
    }

    /// A duplicate answer (same `result_type`) wakes nobody and is not
    /// stored twice -- `SynthState::add_answer`'s `isNewAnswer` dedup
    /// (oracle: `SynthInstance.lean:441-449`).
    #[test]
    fn duplicate_answer_wakes_nobody() {
        let mut st = SynthState::default();
        let key = GoalKey::for_test(2);
        st.new_entry(key);
        st.add_waiter(&key, Waiter::Root);
        let first = st.add_answer(&key, Answer::for_test());
        assert_eq!(first, vec![Waiter::Root]);
        let second = st.add_answer(&key, Answer::for_test());
        assert_eq!(second, Vec::<Waiter>::new());
        assert_eq!(st.answers.get(&key).unwrap().answers.len(), 1);
    }
}
